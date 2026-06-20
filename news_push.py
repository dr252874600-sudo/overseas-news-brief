from __future__ import annotations

import argparse
import datetime as dt
import email.utils
import hashlib
import html
import html.parser
import http.client
import json
import os
import re
import shutil
import smtplib
import sqlite3
import subprocess
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field
from email.message import EmailMessage
from pathlib import Path
from typing import Any

try:
    import winreg
except ImportError:
    winreg = None


USER_AGENT = "PersonalOverseasNewsDigest/0.1"
ROOT = Path(__file__).resolve().parent
DB_PATH = ROOT / "news.db"
ENV_PATH = ROOT / ".env"
REPORTS_DIR = ROOT / "reports"
SHELLCRASH_API = "http://192.168.50.1:9999"
MORNING_SCHEDULES = frozenset(
    {
        "50 23 * * *",
        "5,20,35,50 0,1,2,3 * * *",
    }
)
EVENING_SCHEDULES = frozenset(
    {
        "50 9 * * *",
        "5,20,35,50 10,11,12,13,14 * * *",
    }
)


@dataclass
class Article:
    source: str
    title: str
    url: str
    published: dt.datetime
    summary: str = ""
    public_text: str = ""
    topics: list[str] = field(default_factory=list)
    score: float = 0.0
    zh_title: str = ""
    short_summary: str = ""
    zh_summary: str = ""
    en_summary: str = ""
    why_it_matters: str = ""

    @property
    def primary_category(self) -> str:
        priority = [
            "steel_chain",
            "overseas_china_major",
            "finance_business",
            "international_politics",
        ]
        return next((topic for topic in priority if topic in self.topics), "daily_focus")

    @property
    def article_id(self) -> str:
        raw = f"{self.source}|{self.url}|{self.title}".encode("utf-8")
        return hashlib.sha256(raw).hexdigest()


class ParagraphExtractor(html.parser.HTMLParser):
    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.in_paragraph = False
        self.skip_depth = 0
        self.current: list[str] = []
        self.paragraphs: list[str] = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        if tag in {"script", "style", "nav", "footer", "header", "aside", "form"}:
            self.skip_depth += 1
        if tag == "p" and self.skip_depth == 0:
            self.in_paragraph = True
            self.current = []

    def handle_endtag(self, tag: str) -> None:
        if tag == "p" and self.in_paragraph:
            text = clean_text("".join(self.current))
            if len(text) >= 45:
                self.paragraphs.append(text)
            self.in_paragraph = False
            self.current = []
        if tag in {"script", "style", "nav", "footer", "header", "aside", "form"}:
            self.skip_depth = max(0, self.skip_depth - 1)

    def handle_data(self, data: str) -> None:
        if self.in_paragraph and self.skip_depth == 0:
            self.current.append(data)


def utc_now() -> dt.datetime:
    return dt.datetime.now(dt.timezone.utc)


def local_now() -> dt.datetime:
    return dt.datetime.now().astimezone()


def load_local_env() -> None:
    if not ENV_PATH.exists():
        return
    for raw_line in ENV_PATH.read_text(encoding="utf-8-sig").splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        name, value = line.split("=", 1)
        os.environ.setdefault(name.strip(), value.strip())
    if not os.environ.get("HTTPS_PROXY"):
        try:
            with winreg.OpenKey(
                winreg.HKEY_CURRENT_USER,
                r"Software\Microsoft\Windows\CurrentVersion\Internet Settings",
            ) as key:
                enabled, _ = winreg.QueryValueEx(key, "ProxyEnable")
                proxy, _ = winreg.QueryValueEx(key, "ProxyServer")
            if enabled and proxy:
                proxy_url = proxy if "://" in proxy else f"http://{proxy}"
                os.environ["HTTP_PROXY"] = proxy_url
                os.environ["HTTPS_PROXY"] = proxy_url
        except OSError:
            pass


def current_windows_proxy() -> str:
    if winreg is None:
        return ""
    try:
        with winreg.OpenKey(
            winreg.HKEY_CURRENT_USER,
            r"Software\Microsoft\Windows\CurrentVersion\Internet Settings",
        ) as key:
            enabled, _ = winreg.QueryValueEx(key, "ProxyEnable")
            proxy, _ = winreg.QueryValueEx(key, "ProxyServer")
        if enabled and proxy:
            return proxy if "://" in proxy else f"http://{proxy}"
    except OSError:
        return ""
    return ""


def ensure_shellcrash_node() -> None:
    if os.environ.get("DISABLE_SHELLCRASH_CHECK", "").lower() in {"1", "true", "yes"}:
        return
    local_proxy = current_windows_proxy()
    if local_proxy and (
        "127.0.0.1" in local_proxy
        or "localhost" in local_proxy.lower()
    ):
        print(f"检测到本机代理，优先使用当前网络：{local_proxy}", flush=True)
        return

    api = os.environ.get("SHELLCRASH_API", SHELLCRASH_API).rstrip("/")
    opener = urllib.request.build_opener(urllib.request.ProxyHandler({}))
    try:
        with opener.open(f"{api}/proxies", timeout=8) as response:
            payload = json.loads(response.read().decode("utf-8"))
    except Exception as error:
        print(f"[warn] ShellCrash status unavailable: {error}", file=sys.stderr)
        return

    proxies = payload.get("proxies", {})
    groups = [
        (name, item)
        for name, item in proxies.items()
        if item.get("type") == "Selector" and len(item.get("all", [])) >= 10
        and name != "GLOBAL"
    ]
    if not groups:
        return
    group_name, group = max(groups, key=lambda pair: len(pair[1].get("all", [])))
    current_name = group.get("now", "")
    current = proxies.get(current_name, {})

    supported_markers = ("JP", "日", "US", "美")
    current_supported = any(marker in current_name for marker in supported_markers)
    if current.get("alive") is True and current_supported:
        return

    excluded_markers = ("剩余", "距离", "套餐", "更新订阅", "近期")
    region_priority = {
        "JP": 0,
        "日": 0,
        "US": 1,
        "美": 1,
    }
    candidates: list[tuple[int, int, str]] = []
    for name in group.get("all", []):
        item = proxies.get(name, {})
        if item.get("alive") is not True:
            continue
        if any(marker in name for marker in excluded_markers):
            continue
        priorities = [
            priority for marker, priority in region_priority.items() if marker in name
        ]
        if not priorities:
            continue
        history = item.get("history") or []
        delay = history[-1].get("delay", 9999) if history else 9999
        if not isinstance(delay, int) or delay <= 0 or delay > 2000:
            continue
        candidates.append((min(priorities), delay, name))
    if not candidates:
        print("[warn] ShellCrash has no healthy Gemini-compatible node.", file=sys.stderr)
        return

    _, _, selected = min(candidates)
    if selected == current_name:
        return
    endpoint = f"{api}/proxies/{urllib.parse.quote(group_name, safe='')}"
    result = subprocess.run(
        [
            "curl.exe",
            "--silent",
            "--show-error",
            "--fail",
            "--request",
            "PUT",
            "--header",
            "Content-Type: application/json",
            "--data-binary",
            json.dumps({"name": selected}, ensure_ascii=False),
            endpoint,
        ],
        capture_output=True,
        timeout=15,
    )
    if result.returncode != 0:
        print(
            f"[warn] ShellCrash node switch failed: "
            f"{result.stderr.decode('utf-8', errors='replace')[:200]}",
            file=sys.stderr,
        )
        return
    print(f"ShellCrash节点已自动切换为：{selected}", flush=True)
    time.sleep(2)


def request_bytes(url: str, *, timeout: int = 6, attempts: int = 3) -> bytes:
    for attempt in range(1, attempts + 1):
        request = urllib.request.Request(
            url,
            headers={
                "User-Agent": USER_AGENT,
                "Accept": "application/json, application/xml, text/xml, */*",
            },
        )
        try:
            with urllib.request.urlopen(request, timeout=timeout) as response:
                return response.read()
        except (
            urllib.error.URLError,
            TimeoutError,
            http.client.RemoteDisconnected,
        ):
            if attempt == attempts:
                raise
            time.sleep(attempt * 2)
    raise RuntimeError("Request failed.")


def post_json(
    url: str,
    payload: dict[str, Any],
    headers: dict[str, str],
    *,
    attempts: int = 3,
) -> dict[str, Any]:
    body = json.dumps(payload, ensure_ascii=False).encode("utf-8")
    for attempt in range(1, attempts + 1):
        rate_limited = False
        request = urllib.request.Request(
            url,
            data=body,
            method="POST",
            headers={"Content-Type": "application/json", "User-Agent": USER_AGENT, **headers},
        )
        try:
            with urllib.request.urlopen(request, timeout=90) as response:
                return json.loads(response.read().decode("utf-8"))
        except urllib.error.HTTPError as error:
            rate_limited = error.code == 429
            if error.code != 429 and error.code < 500:
                raise
            if attempt == attempts:
                raise
        except (urllib.error.URLError, TimeoutError, http.client.RemoteDisconnected):
            if attempt == attempts:
                raise
        print(f"网络连接或接口额度暂时受限，正在进行第{attempt + 1}次尝试...", flush=True)
        delay = min(90, attempt * 20) if rate_limited else attempt * 5
        time.sleep(delay)
    raise RuntimeError("请求失败。")


def clean_text(value: str | None) -> str:
    if not value:
        return ""
    value = re.sub(r"<[^>]+>", " ", html.unescape(value))
    return re.sub(r"\s+", " ", value).strip()


def parse_date(value: str | None) -> dt.datetime:
    if not value:
        return utc_now()
    try:
        parsed = email.utils.parsedate_to_datetime(value)
        if parsed.tzinfo is None:
            parsed = parsed.replace(tzinfo=dt.timezone.utc)
        return parsed.astimezone(dt.timezone.utc)
    except (TypeError, ValueError):
        pass
    try:
        return dt.datetime.strptime(value, "%Y%m%dT%H%M%SZ").replace(tzinfo=dt.timezone.utc)
    except ValueError:
        pass
    compact = value.replace("Z", "+00:00")
    for candidate in (compact, compact[:15]):
        try:
            parsed = dt.datetime.fromisoformat(candidate)
            if parsed.tzinfo is None:
                parsed = parsed.replace(tzinfo=dt.timezone.utc)
            return parsed.astimezone(dt.timezone.utc)
        except ValueError:
            continue
    return utc_now()


def child_text(element: ET.Element, names: tuple[str, ...]) -> str:
    for child in element.iter():
        local_name = child.tag.rsplit("}", 1)[-1].lower()
        if local_name in names and child.text:
            return child.text.strip()
    return ""


def fetch_rss(source: dict[str, Any], limit: int) -> list[Article]:
    articles: list[Article] = []
    for feed_url in source.get("feeds", []):
        try:
            root = ET.fromstring(request_bytes(feed_url))
        except (ET.ParseError, urllib.error.URLError, TimeoutError) as error:
            print(f"[warn] RSS failed: {source['name']} {feed_url}: {error}", file=sys.stderr)
            continue

        entries = [
            node for node in root.iter()
            if node.tag.rsplit("}", 1)[-1].lower() in {"item", "entry"}
        ]
        for entry in entries[:limit]:
            title = clean_text(child_text(entry, ("title",)))
            link = child_text(entry, ("link",))
            if not link:
                for child in entry:
                    if child.tag.rsplit("}", 1)[-1].lower() == "link":
                        link = child.attrib.get("href", "")
                        if link:
                            break
            summary = clean_text(child_text(entry, ("description", "summary", "content")))
            published = parse_date(child_text(entry, ("pubdate", "published", "updated", "date")))
            if title and link:
                articles.append(Article(source["name"], title, link, published, summary))
    return articles


def fetch_gdelt(source: dict[str, Any], limit: int, lookback_hours: int) -> list[Article]:
    articles: list[Article] = []
    for domain in source.get("domains", []):
        params = {
            "query": f"domain:{domain}",
            "mode": "ArtList",
            "maxrecords": str(limit),
            "format": "json",
            "sort": "HybridRel",
            "timespan": f"{lookback_hours}h",
        }
        url = "https://api.gdeltproject.org/api/v2/doc/doc?" + urllib.parse.urlencode(params)
        try:
            payload = json.loads(request_bytes(url).decode("utf-8"))
        except (json.JSONDecodeError, urllib.error.URLError, TimeoutError) as error:
            print(f"[warn] GDELT failed: {source['name']} {domain}: {error}", file=sys.stderr)
            continue
        for item in payload.get("articles", []):
            title = clean_text(item.get("title"))
            link = item.get("url", "")
            if title and link:
                articles.append(
                    Article(
                        source=source["name"],
                        title=title,
                        url=link,
                        published=parse_date(item.get("seendate")),
                    )
                )
    return articles


def fetch_gdelt_sources(
    sources: list[dict[str, Any]], limit_per_source: int, lookback_hours: int
) -> list[Article]:
    domain_to_source = {
        domain.lower(): source["name"]
        for source in sources
        for domain in source.get("domains", [])
    }
    query = " OR ".join(f"domain:{domain}" for domain in domain_to_source)
    params = {
        "query": f"({query})",
        "mode": "ArtList",
        "maxrecords": str(min(250, max(25, limit_per_source * len(sources)))),
        "format": "json",
        "sort": "HybridRel",
        "timespan": f"{lookback_hours}h",
    }
    url = "https://api.gdeltproject.org/api/v2/doc/doc?" + urllib.parse.urlencode(params)
    try:
        payload = json.loads(request_bytes(url).decode("utf-8"))
    except (json.JSONDecodeError, urllib.error.URLError, TimeoutError) as error:
        print("GDELT连接较慢，正在切换备用新闻源...", flush=True)
        return fetch_google_news_sources(sources, limit_per_source, lookback_hours)

    counts: dict[str, int] = {}
    articles: list[Article] = []
    for item in payload.get("articles", []):
        domain = str(item.get("domain", "")).lower()
        source_name = domain_to_source.get(domain)
        if not source_name:
            source_name = next(
                (name for known, name in domain_to_source.items() if domain.endswith(known)),
                None,
            )
        if not source_name or counts.get(source_name, 0) >= limit_per_source:
            continue
        title = clean_text(item.get("title"))
        link = item.get("url", "")
        if title and link:
            articles.append(
                Article(
                    source=source_name,
                    title=title,
                    url=link,
                    published=parse_date(item.get("seendate")),
                )
            )
            counts[source_name] = counts.get(source_name, 0) + 1
    return articles


def fetch_google_news_sources(
    sources: list[dict[str, Any]], limit_per_source: int, lookback_hours: int
) -> list[Article]:
    source_queries = {
        "Bloomberg": "source:Bloomberg",
        "Reuters": "source:Reuters",
        "Associated Press": 'source:"Associated Press"',
        "AFP": '(source:AFP OR source:"Agence France-Presse")',
    }
    selected = [
        source_queries[source["name"]]
        for source in sources
        if source["name"] in source_queries
    ]
    if not selected:
        return []
    query = f"({' OR '.join(selected)}) when:{max(1, lookback_hours)}h"
    params = {
        "q": query,
        "hl": "en-US",
        "gl": "US",
        "ceid": "US:en",
    }
    url = "https://news.google.com/rss/search?" + urllib.parse.urlencode(params)
    try:
        root = ET.fromstring(request_bytes(url))
    except (ET.ParseError, urllib.error.URLError, TimeoutError) as error:
        print("备用索引暂时无法连接，将继续处理其他媒体。", flush=True)
        return []

    aliases = {
        "Bloomberg": "Bloomberg",
        "Reuters": "Reuters",
        "Associated Press": "Associated Press",
        "AP News": "Associated Press",
        "AFP": "AFP",
        "Agence France-Presse": "AFP",
    }
    counts: dict[str, int] = {}
    articles: list[Article] = []
    for entry in [
        node for node in root.iter()
        if node.tag.rsplit("}", 1)[-1].lower() == "item"
    ]:
        publisher = clean_text(child_text(entry, ("source",)))
        source_name = aliases.get(publisher)
        if not source_name or counts.get(source_name, 0) >= limit_per_source:
            continue
        title = clean_text(child_text(entry, ("title",)))
        title = re.sub(rf"\s+-\s+{re.escape(publisher)}$", "", title).strip()
        link = child_text(entry, ("link",))
        if title and link:
            articles.append(
                Article(
                    source=source_name,
                    title=title,
                    url=link,
                    published=parse_date(child_text(entry, ("pubdate",))),
                    summary=clean_text(child_text(entry, ("description",))),
                )
            )
            counts[source_name] = counts.get(source_name, 0) + 1
    return articles


def fetch_google_query(source: dict[str, Any], limit: int, lookback_hours: int) -> list[Article]:
    articles: list[Article] = []
    excluded_publishers = {
        "24/7 Wall St.",
        "AOL.com",
        "Growth Dragons",
        "IndexBox",
        "simplywall.st",
    }
    per_query = max(3, limit // max(1, len(source.get("queries", []))))
    for query_text in source.get("queries", []):
        params = {
            "q": f"({query_text}) when:{max(1, lookback_hours)}h",
            "hl": "en-US",
            "gl": "US",
            "ceid": "US:en",
        }
        url = "https://news.google.com/rss/search?" + urllib.parse.urlencode(params)
        try:
            root = ET.fromstring(request_bytes(url))
        except (ET.ParseError, urllib.error.URLError, TimeoutError) as error:
            print(f"[warn] Google query failed: {source['name']}: {error}", file=sys.stderr)
            continue
        entries = [
            node for node in root.iter()
            if node.tag.rsplit("}", 1)[-1].lower() == "item"
        ]
        for entry in entries[:per_query]:
            publisher = clean_text(child_text(entry, ("source",))) or source["name"]
            if publisher in excluded_publishers:
                continue
            title = clean_text(child_text(entry, ("title",)))
            title = re.sub(rf"\s+-\s+{re.escape(publisher)}$", "", title).strip()
            link = child_text(entry, ("link",))
            if title and link:
                articles.append(
                    Article(
                        source=publisher,
                        title=title,
                        url=link,
                        published=parse_date(child_text(entry, ("pubdate",))),
                        summary=clean_text(child_text(entry, ("description",))),
                    )
                )
    return articles


def json_ld_article_body(page_html: str) -> str:
    bodies: list[str] = []
    for match in re.finditer(
        r'<script[^>]+type=["\']application/ld\+json["\'][^>]*>(.*?)</script>',
        page_html,
        flags=re.IGNORECASE | re.DOTALL,
    ):
        try:
            payload = json.loads(html.unescape(match.group(1)).strip())
        except (json.JSONDecodeError, TypeError):
            continue
        stack = payload if isinstance(payload, list) else [payload]
        while stack:
            item = stack.pop()
            if isinstance(item, list):
                stack.extend(item)
            elif isinstance(item, dict):
                body = item.get("articleBody")
                if isinstance(body, str) and len(body) > 200:
                    bodies.append(clean_text(body))
                graph = item.get("@graph")
                if isinstance(graph, list):
                    stack.extend(graph)
    return max(bodies, key=len, default="")


def fetch_public_article_text(article: Article) -> str:
    try:
        raw = request_bytes(article.url, timeout=10)
        page_html = raw.decode("utf-8", errors="replace")
    except (urllib.error.URLError, TimeoutError, ValueError):
        return ""

    body = json_ld_article_body(page_html)
    if len(body) >= 400:
        return body[:12000]

    extractor = ParagraphExtractor()
    try:
        extractor.feed(page_html)
    except Exception:
        return ""
    seen: set[str] = set()
    paragraphs: list[str] = []
    for paragraph in extractor.paragraphs:
        normalized = re.sub(r"\W+", "", paragraph.lower())
        if normalized in seen:
            continue
        seen.add(normalized)
        paragraphs.append(paragraph)
        if sum(len(item) for item in paragraphs) >= 12000:
            break
    return "\n\n".join(paragraphs)


def enrich_articles(articles: list[Article]) -> None:
    print("正在读取可公开访问的报道正文，以生成完整事件简报...", flush=True)
    with ThreadPoolExecutor(max_workers=min(8, len(articles))) as executor:
        futures = {
            executor.submit(fetch_public_article_text, article): article
            for article in articles
        }
        for future in as_completed(futures):
            article = futures[future]
            try:
                article.public_text = future.result()
            except Exception:
                article.public_text = ""
    available = sum(1 for article in articles if len(article.public_text) >= 400)
    print(f"已取得 {available}/{len(articles)} 篇报道的公开正文或较完整公开文本。", flush=True)


def classify_and_rank(article: Article, topics: dict[str, list[str]]) -> None:
    haystack = f" {article.title} {article.summary} ".lower()
    matches = []
    for topic, keywords in topics.items():
        if any(
            re.search(
                rf"(?<!\w){re.escape(keyword.strip().lower())}(?!\w)",
                haystack,
                flags=re.IGNORECASE,
            )
            for keyword in keywords
        ):
            matches.append(topic)
    article.topics = matches

    age_hours = max(0.0, (utc_now() - article.published).total_seconds() / 3600)
    freshness = max(0.0, 8.0 - min(age_hours, 8.0))
    article.score = freshness + min(len(matches), 3) * 4
    if "overseas_china_major" in matches:
        article.score += 3
    trusted_sources = {
        "BBC",
        "Bloomberg",
        "Reuters",
        "Associated Press",
        "AP News",
        "AFP",
        "The New York Times",
        "The Wall Street Journal",
        "Al Jazeera",
        "Financial Times",
        "CNBC",
        "Yahoo Finance",
        "S&P Global",
        "Fastmarkets",
        "Argus Media",
    }
    if article.source in trusted_sources:
        article.score += 3


def init_db() -> sqlite3.Connection:
    connection = sqlite3.connect(DB_PATH)
    connection.execute(
        """
        CREATE TABLE IF NOT EXISTS pushed_articles (
            article_id TEXT PRIMARY KEY,
            source TEXT NOT NULL,
            title TEXT NOT NULL,
            url TEXT NOT NULL,
            pushed_at TEXT NOT NULL
        )
        """
    )
    connection.execute(
        """
        CREATE TABLE IF NOT EXISTS sent_slots (
            slot_id TEXT PRIMARY KEY,
            sent_at TEXT NOT NULL
        )
        """
    )
    return connection


def slot_from_schedule_trigger(now: dt.datetime | None = None) -> str | None:
    """Return the intended delivery slot for a GitHub cron trigger.

    GitHub can start scheduled jobs hours late. The cron expression is more
    trustworthy than the runner's actual start time for deciding whether the
    run belongs to the morning or evening brief.
    """
    now = now or local_now()
    schedule = os.getenv("BRIEF_SCHEDULE_CRON", "").strip()
    date = now.date()
    if schedule in MORNING_SCHEDULES:
        return f"{date.isoformat()}-am"
    if schedule in EVENING_SCHEDULES:
        # A delayed evening job may begin after midnight. It still belongs to
        # the previous calendar day's evening brief.
        if now.hour < 8:
            date -= dt.timedelta(days=1)
        return f"{date.isoformat()}-pm"
    return None


def current_schedule_slot(now: dt.datetime | None = None) -> str | None:
    now = now or local_now()
    minutes = now.hour * 60 + now.minute
    date = now.strftime("%Y-%m-%d")
    # Fallback for an older queued GitHub job that lacks its original cron
    # expression. Prefer a late brief over silently skipping it.
    if minutes <= 15 * 60 + 30:
        return f"{date}-am"
    if minutes <= 23 * 60 + 59:
        return f"{date}-pm"
    return None


def is_slot_sent(connection: sqlite3.Connection, slot_id: str) -> bool:
    row = connection.execute(
        "SELECT 1 FROM sent_slots WHERE slot_id = ?", (slot_id,)
    ).fetchone()
    return row is not None


def mark_slot_sent(connection: sqlite3.Connection, slot_id: str) -> None:
    connection.execute(
        """
        INSERT OR IGNORE INTO sent_slots(slot_id, sent_at)
        VALUES (?, ?)
        """,
        (slot_id, utc_now().isoformat()),
    )
    connection.commit()


def scheduled_slot_to_run(connection: sqlite3.Connection) -> str | None:
    slot_id = slot_from_schedule_trigger() or current_schedule_slot()
    if not slot_id:
        print("当前不在上午或下午发送窗口内，本次云端检查跳过。")
        return None
    if is_slot_sent(connection, slot_id):
        print(f"{slot_id} 已经成功发送过，本次云端检查跳过。")
        return None
    print(f"{slot_id} 尚未成功发送，开始补发本档简报。")
    return slot_id


def is_pushed(connection: sqlite3.Connection, article: Article) -> bool:
    row = connection.execute(
        "SELECT 1 FROM pushed_articles WHERE article_id = ?", (article.article_id,)
    ).fetchone()
    return row is not None


def mark_pushed(connection: sqlite3.Connection, articles: list[Article]) -> None:
    connection.executemany(
        """
        INSERT OR IGNORE INTO pushed_articles(article_id, source, title, url, pushed_at)
        VALUES (?, ?, ?, ?, ?)
        """,
        [
            (article.article_id, article.source, article.title, article.url, utc_now().isoformat())
            for article in articles
        ],
    )
    connection.commit()


def extract_response_text(payload: dict[str, Any]) -> str:
    if isinstance(payload.get("output_text"), str):
        return payload["output_text"]
    chunks: list[str] = []
    for output in payload.get("output", []):
        for content in output.get("content", []):
            text = content.get("text")
            if isinstance(text, str):
                chunks.append(text)
    return "\n".join(chunks)


def translation_input(articles: list[Article]) -> tuple[list[dict[str, Any]], str]:
    compact = [
        {
            "id": index,
            "source": article.source,
            "title": article.title,
            "public_excerpt": article.summary[:1200],
            "public_article_text": article.public_text[:6000],
            "topics": article.topics,
        }
        for index, article in enumerate(articles)
    ]
    instructions = (
        "You are an exacting bilingual intelligence brief editor. Return only a JSON array. "
        "For every input item return id, zh_title, short_summary, zh_summary, en_summary, "
        "and why_it_matters. short_summary should be a factual 80-140 Chinese character overview "
        "that captures the event, main actors, most important figure or change, and immediate meaning. "
        "This is not a teaser or short abstract. The reader should understand the report without "
        "opening the source page. The Chinese brief should normally be 400-700 Chinese characters "
        "when enough public text is supplied. Organize it as readable prose covering: background and "
        "context; latest development; named people, companies, countries and institutions; dates, "
        "prices, percentages or other key figures; stated reasons and positions from different sides; "
        "what changed from before; likely implications; and important uncertainties or next steps. "
        "The English brief should faithfully cover the same core information in 150-250 words. "
        "Use only facts in public_excerpt and public_article_text. Never invent context, numbers, "
        "quotes, causes, market reactions or forecasts. If the public material is incomplete, state "
        "exactly which important details are unavailable instead of padding the answer. Paraphrase "
        "rather than reproducing long source passages. Translate into Simplified Chinese without "
        "censorship or sensationalism. why_it_matters should be a neutral work/investment relevance "
        "assessment of 60-120 Chinese characters and must distinguish fact from inference."
    )
    return compact, instructions


def parse_json_array(text: str) -> list[dict[str, Any]]:
    text = text.strip()
    if text.startswith("```"):
        text = re.sub(r"^```(?:json)?\s*|\s*```$", "", text, flags=re.DOTALL)
    return json.loads(text)


def apply_translations(articles: list[Article], translated: list[dict[str, Any]]) -> None:
    by_id = {int(item["id"]): item for item in translated}
    for index, article in enumerate(articles):
        item = by_id.get(index, {})
        article.zh_title = clean_text(item.get("zh_title"))
        article.short_summary = clean_text(item.get("short_summary"))
        article.zh_summary = clean_text(item.get("zh_summary"))
        article.en_summary = clean_text(item.get("en_summary"))
        article.why_it_matters = clean_text(item.get("why_it_matters"))


def validate_brief_quality(articles: list[Article]) -> None:
    incomplete: list[str] = []
    for article in articles:
        if (
            not article.zh_title
            or len(article.short_summary) < 45
            or len(article.zh_summary) < 180
            or len(article.en_summary.split()) < 70
        ):
            incomplete.append(article.title)
    if incomplete:
        raise RuntimeError(
            f"{len(incomplete)}/{len(articles)} articles lack complete bilingual coverage."
        )


def has_chinese(text: str) -> bool:
    return bool(re.search(r"[\u4e00-\u9fff]", text))


def free_translate_to_chinese(text: str, *, limit: int = 1200) -> str:
    text = clean_text(text)
    if not text:
        return ""
    if has_chinese(text):
        return text[:limit]
    query = urllib.parse.urlencode(
        {
            "client": "gtx",
            "sl": "auto",
            "tl": "zh-CN",
            "dt": "t",
            "q": text[:limit],
        }
    )
    try:
        raw = request_bytes(
            f"https://translate.googleapis.com/translate_a/single?{query}",
            timeout=20,
            attempts=2,
        )
        payload = json.loads(raw.decode("utf-8"))
        translated = "".join(
            part[0]
            for part in payload[0]
            if isinstance(part, list) and part and isinstance(part[0], str)
        )
        return clean_text(translated)
    except Exception:
        return ""


def fallback_reason(topic: str) -> str:
    reasons = {
        "international_politics": "该事项可能影响地缘局势、外交判断或相关大宗商品风险，后续需结合更多报道继续跟踪。",
        "finance_business": "该事项可能影响相关市场、行业或重点公司情绪，适合作为投资观察线索而非直接投资建议。",
        "steel_chain": "该事项与钢厂生产、原料成本、钢材价格或进出口环境相关，适合纳入产业链日常观察。",
        "overseas_china_major": "该事项属于海外媒体关注的涉华议题，公开材料仍需进一步交叉核实。",
    }
    return reasons.get(topic, "该事项具有持续跟踪价值，公开材料有限时需等待更多来源确认。")


def article_public_material(article: Article, *, limit: int = 1600) -> str:
    parts = [article.summary, article.public_text]
    material = clean_text(" ".join(part for part in parts if part))
    return material[:limit]


def build_fallback_brief(articles: list[Article]) -> list[Article]:
    fallback_articles: list[Article] = []
    for article in articles[:18]:
        section = article.primary_category
        material = article_public_material(article)
        zh_title = free_translate_to_chinese(article.title, limit=220) or article.title
        zh_material = free_translate_to_chinese(material, limit=1200)
        if zh_material:
            zh_summary = (
                "接口限流保底版：以下内容依据公开标题、RSS摘要或可访问正文片段生成。"
                + zh_material
            )
        else:
            zh_summary = (
                "接口限流保底版：本条暂时无法完成机器翻译，先保留公开英文信息，避免漏发。"
                f"英文标题：{article.title}。"
            )
            if material:
                zh_summary += f"公开摘要：{material[:900]}"
        short_summary = zh_summary[:160]
        en_summary = material or article.title
        fallback_articles.append(
            Article(
                source=article.source,
                title=article.title,
                url=article.url,
                published=article.published,
                summary=short_summary,
                public_text=article.public_text,
                topics=[section],
                score=article.score,
                zh_title=zh_title,
                short_summary=short_summary,
                zh_summary=zh_summary,
                en_summary=en_summary[:1800],
                why_it_matters=fallback_reason(section),
            )
        )
    return fallback_articles


def event_brief_input(articles: list[Article]) -> tuple[list[dict[str, Any]], str]:
    compact = [
        {
            "id": index,
            "source": article.source,
            "title": article.title,
            "url": article.url,
            "published": article.published.isoformat(),
            "public_excerpt": article.summary[:700],
            "public_article_text": article.public_text[:2200],
            "topics": article.topics,
        }
        for index, article in enumerate(articles)
    ]
    instructions = (
        "You are the chief editor of a bilingual daily intelligence brief. Return only a JSON "
        "array. Do not produce one output per article. Cluster reports about the same event into "
        "one event and remove repetition. Each output object must contain: member_ids (input IDs), "
        "section, zh_title, short_summary, zh_summary, en_summary, and why_it_matters. section must "
        "be one of international_politics, finance_business, steel_chain, overseas_china_major. "
        "Select 3-5 major international-political events when enough material exists. For a major "
        "continuing event such as a Middle East war or US-Iran negotiations, use one broad event "
        "headline and organize zh_summary as clearly labeled paragraphs such as '局势概览：', "
        "'美国动态：', '以色列动态：', '伊朗动态：', '关键人物发言：', and '下一步观察：'. "
        "Only include labels supported by the supplied reporting. Finance and business combines "
        "A-shares, Hong Kong and US markets, major companies, important industries, technology and "
        "AI. Select 3-5 major market or industry events when enough material exists and likewise "
        "break each one into concrete "
        "subtopics such as market move, company action, industry impact and numbers. Steel-chain "
        "coverage should normally contain 2-4 events and must prioritize Chinese steel mills, "
        "production and inventory changes, iron ore, "
        "coking coal, coke, scrap and Chinese finished-steel prices. International steel news is "
        "included mainly when it directly affects Chinese imports, exports, tariffs or trade flows. "
        "overseas_china_major is exceptional, not routine China coverage: include it only when an "
        "overseas outlet gives major prominence to a consequential China-related matter that is "
        "unlikely to be substantially covered by domestic mainstream media. Do not infer domestic "
        "non-coverage from sensitive subject matter alone; say when that comparison cannot be "
        "verified. short_summary must be 90-160 Chinese characters. zh_summary should normally be "
        "500-900 Chinese characters for a well-sourced event and must include concrete actors, "
        "positions, dates, figures, disagreements and uncertainties. en_summary should cover the "
        "same facts in 180-300 English words. Use only supplied facts, distinguish facts from "
        "inference, and explicitly state missing information. Prefer two or more credible sources "
        "for a merged event, but retain an important single-source event when justified."
    )
    return compact, instructions


def apply_event_brief(
    articles: list[Article], editorial: list[dict[str, Any]]
) -> list[Article]:
    events: list[Article] = []
    valid_sections = {
        "international_politics",
        "finance_business",
        "steel_chain",
        "overseas_china_major",
    }
    for item in editorial:
        member_ids = [
            int(value)
            for value in item.get("member_ids", [])
            if str(value).isdigit() and 0 <= int(value) < len(articles)
        ]
        if not member_ids:
            continue
        members = [articles[index] for index in member_ids]
        representative = max(members, key=lambda article: article.score)
        sources = list(dict.fromkeys(article.source for article in members))
        section = clean_text(item.get("section"))
        if section not in valid_sections:
            section = representative.primary_category
        events.append(
            Article(
                source="、".join(sources[:4]),
                title=representative.title,
                url=representative.url,
                published=max(article.published for article in members),
                summary=clean_text(item.get("short_summary")),
                public_text="\n\n".join(article.public_text for article in members),
                topics=[section],
                score=max(article.score for article in members),
                zh_title=clean_text(item.get("zh_title")),
                short_summary=clean_text(item.get("short_summary")),
                zh_summary=clean_text(item.get("zh_summary")),
                en_summary=clean_text(item.get("en_summary")),
                why_it_matters=clean_text(item.get("why_it_matters")),
            )
        )
    validate_brief_quality(events)
    return events


def build_event_brief_batch(articles: list[Article]) -> list[Article]:
    compact, instructions = event_brief_input(articles)
    gemini_key = os.environ.get("GEMINI_API_KEY")
    if gemini_key:
        model = os.environ.get("GEMINI_MODEL", "gemini-2.5-flash-lite")
        url = (
            f"https://generativelanguage.googleapis.com/v1beta/models/{model}:generateContent?"
            + urllib.parse.urlencode({"key": gemini_key})
        )
        payload = post_json(
            url,
            {
                "system_instruction": {"parts": [{"text": instructions}]},
                "contents": [
                    {
                        "role": "user",
                        "parts": [{"text": json.dumps(compact, ensure_ascii=False)}],
                    }
                ],
                "generationConfig": {
                    "responseMimeType": "application/json",
                    "temperature": 0.1,
                    "maxOutputTokens": 8192,
                },
            },
            {},
            attempts=4,
        )
        text = payload["candidates"][0]["content"]["parts"][0]["text"]
        return apply_event_brief(articles, parse_json_array(text))
    openai_key = os.environ.get("OPENAI_API_KEY")
    if openai_key:
        payload = post_json(
            "https://api.openai.com/v1/responses",
            {
                "model": os.environ.get("OPENAI_MODEL", "gpt-4.1-mini"),
                "instructions": instructions,
                "input": json.dumps(compact, ensure_ascii=False),
                "max_output_tokens": 12000,
            },
            {"Authorization": f"Bearer {openai_key}"},
        )
        return apply_event_brief(
            articles, parse_json_array(extract_response_text(payload))
        )
    raise RuntimeError("No editorial API key is configured.")


def build_event_brief(articles: list[Article]) -> list[Article]:
    section_order = [
        "international_politics",
        "finance_business",
        "steel_chain",
        "overseas_china_major",
    ]
    section_limits = {
        "international_politics": 6,
        "finance_business": 6,
        "steel_chain": 4,
        "overseas_china_major": 2,
    }
    events: list[Article] = []
    used_ids: set[str] = set()
    for section in section_order:
        batch = [
            article
            for article in articles
            if section in article.topics and article.article_id not in used_ids
        ]
        if not batch:
            continue
        # Keep requests few enough for free-tier limits while preserving category coverage.
        limit = min(len(batch), section_limits.get(section, 4))
        for start in range(0, limit, 6):
            chunk = batch[start : start + 6]
            section_events = build_event_brief_batch(chunk)
            events.extend(section_events)
            used_ids.update(article.article_id for article in chunk)
            time.sleep(int(os.environ.get("EDITORIAL_API_PAUSE_SECONDS", "20")))
    if not events:
        raise RuntimeError("No complete event briefs were generated.")
    return events


def translate_with_openai(articles: list[Article], api_key: str) -> None:
    for start in range(0, len(articles), 4):
        batch = articles[start : start + 4]
        compact, instructions = translation_input(batch)
        payload = post_json(
            "https://api.openai.com/v1/responses",
            {
                "model": os.environ.get("OPENAI_MODEL", "gpt-4.1-mini"),
                "instructions": instructions,
                "input": json.dumps(compact, ensure_ascii=False),
            },
            {"Authorization": f"Bearer {api_key}"},
        )
        apply_translations(batch, parse_json_array(extract_response_text(payload)))


def translate_with_gemini(articles: list[Article], api_key: str) -> None:
    model = os.environ.get("GEMINI_MODEL", "gemini-2.5-flash-lite")
    url = (
        f"https://generativelanguage.googleapis.com/v1beta/models/{model}:generateContent?"
        + urllib.parse.urlencode({"key": api_key})
    )
    for start in range(0, len(articles), 4):
        batch = articles[start : start + 4]
        compact, instructions = translation_input(batch)
        payload = post_json(
            url,
            {
                "system_instruction": {"parts": [{"text": instructions}]},
                "contents": [
                    {
                        "role": "user",
                        "parts": [{"text": json.dumps(compact, ensure_ascii=False)}],
                    }
                ],
                "generationConfig": {
                    "responseMimeType": "application/json",
                    "temperature": 0.1,
                    "maxOutputTokens": 8192,
                },
            },
            {},
        )
        text = payload["candidates"][0]["content"]["parts"][0]["text"]
        apply_translations(batch, parse_json_array(text))


def translate_articles(articles: list[Article]) -> None:
    if not articles:
        return
    gemini_key = os.environ.get("GEMINI_API_KEY")
    if gemini_key:
        print("正在使用 Gemini 免费额度翻译...", flush=True)
        translate_with_gemini(articles, gemini_key)
        validate_brief_quality(articles)
        return
    openai_key = os.environ.get("OPENAI_API_KEY")
    if openai_key:
        translate_with_openai(articles, openai_key)
        validate_brief_quality(articles)
        return
    print("尚未设置翻译密钥，将显示英文内容。", file=sys.stderr)


def format_digest(articles: list[Article]) -> str:
    local_now = dt.datetime.now().astimezone()
    lines = [f"# 海外媒体头条 {local_now:%m-%d %H:%M}", ""]
    topic_names = {
        "international_politics": "国际政治",
        "finance_business": "财经新闻",
        "steel_chain": "钢铁产业链",
        "overseas_china_major": "海外涉华重大报道",
    }
    for index, article in enumerate(articles, start=1):
        title = article.zh_title or article.title
        labels = " / ".join(topic_names.get(topic, topic) for topic in article.topics)
        lines.extend(
            [
                f"**{index}. [{title}]({article.url})**",
                f"> {article.source}" + (f" · {labels}" if labels else ""),
                article.zh_summary or article.summary[:240] or "暂无摘要，请打开原文查看。",
            ]
        )
        if article.why_it_matters:
            lines.append(f"关注点：{article.why_it_matters}")
        lines.extend([f"英文：{article.title}", ""])
    return "\n".join(lines).strip()


def report_sections(articles: list[Article]) -> list[tuple[str, list[Article]]]:
    labels = [
        ("international_politics", "国际政治与地缘局势"),
        ("finance_business", "财经新闻"),
        ("steel_chain", "钢铁产业链"),
        ("overseas_china_major", "海外涉华重大报道"),
    ]
    sections: list[tuple[str, list[Article]]] = []
    for key, label in labels:
        items = [article for article in articles if article.primary_category == key]
        if items:
            sections.append((label, items))
    return sections


def format_summary_html(text: str) -> str:
    escaped = html.escape(text)
    labels = [
        "局势概览",
        "市场概览",
        "美国动态",
        "以色列动态",
        "伊朗动态",
        "中国动态",
        "钢厂动态",
        "原料价格",
        "钢材价格",
        "进出口动态",
        "公司动态",
        "行业影响",
        "关键人物发言",
        "关键数据",
        "下一步观察",
    ]
    for label in labels:
        escaped = re.sub(
            rf"\s*{re.escape(label)}：\s*",
            f'<br><strong class="detail-label">{label}：</strong> ',
            escaped,
        )
    return escaped.removeprefix("<br>")


def render_report_html(articles: list[Article]) -> str:
    now = dt.datetime.now().astimezone()
    summary_items = "".join(
        (
            f'<li><strong>{html.escape(article.zh_title or article.title)}</strong>'
            f'<span>{html.escape((article.short_summary or article.zh_summary or article.summary or "公开信息有限。")[:220])}</span></li>'
        )
        for article in articles
    )
    section_html: list[str] = []
    for section_name, items in report_sections(articles):
        entries: list[str] = []
        for index, article in enumerate(items, start=1):
            published = article.published.astimezone().strftime("%Y-%m-%d %H:%M")
            zh_summary = article.zh_summary or article.summary or "公开信息有限，暂无详细摘要。"
            en_summary = article.en_summary or article.summary or "Limited public excerpt available."
            entries.append(
                f"""
                <article class="story">
                  <div class="story-number">{index:02d}</div>
                  <div class="story-body">
                    <h3>{html.escape(article.zh_title or article.title)}</h3>
                    <div class="english-title">{html.escape(article.title)}</div>
                    <div class="meta">{html.escape(article.source)} · {published}</div>
                    <div class="summary zh"><strong>详细中文报道</strong><p>{format_summary_html(zh_summary)}</p></div>
                    <div class="summary en"><strong>Detailed English brief</strong><p>{html.escape(en_summary)}</p></div>
                    <div class="relevance"><strong>关注点</strong> {html.escape(article.why_it_matters or "供工作与市场观察参考。")}</div>
                    <a class="source-link" href="{html.escape(article.url, quote=True)}">查看原始报道</a>
                  </div>
                </article>
                """
            )
        section_html.append(
            f'<section><h2>{html.escape(section_name)}</h2>{"".join(entries)}</section>'
        )

    return f"""<!doctype html>
<html lang="zh-CN">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>海外新闻与产业简报 {now:%Y-%m-%d}</title>
<style>
  * {{ box-sizing: border-box; }}
  body {{ margin:0; background:#f3f5f7; color:#17202a; font-family:"Microsoft YaHei","PingFang SC",Arial,sans-serif; line-height:1.75; }}
  .page {{ max-width:820px; margin:0 auto; background:#fff; }}
  header {{ padding:38px 42px 28px; border-top:6px solid #b42318; border-bottom:1px solid #d9dee3; }}
  .kicker {{ color:#b42318; font-size:13px; font-weight:700; }}
  h1 {{ margin:6px 0 4px; font-size:30px; letter-spacing:0; }}
  .date {{ color:#667085; font-size:14px; }}
  .intro {{ margin:0; padding:20px 42px; background:#f8fafc; color:#475467; font-size:14px; }}
  .overview {{ margin:0; padding:24px 42px 20px; background:#fff7ed; border-bottom:1px solid #fed7aa; }}
  .overview h2 {{ border:0; padding:0; margin-bottom:12px; font-size:18px; }}
  .overview ol {{ margin:0; padding-left:22px; }}
  .overview li {{ padding:7px 0; }}
  .overview span {{ display:block; margin-top:2px; color:#667085; font-size:13px; line-height:1.65; }}
  section {{ padding:26px 42px 10px; }}
  h2 {{ margin:0; padding-bottom:9px; border-bottom:2px solid #17202a; font-size:21px; }}
  .story {{ display:flex; gap:18px; padding:24px 0; border-bottom:1px solid #e4e7ec; }}
  .story-number {{ flex:0 0 34px; color:#b42318; font-size:15px; font-weight:700; }}
  .story-body {{ min-width:0; }}
  h3 {{ margin:0 0 3px; font-size:18px; line-height:1.45; }}
  .english-title {{ color:#475467; font-family:Georgia,serif; font-size:14px; line-height:1.45; }}
  .meta {{ margin:8px 0 14px; color:#667085; font-size:12px; }}
  .summary {{ margin:12px 0; }}
  .summary strong, .relevance strong {{ color:#344054; font-size:13px; }}
  .summary .detail-label {{ display:inline-block; margin-top:8px; color:#17202a; font-size:14px; }}
  .summary p {{ margin:4px 0 0; }}
  .en {{ color:#344054; font-family:Georgia,"Times New Roman",serif; font-size:14px; }}
  .relevance {{ margin-top:14px; padding:10px 12px; border-left:3px solid #d0d5dd; background:#f9fafb; color:#344054; font-size:13px; }}
  .source-link {{ display:inline-block; margin-top:12px; color:#175cd3; font-size:13px; text-decoration:none; }}
  footer {{ padding:24px 42px 34px; color:#667085; font-size:12px; }}
  @media(max-width:640px) {{
    header, section, footer {{ padding-left:20px; padding-right:20px; }}
    .intro {{ padding-left:20px; padding-right:20px; }}
    .overview {{ padding-left:20px; padding-right:20px; }}
    h1 {{ font-size:25px; }}
    .story {{ gap:10px; }}
  }}
  @media print {{
    body {{ background:#fff; }}
    .page {{ max-width:none; }}
    .story {{ break-inside:avoid; }}
  }}
</style>
</head>
<body><main class="page">
<header>
  <div class="kicker">DAILY INTELLIGENCE BRIEF</div>
  <h1>海外新闻与产业简报</h1>
  <div class="date">{now:%Y年%m月%d日 %H:%M}</div>
</header>
<p class="intro">以事件为单位聚合多家媒体报道，重点覆盖国际政治、财经新闻、国内钢铁产业链，以及海外重点报道但国内主流媒体可能未充分报道的重大涉华事件。同一事件合并呈现，并按国家、机构、人物、市场和价格动态拆分具体情况。</p>
<div class="overview"><h2>全部新闻摘要</h2><ol>{summary_items}</ol></div>
{"".join(section_html)}
<footer>本简报由个人新闻助手根据公开资料自动编辑，不复制媒体全文。付费墙媒体仅依据公开可见信息；涉及投资或重大工作决策时，仍应交叉核实关键数字和后续进展。</footer>
</main></body></html>"""


def create_report_files(articles: list[Article]) -> tuple[Path, Path | None]:
    REPORTS_DIR.mkdir(exist_ok=True)
    stamp = dt.datetime.now().astimezone().strftime("%Y-%m-%d_%H%M")
    html_path = REPORTS_DIR / f"海外新闻与产业简报_{stamp}.html"
    pdf_path = REPORTS_DIR / f"海外新闻与产业简报_{stamp}.pdf"
    html_path.write_text(render_report_html(articles), encoding="utf-8")

    browser_path = (
        shutil.which("google-chrome")
        or shutil.which("chromium")
        or shutil.which("chromium-browser")
    )
    edge = Path(browser_path) if browser_path else Path(r"C:\Program Files (x86)\Microsoft\Edge\Application\msedge.exe")
    if not edge.exists():
        edge = Path(r"C:\Program Files\Microsoft\Edge\Application\msedge.exe")
    if not edge.exists():
        print("[warn] Browser not found; PDF attachment will be skipped.", file=sys.stderr)
        return html_path, None
    edge_profile = REPORTS_DIR / ".edge-pdf-profile"
    subprocess.run(
        [
            str(edge),
            "--headless",
            "--disable-gpu",
            "--no-pdf-header-footer",
            f"--user-data-dir={edge_profile}",
            f"--print-to-pdf={pdf_path}",
            html_path.as_uri(),
        ],
        cwd=ROOT,
        check=True,
        timeout=90,
    )
    return html_path, pdf_path


def publish_report_to_github_pages(html_path: Path) -> str:
    repo_value = os.environ.get("GITHUB_PAGES_REPO_DIR", "").strip()
    pages_url = os.environ.get("GITHUB_PAGES_URL", "").strip().rstrip("/")
    if not repo_value or not pages_url:
        raise RuntimeError("GitHub Pages尚未完成首次设置。")

    repo_dir = Path(repo_value).expanduser().resolve()
    git_path = shutil.which("git")
    git_exe = Path(git_path) if git_path else Path(r"C:\Program Files\Git\cmd\git.exe")
    if not git_exe.exists():
        raise RuntimeError("未找到Git。")
    if not (repo_dir / ".git").exists():
        raise RuntimeError("GitHub Pages本地仓库尚未建立。")

    archive_dir = repo_dir / "archive"
    archive_dir.mkdir(parents=True, exist_ok=True)
    stamp = dt.datetime.now().astimezone().strftime("%Y-%m-%d_%H%M")
    archive_name = f"brief_{stamp}.html"
    shutil.copy2(html_path, repo_dir / "index.html")
    shutil.copy2(html_path, archive_dir / archive_name)
    (repo_dir / ".nojekyll").touch()

    commands = [
        [str(git_exe), "add", "index.html", ".nojekyll", f"archive/{archive_name}", "news.db"],
        [str(git_exe), "commit", "-m", f"Publish brief {stamp}"],
        [str(git_exe), "push", "origin", "main"],
    ]
    for command in commands:
        attempts = 5 if command[1] == "push" else 1
        for attempt in range(1, attempts + 1):
            result = subprocess.run(
                command,
                cwd=repo_dir,
                capture_output=True,
                text=True,
                encoding="utf-8",
                errors="replace",
                timeout=120,
            )
            if result.returncode == 0:
                break
            combined = f"{result.stdout}\n{result.stderr}"
            if command[1] == "commit" and "nothing to commit" in combined.lower():
                break
            if attempt == attempts:
                raise RuntimeError(f"GitHub Pages发布失败：{combined.strip()[:500]}")
            print(f"GitHub连接暂时失败，正在重试上传（{attempt + 1}/{attempts}）...", flush=True)
            time.sleep(attempt * 5)
    return f"{pages_url}/archive/{archive_name}"


def send_163_email(
    html_path: Path, pdf_path: Path | None, *, subject_prefix: str = ""
) -> None:
    sender = os.environ["EMAIL_163_ADDRESS"]
    receiver = os.environ.get("EMAIL_RECIPIENT", sender)
    message = EmailMessage()
    today = dt.datetime.now().astimezone().strftime("%Y-%m-%d")
    message["Subject"] = f"{subject_prefix}海外新闻与产业简报 | {today}"
    message["From"] = sender
    message["To"] = receiver
    message.set_content("请使用支持HTML的邮件客户端阅读本简报。")
    message.add_alternative(html_path.read_text(encoding="utf-8"), subtype="html")
    if pdf_path and pdf_path.exists():
        message.add_attachment(
            pdf_path.read_bytes(),
            maintype="application",
            subtype="pdf",
            filename=pdf_path.name,
        )
    with smtplib.SMTP_SSL("smtp.163.com", 465, timeout=30) as smtp:
        smtp.login(sender, os.environ["EMAIL_163_AUTH_CODE"])
        smtp.send_message(message)


def articles_from_latest_report() -> list[Article]:
    reports = sorted(REPORTS_DIR.glob("*.html"), key=lambda path: path.stat().st_mtime, reverse=True)
    if not reports:
        raise RuntimeError("没有找到可复用的历史HTML简报。")
    page = reports[0].read_text(encoding="utf-8")
    category_map = {
        "国际政治与地缘局势": "international_politics",
        "财经新闻": "finance_business",
        "钢铁产业链": "steel_chain",
        "海外涉华重大报道": "overseas_china_major",
    }
    articles: list[Article] = []
    section_pattern = re.compile(
        r"<section><h2>(.*?)</h2>(.*?)</section>",
        flags=re.DOTALL | re.IGNORECASE,
    )
    story_pattern = re.compile(
        r'<article class="story">.*?<h3>(.*?)</h3>'
        r'.*?<div class="english-title">(.*?)</div>'
        r'.*?<div class="meta">(.*?)</div>'
        r'.*?<div class="summary zh">.*?<p>(.*?)</p></div>'
        r'.*?<div class="summary en">.*?<p>(.*?)</p></div>'
        r'.*?<div class="relevance">.*?</strong>\s*(.*?)</div>'
        r'.*?<a class="source-link" href="(.*?)">',
        flags=re.DOTALL | re.IGNORECASE,
    )
    for section_match in section_pattern.finditer(page):
        section_name = clean_text(section_match.group(1))
        topic = category_map.get(section_name, "international_politics")
        for match in story_pattern.finditer(section_match.group(2)):
            meta = clean_text(match.group(3))
            source = meta.split("·", 1)[0].strip()
            zh_summary = clean_text(match.group(4))
            article = Article(
                source=source,
                title=clean_text(match.group(2)),
                url=html.unescape(match.group(7)),
                published=utc_now(),
                summary=zh_summary,
                topics=[topic],
                zh_title=clean_text(match.group(1)),
                short_summary=zh_summary[:140],
                zh_summary=zh_summary,
                en_summary=clean_text(match.group(5)),
                why_it_matters=clean_text(match.group(6)),
            )
            articles.append(article)
    if not articles:
        raise RuntimeError(f"无法从历史简报恢复新闻：{reports[0].name}")
    return articles


def replay_latest_report(*, rebuild_details: bool = True) -> None:
    articles = articles_from_latest_report()
    if rebuild_details:
        enrich_articles(articles)
        print("正在为历史新闻重新生成详细中英文报道...", flush=True)
        translate_articles(articles)
    html_path, pdf_path = create_report_files(articles)
    send_163_email(html_path, pdf_path, subject_prefix="【格式测试】")
    try:
        web_url = publish_report_to_github_pages(html_path)
    except Exception:
        web_url = ""
    push_wechat_notice(
        f"新版简报格式测试（{len(articles)}条）",
        [article.zh_title or article.title for article in articles],
        (
            "点击本卡片查看全部摘要和详细内容。"
            if web_url
            else "网页暂未发布，全部新闻已按新版格式发送至163邮箱。"
        ),
        target_url=web_url or "https://mail.163.com/",
    )
    print(f"测试完成：复用了 {len(articles)} 条历史新闻，并重新生成了详细报道。")


def wecom_access_token() -> str:
    corp_id = os.environ["WECOM_CORP_ID"]
    secret = os.environ["WECOM_APP_SECRET"]
    query = urllib.parse.urlencode({"corpid": corp_id, "corpsecret": secret})
    payload = json.loads(
        request_bytes(f"https://qyapi.weixin.qq.com/cgi-bin/gettoken?{query}").decode("utf-8")
    )
    if payload.get("errcode", 0) != 0:
        raise RuntimeError(f"WeCom token error: {payload}")
    return payload["access_token"]


def wechat_test_access_token() -> str:
    query = urllib.parse.urlencode(
        {
            "grant_type": "client_credential",
            "appid": os.environ["WECHAT_TEST_APP_ID"],
            "secret": os.environ["WECHAT_TEST_APP_SECRET"],
        }
    )
    payload = json.loads(
        request_bytes(f"https://api.weixin.qq.com/cgi-bin/token?{query}").decode("utf-8")
    )
    if "access_token" not in payload:
        raise RuntimeError(f"微信测试号获取凭证失败：{payload}")
    return payload["access_token"]


def push_wechat_test(articles: list[Article]) -> None:
    token = wechat_test_access_token()
    endpoint = (
        "https://api.weixin.qq.com/cgi-bin/message/template/send?"
        + urllib.parse.urlencode({"access_token": token})
    )
    summaries: list[str] = []
    english_titles: list[str] = []
    importance_notes: list[str] = []
    sources: list[str] = []
    for index, article in enumerate(articles, start=1):
        title = article.zh_title or article.title
        summary = article.zh_summary or article.summary or "暂无摘要。"
        summaries.append(f"{index}. {title}\n{summary}")
        english_titles.append(f"{index}. {article.title}")
        importance_notes.append(
            f"{index}. {article.why_it_matters or '请结合原文进一步核实。'}"
        )
        if article.source not in sources:
            sources.append(article.source)

    result = post_json(
        endpoint,
        {
            "touser": os.environ["WECHAT_TEST_OPEN_ID"],
            "template_id": os.environ["WECHAT_TEST_TEMPLATE_ID"],
            "url": "https://mail.163.com/",
            "data": {
                "headline": {"value": f"海外新闻简报（{len(articles)}条）"},
                "source": {"value": "、".join(sources)},
                "summary": {"value": "\n\n".join(summaries)},
                "english": {"value": "\n".join(english_titles)},
                "importance": {"value": "\n".join(importance_notes)},
            },
        },
        {},
    )
    if result.get("errcode", 0) != 0:
        raise RuntimeError(f"微信测试号发送失败：{result}")


def push_wechat_notice(
    subject: str,
    headlines: list[str],
    note: str,
    *,
    target_url: str = "https://mail.163.com/",
) -> None:
    token = wechat_test_access_token()
    endpoint = (
        "https://api.weixin.qq.com/cgi-bin/message/template/send?"
        + urllib.parse.urlencode({"access_token": token})
    )
    numbered = [f"{index}. {title}" for index, title in enumerate(headlines, 1)]
    chunks: list[list[str]] = []
    current: list[str] = []
    current_length = 0
    for item in numbered:
        if current and current_length + len(item) + 1 > 700:
            chunks.append(current)
            current = []
            current_length = 0
        current.append(item)
        current_length += len(item) + 1
    if current:
        chunks.append(current)

    for part, chunk in enumerate(chunks, start=1):
        part_subject = subject
        if len(chunks) > 1:
            part_subject += f"（第{part}/{len(chunks)}部分）"
        result = post_json(
            endpoint,
            {
                "touser": os.environ["WECHAT_TEST_OPEN_ID"],
                "template_id": os.environ["WECHAT_TEST_TEMPLATE_ID"],
                "url": target_url,
                "data": {
                    "headline": {"value": part_subject},
                    "source": {"value": "个人海外新闻助手"},
                    "summary": {"value": "\n".join(chunk)},
                    "english": {"value": "完整中英文简报及PDF已发送至163邮箱。"},
                    "importance": {"value": note},
                },
            },
            {},
        )
        if result.get("errcode", 0) != 0:
            raise RuntimeError(f"微信提醒发送失败：{result}")


def send_wechat_test_notice() -> None:
    required = [
        "WECHAT_TEST_APP_ID",
        "WECHAT_TEST_APP_SECRET",
        "WECHAT_TEST_OPEN_ID",
        "WECHAT_TEST_TEMPLATE_ID",
    ]
    missing = [name for name in required if not os.environ.get(name)]
    if missing:
        raise RuntimeError("微信测试号设置不完整，请重新运行“开始设置.vbs”。")
    push_wechat_notice(
        "微信提醒测试成功",
        ["海外新闻与产业简报推送通道已连接"],
        (
            "点击本卡片可直接查看全部摘要和详细内容。"
            if os.environ.get("GITHUB_PAGES_URL")
            else "今后这里将显示今日重点，完整内容请查看163邮箱。"
        ),
        target_url=os.environ.get("GITHUB_PAGES_URL", "https://mail.163.com/"),
    )


def send_failure_notice(message: str) -> None:
    required = [
        "WECHAT_TEST_APP_ID",
        "WECHAT_TEST_APP_SECRET",
        "WECHAT_TEST_OPEN_ID",
        "WECHAT_TEST_TEMPLATE_ID",
    ]
    if not all(os.environ.get(name) for name in required):
        return
    push_wechat_notice(
        "海外新闻简报本次未发送",
        ["系统已自动重试，但未能生成符合质量要求的完整简报"],
        message[:500],
        target_url=os.environ.get(
            "GITHUB_PAGES_URL",
            "https://dr252874600-sudo.github.io/overseas-news-brief/",
        ),
    )


def push_wecom(content: str) -> None:
    webhook_url = os.environ.get("WECOM_WEBHOOK_URL", "").strip()
    if webhook_url:
        result = post_json(
            webhook_url,
            {
                "msgtype": "markdown",
                "markdown": {"content": content[:4000]},
            },
            {},
        )
        if result.get("errcode", 0) != 0:
            raise RuntimeError(f"企业微信群机器人发送失败：{result}")
        return

    token = wecom_access_token()
    payload = {
        "touser": os.environ["WECOM_USER_ID"],
        "msgtype": "markdown",
        "agentid": int(os.environ["WECOM_AGENT_ID"]),
        "markdown": {"content": content[:4000]},
        "safe": 0,
        "enable_duplicate_check": 1,
        "duplicate_check_interval": 1800,
    }
    result = post_json(
        "https://qyapi.weixin.qq.com/cgi-bin/message/send?"
        + urllib.parse.urlencode({"access_token": token}),
        payload,
        {},
    )
    if result.get("errcode", 0) != 0:
        if result.get("errcode") == 60020:
            message = str(result.get("errmsg", ""))
            match = re.search(r"from ip:\s*([0-9.]+)", message)
            current_ip = match.group(1) if match else "错误信息中显示的公网 IP"
            raise RuntimeError(
                "\n企业微信尚未信任这台电脑的网络地址。\n"
                f"请进入企业微信管理后台 → 应用管理 → 海外新闻助手 → 企业可信 IP，添加："
                f"{current_ip}\n"
                "保存后等待约一分钟，再重新发送。"
            )
        raise RuntimeError(f"WeCom send error: {result}")


def push_news(content: str, articles: list[Article]) -> None:
    test_fields = [
        "WECHAT_TEST_APP_ID",
        "WECHAT_TEST_APP_SECRET",
        "WECHAT_TEST_OPEN_ID",
        "WECHAT_TEST_TEMPLATE_ID",
    ]
    if all(os.environ.get(name) for name in test_fields):
        push_wechat_test(articles)
        return
    push_wecom(content)


def collect(config: dict[str, Any]) -> list[Article]:
    print("正在连接海外新闻源，请稍候...", flush=True)
    all_articles: list[Article] = []
    direct_sources = [
        source for source in config["sources"]
        if source["type"] in {"rss", "google_query"}
    ]
    gdelt_sources = [source for source in config["sources"] if source["type"] == "gdelt"]

    def fetch_source(source: dict[str, Any]) -> list[Article]:
        if source["type"] == "rss":
            return fetch_rss(source, config["max_articles_per_source"])
        if source["type"] == "google_query":
            return fetch_google_query(
                source,
                config["max_articles_per_source"],
                config["lookback_hours"],
            )
        print(f"[warn] Unknown source type: {source['type']}", file=sys.stderr)
        return []

    with ThreadPoolExecutor(max_workers=min(8, len(direct_sources) + 1)) as executor:
        futures = {
            executor.submit(fetch_source, source): source["name"]
            for source in direct_sources
        }
        if gdelt_sources:
            futures[
                executor.submit(
                    fetch_gdelt_sources,
                    gdelt_sources,
                    config["max_articles_per_source"],
                    config["lookback_hours"],
                )
            ] = "GDELT sources"
        for future in as_completed(futures):
            try:
                all_articles.extend(future.result())
            except Exception as error:
                print(f"[warn] Source failed: {futures[future]}: {error}", file=sys.stderr)
    print("新闻抓取完成，正在筛选重要头条...", flush=True)

    cutoff = utc_now() - dt.timedelta(hours=config["lookback_hours"])
    unique: dict[str, Article] = {}
    for article in all_articles:
        if article.published < cutoff:
            continue
        classify_and_rank(article, config["topics"])
        if not article.topics:
            continue
        key = re.sub(r"\W+", "", article.title.lower())
        current = unique.get(key)
        if current is None or article.score > current.score:
            unique[key] = article
    return sorted(unique.values(), key=lambda item: item.score, reverse=True)


def select_brief_source_articles(articles: list[Article], max_items: int) -> list[Article]:
    targets = [
        ("international_politics", 8),
        ("finance_business", 8),
        ("steel_chain", 5),
        ("overseas_china_major", 3),
    ]
    selected: list[Article] = []
    used: set[str] = set()

    def add(article: Article) -> bool:
        if article.article_id in used or len(selected) >= max_items:
            return False
        selected.append(article)
        used.add(article.article_id)
        return True

    for topic, target in targets:
        count = 0
        for article in articles:
            if topic not in article.topics:
                continue
            if add(article):
                count += 1
            if count >= target:
                break

    for article in articles:
        if len(selected) >= max_items:
            break
        add(article)

    return selected


def has_enough_public_material(article: Article) -> bool:
    return bool(article.title) and (
        len(article.public_text) >= 200 or len(article.summary) >= 40
    )


def run_once(
    config_path: Path,
    *,
    dry_run: bool,
    email_report: bool = False,
    slot_id: str | None = None,
) -> int:
    config = json.loads(config_path.read_text(encoding="utf-8"))
    ensure_shellcrash_node()
    connection = init_db()
    candidates: list[Article] = []
    collect_attempts = 1 if dry_run else 3
    for attempt in range(1, collect_attempts + 1):
        fresh_articles = [
            article for article in collect(config)
            if not is_pushed(connection, article)
        ]
        candidates = select_brief_source_articles(
            fresh_articles,
            int(config.get("max_push_items", 24)),
        )
        if candidates or attempt == collect_attempts:
            break
        print(
            f"本轮未取得新头条，可能是海外网络暂时不稳定；"
            f"45秒后进行第{attempt + 1}/{collect_attempts}次尝试。",
            flush=True,
        )
        time.sleep(45)
    if not candidates:
        print("本次没有抓取到符合条件的新头条。")
        print("可能是海外网络暂时较慢，请稍后再试。")
        raise RuntimeError(
            "No eligible headlines were collected. The scheduled runner must retry."
        )

    enrich_articles(candidates)
    usable_candidates = [
        article
        for article in candidates
        if has_enough_public_material(article)
    ]
    if len(usable_candidates) < 3:
        raise RuntimeError(
            "Public article material is temporarily unavailable; fewer than three "
            "usable articles remain, so nothing was sent."
        )
    limited_text_count = sum(
        1 for article in usable_candidates if len(article.public_text) < 400
    )
    if limited_text_count:
        print(
            f"其中 {limited_text_count}/{len(usable_candidates)} 篇报道只能依据公开标题或摘要生成，"
            "会在简报中注明信息限制。",
            flush=True,
        )
    source_articles = usable_candidates
    fallback_mode = False
    try:
        print("正在生成可独立阅读的中英文详细事件简报...", flush=True)
        candidates = build_event_brief(source_articles)
    except (
        urllib.error.URLError,
        urllib.error.HTTPError,
        TimeoutError,
        json.JSONDecodeError,
        KeyError,
        RuntimeError,
    ) as error:
        fallback_mode = True
        print(
            f"[warn] 详细中英文简报生成失败，改发保底版：{type(error).__name__}: {error}",
            file=sys.stderr,
            flush=True,
        )
        candidates = build_fallback_brief(source_articles)

    digest = format_digest(candidates)
    print(digest)
    if dry_run:
        if email_report:
            html_path, pdf_path = create_report_files(candidates)
            print(f"\n简报已生成：{html_path.name}")
            print(f"PDF已生成：{pdf_path.name}")
        return 0

    if email_report:
        email_fields = ["EMAIL_163_ADDRESS", "EMAIL_163_AUTH_CODE"]
        missing_email = [name for name in email_fields if not os.environ.get(name)]
        if missing_email:
            raise RuntimeError("尚未完成163邮箱设置。")
        html_path, pdf_path = create_report_files(candidates)
        subject_prefix = "【保底版】" if fallback_mode else ""
        send_163_email(html_path, pdf_path, subject_prefix=subject_prefix)
        mark_pushed(connection, source_articles)
        if slot_id:
            mark_slot_sent(connection, slot_id)
        web_url = ""
        try:
            web_url = publish_report_to_github_pages(html_path)
            print(f"网页发布成功：{web_url}")
        except Exception as error:
            print(f"[warn] 网页暂未发布：{error}", file=sys.stderr)
        test_fields = [
            "WECHAT_TEST_APP_ID",
            "WECHAT_TEST_APP_SECRET",
            "WECHAT_TEST_OPEN_ID",
            "WECHAT_TEST_TEMPLATE_ID",
        ]
        wechat_ok = False
        if all(os.environ.get(name) for name in test_fields):
            try:
                push_wechat_notice(
                    f"海外新闻简报已送达（{len(candidates)}条）",
                    [article.zh_title or article.title for article in candidates],
                    (
                        "点击本卡片查看全部摘要和详细内容。"
                        if web_url
                        else "网页发布暂时失败，完整内容请先查看163邮箱。"
                    ),
                    target_url=web_url or "https://mail.163.com/",
                )
                wechat_ok = True
            except Exception as error:
                print(f"[warn] 微信提醒暂时失败：{error}", file=sys.stderr)
        wechat_text = "微信提醒已同步" if wechat_ok else "微信提醒未确认"
        print(f"\n邮件发送成功，包含 {len(candidates)} 条新闻和PDF附件；{wechat_text}。")
        return 0

    test_fields = [
        "WECHAT_TEST_APP_ID",
        "WECHAT_TEST_APP_SECRET",
        "WECHAT_TEST_OPEN_ID",
        "WECHAT_TEST_TEMPLATE_ID",
    ]
    using_wechat_test = all(os.environ.get(name) for name in test_fields)
    if not using_wechat_test and not os.environ.get("WECOM_WEBHOOK_URL"):
        required = ["WECOM_CORP_ID", "WECOM_APP_SECRET", "WECOM_AGENT_ID", "WECOM_USER_ID"]
        missing = [name for name in required if not os.environ.get(name)]
        if missing:
            raise RuntimeError("Missing environment variables: " + ", ".join(missing))
    push_news(digest, candidates)
    mark_pushed(connection, source_articles)
    if slot_id:
        mark_slot_sent(connection, slot_id)
    print(f"\nPushed {len(candidates)} headlines.")
    return 0


def main() -> int:
    load_local_env()
    parser = argparse.ArgumentParser(description="Overseas news bilingual WeCom digest")
    parser.add_argument(
        "--config", type=Path, default=ROOT / "config.json", help="Path to configuration JSON"
    )
    parser.add_argument("--dry-run", action="store_true", help="Print without pushing or deduping")
    parser.add_argument("--email", action="store_true", help="Generate and send the 163 email report")
    parser.add_argument(
        "--scheduled-check",
        action="store_true",
        help="Only send once for the current morning/evening schedule window",
    )
    parser.add_argument("--test-wechat", action="store_true", help="Send a WeChat test notice")
    parser.add_argument(
        "--failure-notice",
        action="store_true",
        help="Send a WeChat notice after all scheduled retries fail",
    )
    parser.add_argument(
        "--replay-latest",
        action="store_true",
        help="Rebuild and send the latest saved report without fetching news",
    )
    parser.add_argument("--loop", action="store_true", help="Poll continuously")
    args = parser.parse_args()

    if not args.config.exists():
        print(
            f"Configuration not found: {args.config}\n"
            "Copy config.example.json to config.json and adjust it.",
            file=sys.stderr,
        )
        return 2

    if args.test_wechat:
        send_wechat_test_notice()
        print("微信测试提醒已发送。")
        return 0
    if args.failure_notice:
        send_failure_notice(
            "可能原因包括海外网络中断、翻译接口额度不足或正文抓取失败。"
            "程序没有发送残缺内容，请检查后重新运行。"
        )
        print("失败提醒已发送。")
        return 0
    if args.replay_latest:
        replay_latest_report()
        return 0

    slot_id = None
    if args.scheduled_check:
        connection = init_db()
        try:
            slot_id = scheduled_slot_to_run(connection)
        finally:
            connection.close()
        if not slot_id:
            return 0

    if not args.loop:
        return run_once(
            args.config,
            dry_run=args.dry_run,
            email_report=args.email,
            slot_id=slot_id,
        )

    while True:
        try:
            run_once(args.config, dry_run=args.dry_run, email_report=args.email)
        except Exception as error:
            print(f"[error] {error}", file=sys.stderr)
        config = json.loads(args.config.read_text(encoding="utf-8"))
        time.sleep(max(1, int(config.get("poll_minutes", 10))) * 60)


if __name__ == "__main__":
    raise SystemExit(main())
