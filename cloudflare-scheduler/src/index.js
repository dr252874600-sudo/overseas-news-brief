const SHANGHAI_TIME_ZONE = "Asia/Shanghai";

function dateInShanghai(timestamp) {
  const parts = new Intl.DateTimeFormat("en-CA", {
    timeZone: SHANGHAI_TIME_ZONE,
    year: "numeric",
    month: "2-digit",
    day: "2-digit",
  }).formatToParts(new Date(timestamp));
  const values = Object.fromEntries(
    parts
      .filter((part) => part.type !== "literal")
      .map((part) => [part.type, part.value]),
  );
  return `${values.year}-${values.month}-${values.day}`;
}

function slotForCron(cron) {
  if (cron === "0 0 * * *") return "am";
  if (cron === "0 10 * * *") return "pm";
  throw new Error(`Unexpected cron trigger: ${cron}`);
}

async function dispatchBrief(event, env) {
  const slot = slotForCron(event.cron);
  const url = `https://api.github.com/repos/${env.GITHUB_OWNER}/${env.GITHUB_REPOSITORY}/actions/workflows/${env.GITHUB_WORKFLOW}/dispatches`;
  const response = await fetch(url, {
    method: "POST",
    headers: {
      Accept: "application/vnd.github+json",
      Authorization: `Bearer ${env.GITHUB_WORKFLOW_TOKEN}`,
      "Content-Type": "application/json",
      "User-Agent": "overseas-news-scheduler",
      "X-GitHub-Api-Version": "2022-11-28",
    },
    body: JSON.stringify({
      ref: "main",
      inputs: {
        delivery_slot: slot,
        delivery_date: dateInShanghai(event.scheduledTime),
      },
    }),
  });

  if (!response.ok) {
    throw new Error(`GitHub workflow dispatch failed: ${response.status} ${await response.text()}`);
  }
}

export default {
  async scheduled(event, env, ctx) {
    ctx.waitUntil(dispatchBrief(event, env));
  },

  async fetch() {
    return new Response("Overseas news scheduler is ready.");
  },
};
