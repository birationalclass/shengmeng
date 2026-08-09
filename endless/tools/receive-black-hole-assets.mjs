import http from "node:http";
import { mkdir, writeFile } from "node:fs/promises";
import path from "node:path";

const outputDirectory = path.resolve(process.argv[2] || "assets/black-hole-flipbook");
const palettes = new Set(["gold", "blue", "violet", "red"]);
const received = new Set();
await mkdir(outputDirectory, { recursive:true });

function respond(response, status, body = "ok") {
  response.writeHead(status, {
    "access-control-allow-origin":"*",
    "access-control-allow-methods":"POST,OPTIONS",
    "content-type":"text/plain; charset=utf-8"
  });
  response.end(body);
}

const server = http.createServer(async (request, response) => {
  if (request.method === "OPTIONS") { respond(response, 204, ""); return; }
  const url = new URL(request.url, "http://127.0.0.1:4181");
  if (request.method !== "POST") { respond(response, 405, "POST only"); return; }
  if (url.pathname === "/done") {
    respond(response, 200, `received ${received.size}/8`);
    console.log(`COMPLETE ${received.size}/8`);
    setTimeout(() => server.close(), 250);
    return;
  }
  const palette = url.searchParams.get("palette");
  const kind = url.pathname.slice(1);
  if (!palettes.has(palette) || !["sheet", "poster"].includes(kind)) { respond(response, 400, "invalid target"); return; }
  const chunks = [];
  for await (const chunk of request) chunks.push(chunk);
  const fileName = kind === "sheet" ? `black-hole-${palette}-clean.webp` : `poster-${palette}-clean.webp`;
  await writeFile(path.join(outputDirectory, fileName), Buffer.concat(chunks));
  received.add(`${kind}:${palette}`);
  console.log(`${kind.toUpperCase()} ${palette} ${Buffer.concat(chunks).length}`);
  respond(response, 200);
});

server.listen(4181, "127.0.0.1", () => console.log(`READY ${outputDirectory}`));
