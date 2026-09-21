// Read-only audit of the downloaded share payload and the user's replacement.
const fs = require('node:fs');
const html = fs.readFileSync(process.argv[2], 'utf8');
const archive = fs.readFileSync(process.argv[3], 'utf8');
const match = html.match(/streamController\.enqueue\(("(?:[^"\\]|\\.)*")\)/);
if (!match) throw Error('No shared conversation payload');
const data = JSON.parse(JSON.parse(match[1]));
const cache = new Map();
function decode(i) {
  if (i < 0) return null;
  if (cache.has(i)) return cache.get(i);
  const v = data[i];
  if (!v || typeof v !== 'object') return v;
  const out = Array.isArray(v) ? [] : {};
  cache.set(i, out);
  if (Array.isArray(v)) v.forEach(x => out.push(typeof x === 'number' ? decode(x) : x));
  else for (const [k, x] of Object.entries(v)) out[k.startsWith('_') ? decode(+k.slice(1)) : k] = decode(x);
  return out;
}
const conv = decode(0).loaderData['routes/share.$shareId.($action)'].serverResponse.data;
const messages = conv.linear_conversation.map(n => n.message).filter(Boolean);
const visible = messages.filter(m =>
  (m.author.role === 'user' && m.content.content_type === 'text') ||
  (m.author.role === 'assistant' && m.channel === 'final'));
const counts = {};
for (const m of visible) counts[m.author.role] = (counts[m.author.role] || 0) + 1;
const headings = [...archive.matchAll(/^## (User|ChatGPT)\s*$/gm)].map(m => m[1]);
console.log(JSON.stringify({payloadVisibleCounts: counts, archiveTurns: headings.length,
  archiveUser: headings.filter(x => x === 'User').length,
  archiveAssistant: headings.filter(x => x === 'ChatGPT').length}, null, 2));
// Check beginning and ending lexical landmarks per message, not just counts.
const norm = s => s.toLowerCase().replace(/[^\p{L}\p{N}]+/gu, ' ').trim();
const plain = norm(archive);
for (const [i, m] of visible.entries()) {
  const text = (m.content.parts || []).filter(p => typeof p === 'string').join('\n');
  const words = norm(text).split(' ');
  const start = words.slice(0, 9).join(' ');
  const end = words.slice(-9).join(' ');
  if (!plain.includes(start) || !plain.includes(end))
    console.log(JSON.stringify({turn:i+1,role:m.author.role,startFound:plain.includes(start),endFound:plain.includes(end),start,end}));
}
