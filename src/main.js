import "./style.css";

const canvas = document.querySelector("#game");
const gameFrame = document.querySelector("#gameFrame");
const ctx = canvas.getContext("2d");
const W = canvas.width;
const H = canvas.height;

const mask = document.createElement("canvas");
mask.width = W; mask.height = H;
const mctx = mask.getContext("2d", { willReadFrequently: true });
const solidMask = document.createElement("canvas");
solidMask.width = W; solidMask.height = H;
const sctx = solidMask.getContext("2d", { willReadFrequently: true });
const dull = document.createElement("canvas");
const nice = document.createElement("canvas");
const reveal = document.createElement("canvas");
const captureLayer = document.createElement("canvas");
dull.width = nice.width = reveal.width = captureLayer.width = W; dull.height = nice.height = reveal.height = captureLayer.height = H;
const rctx = reveal.getContext("2d");
const cctx = captureLayer.getContext("2d");
const CAPTURE_SCALE = 4;
const captureGrid = document.createElement("canvas");
captureGrid.width = Math.ceil(W / CAPTURE_SCALE); captureGrid.height = Math.ceil(H / CAPTURE_SCALE);
const gridCtx = captureGrid.getContext("2d", { willReadFrequently: true });

const ui = {
  start: document.querySelector("#startScreen"), end: document.querySelector("#endScreen"),
  startBtn: document.querySelector("#startBtn"), restartBtn: document.querySelector("#restartBtn"),
  score: document.querySelector("#score"), finalScore: document.querySelector("#finalScore"),
  finalTitle: document.querySelector("#finalTitle"), finalCopy: document.querySelector("#finalCopy"),
  time: document.querySelector("#time"), meter: document.querySelector("#meterFill"),
  toast: document.querySelector("#toast"), boost: document.querySelector("#boostPill"),
  boostBar: document.querySelector("#boostBar"), sound: document.querySelector("#soundBtn"),
  assetNote: document.querySelector("#assetNote")
};

const joystickEl = document.querySelector("#virtualJoystick");
const joystickNub = document.querySelector("#joystickNub");
const joystick = { active: false, pointerId: null, originX: 0, originY: 0, dx: 0, dy: 0, strength: 0 };

const keys = new Set();
const player = { x: W / 2, y: H / 2, vx: 0, vy: 0, angle: 0, radius: 13, outside: false, trail: [], invuln: 0 };
let state = "menu";
let last = performance.now();
let timeLeft = 60;
let score = 0;
let boost = 0;
let apples = [];
let leaves = [];
let particles = [];
let floatingTexts = [];
let shake = 0;
let nextApple = 1;
let nextLeaf = .4;
let baselineFilled = 0;
let toastTimer;
let muted = false;
let audioCtx;

function rand(min, max) { return min + Math.random() * (max - min); }
function clamp(v, min, max) { return Math.max(min, Math.min(max, v)); }
function dist(a, b) { return Math.hypot(a.x - b.x, a.y - b.y); }

function distanceToSegment(point, start, end) {
  const dx = end.x - start.x, dy = end.y - start.y;
  const lengthSquared = dx * dx + dy * dy;
  if (!lengthSquared) return dist(point, start);
  const t = clamp(((point.x - start.x) * dx + (point.y - start.y) * dy) / lengthSquared, 0, 1);
  return Math.hypot(point.x - (start.x + t * dx), point.y - (start.y + t * dy));
}

function formatTime(seconds) {
  const whole = Math.max(0, Math.ceil(seconds));
  return `${Math.floor(whole / 60)}:${String(whole % 60).padStart(2, "0")}`;
}

function buildEnclosedCapture(trail) {
  const gw = captureGrid.width, gh = captureGrid.height, cellCount = gw * gh;
  gridCtx.clearRect(0, 0, gw, gh);
  gridCtx.imageSmoothingEnabled = true;
  gridCtx.drawImage(solidMask, 0, 0, W, H, 0, 0, gw, gh);
  const existingPixels = gridCtx.getImageData(0, 0, gw, gh).data;
  const existing = new Uint8Array(cellCount);
  for (let i = 0; i < cellCount; i++) existing[i] = existingPixels[i * 4 + 3] > 30 ? 1 : 0;

  gridCtx.save();
  gridCtx.strokeStyle = "#fff"; gridCtx.lineWidth = 10; gridCtx.lineCap = "round"; gridCtx.lineJoin = "round";
  gridCtx.beginPath(); gridCtx.moveTo(trail[0].x / CAPTURE_SCALE, trail[0].y / CAPTURE_SCALE);
  trail.slice(1).forEach(point => gridCtx.lineTo(point.x / CAPTURE_SCALE, point.y / CAPTURE_SCALE));
  gridCtx.stroke(); gridCtx.restore();

  const barrierPixels = gridCtx.getImageData(0, 0, gw, gh).data;
  const blocked = new Uint8Array(cellCount), reachable = new Uint8Array(cellCount), queue = new Int32Array(cellCount);
  for (let i = 0; i < cellCount; i++) blocked[i] = barrierPixels[i * 4 + 3] > 30 ? 1 : 0;
  let head = 0, tail = 0;
  const enqueue = index => { if (!blocked[index] && !reachable[index]) { reachable[index] = 1; queue[tail++] = index; } };
  for (let x = 0; x < gw; x++) { enqueue(x); enqueue((gh - 1) * gw + x); }
  for (let y = 1; y < gh - 1; y++) { enqueue(y * gw); enqueue(y * gw + gw - 1); }
  while (head < tail) {
    const index = queue[head++], x = index % gw;
    if (x > 0) enqueue(index - 1); if (x < gw - 1) enqueue(index + 1);
    if (index >= gw) enqueue(index - gw); if (index < cellCount - gw) enqueue(index + gw);
  }

  const capturePixels = gridCtx.createImageData(gw, gh);
  const captured = new Uint8Array(cellCount);
  for (let i = 0; i < cellCount; i++) {
    if (!reachable[i] && !existing[i]) {
      captured[i] = 1;
      capturePixels.data[i * 4] = capturePixels.data[i * 4 + 1] = capturePixels.data[i * 4 + 2] = capturePixels.data[i * 4 + 3] = 255;
    }
  }
  gridCtx.putImageData(capturePixels, 0, 0);
  cctx.clearRect(0, 0, W, H); cctx.imageSmoothingEnabled = false;
  cctx.drawImage(captureGrid, 0, 0, gw, gh, 0, 0, W, H);
  return point => {
    const x = clamp(Math.floor(point.x / CAPTURE_SCALE), 0, gw - 1), y = clamp(Math.floor(point.y / CAPTURE_SCALE), 0, gh - 1);
    return captured[y * gw + x] === 1;
  };
}

function roundedRect(g, x, y, w, h, r) {
  g.beginPath(); g.roundRect(x, y, w, h, r); g.fill();
}

function makePlaceholder(g, isNice) {
  const bg = isNice ? "#f4d7c4" : "#858487";
  const road = isNice ? "#ead8ca" : "#706f73";
  const line = isNice ? "#fff1e5" : "#939196";
  g.fillStyle = bg; g.fillRect(0, 0, W, H);
  g.save();
  g.translate(W / 2, H / 2); g.rotate(-.09); g.translate(-W / 2, -H / 2);
  g.fillStyle = road;
  for (let x = -100; x < W + 200; x += 245) g.fillRect(x, -100, 78, H + 200);
  for (let y = -100; y < H + 200; y += 210) g.fillRect(-100, y, W + 200, 72);
  g.strokeStyle = line; g.lineWidth = 3; g.setLineDash([18, 18]);
  for (let x = -61; x < W + 200; x += 245) { g.beginPath(); g.moveTo(x, -100); g.lineTo(x, H + 100); g.stroke(); }
  for (let y = -64; y < H + 200; y += 210) { g.beginPath(); g.moveTo(-100, y); g.lineTo(W + 100, y); g.stroke(); }
  g.setLineDash([]);
  const colors = isNice ? ["#ff9abb", "#ffd46c", "#9bd37b", "#ae8be0", "#f7776c"] : ["#9a999b", "#77767a", "#aaa8aa", "#66666a"];
  let seed = 17;
  const seeded = () => ((seed = seed * 16807 % 2147483647) - 1) / 2147483646;
  for (let gx = -20; gx < W; gx += 245) {
    for (let gy = -15; gy < H; gy += 210) {
      const insetX = 22 + seeded() * 20, insetY = 21 + seeded() * 14;
      const bw = 105 + seeded() * 45, bh = 66 + seeded() * 45;
      g.fillStyle = "rgba(43,29,47,.18)"; roundedRect(g, gx + insetX + 8, gy + insetY + 9, bw, bh, 5);
      g.fillStyle = colors[Math.floor(seeded() * colors.length)]; roundedRect(g, gx + insetX, gy + insetY, bw, bh, 5);
      g.fillStyle = isNice ? "rgba(255,255,255,.34)" : "rgba(255,255,255,.08)";
      for (let wy = gy + insetY + 13; wy < gy + insetY + bh - 7; wy += 17) {
        for (let wx = gx + insetX + 13; wx < gx + insetX + bw - 7; wx += 22) g.fillRect(wx, wy, 9, 7);
      }
      if (isNice) {
        for (let t = 0; t < 5; t++) {
          g.fillStyle = ["#4f9a58", "#79b95e", "#357a4b"][Math.floor(seeded() * 3)];
          g.beginPath(); g.arc(gx + 170 + seeded() * 35, gy + 30 + seeded() * 130, 7 + seeded() * 8, 0, Math.PI * 2); g.fill();
        }
      }
    }
  }
  g.restore();
  const vignette = g.createRadialGradient(W / 2, H / 2, H * .2, W / 2, H / 2, W * .75);
  vignette.addColorStop(0, "transparent"); vignette.addColorStop(1, isNice ? "rgba(139,62,102,.1)" : "rgba(20,16,22,.24)");
  g.fillStyle = vignette; g.fillRect(0, 0, W, H);
}

makePlaceholder(dull.getContext("2d"), false);
makePlaceholder(nice.getContext("2d"), true);

async function loadMap(path, target) {
  return new Promise(resolve => {
    const img = new Image();
    img.onload = () => { const g = target.getContext("2d"); g.clearRect(0, 0, W, H); g.drawImage(img, 0, 0, W, H); resolve(true); };
    img.onerror = () => resolve(false);
    img.src = `${path}?v=${Date.now()}`;
  });
}

Promise.all([loadMap("/stad_dull.png", dull), loadMap("/stad_nice.png", nice)]).then(([a, b]) => {
  if (a && b) ui.assetNote.textContent = "City images loaded · go make it lovely";
});

function resetMask() {
  sctx.clearRect(0, 0, W, H);
  sctx.fillStyle = "#fff"; sctx.beginPath(); sctx.arc(W / 2, H / 2, 70, 0, Math.PI * 2); sctx.fill();
  refreshDisplayMask();
  baselineFilled = countMaskSamples().filled;
}

function refreshDisplayMask() {
  mctx.clearRect(0, 0, W, H);
  mctx.save(); mctx.filter = "blur(12px)"; mctx.drawImage(solidMask, 0, 0); mctx.restore();
}

function isSafe(x, y) {
  if (x < 0 || x >= W || y < 0 || y >= H) return false;
  return sctx.getImageData(x | 0, y | 0, 1, 1).data[3] > 80;
}

function countMaskSamples() {
  const data = sctx.getImageData(0, 0, W, H).data;
  let filled = 0, total = 0;
  for (let y = 0; y < H; y += 8) for (let x = 0; x < W; x += 8) { total++; if (data[(y * W + x) * 4 + 3] > 80) filled++; }
  return { filled, total };
}

function recalcScore() {
  const { filled, total } = countMaskSamples();
  score = Math.min(100, Math.max(0, Math.round((filled - baselineFilled) / (total - baselineFilled) * 100)));
  ui.score.textContent = score; ui.meter.style.width = `${score}%`;
}

function beep(freq = 440, duration = .08, type = "sine", volume = .035) {
  if (muted) return;
  audioCtx ||= new (window.AudioContext || window.webkitAudioContext)();
  const osc = audioCtx.createOscillator(), gain = audioCtx.createGain();
  osc.type = type; osc.frequency.setValueAtTime(freq, audioCtx.currentTime);
  gain.gain.setValueAtTime(volume, audioCtx.currentTime); gain.gain.exponentialRampToValueAtTime(.0001, audioCtx.currentTime + duration);
  osc.connect(gain).connect(audioCtx.destination); osc.start(); osc.stop(audioCtx.currentTime + duration);
}

function showToast(text) {
  ui.toast.textContent = text; ui.toast.classList.add("show");
  clearTimeout(toastTimer); toastTimer = setTimeout(() => ui.toast.classList.remove("show"), 1500);
}

function burst(x, y, count, palette, force = 150) {
  for (let i = 0; i < count; i++) {
    const a = Math.random() * Math.PI * 2, s = rand(force * .35, force);
    particles.push({ x, y, vx: Math.cos(a) * s, vy: Math.sin(a) * s, life: rand(.45, 1.2), max: 1.2, size: rand(4, 11), color: palette[i % palette.length], spin: rand(-7, 7), angle: rand(0, 6), gravity: rand(30, 160) });
  }
}

function spawnApple() {
  let p = { x: rand(70, W - 70), y: rand(70, H - 70) };
  for (let tries = 0; tries < 40 && isSafe(p.x, p.y); tries++) p = { x: rand(70, W - 70), y: rand(70, H - 70) };
  apples.push({ ...p, phase: rand(0, 6), life: 14 });
}

function spawnLeaf() {
  const side = Math.random() < .5 ? "left" : "top";
  const speed = rand(95, 190);
  leaves.push(side === "left"
    ? { x: -30, y: rand(20, H - 20), vx: speed, vy: rand(20, 70), angle: rand(0, 6), spin: rand(-4, 5), size: rand(12, 21) }
    : { x: rand(20, W - 20), y: -30, vx: rand(30, 80), vy: speed, angle: rand(0, 6), spin: rand(-4, 5), size: rand(12, 21) });
}

function beginGame() {
  releaseJoystick();
  resetMask(); recalcScore();
  Object.assign(player, { x: W / 2, y: H / 2, vx: 0, vy: 0, angle: 0, outside: false, trail: [], invuln: 1 });
  timeLeft = 60; boost = 0; apples = []; leaves = []; particles = []; floatingTexts = []; nextApple = 1.8; nextLeaf = .5;
  ui.time.textContent = "1:00"; ui.boost.classList.remove("show"); ui.start.classList.add("hidden"); ui.end.classList.add("hidden");
  state = "playing"; last = performance.now();
  beep(520, .08); setTimeout(() => beep(660, .1), 90); setTimeout(() => beep(880, .14), 190);
}

function closeTerritory() {
  if (player.trail.length < 5) { player.trail = []; player.outside = false; return; }
  const before = score;
  const wasCaptured = buildEnclosedCapture(player.trail);
  sctx.drawImage(captureLayer, 0, 0);
  refreshDisplayMask();
  const capturedLeaves = leaves.filter(leaf => !leaf.hit && wasCaptured(leaf));
  capturedLeaves.forEach(leaf => {
    leaf.hit = true;
    timeLeft += 5;
    burst(leaf.x, leaf.y, 16, ["#c8ef65", "#ffcf54", "#ff4f91", "#ffffff"], 190);
    floatingTexts.push({ x: leaf.x, y: leaf.y, text: "+5 SECONDS", life: 1.5 });
  });
  recalcScore();
  const gained = Math.max(1, score - before);
  floatingTexts.push({ x: player.x, y: player.y - 30, text: `+${gained}% LOVE`, life: 1.5 });
  burst(player.x, player.y, 35, ["#ff4f91", "#ffd35f", "#c8ef65", "#ffffff"], 230);
  showToast(capturedLeaves.length ? `LEAF LOVED! +${capturedLeaves.length * 5} SECONDS` : gained >= 8 ? "BIG LOVE ENERGY!" : "AREA NICEIFIED!");
  beep(620, .08, "triangle", .05); setTimeout(() => beep(910, .12, "triangle", .04), 85);
  player.trail = []; player.outside = false;
}

function hitLeaf(leaf) {
  const hitX = leaf.x, hitY = leaf.y;
  player.invuln = 1.8; player.trail = []; player.outside = false; player.x = W / 2; player.y = H / 2; player.vx = 0; player.vy = 0; timeLeft = Math.max(0, timeLeft - 10); shake = 14;
  burst(hitX, hitY, 22, ["#9caa4d", "#5d7437", "#efbe55"], 210);
  floatingTexts.push({ x: hitX, y: hitY, text: "-10 SECONDS", life: 1.4 });
  showToast("TRAIL CUT! BACK TO THE START"); beep(150, .25, "sawtooth", .05);
}

function update(dt) {
  particles.forEach(p => { p.x += p.vx * dt; p.y += p.vy * dt; p.vy += p.gravity * dt; p.angle += p.spin * dt; p.life -= dt; });
  particles = particles.filter(p => p.life > 0);
  floatingTexts.forEach(t => { t.y -= 30 * dt; t.life -= dt; }); floatingTexts = floatingTexts.filter(t => t.life > 0);
  if (state !== "playing") return;

  timeLeft -= dt; boost = Math.max(0, boost - dt); player.invuln = Math.max(0, player.invuln - dt); shake *= Math.pow(.02, dt);
  ui.time.textContent = formatTime(timeLeft);
  ui.time.style.color = timeLeft < 10 ? "#f52e79" : "";
  ui.boost.classList.toggle("show", boost > 0); ui.boostBar.style.transform = `scaleX(${boost / 4})`;
  if (timeLeft <= 0) return endGame();

  let dx = 0, dy = 0;
  if (keys.has("ArrowLeft") || keys.has("KeyA") || keys.has("left")) dx--;
  if (keys.has("ArrowRight") || keys.has("KeyD") || keys.has("right")) dx++;
  if (keys.has("ArrowUp") || keys.has("KeyW") || keys.has("up")) dy--;
  if (keys.has("ArrowDown") || keys.has("KeyS") || keys.has("down")) dy++;
  if (joystick.active && joystick.strength > .08) { dx = joystick.dx; dy = joystick.dy; }
  if (dx || dy) {
    const len = Math.hypot(dx, dy); dx /= len; dy /= len; player.angle = Math.atan2(dy, dx);
    const inputStrength = joystick.active ? Math.max(.28, joystick.strength) : 1;
    const speed = (boost > 0 ? 856 : 380) * inputStrength; player.vx += (dx * speed - player.vx) * Math.min(1, dt * 12); player.vy += (dy * speed - player.vy) * Math.min(1, dt * 12);
  } else { player.vx *= Math.pow(.0005, dt); player.vy *= Math.pow(.0005, dt); }
  const previousPosition = { x: player.x, y: player.y };
  player.x = clamp(player.x + player.vx * dt, 16, W - 16); player.y = clamp(player.y + player.vy * dt, 16, H - 16);

  const safe = isSafe(player.x, player.y);
  if (!safe && !player.outside) { player.outside = true; player.trail = [previousPosition, { x: player.x, y: player.y }]; beep(330, .07, "triangle", .025); }
  if (player.outside) {
    const prev = player.trail[player.trail.length - 1];
    if (dist(prev, player) > 8) player.trail.push({ x: player.x, y: player.y });
    if (safe && player.trail.length > 4) closeTerritory();
  }

  nextApple -= dt; if (nextApple <= 0 && apples.length < 2) { spawnApple(); nextApple = rand(7, 11) / 1.6; }
  apples.forEach(a => { a.phase += dt * 3; a.life -= dt; if (dist(a, player) < 29) { a.hit = true; boost = 4; burst(a.x, a.y, 18, ["#f23b50", "#ffcf54", "#fff"], 170); showToast("APPLE POWER — ZOOM!"); beep(780, .1, "square", .035); } });
  apples = apples.filter(a => !a.hit && a.life > 0);

  nextLeaf -= dt; if (nextLeaf <= 0) { spawnLeaf(); nextLeaf = rand(.65, 1.25) * (timeLeft / 60 * .35 + .65); }
  leaves.forEach(l => {
    l.x += l.vx * dt; l.y += l.vy * dt; l.angle += l.spin * dt;
    if (!player.outside || player.invuln > 0) return;
    const hitsPlayer = dist(l, player) < l.size + player.radius;
    const hitsTrail = player.trail.some((point, i) => i > 0 && distanceToSegment(l, player.trail[i - 1], point) < l.size + 7);
    if (hitsPlayer || hitsTrail) { l.hit = true; hitLeaf(l); }
  });
  leaves = leaves.filter(l => !l.hit && l.x < W + 50 && l.y < H + 50);
}

function drawHeart(g, x, y, size, color, rotation = 0) {
  g.save(); g.translate(x, y); g.rotate(rotation); g.scale(size / 30, size / 30); g.beginPath(); g.moveTo(0, 8); g.bezierCurveTo(-18, -4, -16, -19, -6, -19); g.bezierCurveTo(0, -19, 4, -15, 6, -10); g.bezierCurveTo(9, -17, 15, -20, 21, -16); g.bezierCurveTo(31, -7, 20, 5, 0, 19); g.closePath(); g.fillStyle = color; g.fill(); g.restore();
}

function render() {
  if (window.innerWidth <= 700) {
    const displayedWidth = gameFrame.clientHeight * (W / H);
    const projectedPlayerX = player.x / W * displayedWidth;
    const cameraX = clamp(gameFrame.clientWidth / 2 - projectedPlayerX, gameFrame.clientWidth - displayedWidth, 0);
    canvas.style.transform = `translateX(${cameraX}px)`;
  } else canvas.style.transform = "";
  ctx.save();
  if (shake > .2) ctx.translate(rand(-shake, shake), rand(-shake, shake));
  ctx.drawImage(dull, 0, 0);
  rctx.clearRect(0, 0, W, H);
  rctx.globalCompositeOperation = "source-over"; rctx.drawImage(nice, 0, 0);
  rctx.globalCompositeOperation = "destination-in"; rctx.drawImage(mask, 0, 0);
  rctx.globalCompositeOperation = "source-over"; ctx.drawImage(reveal, 0, 0);

  if (state === "playing" && player.outside && player.trail.length) {
    ctx.save(); ctx.lineCap = "round"; ctx.lineJoin = "round";
    ctx.strokeStyle = "rgba(74,36,79,.45)"; ctx.lineWidth = 18; ctx.beginPath(); ctx.moveTo(player.trail[0].x, player.trail[0].y); player.trail.forEach(p => ctx.lineTo(p.x, p.y)); ctx.stroke();
    ctx.strokeStyle = "#ff6a9f"; ctx.lineWidth = 11; ctx.stroke();
    ctx.strokeStyle = "rgba(255,255,255,.9)"; ctx.lineWidth = 3; ctx.setLineDash([6, 12]); ctx.stroke(); ctx.restore();
  }

  leaves.forEach(l => {
    ctx.save(); ctx.translate(l.x, l.y); ctx.rotate(l.angle); ctx.fillStyle = "rgba(43,29,47,.22)"; ctx.beginPath(); ctx.ellipse(3, 5, l.size * .65, l.size, 0, 0, Math.PI * 2); ctx.fill();
    ctx.fillStyle = "#8fa344"; ctx.strokeStyle = "#42562e"; ctx.lineWidth = 2; ctx.beginPath(); ctx.moveTo(0, l.size); ctx.bezierCurveTo(-l.size, l.size * .35, -l.size, -l.size * .55, 0, -l.size); ctx.bezierCurveTo(l.size, -l.size * .35, l.size, l.size * .5, 0, l.size); ctx.fill(); ctx.stroke(); ctx.beginPath(); ctx.moveTo(0, l.size); ctx.lineTo(0, -l.size * .8); ctx.stroke(); ctx.restore();
  });

  apples.forEach(a => {
    const bob = Math.sin(a.phase) * 4; ctx.save(); ctx.translate(a.x, a.y + bob); ctx.shadowColor = "rgba(65,21,48,.28)"; ctx.shadowBlur = 10; ctx.shadowOffsetY = 7;
    ctx.fillStyle = "#ef4056"; ctx.strokeStyle = "#592c3d"; ctx.lineWidth = 2.5; ctx.beginPath(); ctx.arc(-7, 2, 12, 0, Math.PI * 2); ctx.arc(7, 2, 12, 0, Math.PI * 2); ctx.arc(0, 8, 15, 0, Math.PI); ctx.fill(); ctx.stroke(); ctx.shadowColor = "transparent";
    ctx.strokeStyle = "#49372b"; ctx.lineWidth = 4; ctx.beginPath(); ctx.moveTo(0, -7); ctx.quadraticCurveTo(1, -17, 8, -21); ctx.stroke(); ctx.fillStyle = "#7caf4b"; ctx.beginPath(); ctx.ellipse(12, -17, 7, 4, -.5, 0, Math.PI * 2); ctx.fill(); ctx.restore();
  });

  if (state === "playing") {
    ctx.save(); ctx.translate(player.x, player.y); ctx.rotate(player.angle); if (boost > 0) { for (let i = 0; i < 3; i++) drawHeart(ctx, -30 - i * 13 - Math.random() * 4, rand(-7, 7), 8 - i, `rgba(255,79,145,${.7 - i * .18})`); }
    ctx.shadowColor = "rgba(44,21,49,.32)"; ctx.shadowBlur = 10; ctx.shadowOffsetY = 6; drawHeart(ctx, 0, 0, 28, player.invuln > 0 && Math.sin(performance.now() / 70) > 0 ? "#fff" : "#ff4f91"); ctx.shadowColor = "transparent";
    ctx.fillStyle = "#2b1d2f"; ctx.beginPath(); ctx.arc(8, -5, 2.3, 0, 6.3); ctx.arc(13, -1, 2.3, 0, 6.3); ctx.fill(); ctx.restore();
  }

  particles.forEach(p => { ctx.save(); ctx.globalAlpha = Math.min(1, p.life * 2); ctx.translate(p.x, p.y); ctx.rotate(p.angle); ctx.fillStyle = p.color; ctx.fillRect(-p.size / 2, -p.size / 3, p.size, p.size * .66); ctx.restore(); });
  floatingTexts.forEach(t => { ctx.save(); ctx.globalAlpha = Math.min(1, t.life * 2); ctx.font = "800 20px Manrope"; ctx.textAlign = "center"; ctx.lineWidth = 5; ctx.strokeStyle = "#fff9ef"; ctx.strokeText(t.text, t.x, t.y); ctx.fillStyle = "#4a244f"; ctx.fillText(t.text, t.x, t.y); ctx.restore(); });
  ctx.restore();
}

function endGame() {
  releaseJoystick();
  state = "ended"; timeLeft = 0; ui.time.textContent = "0:00"; ui.finalScore.textContent = score;
  const results = score >= 70 ? ["LOVE LEGEND!", "The whole block is blushing. Honestly iconic."] : score >= 40 ? ["HEART-WARMING!", "You left this little city much brighter than you found it."] : score >= 15 ? ["A LOVELY START!", "A little kindness goes a long way. Another round?"] : ["LOVE NEEDS YOU!", "The leaves were ruthless. Give the city another chance?"];
  ui.finalTitle.textContent = results[0]; ui.finalCopy.textContent = results[1];
  for (let i = 0; i < 180; i++) particles.push({ x: rand(0, W), y: rand(-H * .4, 0), vx: rand(-40, 40), vy: rand(80, 220), life: rand(2.5, 5), max: 5, size: rand(5, 13), color: ["#ff4f91", "#ffd35f", "#c8ef65", "#8dd9e8", "#fff"][i % 5], spin: rand(-8, 8), angle: rand(0, 6), gravity: 50 });
  setTimeout(() => ui.end.classList.remove("hidden"), 450); beep(520, .15, "triangle", .05); setTimeout(() => beep(780, .2, "triangle", .05), 170);
}

function loop(now) {
  const dt = Math.min(.033, (now - last) / 1000 || 0); last = now; update(dt); render(); requestAnimationFrame(loop);
}

window.addEventListener("keydown", e => { if (["ArrowUp", "ArrowDown", "ArrowLeft", "ArrowRight", "Space"].includes(e.code)) e.preventDefault(); keys.add(e.code); if (e.code === "Space" && state !== "playing") beginGame(); });
window.addEventListener("keyup", e => keys.delete(e.code));

function moveJoystick(clientX, clientY) {
  const dx = clientX - joystick.originX, dy = clientY - joystick.originY;
  const distance = Math.hypot(dx, dy), maxDistance = 46;
  const scale = distance > maxDistance ? maxDistance / distance : 1;
  const nubX = dx * scale, nubY = dy * scale;
  joystick.dx = distance ? dx / distance : 0; joystick.dy = distance ? dy / distance : 0;
  joystick.strength = clamp(distance / maxDistance, 0, 1);
  joystickNub.style.transform = `translate(${nubX}px, ${nubY}px)`;
}

function releaseJoystick(e) {
  if (!joystick.active || (e && e.pointerId !== joystick.pointerId)) return;
  joystick.active = false; joystick.pointerId = null; joystick.dx = 0; joystick.dy = 0; joystick.strength = 0;
  joystickEl.classList.remove("active"); joystickNub.style.transform = "";
}

canvas.addEventListener("pointerdown", e => {
  if (state !== "playing" || e.button > 0) return;
  e.preventDefault();
  const frameRect = gameFrame.getBoundingClientRect();
  joystick.active = true; joystick.pointerId = e.pointerId; joystick.originX = e.clientX; joystick.originY = e.clientY;
  joystickEl.style.left = `${e.clientX - frameRect.left}px`; joystickEl.style.top = `${e.clientY - frameRect.top}px`;
  joystickEl.classList.add("active"); joystickNub.style.transform = ""; canvas.setPointerCapture(e.pointerId);
});
canvas.addEventListener("pointermove", e => { if (joystick.active && e.pointerId === joystick.pointerId) { e.preventDefault(); moveJoystick(e.clientX, e.clientY); } });
canvas.addEventListener("pointerup", releaseJoystick); canvas.addEventListener("pointercancel", releaseJoystick);
canvas.addEventListener("contextmenu", e => e.preventDefault());
document.querySelectorAll("[data-title-start]").forEach(button => button.addEventListener("click", beginGame));
ui.restartBtn.addEventListener("click", beginGame);
ui.sound.addEventListener("click", () => { muted = !muted; ui.sound.classList.toggle("muted", muted); if (!muted) beep(620); });
resetMask(); recalcScore(); requestAnimationFrame(loop);
