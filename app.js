(() => {
  const COLORS = ["R", "B", "Y"];
  const COLOR_NAME = { R: "Rot", B: "Blau", Y: "Gelb" };
  const t = (k) => (window.t ? window.t(k) : k);
  function colorName(c) {
    return c === "R" ? t("red") : c === "B" ? t("blue") : t("yellow");
  }
  const ALL = [];
  for (const c of COLORS) for (let n = 1; n <= 8; n++) ALL.push(c + n);

  const $ = (id) => document.getElementById(id);

  function parse(id) {
    return { color: id[0], n: +id.slice(1) };
  }

  function comboPoints(ids) {
    if (ids.length !== 3) return 0;
    const cards = ids.map(parse).sort((a, b) => a.n - b.n);
    const ns = cards.map((c) => c.n);
    const cs = cards.map((c) => c.color);
    if (ns[0] === ns[1] && ns[1] === ns[2]) return 10 * ns[0] + 10;
    if (ns[1] === ns[0] + 1 && ns[2] === ns[1] + 1) {
      const same = cs[0] === cs[1] && cs[1] === cs[2];
      const mixed = 10 * ns[0];
      return same ? mixed + 40 : mixed;
    }
    return 0;
  }

  function allCombos(field) {
    const out = [];
    const n = field.length;
    for (let i = 0; i < n; i++)
      for (let j = i + 1; j < n; j++)
        for (let k = j + 1; k < n; k++) {
          const ids = [field[i], field[j], field[k]];
          const pts = comboPoints(ids);
          if (pts) out.push({ ids, pts });
        }
    out.sort((a, b) => b.pts - a.pts);
    return out;
  }

  function chest(score) {
    if (score >= 400) return "gold";
    if (score >= 300) return "silver";
    return "bronze";
  }

  function chestValue(score) {
    if (score >= 400) return 3;
    if (score >= 300) return 2;
    return 1;
  }

  /* Heuristic value of a remaining-deck position.
     Prefers gold chance, then silver, then raw points. */
  function leftoverPotential(cards) {
    const byN = Array(9).fill(0);
    const byC = { R: [], B: [], Y: [] };
    for (const id of cards) {
      const p = parse(id);
      byN[p.n]++;
      byC[p.color].push(p.n);
    }
    let est = 0;
    for (let n = 1; n <= 8; n++) {
      if (byN[n] === 3) est += 10 * n + 10;
      else if (byN[n] === 2) est += (10 * n + 10) * 0.2;
    }
    for (const c of COLORS) {
      const s = [...new Set(byC[c])].sort((a, b) => a - b);
      for (const n of s) if (s.includes(n + 1) && s.includes(n + 2)) est += 10 * n + 40;
    }
    return est;
  }

  function packPoints(cards) {
    let pool = cards.filter(Boolean);
    let total = 0;
    for (let guard = 0; guard < 8; guard++) {
      const combos = allCombos(pool);
      if (!combos.length) break;
      const c = combos[0];
      total += c.pts;
      pool = pool.filter((id) => !c.ids.includes(id));
    }
    return total;
  }

  function exactMaxPack(cards) {
    const start = cards.filter(Boolean).slice().sort();
    const memo = new Map();
    function rec(arr) {
      const key = arr.join(",");
      if (memo.has(key)) return memo.get(key);
      let best = 0;
      const combos = allCombos(arr);
      for (let i = 0; i < combos.length; i++) {
        const c = combos[i];
        const used = new Set(c.ids);
        const next = arr.filter((id) => !used.has(id));
        const v = c.pts + rec(next);
        if (v > best) best = v;
      }
      memo.set(key, best);
      return best;
    }
    return rec(start);
  }

  function reachableCap(score) {
    const pool = cardsLeftPool();
    const hard = score + 100 * Math.floor(pool.length / 3);
    if (pool.length <= 14) return Math.min(hard, score + exactMaxPack(pool));
    return hard;
  }

  function policyScore(floorPts, optimisticPts, takeTiny) {
    let u = 0;
    if (floorPts >= 400) u = 4000 + floorPts;
    else if (floorPts >= 300 && optimisticPts >= 400) u = 2800 + optimisticPts;
    else if (floorPts >= 300) u = 2200 + floorPts + Math.min(optimisticPts, 399) * 0.05;
    else if (optimisticPts >= 400) u = 1400 + optimisticPts;
    else if (optimisticPts >= 300) u = 900 + optimisticPts;
    else u = optimisticPts;
    if (floorPts < 300 && takeTiny) u -= 80;
    return u;
  }

  function engineMove(live, remain, score) {
    const E = window.OkeyEngine;
    if (!E) return chooseSimAction(live, remain, score);
    const s = E.createState();
    s.score = score;
    s.consumed = new Set(state.used);
    s.board = state.field.slice();
    if (!state.policyCache) state.policyCache = E.createPolicyCache();
    const mv = E.suggest(s, { cache: state.policyCache, mode: "heuristic" });
    if (!mv) return chooseSimAction(live, remain, score);
    if (mv.kind === "pick" && mv.score > 0) return { kind: "take", ids: mv.cards, pts: mv.score };
    if (mv.kind === "discard") return { kind: "discard", ids: mv.cards, pts: 0 };
    return chooseSimAction(live, remain, score);
  }

  function chooseSimAction(live, remain, score) {
    const combos = allCombos(live);
    const needG = 400 - score;
    const needS = 300 - score;
    const takeOf = (c) => ({ kind: "take", ids: c.ids, pts: c.pts, afterScore: score + c.pts });
    if (combos.length) {
      const hitG = needG > 0 ? combos.filter((c) => c.pts >= needG).sort((a, b) => a.pts - b.pts)[0] : null;
      if (hitG) return takeOf(hitG);
      const hitS = needS > 0 ? combos.filter((c) => c.pts >= needS).sort((a, b) => a.pts - b.pts)[0] : null;
      if (hitS) return takeOf(hitS);
      if (combos[0].pts >= 30) return takeOf(combos[0]);
      if (combos[0].pts >= 10 && remain.length <= 8) return takeOf(combos[0]);
    }
    if (!live.length) return null;
    const dump = live.slice().sort((a, b) => parse(a).n - parse(b).n)[0];
    return { kind: "discard", ids: [dump], pts: 0, afterScore: score };
  }

  function chestOdds(score) {
    const pool = cardsLeftPool();
    const maxC = Math.floor(pool.length / 3);
    const cap = reachableCap(score);
    if (score >= 400) return { gold: 1, silver: 0, bronze: 0, evPts: score };
    if (maxC <= 0) {
      const ch = chest(score);
      return { gold: ch === "gold" ? 1 : 0, silver: ch === "silver" ? 1 : 0, bronze: ch === "bronze" ? 1 : 0, evPts: score };
    }
    if (score < 300 && cap < 300) return { gold: 0, silver: 0, bronze: 1, evPts: cap };
    if (score >= 300 && cap < 400) return { gold: 0, silver: 1, bronze: 0, evPts: cap };
    const expP = Math.min(cap, score + 42 * maxC);
    if (score >= 300) {
      const g = Math.min(0.7, Math.max(0.08, (cap - 400 + 80) / 160));
      return { gold: g, silver: 1 - g, bronze: 0, evPts: expP };
    }
    const s = Math.min(0.72, Math.max(0.12, (cap - 280) / 180));
    const g = cap >= 400 ? Math.min(0.4, (cap - 400) / 200) : 0;
    const b = Math.max(0.08, 1 - s - g);
    return { gold: g, silver: s, bronze: b, evPts: expP };
  }

  function greedyFinish(field, remain, score) {
    let f = field.filter(Boolean);
    let r = remain.slice();
    let s = score;
    for (let step = 0; step < 12; step++) {
      if (f.length + r.length < 3) break;
      const act = chooseSimAction(f, r, s);
      if (!act) break;
      if (act.kind === "take") {
        s += act.pts;
        f = f.filter((id) => !act.ids.includes(id));
      } else {
        f = f.filter((id) => id !== act.ids[0]);
      }
      while (f.length < 5 && r.length) f.push(r.shift());
    }
    return s;
  }

  function evalState(field, remain, score, sims) {
    const cardsLeft = field.filter(Boolean).length + remain.length;
    if (cardsLeft < 3) {
      return {
        kind: "end",
        evChest: chestValue(score),
        evPts: score,
        gold: score >= 400 ? 1 : 0,
        silver: score >= 300 && score < 400 ? 1 : 0,
        bronze: score < 300 ? 1 : 0,
      };
    }

    const live = field.filter(Boolean);
    const combos = allCombos(live);
    let best = null;

    const consider = (kind, payload, ptsGain, nextFieldBase) => {
      let g = 0, s = 0, b = 0, ptsSum = 0, chestSum = 0;
      for (let t = 0; t < sims; t++) {
        const bag = remain.slice();
        shuffle(bag);
        const nextScore = score + ptsGain;
        const need = 5 - nextFieldBase.length;
        const drawn = bag.splice(0, Math.max(0, need));
        const nf = nextFieldBase.concat(drawn);
        const endScore = nextScore + leftoverPotential(bag.concat(nf)) * 0.45;
        const ch = chest(endScore);
        if (ch === "gold") g++;
        else if (ch === "silver") s++;
        else b++;
        ptsSum += endScore;
        chestSum += chestValue(endScore);
      }
      const res = {
        kind,
        payload,
        ptsGain,
        gold: g / sims,
        silver: s / sims,
        bronze: b / sims,
        evPts: ptsSum / sims,
        evChest: chestSum / sims,
      };
      if (!best || better(res, best)) best = res;
    };

    for (const c of combos) {
      consider("take", c.ids, c.pts, live.filter((id) => !c.ids.includes(id)));
    }
    for (const id of live) {
      consider("discard", [id], 0, live.filter((x) => x !== id));
    }
    return best || {
      kind: "end",
      evChest: chestValue(score),
      evPts: score,
      gold: score >= 400 ? 1 : 0,
      silver: score >= 300 && score < 400 ? 1 : 0,
      bronze: score < 300 ? 1 : 0,
    };
  }

  function better(a, b) {
    const aSafe = a.gold + a.silver;
    const bSafe = b.gold + b.silver;
    if (Math.abs(aSafe - bSafe) > 0.015) return aSafe > bSafe;
    if (Math.abs(a.gold - b.gold) > 0.015) return a.gold > b.gold;
    if (Math.abs(a.silver - b.silver) > 0.015) return a.silver > b.silver;
    return a.evPts > b.evPts;
  }

  function shuffle(a) {
    for (let i = a.length - 1; i > 0; i--) {
      const j = (Math.random() * (i + 1)) | 0;
      [a[i], a[j]] = [a[j], a[i]];
    }
    return a;
  }

  /* ---------- state ---------- */
  const state = {
    field: [null, null, null, null, null],
    used: new Set(),
    remain: new Set(ALL),
    score: 0,
    pick: [],
    history: [],
    suggestion: null,
    session: { games: 0, gold: 0, silver: 0, bronze: 0, pts: 0 },
    lifetime: loadLifetime(),
    pendingColor: null,
    arisePlayed: false,
    runLogged: false,
    failShown: false,
    goldLockShown: false,
    endShown: false,
    toldShown: false,
    keepPlaying: false,
  };

  function needExp(level) {
    if (level >= 100) return 0;
    return 50 * level;
  }
  function rankOf(lv) {
    if (lv >= 100) return { name: t("endrank"), key: "end", art: "jinwoo.jpg" };
    if (lv >= 75) return { name: t("monarch"), key: "monarch", art: "jinwoo.jpg" };
    if (lv >= 50) return { name: t("igris"), key: "igris", art: "igris.jpg" };
    if (lv >= 25) return { name: t("soldier"), key: "soldier", art: "igris-full.jpg" };
    return { name: t("amateur"), key: "newbie", art: "igris.jpg" };
  }
  const hunt = loadHunt();
  function loadHunt() {
    try {
      const raw = localStorage.getItem("okey-jinchuriki-hunt");
      if (raw) return JSON.parse(raw);
    } catch (_) {}
    return { level: 1, exp: 0 };
  }
  function saveHunt() {
    localStorage.setItem("okey-jinchuriki-hunt", JSON.stringify(hunt));
  }
  function grantExp(n) {
    if (hunt.level >= 100) {
      hunt.level = 100;
      hunt.exp = 0;
      saveHunt();
      renderLevel("MAX");
      return;
    }
    hunt.exp += n;
    let ups = 0;
    while (hunt.level < 100 && hunt.exp >= needExp(hunt.level)) {
      hunt.exp -= needExp(hunt.level);
      hunt.level++;
      ups++;
    }
    if (hunt.level >= 100) {
      hunt.level = 100;
      hunt.exp = 0;
    }
    saveHunt();
    renderLevel((ups ? "LEVEL UP ×" + ups + " · " : "") + "+" + n + " EXP");
    if (ups) flashLevelUp();
  }
  function renderLevel(note) {
    const r = rankOf(hunt.level);
    const need = needExp(hunt.level) || 1;
    const pct = hunt.level >= 100 ? 100 : Math.min(100, (hunt.exp / need) * 100);
    if ($("rankName")) $("rankName").textContent = r.name.toUpperCase();
    if ($("lvNow")) $("lvNow").textContent = hunt.level >= 100 ? "LV.100" : "LV." + hunt.level;
    if ($("lvNeed")) $("lvNeed").textContent = hunt.level >= 100 ? "MAX" : hunt.exp + " / " + need + " EXP";
    if ($("xpFill")) $("xpFill").style.width = pct + "%";
    const w = $("walker");
    if (w) {
      w.style.left = "";
      w.className = "swordsman " + r.key;
    }
    if ($("rankArt")) $("rankArt").src = r.art; /* unused if poses in markup */
    if ($("xpGain") && note) $("xpGain").textContent = note;
  }
  function flashLevelUp() {
    const p = document.querySelector(".hunt-panel");
    if (p) {
      p.classList.add("lvlup");
      setTimeout(() => p.classList.remove("lvlup"), 1200);
    }
    try {
      const ctx = ensureAudio();
      const now = ctx.currentTime;
      const o = ctx.createOscillator();
      o.type = "sine";
      o.frequency.setValueAtTime(90, now);
      o.frequency.exponentialRampToValueAtTime(40, now + 0.35);
      const g = ctx.createGain();
      g.gain.setValueAtTime(0.0001, now);
      g.gain.exponentialRampToValueAtTime(0.28, now + 0.03);
      g.gain.exponentialRampToValueAtTime(0.0001, now + 0.4);
      o.connect(g).connect(ctx.destination);
      o.start(now);
      o.stop(now + 0.42);
    } catch (_) {}
  }

  function loadLifetime() {
    try {
      const raw = localStorage.getItem("okey-jinchuriki-vault");
      if (raw) return JSON.parse(raw);
    } catch (_) {}
    return { total: 0, gold: 0, silver: 0, bronze: 0 };
  }

  const recent = loadRecent();
  function loadRecent() {
    try {
      const raw = localStorage.getItem("okey-jinchuriki-recent");
      if (raw) return JSON.parse(raw);
    } catch (_) {}
    return [];
  }
  function pushRecent(score, ch, exp) {
    recent.unshift({ score, ch, exp, t: Date.now() });
    if (recent.length > 10) recent.length = 10;
    localStorage.setItem("okey-jinchuriki-recent", JSON.stringify(recent));
    renderRecent();
  }
  function renderRecent() {
    const box = $("recentList");
    if (!box) return;
    box.innerHTML = "";
    const head = document.createElement("div");
    head.className = "recent-row head";
    head.innerHTML = "<span>#</span><span>" + t("points") + "</span><span></span><span>EXP</span>";
    box.appendChild(head);
    if (!recent.length) {
      const row = document.createElement("div");
      row.className = "recent-row";
      row.innerHTML = "<span>—</span><span>—</span><span>—</span><span>—</span>";
      box.appendChild(row);
      return;
    }
    recent.forEach((r, i) => {
      const row = document.createElement("div");
      row.className = "recent-row " + r.ch;
      row.innerHTML =
        "<span>" + (i + 1) + "</span>" +
        "<span>" + r.score + "</span>" +
        "<span>" + t(r.ch) + "</span>" +
        "<span>+" + r.exp + "</span>";
      box.appendChild(row);
    });
  }
  const badges = loadBadges();
  function loadBadges() {
    try {
      const raw = localStorage.getItem("okey-jinchuriki-badges");
      if (raw) return JSON.parse(raw);
    } catch (_) {}
    return {};
  }
  function saveBadges() {
    localStorage.setItem("okey-jinchuriki-badges", JSON.stringify(badges));
  }
  function unlockBadges(ch) {
    if (ch === "gold") badges.gold = 1;
    if (ch === "silver") badges.silver = 1;
    if ((state.lifetime.total || 0) >= 10) badges.ten = 1;
    if (hunt.level >= 25) badges.lv25 = 1;
    if (hunt.level >= 50) badges.lv50 = 1;
    if (hunt.level >= 75) badges.lv75 = 1;
    if (hunt.level >= 100) badges.lv100 = 1;
    saveBadges();
    renderBadges();
  }
  function renderBadges() {
    const g = $("badgeGrid");
    if (!g) return;
    const items = [
      ["gold", "bGold"],
      ["silver", "bSilver"],
      ["ten", "bTen"],
      ["lv25", "bLv25"],
      ["lv50", "bLv50"],
      ["lv75", "bLv75"],
      ["lv100", "bLv100"],
    ];
    g.innerHTML = "";
    items.forEach(([id, key]) => {
      const el = document.createElement("span");
      el.className = "badge" + (badges[id] ? " on" : "");
      el.textContent = t(key);
      g.appendChild(el);
    });
  }

  const CLAN = "okey-jinchuriki-clan";
  const CLAN_SEED = { gold: 3188, silver: 25227, bronze: 28843, total: 57258 };
  const CLAN_API = "https://abacus.jasoncameron.dev";
  async function clanGet(key) {
    const r = await fetch(CLAN_API + "/get/" + CLAN + "/" + key);
    const j = await r.json();
    return Number(j.value) || 0;
  }
  async function clanHit(key) {
    const r = await fetch(CLAN_API + "/hit/" + CLAN + "/" + key);
    const j = await r.json();
    return Number(j.value) || 0;
  }
  async function loadClan() {
    paintClan({ gold: 0, silver: 0, bronze: 0, total: 0 });
    try {
      const [gold, silver, bronze, total] = await Promise.all([
        clanGet("gold"), clanGet("silver"), clanGet("bronze"), clanGet("total"),
      ]);
      paintClan({ gold, silver, bronze, total });
    } catch (_) {}
  }
  function paintClan(v) {
    const gold = CLAN_SEED.gold + (v.gold || 0);
    const silver = CLAN_SEED.silver + (v.silver || 0);
    const bronze = CLAN_SEED.bronze + (v.bronze || 0);
    const total = CLAN_SEED.total + (v.total || 0);
    if ($("gTotal")) $("gTotal").textContent = total;
    if ($("gGold")) $("gGold").textContent = gold;
    if ($("gSilver")) $("gSilver").textContent = silver;
    if ($("gBronze")) $("gBronze").textContent = bronze;
    const pct = (n) => (total ? Math.round((n / total) * 100) + "%" : "0%");
    if ($("gGoldPct")) $("gGoldPct").textContent = pct(gold);
    if ($("gSilverPct")) $("gSilverPct").textContent = pct(silver);
    if ($("gBronzePct")) $("gBronzePct").textContent = pct(bronze);
  }
  async function pushGlobal(ch) {
    try {
      await Promise.all([clanHit(ch), clanHit("total")]);
      loadClan();
    } catch (_) {}
  }

  function saveLifetime() {
    localStorage.setItem("okey-jinchuriki-vault", JSON.stringify(state.lifetime));
  }

  function renderVault() {
    const v = state.lifetime;
    const t = v.total || 0;
    $("cTotal").textContent = t;
    $("cGold").textContent = v.gold;
    $("cSilver").textContent = v.silver;
    $("cBronze").textContent = v.bronze;
    $("cGoldPct").textContent = t ? Math.round((v.gold / t) * 100) + "%" : "0%";
    $("cSilverPct").textContent = t ? Math.round((v.silver / t) * 100) + "%" : "0%";
    $("cBronzePct").textContent = t ? Math.round((v.bronze / t) * 100) + "%" : "0%";
  }

  let audioCtx = null;
  function ensureAudio() {
    if (!audioCtx) audioCtx = new (window.AudioContext || window.webkitAudioContext)();
    if (audioCtx.state === "suspended") audioCtx.resume();
    return audioCtx;
  }

  function playArise() {
    const fx = $("ariseFx");
    const ag = $("ariseGif");
    if (ag) ag.src = "igris-crack.gif?t=" + Date.now();
    fx.hidden = false;
    fx.classList.add("is-open");
    const sfx = $("ariseSfx");
    if (sfx) {
      try { sfx.currentTime = 0; } catch (_) {}
      sfx.volume = 0.9;
      sfx.play().catch(() => {});
    }
    setTimeout(() => {
      fx.hidden = true;
      fx.classList.remove("is-open");
    }, 2800);

    try {
      const ctx = ensureAudio();
      const now = ctx.currentTime;
      const master = ctx.createGain();
      master.gain.setValueAtTime(0.0001, now);
      master.gain.exponentialRampToValueAtTime(0.35, now + 0.08);
      master.gain.exponentialRampToValueAtTime(0.0001, now + 2.4);
      master.connect(ctx.destination);

      const osc = ctx.createOscillator();
      osc.type = "sawtooth";
      osc.frequency.setValueAtTime(70, now);
      osc.frequency.exponentialRampToValueAtTime(28, now + 2.1);
      const f = ctx.createBiquadFilter();
      f.type = "lowpass";
      f.frequency.setValueAtTime(420, now);
      f.frequency.exponentialRampToValueAtTime(140, now + 2);
      osc.connect(f).connect(master);
      osc.start(now);
      osc.stop(now + 2.3);

      const noiseBuf = ctx.createBuffer(1, ctx.sampleRate * 0.5, ctx.sampleRate);
      const data = noiseBuf.getChannelData(0);
      for (let i = 0; i < data.length; i++) data[i] = (Math.random() * 2 - 1) * (1 - i / data.length);
      const noise = ctx.createBufferSource();
      noise.buffer = noiseBuf;
      const ng = ctx.createGain();
      ng.gain.setValueAtTime(0.18, now);
      ng.gain.exponentialRampToValueAtTime(0.001, now + 0.45);
      noise.connect(ng).connect(master);
      noise.start(now);
    } catch (_) {}

    }


  function cardsLeftPool() {
    return state.field.filter(Boolean).concat([...state.remain]);
  }

  function silverImpossible() {
    const pool = cardsLeftPool();
    if (state.score >= 300) return false;
    if (state.score === 0 && state.used.size === 0) return false;
    return reachableCap(state.score) < 300;
  }

  function goldLockedOut() {
    if (state.score < 300 || state.score >= 400) return false;
    return reachableCap(state.score) < 400;
  }

  function noMovesLeft() {
    const live = state.field.filter(Boolean);
    const left = live.length + state.remain.size;
    if (left >= 3 && allCombos(live).length) return false;
    if (state.remain.size > 0 && live.length > 0) return false;
    return live.length + state.remain.size < 3 || (!allCombos(live).length && state.remain.size === 0);
  }

  function openSys(kind, msg, mode) {
    const m = $("failModal");
    if (!m) return;
    if (kind === "fail" && state.failShown) return;
    if (kind === "goldlock" && state.goldLockShown) return;
    if (kind === "end" && state.endShown) return;
    if (kind === "toldyou" && state.toldShown) return;
    if (kind === "fail") state.failShown = true;
    if (kind === "goldlock") state.goldLockShown = true;
    if (kind === "end") state.endShown = true;
    if (kind === "toldyou") state.toldShown = true;
    $("sysMsg").textContent = msg;
    const reset = $("btnSysReset");
    const ok = $("btnFailOk");
    const cont = $("btnContinue");
    reset.style.display = "block";
    ok.style.display = "none";
    cont.style.display = (mode === "fail" || mode === "lock") ? "block" : "none";
    m.hidden = false;
    m.classList.add("is-open");
  }

  function showFailModal() {
    if (state.keepPlaying) return;
    if (!silverImpossible()) return;
    const cap = reachableCap(state.score);
    openSys(
      "fail",
      t("bronzeSorry") + " (" + state.score + " + max. " + Math.max(0, cap - state.score) + " = " + cap + ")",
      "fail"
    );
  }

  function showGoldLockModal() {
    if (!goldLockedOut()) return;
    openSys("goldlock", t("goldLock"), "lock");
  }

  function showEndModal() {
    if (!noMovesLeft()) return;
    finishRun();
    const ch = chest(state.score);
    if (state.keepPlaying && ch === "bronze") {
      openSys("toldyou", t("toldYou"), "end");
      return;
    }
    openSys(
      "end",
      t("endGame") + " " + t(ch) + " (" + state.score + " " + t("pts") + ").",
      "end"
    );
  }

  function hideFailModal() {
    const m = $("failModal");
    if (!m) return;
    m.hidden = true;
    m.classList.remove("is-open");
  }

  function maybeArise(goldP) {
    const locked = state.score >= 400;
    if (locked && !state.arisePlayed) {
      state.arisePlayed = true;
      playArise();
    }
    if (!locked) state.arisePlayed = false;
  }

  function snapshot() {
    return {
      field: state.field.slice(),
      used: [...state.used],
      remain: [...state.remain],
      score: state.score,
      pick: state.pick.slice(),
    };
  }

  function restore(s) {
    state.field = s.field;
    state.used = new Set(s.used);
    state.remain = new Set(s.remain);
    state.score = s.score;
    state.pick = s.pick;
  }

  function pushHist() {
    state.history.push(snapshot());
    if (state.history.length > 80) state.history.shift();
  }

  function fieldReady() {
    return state.field.every(Boolean);
  }

  /* ---------- UI ---------- */
  function renderPalette() {
    const pal = $("palette");
    pal.innerHTML = "";
    for (const c of COLORS) {
      const row = document.createElement("div");
      row.className = "prow " + c;
      for (let n = 1; n <= 8; n++) {
        const id = c + n;
        const el = document.createElement("button");
        el.type = "button";
        el.className = `pcard c-${c}` + (state.used.has(id) || state.field.includes(id) ? " used" : "");
        el.textContent = n;
        el.title = COLOR_NAME[c] + " " + n;
        el.addEventListener("click", () => addToField(id));
        row.appendChild(el);
      }
      pal.appendChild(row);
    }
  }

  function renderField() {
    const box = $("field");
    box.innerHTML = "";
    state.field.forEach((id, i) => {
      const el = document.createElement("div");
      el.className = "slot" + (id ? ` filled c-${id[0]}` : " empty");
      if (!id && i === firstEmpty() && state.field.some(Boolean)) {
        el.classList.add("next-in");
        const tag = document.createElement("span");
        tag.className = "tag tag-next";
        tag.textContent = t("here");
        el.appendChild(tag);
      }
      if (id && state.pick.includes(id)) el.classList.add("picked");
      const sug = state.suggestion;
      if (id && state.pick.includes(id)) {
        const tag = document.createElement("span");
        tag.className = "tag tag-on";
        tag.textContent = t("picked");
        el.appendChild(tag);
      } else if (id && sug && sug.kind === "take" && sug.payload.includes(id)) {
        el.classList.add("suggest");
        const tag = document.createElement("span");
        tag.className = "tag tag-pick";
        tag.textContent = t("pick");
        el.appendChild(tag);
      } else if (id && sug && sug.kind === "discard" && sug.payload[0] === id) {
        el.classList.add("dump");
        const tag = document.createElement("span");
        tag.className = "tag tag-dump";
        tag.textContent = t("dump");
        el.appendChild(tag);
      }
      const num = document.createElement("span");
      num.textContent = id ? id.slice(1) : "?";
      el.appendChild(num);
      el.addEventListener("click", () => {
        if (!id) return;
        togglePick(id);
      });
      el.addEventListener("contextmenu", (e) => {
        e.preventDefault();
        if (id) discard(id);
      });
      box.appendChild(el);
    });
  }

  function renderRemain() {
    const g = $("remainGrid");
    g.innerHTML = "";
    for (const c of COLORS) {
      const row = document.createElement("div");
      row.className = "remain-row";
      for (let n = 1; n <= 8; n++) {
        const id = c + n;
        const d = document.createElement("div");
        const onField = state.field.includes(id);
        d.className = "dot" + (state.remain.has(id) || onField ? ` on c-${c}` : "");
        if (onField) d.style.outline = "1px solid #fff";
        d.textContent = n;
        row.appendChild(d);
      }
      g.appendChild(row);
    }
    $("remainCount").textContent = " · " + state.remain.size + " im Stapel · " + state.field.filter(Boolean).length + " offen";
  }

  function renderPick() {
    const row = $("pickRow");
    row.innerHTML = "";
    state.pick.forEach((id) => {
      const el = document.createElement("div");
      el.className = `slot filled c-${id[0]}`;
      el.style.width = "48px";
      el.style.height = "64px";
      el.style.fontSize = "20px";
      el.textContent = id.slice(1);
      row.appendChild(el);
    });
    const pts = comboPoints(state.pick);
    if (state.pick.length === 3) {
      $("pickPts").textContent = pts ? pts + " Punkte" : "Keine gültige Kombi";
      $("btnConfirm").disabled = !pts;
    } else {
      $("pickPts").textContent = state.pick.length + "/3 ausgewählt";
      $("btnConfirm").disabled = true;
    }
  }

  function renderScore() {
    $("score").textContent = state.score;
    $("barFill").style.width = Math.min(100, (state.score / 500) * 100) + "%";
    const ch = chest(state.score);
    $("chestNow").textContent = ch === "gold" ? "Gold" : ch === "silver" ? "Silber" : "Bronze";
    $("chestNow").style.color = ch === "gold" ? "var(--gold)" : ch === "silver" ? "var(--silver)" : "var(--bronze)";
  }

  function renderSession() {
    const s = state.session;
    $("sGames").textContent = s.games;
    $("sAvg").textContent = s.games ? Math.round(s.pts / s.games) : "–";
    $("sGold").textContent = s.gold;
    $("sSilver").textContent = s.silver;
    $("sBronze").textContent = s.bronze;
    renderVault();
  }

  function log(msg) {
    const ol = $("log");
    const li = document.createElement("li");
    li.textContent = msg;
    ol.prepend(li);
  }

  function suggestText(s) {
    if (!s || !s.kind) return "Keine Auswertung.";
    const pct = (x) => Math.round(x * 1000) / 10 + "%";
    if (s.kind === "take") {
      const names = s.payload.map((id) => COLOR_NAME[id[0]] + " " + id.slice(1)).join(" · ");
      return `NEHMEN: ${names}\n+${s.ptsGain} Punkte\nGold ${pct(s.gold)} · Silber ${pct(s.silver)} · Bronze ${pct(s.bronze)}\nErwartete Endpunkte ≈ ${Math.round(s.evPts)}`;
    }
    if (s.kind === "discard") {
      const id = s.payload[0];
      return `ABWERFEN: ${COLOR_NAME[id[0]]} ${id.slice(1)}\nDanach neue Karte ziehen.\nGold ${pct(s.gold)} · Silber ${pct(s.silver)} · Bronze ${pct(s.bronze)}\nErwartete Endpunkte ≈ ${Math.round(s.evPts)}`;
    }
    return "Runde beenden.";
  }

  function updateSuggestion() {
    if (!fieldReady()) {
      state.suggestion = null;
      const ban = $("cmdBanner");
      if (ban) {
        ban.className = "cmd-banner wait";
        ban.textContent = t("waitCmd");
      }
      $("suggestion").textContent = t("waitDeal");
      $("btnUse").disabled = true;
      const filled = state.field.filter(Boolean).length;
      const fresh = state.score === 0 && state.used.size === 0 && filled === 0;
      if (fresh) {
        paintPct(0.33, 0.33, 0.34);
        $("evalNote").textContent = t("wait5");
      } else {
        const odds = chestOdds(state.score);
        paintPct(odds.gold, odds.silver, odds.bronze);
        $("evalNote").textContent = t("nextCard");
      }
      if (ban) {
        ban.textContent = filled
          ? "Noch " + (5 - filled) + " Karte(n) eintragen."
          : t("waitCmd");
      }
      if (!fresh) checkNotices();
      return;
    }
    const field = state.field.slice();
    const remain = [...state.remain];
    const live = field.filter(Boolean);
    const act = engineMove(live, remain, state.score);
    const left = live.length + remain.length;
    const odds = chestOdds(state.score);
    let res;
    if (!act) {
      res = { kind: "end", gold: odds.gold, silver: odds.silver, bronze: odds.bronze, evPts: odds.evPts, evChest: chestValue(state.score), payload: [], ptsGain: 0 };
    } else {
      res = {
        kind: act.kind,
        payload: act.ids,
        ptsGain: act.pts,
        gold: odds.gold,
        silver: odds.silver,
        bronze: odds.bronze,
        evPts: odds.evPts,
        evChest: 0,
      };
    }
    state.suggestion = res;
    paintSuggest(res);
    renderField();
    $("btnUse").disabled = !res.kind || res.kind === "end";
    paintRates(res);
    function paintSuggest(res) {
    $("suggestion").textContent = suggestText(res);
    const ban = $("cmdBanner");
    if (!ban) return;
    if (res.kind === "take") {
      ban.className = "cmd-banner take";
      ban.textContent = t("select") + ": " + res.payload.map((id) => colorName(id[0]) + " " + id.slice(1)).join("  +  ") + "   (+" + res.ptsGain + ")";
    } else if (res.kind === "discard") {
      ban.className = "cmd-banner dump";
      ban.textContent = t("discard") + ": " + colorName(res.payload[0][0]) + " " + res.payload[0].slice(1);
    } else {
      ban.className = "cmd-banner wait";
      ban.textContent = t("noMoves");
    }
  }
  function paintPct(g, s, b) {
    $("pGold").textContent = Math.round(g * 100) + "%";
    $("pSilver").textContent = Math.round(s * 100) + "%";
    $("pBronze").textContent = Math.round(b * 100) + "%";
    $("barGold").style.width = g * 100 + "%";
    $("barSilver").style.width = s * 100 + "%";
    $("barBronze").style.width = b * 100 + "%";
  }
  function paintRates(res) {
    const gp = Math.round(res.gold * 1000) / 10;
    const sp = Math.round(res.silver * 1000) / 10;
    const bp = Math.round(res.bronze * 1000) / 10;
    $("pGold").textContent = gp + "%";
    $("pSilver").textContent = sp + "%";
    $("pBronze").textContent = bp + "%";
    $("barGold").style.width = gp + "%";
    $("barSilver").style.width = sp + "%";
    $("barBronze").style.width = bp + "%";
    $("evalNote").textContent =
      res.kind === "take" ? "Befehl: Kombi nehmen." : res.kind === "discard" ? "Befehl: Karte in den Schatten werfen." : "Keine weiteren Züge.";
    if (state.score >= 400) maybeArise(1);
    checkNotices();
  }
  }

  function renderAll() {
    renderPalette();
    renderField();
    renderRemain();
    renderPick();
    renderScore();
    renderSession();
  }

  /* ---------- actions ---------- */
  function firstEmpty() {
    return state.field.findIndex((x) => !x);
  }

  function addToField(id) {
    if (state.used.has(id) || state.field.includes(id)) return;
    const i = firstEmpty();
    if (i < 0) return;
    pushHist();
    state.field[i] = id;
    state.remain.delete(id);
    state.pick = [];
    renderAll();
    updateSuggestion();
  }

  function togglePick(id) {
    if (!id) return;
    if (state.pick.includes(id)) state.pick = state.pick.filter((x) => x !== id);
    else if (state.pick.length < 3) state.pick = state.pick.concat(id);
    if (state.pick.length === 3 && comboPoints(state.pick)) {
      takeCombo(state.pick.slice());
      return;
    }
    renderField();
    renderPick();
  }

  function takeCombo(ids) {
    const pts = comboPoints(ids);
    if (!pts) return;
    pushHist();
    ids.forEach((id) => {
      state.used.add(id);
      const i = state.field.indexOf(id);
      if (i >= 0) state.field[i] = null;
    });
    state.score += pts;
    state.pick = [];
    log(`+${pts}  (${ids.join(" ")})  → ${state.score}`);
    if ($("practice") && $("practice").checked) fillPracticeGaps();
    renderAll();
    updateSuggestion();
    maybeEnd();
  }

  function fillPracticeGaps() {
    const bag = [...state.remain];
    shuffle(bag);
    while (firstEmpty() >= 0 && bag.length) {
      const id = bag.shift();
      if (!id || state.used.has(id) || state.field.includes(id)) continue;
      state.field[firstEmpty()] = id;
      state.remain.delete(id);
    }
  }

  function compactField() {
    const live = state.field.filter(Boolean);
    state.field = [live[0] || null, live[1] || null, live[2] || null, live[3] || null, live[4] || null];
  }

  function discard(id) {
    if (!id) return;
    pushHist();
    state.used.add(id);
    const i = state.field.indexOf(id);
    if (i >= 0) state.field[i] = null;
    state.pick = [];
    log(`Abwurf ${id}`);
    if ($("practice") && $("practice").checked) fillPracticeGaps();
    renderAll();
    updateSuggestion();
    maybeEnd();
  }

  function checkNotices() {
    if (silverImpossible()) showFailModal();
    else if (goldLockedOut()) showGoldLockModal();
    if (noMovesLeft()) showEndModal();
  }

  function maybeEnd() {
    checkNotices();
  }

  function finishRun() {
    if (state.runLogged) return;
    state.runLogged = true;
    const ch = chest(state.score);
    state.session.games++;
    state.session.pts += state.score;
    state.session[ch]++;
    state.lifetime.total++;
    state.lifetime[ch]++;
    saveLifetime();
    pushGlobal(ch);
    const gained = ch === "gold" ? 50 : ch === "silver" ? 25 : 1;
    grantExp(gained);
    pushRecent(state.score, ch, gained);
    unlockBadges(ch);
    log(`Runde Ende: ${state.score} → ${ch.toUpperCase()} TRUHE (+${gained} EXP)`);
    renderSession();
    $("evalNote").textContent = t("done");
    if (ch === "gold") maybeArise(1);
  }

  function useSuggestion() {
    const s = state.suggestion;
    if (!s) return;
    if (s.kind === "take") {
      takeCombo(s.payload.slice());
    } else if (s.kind === "discard") {
      discard(s.payload[0]);
    }
  }

  function confirmPick() {
    if (state.pick.length === 3 && comboPoints(state.pick)) takeCombo(state.pick.slice());
  }

  function undo() {
    const prev = state.history.pop();
    if (!prev) return;
    restore(prev);
    renderAll();
    updateSuggestion();
  }

  function reset() {
    if (state.score && fieldReady()) {
      /* count current if user resets mid/end */
    }
    state.field = [null, null, null, null, null];
    state.used = new Set();
    state.remain = new Set(ALL);
    state.score = 0;
    state.pick = [];
    state.history = [];
    state.suggestion = null;
    state.arisePlayed = false;
    state.runLogged = false;
    state.policyCache = window.OkeyEngine ? window.OkeyEngine.createPolicyCache() : null;
    state.failShown = false;
    state.goldLockShown = false;
    state.endShown = false;
    state.toldShown = false;
    state.keepPlaying = false;
    hideFailModal();
    $("log").innerHTML = "";
    renderAll();
    updateSuggestion();
  }

  function dealPractice() {
    reset();
    const bag = shuffle(ALL.slice());
    for (let i = 0; i < 5; i++) {
      const id = bag[i];
      state.field[i] = id;
      state.remain.delete(id);
    }
    renderAll();
    updateSuggestion();
  }

  /* keyboard */
  document.addEventListener("keydown", (e) => {
    const k = e.key.toUpperCase();
    if (k === "R" || k === "B" || k === "Y") {
      state.pendingColor = k;
      return;
    }
    if (state.pendingColor && k >= "1" && k <= "8") {
      addToField(state.pendingColor + k);
      state.pendingColor = null;
      return;
    }
    if (e.code === "Space") {
      e.preventDefault();
      useSuggestion();
    }
    if (e.key === "Enter") confirmPick();
    if (e.key === "Backspace") {
      e.preventDefault();
      undo();
    }
    if (e.key === "Escape") reset();
  });

  $("btnConfirm").addEventListener("click", confirmPick);
  $("btnUse").addEventListener("click", useSuggestion);
  $("btnUndo").addEventListener("click", undo);
  $("btnReset").addEventListener("click", reset);
  $("practice").addEventListener("change", (e) => {
    if (e.target.checked) dealPractice();
  });
  $("btnFailOk").addEventListener("click", hideFailModal);
  $("btnSysReset").addEventListener("click", () => {
    finishRun();
    hideFailModal();
    reset();
  });
  document.getElementById("langBar").addEventListener("click", (e) => {
    const btn = e.target.closest("[data-lang]");
    if (!btn) return;
    window.setLang(btn.getAttribute("data-lang"));
    renderAll();
    updateSuggestion();
    renderLevel();
    renderRecent();
    renderBadges();
  });
  $("btnContinue").addEventListener("click", () => {
    state.keepPlaying = true;
    hideFailModal();
  });
  $("logToggle").addEventListener("click", () => {
    const panel = document.querySelector(".log-panel");
    panel.classList.toggle("closed");
    $("logToggle").textContent = panel.classList.contains("closed") ? "Kampflog ▸" : "Kampflog ▾";
  });
  $("btnResetStats").addEventListener("click", () => {
    if (!confirm("Kisten-Archiv wirklich löschen?")) return;
    state.lifetime = { total: 0, gold: 0, silver: 0, bronze: 0 };
    saveLifetime();
    renderVault();
  });
  document.addEventListener("click", () => { try { ensureAudio(); } catch (_) {} }, { once: true });

  if (window.applyI18n) window.applyI18n();
  renderAll();
  renderLevel();
  renderRecent();
  renderBadges();
  loadClan();
  updateSuggestion();
  if ($("btnMusic")) {
    const bgm = $("bgm");
    if (bgm) bgm.volume = 0.45;
    $("btnMusic").addEventListener("click", () => {
      if (!bgm) return;
      if (bgm.paused) {
        bgm.play().catch(() => {});
        $("btnMusic").classList.add("on");
        $("btnMusic").textContent = "MUSIK AN";
      } else {
        bgm.pause();
        $("btnMusic").classList.remove("on");
        $("btnMusic").textContent = "MUSIK";
      }
    });
  }
  $("btnHelp").addEventListener("click", () => {
    $("helpBody").textContent = t("helpTxt");
    $("helpModal").hidden = false;
  });
  $("btnHelpOk").addEventListener("click", () => {
    $("helpModal").hidden = true;
  });
})();
