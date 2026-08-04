(() => {
  "use strict";

  const W = 1280;
  const H = 720;

  const $ = (selector) => document.querySelector(selector);
  const $$ = (selector) => [...document.querySelectorAll(selector)];
  const canvas = $("#gameCanvas");
  const ctx = canvas.getContext("2d");

  const FACTIONS = {
    neutral: { name: "无人驻守", color: "#9b9483", dark: "#514f47", light: "#d8cfba" },
    player: { name: "苍穹军团", color: "#45c8d3", dark: "#145f70", light: "#b6f6f6" },
    red: { name: "赤焰军团", color: "#e96754", dark: "#7d2f2a", light: "#ffc1ad" },
    gold: { name: "金狮军团", color: "#e3b44f", dark: "#79551d", light: "#ffe7a1" },
  };

  const BUILDINGS = {
    village: {
      name: "村落",
      icon: "⌂",
      description: "持续招募守军，是扩张领地的基础。",
      softCap: [0, 30, 48, 70, 96],
      production: [0, 1.5, 2.15, 2.9, 3.8],
      defense: 1,
      costs: [0, 0, 14, 25, 40],
    },
    fort: {
      name: "要塞",
      icon: "♜",
      description: "驻军软上限较高，防御时能削弱来犯部队。",
      softCap: [0, 42, 68, 96, 132],
      production: [0, 1.75, 2.55, 3.4, 4.5],
      defense: 1.22,
      costs: [0, 0, 18, 32, 50],
    },
    tower: {
      name: "箭塔",
      icon: "⌖",
      description: "不自动产兵；三级附带减速，四级可俘虏敌兵并组织突袭。",
      softCap: [0, 28, 42, 58, 78],
      production: [0, 0, 0, 0, 0],
      defense: 1.12,
      costs: [0, 0, 15, 27, 42],
      range: [0, 132, 158, 198, 232],
      damage: [0, 1.35, 2.15, 3.25, 4.6],
      cooldown: [0, 0.86, 0.72, 0.6, 0.48],
    },
    stable: {
      name: "驿站",
      icon: "♞",
      description: "从这里出发的部队行军速度提高 55%。",
      softCap: [0, 32, 50, 72, 100],
      production: [0, 1.15, 1.75, 2.4, 3.2],
      defense: 0.95,
      costs: [0, 0, 13, 23, 38],
    },
    armory: {
      name: "军械所",
      icon: "⚒",
      description: "从这里出征的部队战力提高 25%。",
      softCap: [0, 34, 54, 76, 104],
      production: [0, 1.05, 1.6, 2.2, 3],
      defense: 1,
      costs: [0, 0, 16, 28, 45],
    },
  };

  const BUILDING_TYPES = ["village", "fort", "tower", "stable", "armory"];

  const DIFFICULTIES = {
    relaxed: { label: "新兵", aiInterval: 2.65, aiProduction: 0.82, aiPower: 0.92, aggression: 0.76 },
    normal: { label: "将领", aiInterval: 1.82, aiProduction: 1, aiPower: 1, aggression: 1 },
    hard: { label: "统帅", aiInterval: 1.18, aiProduction: 1.22, aiPower: 1.1, aggression: 1.26 },
  };

  const LEVELS = [
    {
      name: "苍翠边境",
      shortName: "边境",
      subtitle: "Forest Verge",
      objective: "穿过旧哨塔，攻占赤焰要塞",
      theme: "forest",
      par: [90, 130],
      nodes: [
        [0, 150, 370, "fort", "player", 28, 1],
        [1, 350, 225, "village", "neutral", 9, 1],
        [2, 360, 505, "stable", "neutral", 12, 1],
        [3, 610, 360, "tower", "neutral", 17, 1],
        [4, 820, 200, "village", "neutral", 13, 1],
        [5, 815, 515, "armory", "neutral", 16, 1],
        [6, 1100, 360, "fort", "red", 27, 1],
        [7, 1015, 135, "village", "neutral", 10, 1],
      ],
      edges: [[0,1],[0,2],[1,3],[2,3],[3,4],[3,5],[4,6],[5,6],[4,7],[7,6]],
    },
    {
      name: "双河争渡",
      shortName: "双河",
      subtitle: "Twin Rivers",
      objective: "争夺两座桥头堡，击溃两支敌军",
      theme: "river",
      par: [140, 205],
      nodes: [
        [0, 125, 205, "fort", "player", 31, 1],
        [1, 130, 520, "village", "neutral", 12, 1],
        [2, 335, 345, "stable", "neutral", 16, 1],
        [3, 515, 175, "tower", "neutral", 20, 1],
        [4, 515, 525, "tower", "neutral", 20, 1],
        [5, 710, 350, "armory", "neutral", 24, 1],
        [6, 900, 195, "village", "neutral", 15, 1],
        [7, 900, 515, "village", "neutral", 15, 1],
        [8, 1145, 530, "fort", "red", 32, 1],
        [9, 1145, 175, "fort", "gold", 32, 1],
      ],
      edges: [[0,1],[0,2],[1,2],[2,3],[2,4],[3,5],[4,5],[5,6],[5,7],[6,9],[7,8],[6,7],[8,9]],
    },
    {
      name: "烬火王冠",
      shortName: "王冠",
      subtitle: "Ashen Crown",
      objective: "控制中央军械所，统一火山环城",
      theme: "volcano",
      par: [185, 275],
      nodes: [
        [0, 635, 615, "fort", "player", 35, 1],
        [1, 330, 585, "village", "neutral", 14, 1],
        [2, 125, 420, "stable", "neutral", 18, 1],
        [3, 170, 165, "fort", "red", 34, 1],
        [4, 420, 105, "tower", "neutral", 22, 1],
        [5, 635, 290, "armory", "neutral", 31, 1],
        [6, 855, 105, "tower", "neutral", 22, 1],
        [7, 1110, 165, "fort", "gold", 34, 1],
        [8, 1155, 420, "stable", "neutral", 18, 1],
        [9, 945, 585, "village", "neutral", 14, 1],
        [10, 405, 405, "village", "neutral", 17, 1],
        [11, 865, 405, "village", "neutral", 17, 1],
      ],
      edges: [[0,1],[0,9],[0,5],[1,2],[1,10],[2,3],[2,10],[3,4],[4,5],[4,10],[5,6],[5,10],[5,11],[6,7],[6,11],[7,8],[8,9],[8,11],[9,11],[10,11]],
    },
    {
      name: "霜脊隘口",
      shortName: "霜脊",
      subtitle: "Frostbound Pass",
      objective: "控制冰桥箭塔，突破北境双堡",
      theme: "snow",
      par: [200, 300],
      nodes: [
        [0, 120, 360, "fort", "player", 36, 1],
        [1, 315, 190, "village", "neutral", 15, 1],
        [2, 320, 535, "stable", "neutral", 18, 1],
        [3, 535, 350, "tower", "neutral", 24, 2],
        [4, 715, 145, "armory", "neutral", 21, 1],
        [5, 725, 550, "village", "neutral", 17, 1],
        [6, 900, 350, "tower", "neutral", 26, 2],
        [7, 1095, 150, "fort", "gold", 38, 2],
        [8, 1120, 535, "fort", "red", 38, 2],
        [9, 930, 105, "village", "neutral", 14, 1],
        [10, 940, 610, "village", "neutral", 14, 1],
      ],
      edges: [[0,1],[0,2],[1,3],[2,3],[3,4],[3,5],[4,6],[5,6],[4,9],[5,10],[6,7],[6,8],[7,9],[8,10]],
    },
    {
      name: "流沙迷城",
      shortName: "流沙",
      subtitle: "Shifting Dunes",
      objective: "沿绿洲补给线推进，夺取沙海军械所",
      theme: "desert",
      par: [220, 330],
      nodes: [
        [0, 135, 575, "fort", "player", 38, 1],
        [1, 145, 265, "village", "neutral", 16, 1],
        [2, 340, 430, "stable", "neutral", 21, 1],
        [3, 365, 120, "tower", "neutral", 23, 2],
        [4, 560, 275, "village", "neutral", 18, 1],
        [5, 585, 560, "armory", "neutral", 28, 2],
        [6, 760, 410, "tower", "neutral", 26, 2],
        [7, 820, 120, "village", "neutral", 18, 1],
        [8, 990, 280, "stable", "neutral", 22, 1],
        [9, 1110, 100, "fort", "gold", 42, 2],
        [10, 1135, 545, "fort", "red", 42, 2],
        [11, 930, 590, "village", "neutral", 17, 1],
      ],
      edges: [[0,1],[0,2],[1,2],[1,3],[2,4],[2,5],[3,4],[4,6],[5,6],[5,11],[6,7],[6,8],[6,11],[7,9],[7,8],[8,9],[8,10],[8,11],[10,11]],
    },
    {
      name: "风暴群岛",
      shortName: "群岛",
      subtitle: "Storm Isles",
      objective: "跨越岛链，利用驿站抢占中央海塔",
      theme: "islands",
      par: [240, 360],
      nodes: [
        [0, 105, 350, "fort", "player", 40, 2],
        [1, 275, 170, "stable", "neutral", 20, 1],
        [2, 280, 535, "village", "neutral", 18, 1],
        [3, 470, 330, "tower", "neutral", 27, 2],
        [4, 625, 115, "village", "neutral", 19, 1],
        [5, 635, 570, "armory", "neutral", 29, 2],
        [6, 760, 335, "tower", "neutral", 32, 3],
        [7, 890, 125, "stable", "neutral", 22, 2],
        [8, 900, 565, "village", "neutral", 20, 1],
        [9, 1085, 305, "armory", "neutral", 27, 2],
        [10, 1180, 105, "fort", "gold", 45, 2],
        [11, 1180, 585, "fort", "red", 45, 2],
        [12, 1030, 440, "tower", "neutral", 25, 2],
      ],
      edges: [[0,1],[0,2],[1,3],[2,3],[3,4],[3,5],[4,6],[5,6],[6,7],[6,8],[7,9],[7,10],[8,9],[8,11],[8,12],[9,10],[9,11],[9,12],[10,12],[11,12]],
    },
    {
      name: "荆棘高地",
      shortName: "高地",
      subtitle: "Thorn Highlands",
      objective: "守住峡谷通道，瓦解三线合围",
      theme: "highlands",
      par: [260, 390],
      nodes: [
        [0, 640, 610, "fort", "player", 44, 2],
        [1, 350, 570, "village", "neutral", 20, 1],
        [2, 925, 570, "village", "neutral", 20, 1],
        [3, 190, 410, "stable", "neutral", 23, 2],
        [4, 1080, 410, "armory", "neutral", 26, 2],
        [5, 405, 335, "tower", "neutral", 29, 3],
        [6, 865, 335, "tower", "neutral", 29, 3],
        [7, 640, 350, "fort", "neutral", 34, 2],
        [8, 165, 145, "fort", "red", 46, 2],
        [9, 1110, 145, "fort", "gold", 46, 2],
        [10, 420, 105, "village", "neutral", 21, 2],
        [11, 850, 105, "village", "neutral", 21, 2],
        [12, 640, 90, "tower", "neutral", 36, 3],
      ],
      edges: [[0,1],[0,2],[0,7],[1,3],[1,5],[2,4],[2,6],[3,5],[3,8],[4,6],[4,9],[5,7],[5,10],[6,7],[6,11],[7,12],[8,10],[9,11],[10,12],[11,12]],
    },
    {
      name: "天穹决战",
      shortName: "决战",
      subtitle: "Citadel of Dawn",
      objective: "攻克四级王庭箭塔，结束疆域战争",
      theme: "citadel",
      par: [300, 450],
      nodes: [
        [0, 110, 610, "fort", "player", 48, 2],
        [1, 105, 330, "village", "neutral", 21, 2],
        [2, 285, 485, "stable", "neutral", 24, 2],
        [3, 315, 195, "tower", "neutral", 30, 3],
        [4, 500, 355, "armory", "neutral", 32, 2],
        [5, 640, 575, "village", "neutral", 23, 2],
        [6, 640, 330, "tower", "neutral", 44, 4],
        [7, 640, 105, "fort", "gold", 50, 3],
        [8, 800, 355, "armory", "neutral", 32, 2],
        [9, 980, 195, "tower", "neutral", 30, 3],
        [10, 1010, 485, "stable", "neutral", 24, 2],
        [11, 1170, 610, "fort", "red", 48, 2],
        [12, 1175, 330, "village", "neutral", 21, 2],
        [13, 850, 585, "village", "neutral", 22, 2],
        [14, 440, 95, "village", "neutral", 22, 2],
      ],
      edges: [[0,1],[0,2],[1,2],[1,3],[2,4],[2,5],[3,4],[3,14],[4,6],[4,14],[5,6],[5,13],[6,7],[6,8],[6,13],[7,9],[7,14],[8,9],[8,10],[9,12],[10,11],[10,12],[10,13],[11,12]],
    },
  ];

  const ACCOUNT_STORE = loadAccountStore();
  const INITIAL_ACCOUNT = ACCOUNT_STORE.accounts.find((account) => account.id === ACCOUNT_STORE.currentId) || ACCOUNT_STORE.accounts[0];
  const CAMPAIGN_POSITIONS = [[95,430],[215,330],[345,420],[470,245],[585,365],[700,215],[820,335],[920,165]];

  const state = {
    levelIndex: 0,
    difficulty: INITIAL_ACCOUNT.settings?.difficulty || "normal",
    nodes: [],
    edges: [],
    armies: [],
    particles: [],
    floaters: [],
    shots: [],
    selection: new Set(),
    elapsed: 0,
    lastTime: 0,
    started: false,
    paused: false,
    gameOver: false,
    speed: INITIAL_ACCOUNT.settings?.speed || 1,
    sendRatio: 0.5,
    sound: INITIAL_ACCOUNT.settings?.sound !== false,
    effects: INITIAL_ACCOUNT.settings?.effects !== false,
    nextArmyId: 1,
    aiTimers: { red: 0, gold: 0 },
    towerTimer: 0,
    uiTimer: 0,
    drag: null,
    pointer: { x: 0, y: 0 },
    hoveredNode: null,
    decor: [],
    accountStore: ACCOUNT_STORE,
    progress: INITIAL_ACCOUNT.progress,
  };

  let audioContext = null;
  let toastTimer = null;

  function freshProgress() {
    return { unlocked: 1, stars: {}, best: {} };
  }

  function freshSettings() {
    return { sound: true, effects: true, speed: 1, difficulty: "normal" };
  }

  function freshStats() {
    return { battles: 0, wins: 0, totalTime: 0, recruited: 0 };
  }

  function loadAccountStore() {
    try {
      const saved = JSON.parse(localStorage.getItem("frontier-claim-accounts-v1"));
      if (saved?.accounts?.length) {
        saved.accounts.forEach((account) => {
          account.progress ||= freshProgress();
          account.settings = { ...freshSettings(), ...(account.settings || {}) };
          account.stats = { ...freshStats(), ...(account.stats || {}) };
        });
        return saved;
      }
    } catch {
      // Fall through to a fresh local account store.
    }
    let legacy = freshProgress();
    try { legacy = JSON.parse(localStorage.getItem("frontier-claim-progress")) || legacy; } catch { /* optional migration */ }
    const guest = {
      id: "guest", name: "游客指挥官", pinHash: "", createdAt: Date.now(),
      progress: legacy, settings: freshSettings(), stats: freshStats(),
    };
    const store = { version: 1, currentId: guest.id, accounts: [guest] };
    try { localStorage.setItem("frontier-claim-accounts-v1", JSON.stringify(store)); } catch { /* storage is optional */ }
    return store;
  }

  function activeAccount() {
    return state.accountStore.accounts.find((account) => account.id === state.accountStore.currentId) || state.accountStore.accounts[0];
  }

  function saveAccountStore() {
    const account = activeAccount();
    if (account) {
      account.progress = state.progress;
      account.settings = { sound: state.sound, effects: state.effects, speed: state.speed, difficulty: state.difficulty };
    }
    try { localStorage.setItem("frontier-claim-accounts-v1", JSON.stringify(state.accountStore)); } catch { /* storage is optional */ }
  }

  function saveProgress() {
    saveAccountStore();
    try { localStorage.setItem("frontier-claim-progress", JSON.stringify(state.progress)); } catch { /* legacy mirror */ }
  }

  function cloneLevel(index) {
    const level = LEVELS[index];
    state.nodes = level.nodes.map(([id, x, y, type, owner, units, levelValue]) => ({
      id, x, y, type, owner, units, level: levelValue, productionCarry: 0, overloadTimer: 0,
      pulse: Math.random() * Math.PI * 2, shotTimer: Math.random() * .35, killCharge: 0, captives: 0, raidTimer: 0,
    }));
    state.edges = level.edges.map(([a, b]) => ({ a, b }));
  }

  function resetLevel(index = state.levelIndex) {
    state.levelIndex = index;
    cloneLevel(index);
    state.armies.length = 0;
    state.particles.length = 0;
    state.floaters.length = 0;
    state.shots.length = 0;
    state.selection.clear();
    state.elapsed = 0;
    state.gameOver = false;
    state.paused = false;
    state.aiTimers = { red: 0.7, gold: 1.15 };
    state.towerTimer = 0;
    state.nextArmyId = 1;
    state.decor = createDecor(index);
    $("#pauseVeil").classList.add("hidden");
    $("#pauseIcon").textContent = "Ⅱ";
    $("#pauseButton").classList.remove("active");
    updateStaticUI();
    updateUI(true);
  }

  function createDecor(index) {
    let seed = 9357 + index * 811;
    const random = () => {
      seed = (seed * 9301 + 49297) % 233280;
      return seed / 233280;
    };
    const items = [];
    for (let i = 0; i < 115; i++) {
      items.push({
        x: random() * W, y: random() * H, r: 1.5 + random() * 7,
        kind: random() > 0.72 ? 1 : 0, alpha: 0.06 + random() * 0.1,
      });
    }
    return items;
  }

  function connected(a, b) {
    return state.edges.some((edge) => (edge.a === a && edge.b === b) || (edge.a === b && edge.b === a));
  }

  function neighbors(id) {
    return state.edges
      .filter((edge) => edge.a === id || edge.b === id)
      .map((edge) => nodeById(edge.a === id ? edge.b : edge.a));
  }

  function findRoute(source, target, owner = source?.owner) {
    if (!source || !target || source.id === target.id || source.owner !== owner) return null;
    const queue = [[source.id]];
    const visited = new Set([source.id]);
    while (queue.length) {
      const path = queue.shift();
      const currentId = path[path.length - 1];
      for (const next of neighbors(currentId)) {
        if (visited.has(next.id)) continue;
        const nextPath = [...path, next.id];
        if (next.id === target.id) return nextPath;
        if (next.owner === owner) {
          visited.add(next.id);
          queue.push(nextPath);
        }
      }
    }
    return null;
  }

  function nodeById(id) { return state.nodes.find((node) => node.id === id); }

  function softCap(node) { return BUILDINGS[node.type].softCap[node.level]; }
  function upgradeCost(node) { return node.level >= 4 ? Infinity : BUILDINGS[node.type].costs[node.level + 1]; }

  function initAudio() {
    if (!audioContext) {
      const AC = window.AudioContext || window.webkitAudioContext;
      if (AC) audioContext = new AC();
    }
    if (audioContext?.state === "suspended") audioContext.resume();
  }

  function tone(frequency, duration = 0.08, type = "sine", volume = 0.025, delay = 0) {
    if (!state.sound) return;
    initAudio();
    if (!audioContext) return;
    const start = audioContext.currentTime + delay;
    const oscillator = audioContext.createOscillator();
    const gain = audioContext.createGain();
    oscillator.type = type;
    oscillator.frequency.setValueAtTime(frequency, start);
    gain.gain.setValueAtTime(0.0001, start);
    gain.gain.exponentialRampToValueAtTime(volume, start + 0.012);
    gain.gain.exponentialRampToValueAtTime(0.0001, start + duration);
    oscillator.connect(gain).connect(audioContext.destination);
    oscillator.start(start);
    oscillator.stop(start + duration + 0.02);
  }

  function playSound(name) {
    if (name === "select") tone(440, 0.06, "triangle", 0.018);
    if (name === "send") { tone(260, 0.08, "triangle", 0.02); tone(370, 0.09, "triangle", 0.015, 0.045); }
    if (name === "capture") { tone(420, 0.12, "sine", 0.025); tone(620, 0.18, "sine", 0.02, 0.08); }
    if (name === "lost") { tone(250, 0.12, "sawtooth", 0.018); tone(165, 0.2, "sawtooth", 0.015, 0.08); }
    if (name === "upgrade") { tone(380, 0.08, "triangle", 0.022); tone(520, 0.08, "triangle", 0.02, 0.07); tone(690, 0.14, "triangle", 0.018, 0.14); }
    if (name === "victory") [392, 523, 659, 784].forEach((f, i) => tone(f, 0.3, "triangle", 0.028, i * 0.12));
    if (name === "defeat") [330, 277, 220].forEach((f, i) => tone(f, 0.32, "sawtooth", 0.018, i * 0.16));
  }

  function showToast(message) {
    const el = $("#toast");
    el.textContent = message;
    el.classList.add("show");
    clearTimeout(toastTimer);
    toastTimer = setTimeout(() => el.classList.remove("show"), 1700);
  }

  function formatTime(seconds) {
    const total = Math.floor(seconds);
    return `${String(Math.floor(total / 60)).padStart(2, "0")}:${String(total % 60).padStart(2, "0")}`;
  }

  function updateStaticUI() {
    const level = LEVELS[state.levelIndex];
    $("#levelName").textContent = level.name;
    $("#levelObjective").textContent = level.objective;
    $("#levelShort").textContent = String(state.levelIndex + 1).padStart(2, "0");
    $("#parText").textContent = `三星目标 ${formatTime(level.par[0])}`;
    $("#statusText").textContent = `${DIFFICULTIES[state.difficulty].label}难度 · ${level.subtitle}`;
  }

  function updateUI(force = false) {
    state.uiTimer = force ? 0 : state.uiTimer;
    [...state.selection].forEach((id) => {
      if (nodeById(id)?.owner !== "player") state.selection.delete(id);
    });
    const playerNodes = state.nodes.filter((node) => node.owner === "player");
    const enemyNodes = state.nodes.filter((node) => node.owner === "red" || node.owner === "gold");
    const claimed = state.nodes.filter((node) => node.owner !== "neutral").length;
    $("#timerText").textContent = formatTime(state.elapsed);
    $("#playerCount").textContent = playerNodes.length;
    $("#enemyCount").textContent = enemyNodes.length;
    $("#territoryProgress").style.width = `${(playerNodes.length / state.nodes.length) * 100}%`;
    const selected = [...state.selection].map(nodeById).filter(Boolean);
    const totalUnits = selected.reduce((sum, node) => sum + Math.floor(node.units), 0);
    $("#selectionCount").textContent = `${selected.length} 个据点`;
    $("#selectionUnits").textContent = selected.length ? `可调动约 ${Math.floor(totalUnits * state.sendRatio)} 名士兵` : "等待命令";

    const upgradeButton = $("#upgradeButton");
    if (selected.length === 1) {
      const node = selected[0];
      const cost = upgradeCost(node);
      const can = node.level < 4 && node.units >= cost;
      upgradeButton.disabled = !can;
      $("#upgradeCost").textContent = node.level >= 4 ? "已达最高等级" : `消耗 ${cost} 名守军`;
    } else {
      upgradeButton.disabled = true;
      $("#upgradeCost").textContent = selected.length > 1 ? "仅可升级单个据点" : "选择单个据点";
    }

    const convertSelect = $("#convertType");
    const convertButton = $("#convertButton");
    if (selected.length === 1 && selected[0].owner === "player") {
      const node = selected[0];
      convertSelect.disabled = false;
      [...convertSelect.options].forEach((option) => { option.disabled = option.value === node.type; });
      if (convertSelect.value === node.type) {
        convertSelect.value = BUILDING_TYPES.find((type) => type !== node.type);
      }
      convertButton.disabled = !convertSelect.value || convertSelect.value === node.type;
      $("#convertCost").textContent = `全部驻军 → Lv.1 ${BUILDINGS[convertSelect.value].name}`;
    } else {
      convertSelect.disabled = true;
      convertButton.disabled = true;
      $("#convertCost").textContent = selected.length > 1 ? "仅可改建单个据点" : "选择单个据点";
    }

    const inspectNode = state.hoveredNode || (selected.length === 1 ? selected[0] : null);
    updateIntel(inspectNode, claimed);
  }

  function updateIntel(node) {
    if (!node) {
      $("#intelIcon").textContent = "⌂";
      $("#intelTitle").textContent = "选择己方据点";
      $("#intelText").textContent = "按住友方据点拖向目标，松开后出兵；从空地拖动可框选多个据点。";
      $("#intelStats").classList.add("hidden");
      return;
    }
    const building = BUILDINGS[node.type];
    const overloaded = node.units > softCap(node);
    $("#intelIcon").textContent = building.icon;
    $("#intelTitle").textContent = `${FACTIONS[node.owner].name} · ${building.name}`;
    $("#intelText").textContent = building.description;
    const stats = $("#intelStats");
    const towerStats = node.type === "tower" ? `
      <div><span>攻击范围</span><b>${BUILDINGS.tower.range[node.level]}</b></div>
      <div><span>单次伤害</span><b>${BUILDINGS.tower.damage[node.level].toFixed(1)}</b></div>
      <div><span>攻击特性</span><b>${node.level >= 4 ? `击杀进度 ${node.killCharge || 0}/4` : node.level >= 3 ? "范围减速" : "穿透箭矢"}</b></div>
      <div><span>俘虏营</span><b>${node.level >= 4 ? `${node.captives || 0}/10` : "四级解锁"}</b></div>` : "";
    stats.innerHTML = `
      <div><span>据点等级</span><b>Lv.${node.level}</b></div>
      <div><span>驻军</span><b>${Math.floor(node.units)}（无上限）</b></div>
      <div><span>驻军软上限</span><b>${softCap(node)}</b></div>
      <div><span>超载损耗</span><b>${overloaded ? "生效中 · -1/秒" : "超过后 -1/秒"}</b></div>
      <div><span>产兵速度</span><b>${BUILDINGS[node.type].production[node.level].toFixed(1)}/秒</b></div>
      ${towerStats}
      <div><span>相连道路</span><b>${neighbors(node.id).length} 条</b></div>`;
    stats.classList.remove("hidden");
  }

  function sendArmy(source, target, ratio = state.sendRatio, owner = source?.owner, route = null) {
    const routeIds = route || findRoute(source, target, owner);
    if (!source || !target || source.id === target.id || source.owner !== owner || !routeIds || routeIds.length < 2) return false;
    const units = Math.floor(source.units * ratio);
    if (units < 1) return false;
    source.units -= units;
    const type = BUILDINGS[source.type];
    state.armies.push({
      id: state.nextArmyId++, owner, route: [...routeIds], segmentIndex: 0,
      from: routeIds[0], to: routeIds[1], finalTarget: target.id,
      x: source.x, y: source.y, progress: 0, units,
      speed: source.type === "stable" ? 1.55 : 1,
      power: source.type === "armory" ? 1.25 : 1,
      bob: Math.random() * Math.PI * 2, slowTimer: 0,
    });
    return true;
  }

  function dispatchSelection(target) {
    const sources = [...state.selection].map(nodeById).filter((node) => node?.owner === "player");
    if (!sources.length || !target) return;
    let sent = 0;
    let relayed = 0;
    sources.forEach((source) => {
      const route = findRoute(source, target, "player");
      if (route && sendArmy(source, target, state.sendRatio, "player", route)) {
        sent++;
        if (route.length > 2) relayed++;
      }
    });
    if (sent) {
      playSound("send");
      burst(sources[0].x, sources[0].y, FACTIONS.player.light, 5, 0.6);
      showToast(relayed
        ? `${sent} 支部队出征，其中 ${relayed} 支沿友方据点中转`
        : `${sent} 支部队已向${BUILDINGS[target.type].name}进军`);
      updateUI(true);
    } else {
      showToast("所选据点无法通过友方道路抵达该目标");
    }
  }

  function upgradeSelected() {
    const selected = [...state.selection].map(nodeById).filter(Boolean);
    if (selected.length !== 1) return;
    const node = selected[0];
    const cost = upgradeCost(node);
    if (node.owner !== "player" || node.level >= 4 || node.units < cost) return;
    node.units -= cost;
    node.level++;
    burst(node.x, node.y - 15, FACTIONS.player.light, 20, 1.2);
    addFloater(node.x, node.y - 55, `升级至 Lv.${node.level}`, "#ffe49b");
    playSound("upgrade");
    updateUI(true);
  }

  function convertSelected() {
    const selected = [...state.selection].map(nodeById).filter(Boolean);
    if (selected.length !== 1) return;
    const node = selected[0];
    const nextType = $("#convertType").value;
    if (node.owner !== "player" || !BUILDINGS[nextType] || nextType === node.type) return;
    const previousName = BUILDINGS[node.type].name;
    const lostGarrison = Math.floor(node.units);
    const lostCaptives = node.captives || 0;
    node.type = nextType;
    node.level = 1;
    node.units = 0;
    node.productionCarry = 0;
    node.overloadTimer = 0;
    node.shotTimer = Math.random() * .35;
    node.killCharge = 0;
    node.captives = 0;
    node.raidTimer = 0;
    burst(node.x, node.y - 8, FACTIONS.player.light, 28, 1.25);
    addFloater(node.x, node.y - 58, `${previousName} → ${BUILDINGS[nextType].name} Lv.1`, "#ffe49b", 1.4);
    playSound("upgrade");
    showToast(`改建完成：牺牲 ${lostGarrison} 名驻军${lostCaptives ? `和 ${lostCaptives} 名俘虏` : ""}`);
    updateUI(true);
  }

  function update(dt) {
    if (!state.started || state.paused || state.gameOver) return;
    const scaledDt = Math.min(dt, 0.05) * state.speed;
    state.elapsed += scaledDt;
    updateProduction(scaledDt);
    updateArmies(scaledDt);
    updateTowers(scaledDt);
    updateAI(scaledDt);
    updateEffects(scaledDt);
    checkOutcome();
    state.uiTimer += scaledDt;
    if (state.uiTimer > 0.12) { state.uiTimer = 0; updateUI(); }
  }

  function updateProduction(dt) {
    const difficulty = DIFFICULTIES[state.difficulty];
    state.nodes.forEach((node) => {
      const limit = softCap(node);
      if (node.owner !== "neutral" && node.units < limit) {
        let rate = BUILDINGS[node.type].production[node.level];
        if (node.owner !== "player") rate *= difficulty.aiProduction;
        node.units = Math.min(limit, node.units + rate * dt);
      }
      if (node.units > limit) {
        node.overloadTimer = (node.overloadTimer || 0) + dt;
        while (node.overloadTimer >= 1 && node.units > 0) {
          node.units -= 1;
          node.overloadTimer -= 1;
        }
      } else {
        node.overloadTimer = 0;
      }
    });
  }

  function updateArmies(dt) {
    for (let i = state.armies.length - 1; i >= 0; i--) {
      const army = state.armies[i];
      army.slowTimer = Math.max(0, (army.slowTimer || 0) - dt);
      const from = nodeById(army.from);
      const to = nodeById(army.to);
      if (!from || !to || army.units <= 0) { state.armies.splice(i, 1); continue; }
      const distance = Math.hypot(to.x - from.x, to.y - from.y);
      const slowMultiplier = army.slowTimer > 0 ? .52 : 1;
      army.progress += (88 * army.speed * slowMultiplier * dt) / distance;
      const eased = Math.min(1, army.progress);
      army.x = from.x + (to.x - from.x) * eased;
      army.y = from.y + (to.y - from.y) * eased;
      if (Math.random() < dt * 6) {
        state.particles.push({ x: army.x, y: army.y + 5, vx: (Math.random() - .5) * 8, vy: -3, life: .45, maxLife: .45, color: "#ded0aa", size: 2 });
      }
      if (army.progress >= 1) {
        const hasNextSegment = army.route && army.segmentIndex < army.route.length - 2;
        if (hasNextSegment) {
          army.segmentIndex++;
          army.from = army.route[army.segmentIndex];
          army.to = army.route[army.segmentIndex + 1];
          army.progress = 0;
          army.x = to.x;
          army.y = to.y;
          burst(to.x, to.y, FACTIONS[army.owner].color, 3, .35);
        } else {
          resolveArrival(army, to);
          state.armies.splice(i, 1);
        }
      }
    }
  }

  function resolveArrival(army, target) {
    if (army.owner === target.owner) {
      target.units += army.units;
      addFloater(target.x, target.y - 50, `+${Math.ceil(army.units)}`, FACTIONS[army.owner].light);
      burst(target.x, target.y, FACTIONS[army.owner].color, 7, .6);
      return;
    }
    const difficultyPower = army.owner === "player" ? 1 : DIFFICULTIES[state.difficulty].aiPower;
    const attackPower = army.units * army.power * difficultyPower;
    const defense = BUILDINGS[target.type].defense * (1 + (target.level - 1) * 0.08);
    const defendedUnits = target.units * defense;
    const previousOwner = target.owner;
    if (attackPower > defendedUnits) {
      const surplusPower = attackPower - defendedUnits;
      target.owner = army.owner;
      target.units = Math.max(1, surplusPower / (army.power * difficultyPower));
      target.level = Math.max(1, target.level - (previousOwner === "neutral" ? 0 : 1));
      if (target.type === "tower") {
        target.killCharge = 0;
        target.captives = 0;
        target.raidTimer = 0;
      }
      addFloater(target.x, target.y - 56, "占领！", FACTIONS[army.owner].light);
      burst(target.x, target.y, FACTIONS[army.owner].color, 25, 1.15);
      if (army.owner === "player") playSound("capture");
      else if (previousOwner === "player") playSound("lost");
    } else {
      target.units = Math.max(0, (defendedUnits - attackPower) / defense);
      addFloater(target.x, target.y - 52, `-${Math.ceil(attackPower / defense)}`, "#f4b29f");
      burst(target.x, target.y, "#e8c286", 12, .8);
    }
    updateUI(true);
  }

  function updateTowers(dt) {
    state.nodes.filter((node) => node.type === "tower" && node.owner !== "neutral").forEach((tower) => {
      const towerStats = BUILDINGS.tower;
      tower.raidTimer = Math.max(0, (tower.raidTimer || 0) - dt);
      if (tower.level >= 4 && (tower.captives || 0) >= 10 && tower.raidTimer <= 0) {
        tower.raidTimer = 1;
        while (tower.captives >= 10 && launchCaptiveRaid(tower)) {
          // Launch every complete group while a reachable target exists.
        }
      }
      tower.shotTimer -= dt;
      if (tower.shotTimer > 0) return;
      const target = state.armies
        .filter((army) => army.owner !== tower.owner && Math.hypot(army.x - tower.x, army.y - tower.y) < towerStats.range[tower.level])
        .sort((a, b) => Math.hypot(a.x - tower.x, a.y - tower.y) - Math.hypot(b.x - tower.x, b.y - tower.y))[0];
      if (!target) return;
      tower.shotTimer = towerStats.cooldown[tower.level];
      const before = Math.max(0, target.units);
      const damage = Math.min(before, towerStats.damage[tower.level]);
      target.units = Math.max(0, before - damage);
      if (tower.level >= 3) target.slowTimer = Math.max(target.slowTimer || 0, 1.75);
      const shotColors = ["", "#ffe5a6", "#ffb96d", "#80edff", "#d9a2ff"];
      state.shots.push({
        sx: tower.x, sy: tower.y - 34, tx: target.x, ty: target.y,
        life: .12 + tower.level * .035, maxLife: .12 + tower.level * .035,
        color: shotColors[tower.level], level: tower.level,
      });
      const killed = Math.max(0, Math.ceil(before) - Math.ceil(target.units));
      if (tower.level >= 4 && killed) {
        tower.killCharge += killed;
        while (tower.killCharge >= 4) {
          tower.killCharge -= 4;
          capturePrisoner(tower, target);
        }
      }
      const damageColor = tower.level >= 4 ? "#e3b4ff" : tower.level >= 3 ? "#a8f3ff" : "#ffd0a1";
      addFloater(target.x, target.y - 20, `-${damage.toFixed(tower.level === 1 ? 1 : 0)}`, damageColor, .65);
      burst(target.x, target.y, shotColors[tower.level], 2 + tower.level * 2, .35 + tower.level * .08);
    });
  }

  function capturePrisoner(tower, targetArmy) {
    const faction = FACTIONS[tower.owner];
    tower.captives = (tower.captives || 0) + 1;
    if (tower.owner === "player") {
      const account = activeAccount();
      if (account) account.stats.recruited++;
    }
    addFloater(targetArmy.x, targetArmy.y - 34, `俘虏 +1 · ${tower.captives}/10`, "#e3b4ff", 1.2);
    burst(targetArmy.x, targetArmy.y, faction.light, 10, .65);
    if (tower.captives >= 10) launchCaptiveRaid(tower);
  }

  function launchCaptiveRaid(tower) {
    const reachable = state.nodes
      .filter((node) => node.owner !== tower.owner)
      .map((node) => ({ node, route: findRoute(tower, node, tower.owner) }))
      .filter((candidate) => candidate.route?.length >= 2);
    if (!reachable.length || (tower.captives || 0) < 10) return false;
    const minimumUnits = Math.min(...reachable.map(({ node }) => node.units));
    const weakest = reachable.filter(({ node }) => Math.abs(node.units - minimumUnits) < .001);
    const chosen = weakest[Math.floor(Math.random() * weakest.length)];
    const target = chosen.node;
    const route = chosen.route;
    tower.captives -= 10;
    state.armies.push({
      id: state.nextArmyId++, owner: tower.owner, route: [...route], segmentIndex: 0,
      from: route[0], to: route[1], finalTarget: target.id,
      x: tower.x, y: tower.y, progress: 0, units: 10,
      speed: 1.18, power: 1, slowTimer: 0,
      recruited: true, captiveRaid: true, bob: Math.random() * Math.PI * 2,
    });
    addFloater(tower.x, tower.y - 62, "俘虏突袭 ×10", "#e3b4ff", 1.35);
    burst(tower.x, tower.y, FACTIONS[tower.owner].light, 18, .9);
    tone(720, .16, "sine", .02);
    tone(940, .22, "triangle", .014, .08);
    if (tower.owner === "player") showToast(`箭塔派出 10 名俘虏，突袭驻军最少的${BUILDINGS[target.type].name}`);
    return true;
  }

  function updateAI(dt) {
    for (const owner of ["red", "gold"]) {
      if (!state.nodes.some((node) => node.owner === owner)) continue;
      state.aiTimers[owner] -= dt;
      if (state.aiTimers[owner] <= 0) {
        state.aiTimers[owner] = DIFFICULTIES[state.difficulty].aiInterval * (0.82 + Math.random() * .36);
        aiThink(owner);
      }
    }
  }

  function aiThink(owner) {
    const owned = state.nodes.filter((node) => node.owner === owner);
    if (!owned.length) return;
    const difficulty = DIFFICULTIES[state.difficulty];

    const upgradeCandidates = owned.filter((node) => node.level < 4 && node.units >= upgradeCost(node) + 8);
    if (upgradeCandidates.length && Math.random() < 0.23 / difficulty.aggression) {
      const node = upgradeCandidates.sort((a, b) => b.units - a.units)[0];
      node.units -= upgradeCost(node);
      node.level++;
      burst(node.x, node.y, FACTIONS[owner].light, 12, .9);
      addFloater(node.x, node.y - 50, `Lv.${node.level}`, FACTIONS[owner].light);
      return;
    }

    const options = [];
    owned.forEach((source) => {
      if (source.units < 8) return;
      neighbors(source.id).forEach((target) => {
        if (target.owner === owner) {
          const isFrontier = neighbors(target.id).some((n) => n.owner !== owner && n.owner !== "neutral");
          if (isFrontier && target.units < source.units * .34) {
            options.push({ source, target, reinforce: true, score: 17 + (source.units - target.units) * .18 });
          }
          return;
        }
        const available = Math.floor(source.units * (Math.random() < .17 ? 1 : .5));
        const effective = available * (source.type === "armory" ? 1.25 : 1) * difficulty.aiPower;
        const needed = target.units * BUILDINGS[target.type].defense;
        let score = target.owner === "neutral" ? 32 : 42;
        if (target.owner === "player") score += 12;
        if (target.type === "tower") score += 9;
        if (target.type === "armory" || target.type === "stable") score += 7;
        score += (effective - needed) * 1.1;
        score += neighbors(target.id).filter((n) => n.owner !== owner).length * 2;
        score += Math.random() * 16;
        options.push({ source, target, ratio: available >= source.units * .85 ? 1 : .5, score, winnable: effective > needed * .82 });
      });
    });
    if (!options.length) return;
    options.sort((a, b) => b.score - a.score);
    let choice = options.find((option) => option.winnable) || options[0];
    if (!choice.reinforce && !choice.winnable && Math.random() > .16 * difficulty.aggression) return;
    sendArmy(choice.source, choice.target, choice.reinforce ? .5 : choice.ratio, owner);

    if (!choice.reinforce && difficulty.aggression > 1.15) {
      const support = owned.find((source) => source.id !== choice.source.id && connected(source.id, choice.target.id) && source.units > 12);
      if (support && Math.random() < .42) sendArmy(support, choice.target, .5, owner);
    }
  }

  function updateEffects(dt) {
    for (let i = state.particles.length - 1; i >= 0; i--) {
      const p = state.particles[i];
      p.life -= dt; p.x += p.vx * dt; p.y += p.vy * dt; p.vy += 20 * dt;
      if (p.life <= 0) state.particles.splice(i, 1);
    }
    for (let i = state.floaters.length - 1; i >= 0; i--) {
      const f = state.floaters[i];
      f.life -= dt; f.y -= 20 * dt;
      if (f.life <= 0) state.floaters.splice(i, 1);
    }
    for (let i = state.shots.length - 1; i >= 0; i--) {
      state.shots[i].life -= dt;
      if (state.shots[i].life <= 0) state.shots.splice(i, 1);
    }
  }

  function burst(x, y, color, count = 12, strength = 1) {
    if (!state.effects) count = Math.max(2, Math.ceil(count * .3));
    for (let i = 0; i < count; i++) {
      const angle = Math.random() * Math.PI * 2;
      const speed = (20 + Math.random() * 55) * strength;
      state.particles.push({ x, y, vx: Math.cos(angle) * speed, vy: Math.sin(angle) * speed - 15, life: .45 + Math.random() * .55, maxLife: 1, color, size: 1.5 + Math.random() * 3 });
    }
  }

  function addFloater(x, y, text, color, life = 1.1) {
    state.floaters.push({ x, y, text, color, life, maxLife: life });
  }

  function checkOutcome() {
    const enemiesExist = state.nodes.some((node) => node.owner === "red" || node.owner === "gold") || state.armies.some((army) => army.owner === "red" || army.owner === "gold");
    const playerExists = state.nodes.some((node) => node.owner === "player") || state.armies.some((army) => army.owner === "player");
    if (!enemiesExist && state.nodes.every((node) => node.owner === "player")) finishGame(true);
    else if (!playerExists) finishGame(false);
  }

  function calculateStars() {
    const [three, two] = LEVELS[state.levelIndex].par;
    return state.elapsed <= three ? 3 : state.elapsed <= two ? 2 : 1;
  }

  function finishGame(victory) {
    if (state.gameOver) return;
    state.gameOver = true;
    const stars = victory ? calculateStars() : 0;
    const account = activeAccount();
    if (account) {
      account.stats.battles++;
      account.stats.totalTime += Math.floor(state.elapsed);
      if (victory) account.stats.wins++;
    }
    if (victory) {
      state.progress.stars[state.levelIndex] = Math.max(state.progress.stars[state.levelIndex] || 0, stars);
      const best = state.progress.best[state.levelIndex];
      if (!best || state.elapsed < best) state.progress.best[state.levelIndex] = state.elapsed;
      state.progress.unlocked = Math.min(LEVELS.length, Math.max(state.progress.unlocked || 1, state.levelIndex + 2));
      playSound("victory");
    } else playSound("defeat");
    saveProgress();
    setTimeout(() => showResult(victory, stars), 500);
  }

  function showResult(victory, stars) {
    $("#resultKicker").textContent = victory ? "战役完成" : "战线失守";
    $("#resultTitle").textContent = victory ? "疆域已统一" : "据点已陷落";
    $("#resultStars").textContent = victory ? "★".repeat(stars) + "☆".repeat(3 - stars) : "☠";
    $("#resultSummary").textContent = victory
      ? `用时 ${formatTime(state.elapsed)} · ${DIFFICULTIES[state.difficulty].label}难度`
      : `坚持了 ${formatTime(state.elapsed)} · 调整路线再试一次`;
    const next = $("#resultNext");
    next.textContent = victory && state.levelIndex < LEVELS.length - 1 ? "下一战役" : "返回战役地图";
    next.dataset.victory = victory ? "1" : "0";
    $("#resultOverlay").classList.add("show");
  }

  function render() {
    ctx.clearRect(0, 0, W, H);
    drawTerrain();
    drawRoads();
    state.armies.forEach(drawArmy);
    state.nodes.forEach(drawNode);
    drawShots();
    drawEffects();
    drawDragSelection();
    drawVignette();
  }

  function drawTerrain() {
    const theme = LEVELS[state.levelIndex].theme;
    const palettes = {
      forest: ["#668569", "#354f43", "#233b36"],
      river: ["#738366", "#445d4d", "#263f3c"],
      volcano: ["#5b5045", "#37322e", "#1f2523"],
      snow: ["#b7ced0", "#67838a", "#314c52"],
      desert: ["#c8ad70", "#8c7046", "#493f31"],
      islands: ["#568a8f", "#285e68", "#173b46"],
      highlands: ["#779064", "#425b43", "#263b35"],
      citadel: ["#8b8b79", "#4d554f", "#293431"],
    };
    const colors = palettes[theme];
    const gradient = ctx.createRadialGradient(W * .48, H * .4, 80, W * .5, H * .5, W * .75);
    gradient.addColorStop(0, colors[0]); gradient.addColorStop(.58, colors[1]); gradient.addColorStop(1, colors[2]);
    ctx.fillStyle = gradient; ctx.fillRect(0, 0, W, H);

    if (theme === "forest") {
      drawRiver([{x:-80,y:665},{x:180,y:600},{x:400,y:680},{x:700,y:620},{x:1000,y:690},{x:1380,y:610}], 75, "#426b69");
    } else if (theme === "river") {
      drawRiver([{x:610,y:-80},{x:575,y:150},{x:650,y:360},{x:590,y:780}], 115, "#3d6f75");
      ctx.save(); ctx.strokeStyle = "rgba(186,224,219,.12)"; ctx.lineWidth = 2;
      for (let i = 0; i < 9; i++) { ctx.beginPath(); ctx.moveTo(548 + (i % 3) * 16, i * 92); ctx.quadraticCurveTo(620, i * 92 + 18, 690, i * 92); ctx.stroke(); }
      ctx.restore();
    } else if (theme === "volcano") {
      const lava = ctx.createRadialGradient(635, 290, 20, 635, 290, 145);
      lava.addColorStop(0, "#e26c34"); lava.addColorStop(.35, "#843b28"); lava.addColorStop(.72, "#392d29"); lava.addColorStop(1, "rgba(40,33,30,0)");
      ctx.fillStyle = lava; ctx.beginPath(); ctx.arc(635, 290, 155, 0, Math.PI * 2); ctx.fill();
      ctx.strokeStyle = "rgba(255,117,48,.38)"; ctx.lineWidth = 3;
      [[635,290,525,180],[635,290,770,180],[635,290,740,440],[635,290,540,465]].forEach(([a,b,c,d]) => {
        ctx.beginPath(); ctx.moveTo(a,b); ctx.quadraticCurveTo((a+c)/2+25,(b+d)/2-15,c,d); ctx.stroke();
      });
    } else if (theme === "snow") {
      drawRiver([{x:600,y:-60},{x:565,y:175},{x:650,y:365},{x:600,y:780}], 92, "#83b2bc");
      ctx.save(); ctx.strokeStyle = "rgba(226,248,248,.24)"; ctx.lineWidth = 2;
      for (let i = 0; i < 13; i++) { ctx.beginPath(); ctx.moveTo(i * 110 - 30, 0); ctx.lineTo(i * 110 + 100, 720); ctx.stroke(); }
      ctx.restore();
    } else if (theme === "desert") {
      ctx.save(); ctx.strokeStyle = "rgba(255,231,174,.14)"; ctx.lineWidth = 3;
      for (let y = 80; y < 720; y += 105) { ctx.beginPath(); ctx.moveTo(-40, y); ctx.bezierCurveTo(260, y - 55, 520, y + 55, 820, y); ctx.bezierCurveTo(1030, y - 38, 1170, y + 30, 1340, y - 8); ctx.stroke(); }
      ctx.restore();
    } else if (theme === "islands") {
      ctx.save();
      state.nodes.forEach((node) => {
        ctx.fillStyle = "rgba(33,67,54,.65)"; ctx.beginPath(); ctx.ellipse(node.x, node.y + 8, 76, 50, -.12, 0, Math.PI * 2); ctx.fill();
        ctx.fillStyle = "rgba(174,171,111,.38)"; ctx.beginPath(); ctx.ellipse(node.x, node.y + 5, 66, 42, -.12, 0, Math.PI * 2); ctx.fill();
      });
      ctx.strokeStyle = "rgba(204,245,241,.12)"; ctx.lineWidth = 2;
      for (let y = 45; y < 720; y += 72) { ctx.beginPath(); ctx.moveTo(0,y); ctx.bezierCurveTo(300,y+18,500,y-18,780,y); ctx.bezierCurveTo(980,y+15,1110,y-14,1280,y); ctx.stroke(); }
      ctx.restore();
    } else if (theme === "highlands") {
      ctx.save(); ctx.strokeStyle = "rgba(207,225,168,.11)"; ctx.lineWidth = 2;
      [[220,250,180],[620,380,230],[1040,245,180]].forEach(([x,y,r]) => { for(let i=0;i<4;i++){ctx.beginPath();ctx.arc(x,y,r+i*26,.25,Math.PI*1.7);ctx.stroke();} });
      ctx.restore();
    } else if (theme === "citadel") {
      ctx.save(); ctx.strokeStyle = "rgba(225,215,178,.12)"; ctx.lineWidth = 3;
      for (let x = 0; x < W; x += 96) { ctx.beginPath(); ctx.moveTo(x,0); ctx.lineTo(x,H); ctx.stroke(); }
      for (let y = 0; y < H; y += 72) { ctx.beginPath(); ctx.moveTo(0,y); ctx.lineTo(W,y); ctx.stroke(); }
      ctx.strokeStyle = "rgba(255,218,132,.18)"; ctx.lineWidth = 5; ctx.beginPath(); ctx.arc(640,330,185,0,Math.PI*2); ctx.stroke();
      ctx.restore();
    }

    state.decor.forEach((item) => {
      ctx.globalAlpha = item.alpha;
      if (theme === "volcano") {
        ctx.fillStyle = item.kind ? "#141a19" : "#b77a52";
        ctx.beginPath(); ctx.arc(item.x, item.y, item.r, 0, Math.PI * 2); ctx.fill();
      } else if (theme === "snow") {
        ctx.fillStyle = item.kind ? "#e8f4f2" : "#b9d5d6";
        ctx.beginPath(); ctx.arc(item.x, item.y, item.r * .5, 0, Math.PI * 2); ctx.fill();
      } else if (theme === "desert") {
        ctx.fillStyle = item.kind ? "#5f6e49" : "#ead393";
        ctx.beginPath(); ctx.arc(item.x, item.y, item.kind ? item.r * .45 : item.r * .28, 0, Math.PI * 2); ctx.fill();
      } else if (theme === "islands") {
        ctx.fillStyle = "#d5eee5"; ctx.beginPath(); ctx.arc(item.x, item.y, item.r * .2, 0, Math.PI * 2); ctx.fill();
      } else if (item.kind) {
        ctx.fillStyle = theme === "river" ? "#2d493f" : "#1d3d32";
        ctx.beginPath(); ctx.moveTo(item.x, item.y - item.r * 2.4); ctx.lineTo(item.x - item.r, item.y + item.r); ctx.lineTo(item.x + item.r, item.y + item.r); ctx.closePath(); ctx.fill();
      } else {
        ctx.fillStyle = "#d2c493"; ctx.beginPath(); ctx.arc(item.x, item.y, item.r * .35, 0, Math.PI * 2); ctx.fill();
      }
    });
    ctx.globalAlpha = 1;
  }

  function drawRiver(points, width, color) {
    ctx.save(); ctx.lineCap = "round"; ctx.lineJoin = "round";
    ctx.strokeStyle = "rgba(17,34,34,.35)"; ctx.lineWidth = width + 18;
    traceSmooth(points); ctx.stroke();
    ctx.strokeStyle = color; ctx.lineWidth = width;
    traceSmooth(points); ctx.stroke();
    ctx.strokeStyle = "rgba(196,229,221,.08)"; ctx.lineWidth = 2;
    traceSmooth(points); ctx.stroke();
    ctx.restore();
  }

  function traceSmooth(points) {
    ctx.beginPath(); ctx.moveTo(points[0].x, points[0].y);
    for (let i = 1; i < points.length - 1; i++) {
      const midX = (points[i].x + points[i + 1].x) / 2;
      const midY = (points[i].y + points[i + 1].y) / 2;
      ctx.quadraticCurveTo(points[i].x, points[i].y, midX, midY);
    }
    ctx.lineTo(points.at(-1).x, points.at(-1).y);
  }

  function drawRoads() {
    state.edges.forEach((edge) => {
      const a = nodeById(edge.a), b = nodeById(edge.b);
      const selectedRoute = state.selection.has(a.id) || state.selection.has(b.id);
      ctx.save(); ctx.lineCap = "round";
      ctx.strokeStyle = "rgba(26,37,31,.42)"; ctx.lineWidth = 14; ctx.beginPath(); ctx.moveTo(a.x, a.y); ctx.lineTo(b.x, b.y); ctx.stroke();
      ctx.strokeStyle = selectedRoute ? "rgba(255,222,154,.52)" : "rgba(210,190,144,.34)"; ctx.lineWidth = selectedRoute ? 5 : 4;
      ctx.setLineDash([5, 9]); ctx.lineDashOffset = -(performance.now() * .015);
      ctx.beginPath(); ctx.moveTo(a.x, a.y); ctx.lineTo(b.x, b.y); ctx.stroke();
      ctx.restore();
    });
  }

  function nodeRadius(node) { return 43 + (node.level - 1) * 5; }

  function drawNode(node) {
    const faction = FACTIONS[node.owner];
    const building = BUILDINGS[node.type];
    const radius = nodeRadius(node);
    const selected = state.selection.has(node.id);
    const hovered = state.hoveredNode?.id === node.id;
    const overloaded = node.units > softCap(node);
    const pulse = .5 + Math.sin(performance.now() * .003 + node.pulse) * .5;
    ctx.save(); ctx.translate(node.x, node.y);

    if (node.owner !== "neutral") {
      const glow = ctx.createRadialGradient(0, 8, 10, 0, 8, radius + 24);
      glow.addColorStop(0, `${faction.color}33`); glow.addColorStop(1, `${faction.color}00`);
      ctx.fillStyle = glow; ctx.beginPath(); ctx.arc(0, 8, radius + 24, 0, Math.PI * 2); ctx.fill();
    }

    if (selected || hovered) {
      if (node.type === "tower") {
        ctx.fillStyle = `${faction.color}0d`;
        ctx.strokeStyle = `${faction.color}55`;
        ctx.lineWidth = 2;
        ctx.setLineDash([12, 9]);
        ctx.lineDashOffset = -performance.now() * .01;
        ctx.beginPath(); ctx.arc(0, 0, BUILDINGS.tower.range[node.level], 0, Math.PI * 2); ctx.fill(); ctx.stroke();
      }
      ctx.strokeStyle = selected ? faction.light : "rgba(255,255,255,.5)";
      ctx.lineWidth = selected ? 3 : 1.5;
      ctx.setLineDash(selected ? [8, 6] : [3, 5]);
      ctx.lineDashOffset = -performance.now() * .025;
      ctx.beginPath(); ctx.arc(0, 0, radius + 12 + pulse * 2, 0, Math.PI * 2); ctx.stroke();
      ctx.setLineDash([]);
    }

    ctx.fillStyle = "rgba(18,29,26,.65)"; ctx.beginPath(); ctx.ellipse(0, 27, radius * .9, 15, 0, 0, Math.PI * 2); ctx.fill();
    ctx.fillStyle = faction.dark; ctx.strokeStyle = faction.color; ctx.lineWidth = 3;
    ctx.beginPath(); ctx.arc(0, 6, radius * .76, 0, Math.PI * 2); ctx.fill(); ctx.stroke();
    ctx.fillStyle = "rgba(238,220,180,.16)"; ctx.beginPath(); ctx.arc(-10, -5, radius * .42, 0, Math.PI * 2); ctx.fill();

    drawBuildingShape(node, faction);

    ctx.fillStyle = "rgba(10,20,19,.92)"; ctx.strokeStyle = overloaded ? "#f3a18f" : faction.color; ctx.lineWidth = 2;
    roundRect(ctx, -20, 28, 40, 25, 12); ctx.fill(); ctx.stroke();
    ctx.fillStyle = overloaded ? "#ffd0c7" : faction.light; ctx.font = "700 14px Segoe UI, sans-serif"; ctx.textAlign = "center"; ctx.textBaseline = "middle";
    ctx.fillText(String(Math.floor(node.units)), 0, 40);

    if (overloaded) {
      ctx.fillStyle = "#f3a18f"; ctx.font = "bold 9px Segoe UI, Microsoft YaHei, sans-serif";
      ctx.fillText("超载 -1/秒", 0, 61);
    }

    ctx.fillStyle = "rgba(7,16,15,.88)"; ctx.strokeStyle = "rgba(240,220,176,.25)"; ctx.lineWidth = 1;
    roundRect(ctx, -23, -radius - 21, 46, 17, 8); ctx.fill(); ctx.stroke();
    ctx.fillStyle = "#d8cdaE"; ctx.font = "9px Segoe UI, sans-serif"; ctx.fillText(`${building.name} · ${node.level}`, 0, -radius - 12);

    if (node.type === "tower" && node.level >= 4) {
      ctx.fillStyle = "rgba(52,31,63,.92)"; ctx.strokeStyle = "rgba(227,180,255,.65)"; ctx.lineWidth = 1;
      roundRect(ctx, -25, -radius - 42, 50, 16, 8); ctx.fill(); ctx.stroke();
      ctx.fillStyle = "#e3b4ff"; ctx.font = "bold 9px Segoe UI, Microsoft YaHei, sans-serif";
      ctx.fillText(`俘 ${node.captives || 0}/10`, 0, -radius - 34);
    }

    if (node.owner === "player" && node.level < 4 && node.units >= upgradeCost(node)) {
      ctx.fillStyle = `rgba(255,215,124,${.68 + pulse * .3})`; ctx.font = "bold 15px Segoe UI"; ctx.fillText("↑", radius * .72, -radius * .62);
    }
    ctx.restore();
  }

  function drawBuildingShape(node, faction) {
    ctx.save(); ctx.translate(0, -6); ctx.lineJoin = "round";
    ctx.strokeStyle = "rgba(15,25,23,.75)"; ctx.lineWidth = 2;
    const wall = node.owner === "neutral" ? "#9b927e" : faction.light;
    const roof = node.owner === "neutral" ? "#5f5a50" : faction.color;
    if (node.type === "village") {
      const count = node.level + 1;
      for (let i = 0; i < count; i++) {
        const ox = (i - (count - 1) / 2) * 14;
        ctx.fillStyle = wall; ctx.fillRect(ox - 7, 1 - Math.abs(i - 1) * 2, 14, 16);
        ctx.fillStyle = roof; ctx.beginPath(); ctx.moveTo(ox - 10, 2); ctx.lineTo(ox, -9); ctx.lineTo(ox + 10, 2); ctx.closePath(); ctx.fill(); ctx.stroke();
      }
    } else if (node.type === "fort") {
      ctx.fillStyle = wall; ctx.fillRect(-24, -2, 48, 25);
      for (const x of [-25, 25]) { ctx.fillRect(x - 7, -15, 14, 38); ctx.fillStyle = roof; ctx.fillRect(x - 9, -20, 18, 7); ctx.fillStyle = wall; }
      ctx.fillStyle = "#25322f"; ctx.fillRect(-6, 10, 12, 13);
      for (let i = -2; i <= 2; i++) { ctx.fillStyle = roof; ctx.fillRect(i * 10 - 3, -8, 7, 8); }
    } else if (node.type === "tower") {
      ctx.fillStyle = wall; ctx.beginPath(); ctx.moveTo(-14, 21); ctx.lineTo(-10, -15); ctx.lineTo(10, -15); ctx.lineTo(14, 21); ctx.closePath(); ctx.fill(); ctx.stroke();
      ctx.fillStyle = roof; ctx.beginPath(); ctx.moveTo(-18, -13); ctx.lineTo(0, -28); ctx.lineTo(18, -13); ctx.closePath(); ctx.fill(); ctx.stroke();
      ctx.fillStyle = "#23302e"; ctx.fillRect(-3, -7, 6, 10);
    } else if (node.type === "stable") {
      ctx.fillStyle = wall; ctx.fillRect(-24, 0, 48, 22);
      ctx.fillStyle = roof; ctx.beginPath(); ctx.moveTo(-28, 1); ctx.lineTo(0, -17); ctx.lineTo(28, 1); ctx.closePath(); ctx.fill(); ctx.stroke();
      ctx.fillStyle = "#283531"; ctx.beginPath(); ctx.arc(0, 17, 8, Math.PI, 0); ctx.lineTo(8,22); ctx.lineTo(-8,22); ctx.closePath(); ctx.fill();
      ctx.fillStyle = faction.dark; ctx.font = "bold 13px Georgia"; ctx.textAlign = "center"; ctx.fillText("♞", 0, 0);
    } else {
      ctx.fillStyle = wall; ctx.fillRect(-22, -1, 44, 24);
      ctx.fillStyle = roof; ctx.beginPath(); ctx.moveTo(-26, 0); ctx.lineTo(-17, -16); ctx.lineTo(20, -16); ctx.lineTo(26, 0); ctx.closePath(); ctx.fill(); ctx.stroke();
      ctx.fillStyle = "#293532"; ctx.font = "bold 15px Georgia"; ctx.textAlign = "center"; ctx.fillText("⚒", 0, 14);
      ctx.fillStyle = "#5b5548"; ctx.fillRect(12, -31, 6, 18);
    }
    ctx.restore();
  }

  function drawArmy(army) {
    const faction = FACTIONS[army.owner];
    const bob = Math.sin(performance.now() * .008 + army.bob) * 2;
    ctx.save(); ctx.translate(army.x, army.y + bob);
    if (army.slowTimer > 0) {
      ctx.strokeStyle = "rgba(128,237,255,.8)"; ctx.lineWidth = 2; ctx.setLineDash([4,4]);
      ctx.beginPath(); ctx.arc(0, 1, 25 + Math.sin(performance.now() * .012) * 3, 0, Math.PI * 2); ctx.stroke();
    }
    if (army.recruited) {
      ctx.fillStyle = "rgba(216,167,255,.18)"; ctx.strokeStyle = "#e3b4ff"; ctx.lineWidth = 2;
      ctx.beginPath(); ctx.arc(0, 0, 18, 0, Math.PI * 2); ctx.fill(); ctx.stroke();
      ctx.fillStyle = "#f1d4ff"; ctx.font = "bold 13px Segoe UI"; ctx.textAlign = "center"; ctx.fillText("↶", 0, -22);
    }
    ctx.fillStyle = "rgba(7,15,14,.35)"; ctx.beginPath(); ctx.ellipse(0, 10, 21, 6, 0, 0, Math.PI * 2); ctx.fill();
    for (let i = 0; i < 5; i++) {
      const ox = (i % 3 - 1) * 7 + (i > 2 ? 3 : 0); const oy = Math.floor(i / 3) * 7 - 4;
      ctx.fillStyle = faction.color; ctx.beginPath(); ctx.arc(ox, oy, 4.5, 0, Math.PI * 2); ctx.fill();
      ctx.fillStyle = faction.light; ctx.beginPath(); ctx.arc(ox - 1, oy - 1, 1.5, 0, Math.PI * 2); ctx.fill();
    }
    ctx.strokeStyle = "#332c21"; ctx.lineWidth = 2; ctx.beginPath(); ctx.moveTo(-12, 4); ctx.lineTo(-12, -20); ctx.stroke();
    ctx.fillStyle = faction.color; ctx.beginPath(); ctx.moveTo(-11, -19); ctx.lineTo(7, -14); ctx.lineTo(-11, -8); ctx.closePath(); ctx.fill();
    ctx.fillStyle = "rgba(8,17,16,.92)"; ctx.strokeStyle = faction.color; ctx.lineWidth = 1.5; roundRect(ctx, 4, -20, 31, 20, 9); ctx.fill(); ctx.stroke();
    ctx.fillStyle = faction.light; ctx.font = "bold 11px Segoe UI"; ctx.textAlign = "center"; ctx.textBaseline = "middle"; ctx.fillText(String(Math.max(0, Math.ceil(army.units))), 19.5, -10);
    ctx.restore();
  }

  function drawShots() {
    state.shots.forEach((shot) => {
      const alpha = shot.life / shot.maxLife;
      ctx.save(); ctx.globalAlpha = alpha; ctx.strokeStyle = shot.color; ctx.lineCap = "round";
      if (shot.level === 1) {
        ctx.lineWidth = 2; ctx.beginPath(); ctx.moveTo(shot.sx, shot.sy); ctx.lineTo(shot.tx, shot.ty); ctx.stroke();
      } else if (shot.level === 2) {
        ctx.lineWidth = 5; ctx.globalAlpha = alpha * .25; ctx.beginPath(); ctx.moveTo(shot.sx, shot.sy); ctx.lineTo(shot.tx, shot.ty); ctx.stroke();
        ctx.globalAlpha = alpha; ctx.lineWidth = 2; ctx.beginPath(); ctx.moveTo(shot.sx, shot.sy); ctx.lineTo(shot.tx, shot.ty); ctx.stroke();
      } else {
        ctx.lineWidth = shot.level === 4 ? 7 : 5; ctx.globalAlpha = alpha * .2; ctx.beginPath(); ctx.moveTo(shot.sx, shot.sy); ctx.lineTo(shot.tx, shot.ty); ctx.stroke();
        ctx.globalAlpha = alpha; ctx.lineWidth = shot.level === 4 ? 2.5 : 2; ctx.setLineDash(shot.level === 4 ? [5,4] : []);
        ctx.beginPath(); ctx.moveTo(shot.sx, shot.sy); ctx.lineTo(shot.tx, shot.ty); ctx.stroke();
        ctx.setLineDash([]); ctx.beginPath(); ctx.arc(shot.tx, shot.ty, 9 + shot.level * 2, 0, Math.PI * 2); ctx.stroke();
      }
      ctx.globalAlpha = alpha; ctx.fillStyle = shot.level === 4 ? "#f4d7ff" : "#fff3bd";
      ctx.beginPath(); ctx.arc(shot.tx, shot.ty, 3 + shot.level, 0, Math.PI * 2); ctx.fill(); ctx.restore();
    });
  }

  function drawEffects() {
    state.particles.forEach((p) => {
      ctx.save(); ctx.globalAlpha = Math.max(0, p.life / p.maxLife); ctx.fillStyle = p.color;
      ctx.beginPath(); ctx.arc(p.x, p.y, p.size, 0, Math.PI * 2); ctx.fill(); ctx.restore();
    });
    state.floaters.forEach((f) => {
      ctx.save(); ctx.globalAlpha = Math.min(1, f.life * 2); ctx.fillStyle = f.color; ctx.strokeStyle = "rgba(7,14,13,.65)"; ctx.lineWidth = 3;
      ctx.font = "bold 14px Segoe UI"; ctx.textAlign = "center"; ctx.strokeText(f.text, f.x, f.y); ctx.fillText(f.text, f.x, f.y); ctx.restore();
    });
  }

  function drawDragSelection() {
    if (!state.drag?.active) return;
    if (state.drag.mode === "box") {
      const x = Math.min(state.drag.startX, state.drag.x), y = Math.min(state.drag.startY, state.drag.y);
      const w = Math.abs(state.drag.x - state.drag.startX), h = Math.abs(state.drag.y - state.drag.startY);
      ctx.save(); ctx.fillStyle = "rgba(69,200,211,.1)"; ctx.strokeStyle = "rgba(182,246,246,.8)"; ctx.setLineDash([7,5]); ctx.lineWidth = 2; ctx.fillRect(x,y,w,h); ctx.strokeRect(x,y,w,h); ctx.restore();
      return;
    }
    if (state.drag.mode === "command") drawCommandPreview();
  }

  function drawCommandPreview() {
    const drag = state.drag;
    const pointer = { x: drag.x, y: drag.y };
    const target = hitNode(pointer);
    const sources = [...state.selection].map(nodeById).filter((node) => node?.owner === "player");
    const routed = target
      ? sources.map((source) => ({ source, route: findRoute(source, target, "player") })).filter((entry) => entry.route)
      : [];
    const valid = routed.length > 0;
    const color = valid ? "#b6f6f6" : "#f3a18f";

    ctx.save();
    ctx.lineCap = "round";
    ctx.lineJoin = "round";
    if (valid) {
      routed.forEach(({ route }) => drawRouteArrow(route, target, color));
    } else {
      const anchor = nodeById(drag.anchorId) || sources[0];
      if (anchor) drawFreeArrow(anchor, pointer, color);
    }

    if (target) {
      ctx.strokeStyle = color;
      ctx.lineWidth = 3;
      ctx.setLineDash([8, 5]);
      ctx.lineDashOffset = -performance.now() * .025;
      ctx.beginPath();
      ctx.arc(target.x, target.y, nodeRadius(target) + 17, 0, Math.PI * 2);
      ctx.stroke();
    }

    const label = valid
      ? `松开发兵 · ${routed.length} 路${routed.some(({ route }) => route.length > 2) ? "中转" : "直达"}`
      : target ? "无友方通路" : "拖向目标据点";
    ctx.setLineDash([]);
    ctx.font = "bold 12px Segoe UI, Microsoft YaHei, sans-serif";
    const width = ctx.measureText(label).width + 22;
    const labelX = Math.max(8, Math.min(W - width - 8, pointer.x + 16));
    const labelY = Math.max(8, Math.min(H - 34, pointer.y + 18));
    ctx.fillStyle = "rgba(8,18,17,.9)";
    ctx.strokeStyle = valid ? "rgba(182,246,246,.65)" : "rgba(243,161,143,.55)";
    ctx.lineWidth = 1.5;
    roundRect(ctx, labelX, labelY, width, 27, 6); ctx.fill(); ctx.stroke();
    ctx.fillStyle = color; ctx.textAlign = "center"; ctx.textBaseline = "middle";
    ctx.fillText(label, labelX + width / 2, labelY + 13.5);
    ctx.restore();
  }

  function drawRouteArrow(route, target, color) {
    const points = route.map(nodeById).filter(Boolean);
    if (points.length < 2) return;
    const previous = points[points.length - 2];
    const angle = Math.atan2(target.y - previous.y, target.x - previous.x);
    const end = {
      x: target.x - Math.cos(angle) * (nodeRadius(target) + 8),
      y: target.y - Math.sin(angle) * (nodeRadius(target) + 8),
    };
    ctx.strokeStyle = "rgba(5,16,15,.72)"; ctx.lineWidth = 11; ctx.setLineDash([]);
    ctx.beginPath(); ctx.moveTo(points[0].x, points[0].y);
    points.slice(1, -1).forEach((point) => ctx.lineTo(point.x, point.y));
    ctx.lineTo(end.x, end.y); ctx.stroke();
    ctx.strokeStyle = color; ctx.lineWidth = 4; ctx.setLineDash([10, 7]);
    ctx.lineDashOffset = -performance.now() * .035;
    ctx.beginPath(); ctx.moveTo(points[0].x, points[0].y);
    points.slice(1, -1).forEach((point) => ctx.lineTo(point.x, point.y));
    ctx.lineTo(end.x, end.y); ctx.stroke();
    drawArrowHead(end.x, end.y, angle, color);
  }

  function drawFreeArrow(anchor, pointer, color) {
    const angle = Math.atan2(pointer.y - anchor.y, pointer.x - anchor.x);
    ctx.strokeStyle = "rgba(5,16,15,.72)"; ctx.lineWidth = 10; ctx.setLineDash([]);
    ctx.beginPath(); ctx.moveTo(anchor.x, anchor.y); ctx.lineTo(pointer.x, pointer.y); ctx.stroke();
    ctx.strokeStyle = color; ctx.lineWidth = 4; ctx.setLineDash([9, 7]); ctx.lineDashOffset = -performance.now() * .035;
    ctx.beginPath(); ctx.moveTo(anchor.x, anchor.y); ctx.lineTo(pointer.x, pointer.y); ctx.stroke();
    drawArrowHead(pointer.x, pointer.y, angle, color);
  }

  function drawArrowHead(x, y, angle, color) {
    ctx.save(); ctx.translate(x, y); ctx.rotate(angle); ctx.fillStyle = color; ctx.setLineDash([]);
    ctx.beginPath(); ctx.moveTo(8, 0); ctx.lineTo(-11, -8); ctx.lineTo(-7, 0); ctx.lineTo(-11, 8); ctx.closePath(); ctx.fill(); ctx.restore();
  }

  function drawVignette() {
    const gradient = ctx.createRadialGradient(W/2,H/2,H*.25,W/2,H/2,W*.72);
    gradient.addColorStop(.55,"rgba(4,11,10,0)"); gradient.addColorStop(1,"rgba(4,11,10,.5)");
    ctx.fillStyle = gradient; ctx.fillRect(0,0,W,H);
    ctx.strokeStyle = "rgba(244,220,169,.11)"; ctx.lineWidth = 2; ctx.strokeRect(9,9,W-18,H-18);
  }

  function roundRect(context, x, y, width, height, radius) {
    const r = Math.min(radius, width / 2, height / 2);
    context.beginPath(); context.moveTo(x + r, y); context.arcTo(x + width, y, x + width, y + height, r); context.arcTo(x + width, y + height, x, y + height, r); context.arcTo(x, y + height, x, y, r); context.arcTo(x, y, x + width, y, r); context.closePath();
  }

  function getPointer(event) {
    const rect = canvas.getBoundingClientRect();
    return { x: (event.clientX - rect.left) * W / rect.width, y: (event.clientY - rect.top) * H / rect.height };
  }

  function hitNode(point) {
    return [...state.nodes].reverse().find((node) => Math.hypot(point.x - node.x, point.y - node.y) <= nodeRadius(node) + 10) || null;
  }

  function onPointerDown(event) {
    if (!state.started || state.paused || state.gameOver) return;
    initAudio();
    const point = getPointer(event);
    const node = hitNode(point);
    let mode = "inspect";
    if (node?.owner === "player") {
      mode = "command";
      const wasSelected = state.selection.has(node.id);
      if (!wasSelected) {
        if (!event.shiftKey) state.selection.clear();
        state.selection.add(node.id);
      }
      state.drag = { mode, anchorId: node.id, wasSelected, startX: point.x, startY: point.y, x: point.x, y: point.y, active: false, shift: event.shiftKey };
      updateUI(true);
    } else {
      mode = node ? "inspect" : "box";
      state.drag = { mode, startX: point.x, startY: point.y, x: point.x, y: point.y, active: false, shift: event.shiftKey };
    }
    canvas.setPointerCapture?.(event.pointerId);
  }

  function onPointerMove(event) {
    const point = getPointer(event); state.pointer = point;
    state.hoveredNode = hitNode(point);
    if (state.drag) {
      state.drag.x = point.x; state.drag.y = point.y;
      if (state.drag.mode !== "inspect" && Math.hypot(point.x - state.drag.startX, point.y - state.drag.startY) > 8) {
        state.drag.active = true;
        canvas.style.cursor = state.drag.mode === "command" ? "grabbing" : "crosshair";
      }
    }
  }

  function onPointerUp(event) {
    if (!state.drag || !state.started || state.paused || state.gameOver) { state.drag = null; return; }
    const point = getPointer(event);
    if (state.drag.mode === "command") {
      if (state.drag.active) {
        const target = hitNode(point);
        if (target) dispatchSelection(target);
        else showToast("请将行军箭头释放在目标据点上");
      } else if (state.drag.shift && state.drag.wasSelected) {
        state.selection.delete(state.drag.anchorId);
      } else {
        playSound("select");
      }
    } else if (state.drag.mode === "box" && state.drag.active) {
      const minX = Math.min(state.drag.startX, point.x), maxX = Math.max(state.drag.startX, point.x);
      const minY = Math.min(state.drag.startY, point.y), maxY = Math.max(state.drag.startY, point.y);
      if (!state.drag.shift) state.selection.clear();
      state.nodes.filter((node) => node.owner === "player" && node.x >= minX && node.x <= maxX && node.y >= minY && node.y <= maxY).forEach((node) => state.selection.add(node.id));
      if (state.selection.size) playSound("select");
    } else {
      if (!state.drag.shift) state.selection.clear();
    }
    state.drag = null;
    canvas.style.cursor = "crosshair";
    updateUI(true);
  }

  function togglePause() {
    if (!state.started || state.gameOver || $("#menuOverlay").classList.contains("show")) return;
    state.paused = !state.paused;
    $("#pauseIcon").textContent = state.paused ? "▶" : "Ⅱ";
    $("#pauseButton").classList.toggle("active", state.paused);
    showToast(state.paused ? "战局已暂停，画面保持可见" : "战局继续");
  }

  function selectAll() {
    state.selection.clear();
    state.nodes.filter((node) => node.owner === "player").forEach((node) => state.selection.add(node.id));
    playSound("select"); updateUI(true);
  }

  function renderBuildingData() {
    const specialText = {
      village: "基础生产建筑；升级主要提高自产速度与驻军软上限。",
      fort: "防御系数较高；适合承受进攻并囤积增援部队。",
      tower: "不自动产兵。3级攻击附带减速；4级每击杀4人俘虏1人，10名俘虏自动突袭可达目标中驻军最少者。",
      stable: "从驿站出发的常规部队获得 1.55× 行军速度。",
      armory: "从军械所出发的常规部队获得 1.25× 出征战力。",
    };
    $("#buildingDataGrid").innerHTML = BUILDING_TYPES.map((type) => {
      const building = BUILDINGS[type];
      const isTower = type === "tower";
      const headers = isTower
        ? ["等级", "软上限", "产兵/秒", "防御", "伤害", "射程", "间隔", "升级消耗"]
        : ["等级", "软上限", "产兵/秒", "防御", "出征战力", "升级消耗"];
      const rows = [1, 2, 3, 4].map((level) => {
        const defense = (building.defense * (1 + (level - 1) * .08)).toFixed(2);
        const power = type === "armory" ? "1.25×" : "1.00×";
        const values = isTower
          ? [level, building.softCap[level], building.production[level].toFixed(1), `${defense}×`, building.damage[level].toFixed(1), building.range[level], `${building.cooldown[level].toFixed(2)}秒`, level === 1 ? "—" : building.costs[level]]
          : [level, building.softCap[level], building.production[level].toFixed(1), `${defense}×`, power, level === 1 ? "—" : building.costs[level]];
        return `<tr>${values.map((value) => `<td>${value}</td>`).join("")}</tr>`;
      }).join("");
      return `<article class="building-data-card ${isTower ? "tower-card" : ""}">
        <header><span>${building.icon}</span><div><h3>${building.name}</h3><small>${building.description}</small></div></header>
        <div style="overflow-x:auto"><table class="building-data-table"><thead><tr>${headers.map((header) => `<th>${header}</th>`).join("")}</tr></thead><tbody>${rows}</tbody></table></div>
        <p class="building-special">${specialText[type]}</p>
      </article>`;
    }).join("");
  }

  function renderCampaignCards() {
    const list = $("#campaignList"); list.innerHTML = "";
    const unlockedCount = state.progress.unlocked || 1;
    const completedCount = LEVELS.filter((_, index) => (state.progress.stars[index] || 0) > 0).length;
    $("#worldProgress").textContent = `已征服 ${completedCount} / ${LEVELS.length}`;
    const routeSvg = $("#campaignRoutes");
    routeSvg.innerHTML = CAMPAIGN_POSITIONS.slice(0, -1).map((point, index) => {
      const next = CAMPAIGN_POSITIONS[index + 1];
      const conquered = index + 1 < unlockedCount ? "conquered" : "";
      const midX = (point[0] + next[0]) / 2;
      return `<path class="${conquered}" d="M ${point[0]} ${point[1]} C ${midX} ${point[1]}, ${midX} ${next[1]}, ${next[0]} ${next[1]}"/>`;
    }).join("");
    LEVELS.forEach((level, index) => {
      const unlocked = index < unlockedCount;
      const stars = state.progress.stars[index] || 0;
      const position = CAMPAIGN_POSITIONS[index];
      const card = document.createElement("button");
      card.type = "button";
      card.className = `campaign-card map-level ${index === state.levelIndex ? "active" : ""} ${stars ? "completed" : ""} ${unlocked ? "" : "locked"}`;
      card.dataset.level = index;
      card.disabled = !unlocked;
      card.style.left = `${position[0] / 10}%`;
      card.style.top = `${position[1] / 5.2}%`;
      card.setAttribute("aria-label", unlocked ? `第${index + 1}关 ${level.name} ${stars}星` : `第${index + 1}关 ${level.name} 未解锁`);
      card.innerHTML = `<span class="map-node-orb">${unlocked ? String(index + 1).padStart(2,"0") : "◆"}</span><span class="map-node-label"><b>${level.name}</b><small>${unlocked ? "★".repeat(stars) + "☆".repeat(3-stars) : "未解锁"}</small></span>`;
      list.appendChild(card);
    });
    $$(".campaign-card").forEach((card) => card.addEventListener("click", () => {
      state.levelIndex = Number(card.dataset.level); renderCampaignCards(); updateStaticUI(); updateMissionBrief(); playSound("select");
    }));
    updateMissionBrief();
    updateAccountUI();
  }

  function updateMissionBrief() {
    const level = LEVELS[state.levelIndex];
    const stars = state.progress.stars[state.levelIndex] || 0;
    const best = state.progress.best[state.levelIndex];
    $("#selectedLevelNumber").textContent = String(state.levelIndex + 1).padStart(2, "0");
    $("#selectedLevelSubtitle").textContent = level.subtitle.toUpperCase();
    $("#selectedLevelName").textContent = level.name;
    $("#selectedLevelObjective").textContent = level.objective;
    $("#selectedLevelStars").textContent = "★".repeat(stars) + "☆".repeat(3 - stars);
    $("#selectedLevelBest").textContent = best ? formatTime(best) : "--:--";
  }

  function updateAccountUI() {
    const account = activeAccount();
    if (!account) return;
    $("#accountName").textContent = account.name;
    $("#accountAvatar").textContent = account.name.trim().charAt(0).toUpperCase() || "游";
    $("#deleteAccountButton").classList.toggle("hidden", account.id === "guest");
    $$(".difficulty-button").forEach((button) => button.classList.toggle("active", button.dataset.difficulty === state.difficulty));
    syncSettingsUI();
  }

  function renderProfiles() {
    const list = $("#profileList");
    list.innerHTML = "";
    state.accountStore.accounts.forEach((account) => {
      const stars = Object.values(account.progress?.stars || {}).reduce((sum, value) => sum + Number(value || 0), 0);
      const button = document.createElement("button");
      button.type = "button";
      button.className = `profile-option ${account.id === state.accountStore.currentId ? "active" : ""}`;
      button.dataset.accountId = account.id;
      button.innerHTML = `<span>${account.name.trim().charAt(0).toUpperCase() || "游"}</span><b>${escapeHtml(account.name)}<small>${account.stats.wins} 胜 · ${stars} 星</small></b><i>${account.pinHash ? "口令" : "免口令"}</i>`;
      list.appendChild(button);
    });
    $$(".profile-option").forEach((button) => button.addEventListener("click", () => requestAccountSwitch(button.dataset.accountId)));
  }

  function escapeHtml(value) {
    return String(value).replace(/[&<>'"]/g, (character) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", "'": "&#39;", '"': "&quot;" }[character]));
  }

  function requestAccountSwitch(id) {
    const account = state.accountStore.accounts.find((item) => item.id === id);
    if (!account) return;
    if (id === state.accountStore.currentId) {
      $("#accountMessage").textContent = "当前已经登录此档案。";
      return;
    }
    if (!account.pinHash) {
      switchAccount(id);
      return;
    }
    state.pendingAccountId = id;
    $("#loginPinArea").classList.remove("hidden");
    $("#loginPin").value = "";
    $("#loginPin").focus();
    $("#accountMessage").textContent = `请输入「${account.name}」的本机口令。`;
  }

  async function hashPin(pin) {
    if (window.crypto?.subtle) {
      const encoded = new TextEncoder().encode(`frontier-claim:${pin}`);
      const digest = await window.crypto.subtle.digest("SHA-256", encoded);
      return [...new Uint8Array(digest)].map((byte) => byte.toString(16).padStart(2, "0")).join("");
    }
    return btoa(`frontier-claim:${pin}`);
  }

  function switchAccount(id) {
    saveAccountStore();
    const account = state.accountStore.accounts.find((item) => item.id === id);
    if (!account) return;
    state.accountStore.currentId = id;
    state.progress = account.progress;
    state.sound = account.settings.sound !== false;
    state.effects = account.settings.effects !== false;
    state.speed = Number(account.settings.speed) || 1;
    state.difficulty = account.settings.difficulty || "normal";
    state.levelIndex = Math.min(Math.max(0, (state.progress.unlocked || 1) - 1), LEVELS.length - 1);
    state.started = false;
    resetLevel(state.levelIndex);
    saveAccountStore();
    renderCampaignCards();
    renderProfiles();
    $("#loginPinArea").classList.add("hidden");
    $("#accountOverlay").classList.remove("show");
    $("#menuOverlay").classList.add("show");
    showToast(`已切换至 ${account.name}`);
  }

  function syncSettingsUI() {
    $("#settingSound").textContent = state.sound ? "开启" : "关闭";
    $("#settingSound").classList.toggle("off", !state.sound);
    $("#settingEffects").textContent = state.effects ? "完整" : "精简";
    $("#settingEffects").classList.toggle("off", !state.effects);
    $$("#settingSpeed button").forEach((button) => button.classList.toggle("active", Number(button.dataset.speed) === state.speed));
    $("#soundIcon").textContent = state.sound ? "♪" : "×";
    $("#soundButton").classList.toggle("muted", !state.sound);
    $("#speedText").textContent = `${state.speed}×`;
  }

  function openAccountPanel() {
    renderProfiles();
    $("#accountMessage").textContent = "";
    $("#loginPinArea").classList.add("hidden");
    $("#accountOverlay").classList.add("show");
  }

  function openSettingsPanel() {
    syncSettingsUI();
    $("#settingsOverlay").classList.add("show");
  }

  function openMenu() {
    if (state.started && !state.gameOver) state.paused = true;
    renderCampaignCards();
    $("#menuOverlay").classList.add("show");
  }

  function startSelectedLevel() {
    initAudio();
    resetLevel(state.levelIndex);
    state.started = true;
    $("#menuOverlay").classList.remove("show");
    $("#resultOverlay").classList.remove("show");
    showToast("按住友方据点拖向目标，松开后出兵");
    playSound("select");
  }

  function bindUI() {
    canvas.addEventListener("pointerdown", onPointerDown);
    canvas.addEventListener("pointermove", onPointerMove);
    canvas.addEventListener("pointerup", onPointerUp);
    canvas.addEventListener("pointerleave", () => { state.hoveredNode = null; });
    canvas.addEventListener("contextmenu", (event) => { event.preventDefault(); state.selection.clear(); updateUI(true); });
    canvas.addEventListener("dblclick", (event) => {
      const node = hitNode(getPointer(event));
      if (node?.owner === "player") { state.selection.clear(); state.selection.add(node.id); upgradeSelected(); }
    });

    $("#pauseButton").addEventListener("click", togglePause);
    $("#restartButton").addEventListener("click", () => { if (state.started) { resetLevel(); state.started = true; showToast("战役已重新开始"); } });
    $("#speedButton").addEventListener("click", () => { state.speed = state.speed === 1 ? 1.5 : state.speed === 1.5 ? 2 : 1; syncSettingsUI(); saveAccountStore(); });
    $("#soundButton").addEventListener("click", () => { state.sound = !state.sound; syncSettingsUI(); saveAccountStore(); if (state.sound) playSound("select"); });
    $("#levelButton").addEventListener("click", openMenu);
    $("#selectAllButton").addEventListener("click", selectAll);
    $("#upgradeButton").addEventListener("click", upgradeSelected);
    $("#convertType").addEventListener("change", () => updateUI(true));
    $("#convertButton").addEventListener("click", convertSelected);
    $$(".ratio-button").forEach((button) => button.addEventListener("click", () => {
      $$(".ratio-button").forEach((b) => b.classList.remove("active")); button.classList.add("active"); state.sendRatio = Number(button.dataset.ratio); updateUI(true);
    }));
    $$(".difficulty-button").forEach((button) => button.addEventListener("click", () => {
      $$(".difficulty-button").forEach((b) => b.classList.remove("active")); button.classList.add("active"); state.difficulty = button.dataset.difficulty; updateStaticUI(); saveAccountStore(); playSound("select");
    }));
    $("#accountButton").addEventListener("click", openAccountPanel);
    $("#accountClose").addEventListener("click", () => $("#accountOverlay").classList.remove("show"));
    $("#settingsButton").addEventListener("click", openSettingsPanel);
    $("#settingsClose").addEventListener("click", () => $("#settingsOverlay").classList.remove("show"));
    $("#buildingDataButton").addEventListener("click", () => { renderBuildingData(); $("#buildingDataOverlay").classList.add("show"); });
    $("#buildingDataClose").addEventListener("click", () => $("#buildingDataOverlay").classList.remove("show"));
    $("#settingSound").addEventListener("click", () => { state.sound = !state.sound; syncSettingsUI(); saveAccountStore(); if (state.sound) playSound("select"); });
    $("#settingEffects").addEventListener("click", () => { state.effects = !state.effects; syncSettingsUI(); saveAccountStore(); });
    $$("#settingSpeed button").forEach((button) => button.addEventListener("click", () => { state.speed = Number(button.dataset.speed); syncSettingsUI(); saveAccountStore(); }));
    $("#resetProgressButton").addEventListener("click", () => {
      if (!window.confirm(`确定重置「${activeAccount().name}」的全部关卡、星级和最佳时间吗？`)) return;
      state.progress = freshProgress();
      activeAccount().progress = state.progress;
      state.levelIndex = 0;
      saveProgress();
      resetLevel(0);
      renderCampaignCards();
      $("#settingsOverlay").classList.remove("show");
      showToast("当前账号的战役进度已重置");
    });
    $("#createAccountForm").addEventListener("submit", async (event) => {
      event.preventDefault();
      const name = $("#newAccountName").value.trim();
      const pin = $("#newAccountPin").value.trim();
      if (name.length < 2) { $("#accountMessage").textContent = "名称至少需要 2 个字符。"; return; }
      if (!/^\d{4}$/.test(pin)) { $("#accountMessage").textContent = "口令必须是 4 位数字。"; return; }
      if (state.accountStore.accounts.some((account) => account.name.toLowerCase() === name.toLowerCase())) { $("#accountMessage").textContent = "这个指挥官名称已存在。"; return; }
      const account = {
        id: `account-${Date.now()}-${Math.random().toString(36).slice(2,7)}`,
        name, pinHash: await hashPin(pin), createdAt: Date.now(),
        progress: freshProgress(), settings: freshSettings(), stats: freshStats(),
      };
      state.accountStore.accounts.push(account);
      $("#createAccountForm").reset();
      switchAccount(account.id);
    });
    $("#loginAccountButton").addEventListener("click", async () => {
      const account = state.accountStore.accounts.find((item) => item.id === state.pendingAccountId);
      const pin = $("#loginPin").value.trim();
      if (!account || await hashPin(pin) !== account.pinHash) { $("#accountMessage").textContent = "口令不正确。"; return; }
      switchAccount(account.id);
    });
    $("#loginPin").addEventListener("keydown", (event) => { if (event.key === "Enter") $("#loginAccountButton").click(); });
    $("#deleteAccountButton").addEventListener("click", () => {
      const current = activeAccount();
      if (!current || current.id === "guest" || !window.confirm(`确定永久删除本机账号「${current.name}」及其全部存档吗？`)) return;
      saveAccountStore();
      state.accountStore.accounts = state.accountStore.accounts.filter((account) => account.id !== current.id);
      const guest = state.accountStore.accounts.find((account) => account.id === "guest") || state.accountStore.accounts[0];
      state.accountStore.currentId = guest.id;
      state.progress = guest.progress;
      state.sound = guest.settings.sound !== false;
      state.effects = guest.settings.effects !== false;
      state.speed = Number(guest.settings.speed) || 1;
      state.difficulty = guest.settings.difficulty || "normal";
      state.levelIndex = Math.min(Math.max(0, (state.progress.unlocked || 1) - 1), LEVELS.length - 1);
      state.started = false;
      resetLevel(state.levelIndex);
      saveAccountStore();
      renderCampaignCards();
      renderProfiles();
      $("#accountOverlay").classList.remove("show");
      showToast("个人账号已从本机删除");
    });
    $("#startButton").addEventListener("click", startSelectedLevel);
    $("#howToButton").addEventListener("click", () => $("#howToOverlay").classList.add("show"));
    $("#howToClose").addEventListener("click", () => $("#howToOverlay").classList.remove("show"));
    $("#howToDone").addEventListener("click", () => $("#howToOverlay").classList.remove("show"));
    $("#resultRestart").addEventListener("click", () => { $("#resultOverlay").classList.remove("show"); startSelectedLevel(); });
    $("#resultNext").addEventListener("click", () => {
      const won = $("#resultNext").dataset.victory === "1";
      $("#resultOverlay").classList.remove("show");
      if (won && state.levelIndex < LEVELS.length - 1) { state.levelIndex++; startSelectedLevel(); }
      else openMenu();
    });

    window.addEventListener("keydown", (event) => {
      if (event.code === "Space") { event.preventDefault(); togglePause(); }
      if (event.key.toLowerCase() === "r" && state.started) { resetLevel(); state.started = true; }
      if (event.key.toLowerCase() === "a" && state.started && !state.paused) selectAll();
      if (event.key.toLowerCase() === "u") upgradeSelected();
      if (event.key === "1" || event.key === "2") {
        const button = $(`.ratio-button[data-ratio="${event.key === "1" ? "0.5" : "1"}"]`);
        button?.click();
      }
      if (event.key === "Escape") {
        if ($("#accountOverlay").classList.contains("show")) $("#accountOverlay").classList.remove("show");
        else if ($("#buildingDataOverlay").classList.contains("show")) $("#buildingDataOverlay").classList.remove("show");
        else if ($("#settingsOverlay").classList.contains("show")) $("#settingsOverlay").classList.remove("show");
        else if ($("#howToOverlay").classList.contains("show")) $("#howToOverlay").classList.remove("show");
        else { state.selection.clear(); updateUI(true); }
      }
    });
    document.addEventListener("visibilitychange", () => {
      if (document.hidden && state.started && !state.gameOver) {
        state.paused = true;
        $("#pauseIcon").textContent = "▶";
        $("#pauseButton").classList.add("active");
      }
    });
  }

  function resizeCanvas() {
    const dpr = Math.min(window.devicePixelRatio || 1, 2);
    canvas.width = W * dpr; canvas.height = H * dpr;
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  }

  function loop(time) {
    const dt = state.lastTime ? (time - state.lastTime) / 1000 : 0;
    state.lastTime = time;
    update(dt);
    render();
    requestAnimationFrame(loop);
  }

  resizeCanvas();
  window.addEventListener("resize", resizeCanvas);
  bindUI();
  resetLevel(0);
  renderCampaignCards();
  requestAnimationFrame(loop);
})();
