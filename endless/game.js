(() => {
  "use strict";

  const $ = (selector) => document.querySelector(selector);
  const $$ = (selector) => [...document.querySelectorAll(selector)];
  const canvas = $("#gameCanvas");
  const ctx = canvas.getContext("2d");
  const W = 1280;
  const H = 720;
  const LINE_Y = 625;
  const TAU = Math.PI * 2;
  const COLORS = { cyan: "#59e6ff", violet: "#9a77ff", frost: "#a6efff", fire: "#ff8d56", gold: "#ffd17a", danger: "#ff5676", green: "#69f0bd", ink: "#e6f5fb" };

  const TURRET_DATA = [
    { x: 154, y: 650, scale: .78, damage: .68, rate: 1.16 },
    { x: 382, y: 646, scale: .92, damage: .9, rate: 1.04 },
    { x: 640, y: 637, scale: 1.18, damage: 1.28, rate: .86, main: true },
    { x: 898, y: 646, scale: .92, damage: .9, rate: 1.04 },
    { x: 1126, y: 650, scale: .78, damage: .68, rate: 1.16 }
  ];

  const ENEMY_TYPES = {
    swarm: { name: "游群", hp: .66, speed: 1.02, radius: 9, damage: 3, score: 10, color: "#ec638f" },
    runner: { name: "疾行体", hp: .5, speed: 1.68, radius: 8, damage: 4, score: 16, color: "#ffb56f" },
    tank: { name: "重甲体", hp: 2.9, speed: .62, radius: 16, damage: 11, score: 36, color: "#b083ff" },
    shield: { name: "护盾体", hp: 1.6, speed: .82, radius: 13, damage: 7, score: 27, color: "#6bbcff", shield: .48 },
    splitter: { name: "裂殖体", hp: 1.35, speed: .9, radius: 12, damage: 7, score: 29, color: "#fb7298", split: true },
    elite: { name: "精英构造", hp: 7.8, speed: .68, radius: 23, damage: 18, score: 160, color: "#ffd17a", elite: true },
    boss: { name: "星潮主宰", hp: 26, speed: .48, radius: 34, damage: 35, score: 680, color: "#ff5676", boss: true }
  };

  const CARD_COLORS = { "雷": COLORS.violet, "霜": COLORS.frost, "火": COLORS.fire, "弹道": COLORS.cyan, "生存": COLORS.green, "超频": COLORS.gold };
  const CARDS = [
    { id: "caliber", name: "增压弹芯", glyph: "◇", rarity: "基础", tags: ["弹道"], max: 5, desc: (r) => `全体炮台伤害提高 ${24 + r * 3}%。`, note: "最稳定的伤害底座；能放大全部元素触发。" },
    { id: "rapid", name: "短周期供能", glyph: "»", rarity: "基础", tags: ["弹道"], max: 5, desc: (r) => `全体炮台攻击速度提高 ${18 + r * 2}%。`, note: "更高频地触发雷、霜、火与命中效果。" },
    { id: "twin", name: "双生棱镜", glyph: "Ⅱ", rarity: "进阶", tags: ["弹道"], max: 2, minWave: 2, desc: (r) => `每次攻击额外发射 1 枚弹体；单枚伤害调整为 ${r ? 78 : 74}%。`, note: "弹体独立触发元素，是多数流派的频率核心。" },
    { id: "pierce", name: "相位穿透", glyph: "↦", rarity: "基础", tags: ["弹道"], max: 3, desc: (r) => `弹体额外穿透 ${r + 1} 个目标，穿透后保留 72% 伤害。`, note: "面对密集游群时，可快速抬高连斩与触发次数。" },
    { id: "crit", name: "弱点演算", glyph: "⌖", rarity: "进阶", tags: ["弹道"], max: 4, minWave: 2, desc: (r) => `暴击率提高 ${8 + r * 3}%，暴击造成 190% 伤害。`, note: "与脆晶标记联动时，控制会直接转化为爆发。" },
    { id: "arc", name: "游弋电弧", glyph: "ϟ", rarity: "武装", tags: ["雷"], max: 4, desc: (r) => `命中有 ${22 + r * 7}% 概率跳跃 ${2 + Math.floor(r / 2)} 次，造成 48% 伤害。`, note: "雷系主组件；解锁超导与等离子组合。" },
    { id: "voltage", name: "高压导体", glyph: "⌁", rarity: "进阶", tags: ["雷"], max: 3, req: ["arc"], desc: (r) => `电弧伤害提高 ${32 + r * 14}%，搜索半径扩大。`, note: "直接强化游弋电弧，也是雷暴核心组件。" },
    { id: "static", name: "标记电场", glyph: "⊙", rarity: "进阶", tags: ["雷", "超频"], max: 2, req: ["arc"], minWave: 3, desc: (r) => `集火标记每 ${1.45 - r * .2} 秒释放一次范围电击。`, note: "让一次准确点击持续压制危险区域。" },
    { id: "frost", name: "寒霜介质", glyph: "✣", rarity: "武装", tags: ["霜"], max: 4, desc: (r) => `命中使目标减速 ${24 + r * 5}%，持续 ${1.8 + r * .35} 秒。`, note: "霜系主组件；为脆晶、碎裂与热震提供条件。" },
    { id: "brittle", name: "脆晶标记", glyph: "✧", rarity: "进阶", tags: ["霜", "弹道"], max: 3, req: ["frost"], desc: (r) => `对减速目标的暴击率额外提高 ${18 + r * 8}%。`, note: "将寒霜控制转换为点杀能力。" },
    { id: "shatter", name: "碎裂传播", glyph: "✺", rarity: "稀有", tags: ["霜"], max: 3, reqRank: ["frost", 2], minWave: 3, desc: (r) => `减速目标死亡时爆炸，造成其最大生命 ${8 + r * 3}% 的范围伤害。`, note: "敌人越密集，霜爆收益越高。" },
    { id: "burn", name: "熔核附着", glyph: "◈", rarity: "武装", tags: ["火"], max: 4, desc: (r) => `命中附加 ${3 + r * .5} 秒灼烧，每秒造成基础伤害的 ${34 + r * 10}%。`, note: "火系主组件；持续处理重甲单位。" },
    { id: "wildfire", name: "野火协议", glyph: "♢", rarity: "进阶", tags: ["火"], max: 3, req: ["burn"], desc: (r) => `燃烧目标死亡时，将灼烧扩散给附近 ${2 + r} 个敌人。`, note: "用一个死亡点燃整片敌潮。" },
    { id: "execute", name: "红线处决", glyph: "⌁", rarity: "进阶", tags: ["火", "弹道"], max: 2, reqRank: ["burn", 2], minWave: 3, desc: (r) => `燃烧目标低于 ${15 + r * 7}% 生命时立即被处决（首领减半）。`, note: "跳过敌人最危险的残血推进阶段。" },
    { id: "recycle", name: "战果回流", glyph: "↻", rarity: "基础", tags: ["生存", "超频"], max: 3, desc: (r) => `每次歼灭额外获得 ${20 + r * 15}% 极限火力充能。`, note: "清怪越快，爆发窗口越多。" },
    { id: "repair", name: "自愈屏障", glyph: "+", rarity: "进阶", tags: ["生存"], max: 3, minWave: 2, desc: (r) => `每波结束修复 ${3 + r * 2} 点屏障；满生命时转化为护盾。`, note: "无尽模式的长期容错来源。" },
    { id: "overdrive", name: "极限增幅", glyph: "∞", rarity: "进阶", tags: ["超频"], max: 3, desc: (r) => `极限火力的射速与伤害增幅提高至 ${72 + r * 12}%。`, note: "在精英进入火力区时手动制造爆发。" },
    { id: "echo", name: "回声校准", glyph: "◎", rarity: "稀有", tags: ["超频", "弹道"], max: 2, req: ["overdrive"], minWave: 4, desc: (r) => `极限火力期间每第 ${5 - r} 次攻击会完整复制一次。`, note: "复制同时继承弹道与元素加成。" },
    { id: "superconduct", name: "超导风暴", glyph: "❄", rarity: "组合", tags: ["雷", "霜"], max: 1, req: ["arc", "frost"], minWave: 3, combo: true, desc: () => "电弧命中会施加寒霜；对已减速目标造成 175% 电弧伤害。", note: "组合点亮：雷击扩散寒霜，寒霜反过来放大雷击。" },
    { id: "plasma", name: "等离子链", glyph: "Ψ", rarity: "组合", tags: ["雷", "火"], max: 1, req: ["arc", "burn"], minWave: 3, combo: true, desc: () => "电弧击中燃烧目标时引爆灼烧，并把剩余伤害传向下一目标。", note: "组合点亮：持续伤害转化为可连锁的瞬间爆发。" },
    { id: "thermal", name: "冷热震荡", glyph: "◐", rarity: "组合", tags: ["霜", "火"], max: 1, req: ["frost", "burn"], minWave: 3, combo: true, desc: () => "同处燃烧与减速状态的敌人首次受击时，额外损失 12% 最大生命。", note: "组合点亮：对重甲和首领尤其有效。" },
    { id: "storm", name: "雷暴核心", glyph: "☈", rarity: "组合", tags: ["雷", "弹道"], max: 1, req: ["voltage", "twin"], minWave: 5, combo: true, desc: () => "每 9 次电弧触发一次全场雷暴，轰击 7 个目标。", note: "组合点亮：高频弹道迅速积累全场雷暴。" },
    { id: "absolute", name: "绝对零度", glyph: "✳", rarity: "组合", tags: ["霜", "弹道"], max: 1, req: ["brittle", "shatter"], minWave: 5, combo: true, desc: () => "对减速目标暴击时冻结 0.75 秒；冻结单位碎裂伤害翻倍。", note: "组合点亮：精确暴击把敌潮锁进连环碎裂。" },
    { id: "phoenix", name: "余烬重生", glyph: "♨", rarity: "组合", tags: ["火", "生存"], max: 1, req: ["wildfire", "repair"], minWave: 5, combo: true, desc: () => "每 60 个灼烧击杀修复 4 点屏障，并点燃全场敌人。", note: "组合点亮：进攻效率直接转化为长期续航。" },
    { id: "singularity", name: "奇点放大器", glyph: "●", rarity: "传说", tags: ["弹道", "超频"], max: 1, minWave: 9, desc: () => "伤害和射速提高 22%，但每波敌军数量增加 12%。", note: "主动提高风险上限，用更猛烈的敌潮换取更高得分。" }
  ];
  const CARD_MAP = Object.fromEntries(CARDS.map((card) => [card.id, card]));
  const COMBOS = [
    { id: "superconduct", name: "超导风暴", glyph: "❄", text: "雷 + 霜 · 传导冻结" },
    { id: "plasma", name: "等离子链", glyph: "Ψ", text: "雷 + 火 · 灼烧爆链" },
    { id: "thermal", name: "冷热震荡", glyph: "◐", text: "霜 + 火 · 百分比热震" },
    { id: "storm", name: "雷暴核心", glyph: "☈", text: "雷 + 弹道 · 全场轰击" },
    { id: "absolute", name: "绝对零度", glyph: "✳", text: "霜 + 暴击 · 冻结碎裂" },
    { id: "phoenix", name: "余烬重生", glyph: "♨", text: "火 + 生存 · 击杀修复" }
  ];
  const ACCOUNT_KEY = "endless-defense-accounts-v1";

  const state = {
    started: false, paused: false, drafting: false, gameOver: false,
    wave: 0, waveTarget: 0, waveSpawned: 0, waveResolved: 0, spawnTimer: 0, waveEnding: false, waveEndTimer: 0, startDelay: 0,
    elapsed: 0, score: 0, kills: 0, chain: 0, chainTimer: 0, coreHp: 100, coreMax: 100, shield: 0,
    protocol: null, cards: new Map(), tagCounts: {}, turrets: [], enemies: [], projectiles: [], particles: [], floaters: [], lightning: [], shockwaves: [],
    focus: null, focusCooldown: 0, overdrive: 0, overdriveTime: 0, staticTimer: 0, arcCount: 0, phoenixKills: 0,
    nextEnemyId: 1, nextProjectileId: 1, lastTime: 0, speed: 1, sound: true, currentOffers: [], rerolled: false,
    bannerTimer: 0, shake: 0, flash: 0, best: { wave: 0, score: 0 },
    accountStore: loadAccountStore(), authenticated: false, pendingAccountId: null, accountWasPaused: false, saveAccumulator: 0
  };

  function loadAccountStore() {
    try {
      const saved = JSON.parse(localStorage.getItem(ACCOUNT_KEY));
      if (saved && Array.isArray(saved.accounts)) return { currentId: saved.currentId || null, accounts: saved.accounts };
    } catch { /* start with a clean local archive */ }
    return { currentId: null, accounts: [] };
  }
  function persistAccountStore() {
    try { localStorage.setItem(ACCOUNT_KEY, JSON.stringify(state.accountStore)); } catch { showToast("本机存储空间不足，记录未能保存"); }
  }
  function activeAccount() {
    if (!state.authenticated) return null;
    return state.accountStore.accounts.find((account) => account.id === state.accountStore.currentId) || null;
  }
  function escapeHtml(text) { return String(text).replace(/[&<>'"]/g, (char) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", "'": "&#39;", '"': "&quot;" })[char]); }
  async function hashPin(pin, salt) {
    try {
      const bytes = new TextEncoder().encode(`${salt}:${pin}:endless-local`);
      const digest = await crypto.subtle.digest("SHA-256", bytes);
      return [...new Uint8Array(digest)].map((byte) => byte.toString(16).padStart(2, "0")).join("");
    } catch {
      let hash = 2166136261;
      for (const char of `${salt}:${pin}:endless-local`) { hash ^= char.charCodeAt(0); hash = Math.imul(hash, 16777619); }
      return `fallback-${(hash >>> 0).toString(16)}`;
    }
  }
  function saveBest() {
    if (state.wave > state.best.wave || state.score > state.best.score) {
      state.best = { wave: Math.max(state.best.wave, state.wave), score: Math.max(state.best.score, state.score) };
      const account = activeAccount();
      if (account) { account.best = { ...state.best }; account.lastPlayedAt = Date.now(); persistAccountStore(); }
    }
    $("#bestRecord").textContent = `第 ${state.best.wave} 波 · ${state.best.score.toLocaleString()} 分`;
  }
  function cardRank(id) { return state.cards.get(id) || 0; }
  function hasCard(id) { return cardRank(id) > 0; }

  function renderProfiles() {
    const accounts = state.accountStore.accounts;
    $("#profileList").innerHTML = accounts.length ? accounts.map((account) => {
      const selected = account.id === state.pendingAccountId;
      const isLast = account.id === state.accountStore.currentId;
      const runText = account.run ? `存档：第 ${account.run.wave || 1} 波 · ${formatTime(account.run.elapsed || 0)}` : "暂无进行中的存档";
      return `<button class="profile-option ${selected ? "active" : ""}" type="button" data-account="${account.id}"><i>${escapeHtml(account.name.slice(0, 1).toUpperCase())}</i><span><b>${escapeHtml(account.name)}</b><small>${runText}</small></span><em>${isLast ? "上次登录" : "选择"}</em></button>`;
    }).join("") : '<div class="profile-empty">这台设备还没有账号，请在右侧创建。</div>';
    $$(".profile-option").forEach((button) => button.addEventListener("click", () => selectAccount(button.dataset.account)));
    $("#loginArea").classList.toggle("hidden", !state.pendingAccountId);
  }

  function selectAccount(id) {
    const account = state.accountStore.accounts.find((item) => item.id === id);
    if (!account) return;
    state.pendingAccountId = id;
    $("#loginPin").value = "";
    $("#loginMessage").textContent = "";
    renderProfiles();
    setTimeout(() => $("#loginPin").focus(), 0);
  }

  function updateAccountUI() {
    const account = activeAccount();
    $("#accountName").textContent = account?.name || "未登录";
    $("#accountAvatar").textContent = account ? account.name.slice(0, 1).toUpperCase() : "?";
    $("#startAccountName").textContent = account?.name || "未登录";
    $("#startAccountAvatar").textContent = account ? account.name.slice(0, 1).toUpperCase() : "?";
    $("#accountClose").classList.toggle("hidden", !account);
    $("#logoutButton").classList.toggle("hidden", !account);
    $("#saveButton").disabled = !account || !state.started || state.gameOver;
  }

  function openAccountPanel(requireLogin = false) {
    if (state.started && !state.gameOver) {
      saveRun(false);
      state.accountWasPaused = state.paused;
      state.paused = true;
      syncPauseUI();
    }
    const remembered = state.accountStore.currentId;
    state.pendingAccountId = state.accountStore.accounts.some((account) => account.id === remembered) ? remembered : state.accountStore.accounts[0]?.id || null;
    renderProfiles(); updateAccountUI();
    $("#loginPin").value = ""; $("#loginMessage").textContent = ""; $("#createAccountMessage").textContent = "";
    $("#accountClose").classList.toggle("hidden", requireLogin || !state.authenticated);
    $("#accountOverlay").classList.add("show");
  }

  function closeAccountPanel() {
    if (!state.authenticated) return;
    $("#accountOverlay").classList.remove("show");
    if (state.started && !state.gameOver && !state.drafting) state.paused = state.accountWasPaused;
    syncPauseUI();
  }

  async function loginSelectedAccount() {
    const account = state.accountStore.accounts.find((item) => item.id === state.pendingAccountId);
    const pin = $("#loginPin").value.trim();
    if (!account || !/^\d{4}$/.test(pin)) { $("#loginMessage").textContent = "请输入 4 位数字口令。"; return; }
    const digest = await hashPin(pin, account.id);
    if (digest !== account.pinHash) { $("#loginMessage").textContent = "口令不正确，请重试。"; playSound("damage"); return; }
    state.authenticated = true;
    state.accountStore.currentId = account.id;
    account.lastLoginAt = Date.now();
    account.best ||= { wave: 0, score: 0 };
    state.best = { ...account.best };
    persistAccountStore();
    $("#accountOverlay").classList.remove("show");
    updateAccountUI(); saveBest(); showStartScreen(); playSound("card");
  }

  async function createAccount(event) {
    event.preventDefault();
    const name = $("#newAccountName").value.trim();
    const pin = $("#newAccountPin").value.trim();
    if (name.length < 2 || name.length > 12) { $("#createAccountMessage").textContent = "名称需要 2–12 个字符。"; return; }
    if (!/^\d{4}$/.test(pin)) { $("#createAccountMessage").textContent = "口令必须是 4 位数字。"; return; }
    if (state.accountStore.accounts.some((account) => account.name.toLowerCase() === name.toLowerCase())) { $("#createAccountMessage").textContent = "这个名称已存在。"; return; }
    const id = `acct-${Date.now().toString(36)}-${Math.random().toString(36).slice(2, 8)}`;
    const account = { id, name, pinHash: await hashPin(pin, id), createdAt: Date.now(), lastLoginAt: Date.now(), lastPlayedAt: null, best: { wave: 0, score: 0 }, run: null };
    state.accountStore.accounts.push(account);
    state.accountStore.currentId = id;
    state.pendingAccountId = id;
    state.authenticated = true;
    state.best = { wave: 0, score: 0 };
    persistAccountStore();
    $("#createAccountForm").reset();
    $("#accountOverlay").classList.remove("show");
    updateAccountUI(); saveBest(); showStartScreen(); playSound("start");
  }

  function logoutAccount() {
    if (state.started && !state.gameOver) saveRun(false);
    state.authenticated = false;
    state.started = false;
    state.paused = true;
    state.drafting = false;
    $("#startOverlay").classList.remove("show");
    $("#cardOverlay").classList.remove("show");
    $("#resultOverlay").classList.remove("show");
    updateAccountUI(); syncPauseUI(); openAccountPanel(true);
  }

  function serializeEnemy(enemy) {
    const { type, dead, hitFlash, ...saved } = enemy;
    return saved;
  }

  function serializeRun() {
    return {
      version: 1, savedAt: Date.now(), wave: state.wave, waveTarget: state.waveTarget, waveSpawned: state.waveSpawned, waveResolved: state.waveResolved,
      spawnTimer: state.spawnTimer, waveEnding: state.waveEnding, waveEndTimer: state.waveEndTimer, startDelay: state.startDelay,
      drafting: state.drafting, elapsed: state.elapsed, score: state.score, kills: state.kills, chain: state.chain, chainTimer: state.chainTimer,
      coreHp: state.coreHp, shield: state.shield, protocol: state.protocol, cards: [...state.cards.entries()],
      enemies: state.enemies.filter((enemy) => !enemy.dead).map(serializeEnemy),
      turrets: state.turrets.map(({ id, cooldown, shotCount, recoil, pulse }) => ({ id, cooldown, shotCount, recoil, pulse })),
      focus: state.focus ? { ...state.focus } : null, focusCooldown: state.focusCooldown, overdrive: state.overdrive, overdriveTime: state.overdriveTime,
      staticTimer: state.staticTimer, arcCount: state.arcCount, phoenixKills: state.phoenixKills, nextEnemyId: state.nextEnemyId, nextProjectileId: state.nextProjectileId
    };
  }

  function saveRun(manual = false) {
    const account = activeAccount();
    if (!account || !state.started || state.gameOver) return false;
    account.run = serializeRun();
    account.lastPlayedAt = Date.now();
    if (state.wave > (account.best?.wave || 0) || state.score > (account.best?.score || 0)) account.best = { wave: Math.max(account.best?.wave || 0, state.wave), score: Math.max(account.best?.score || 0, state.score) };
    persistAccountStore();
    if (manual) { showToast(`已保存 · 第 ${state.wave} 波 · ${formatTime(state.elapsed)}`); playSound("card"); }
    renderResumePanel(); updateAccountUI();
    return true;
  }

  function loadRun() {
    const account = activeAccount(), run = account?.run;
    if (!run || run.version !== 1 || !CARD_MAP[run.protocol]) { showToast("没有可加载的有效存档"); return; }
    Object.assign(state, {
      started: true, paused: false, drafting: false, gameOver: false, wave: run.wave, waveTarget: run.waveTarget, waveSpawned: run.waveSpawned, waveResolved: run.waveResolved,
      spawnTimer: run.spawnTimer, waveEnding: !!run.waveEnding, waveEndTimer: run.waveEndTimer || 0, startDelay: run.startDelay || 0,
      elapsed: run.elapsed || 0, score: run.score || 0, kills: run.kills || 0, chain: run.chain || 0, chainTimer: run.chainTimer || 0,
      coreHp: run.coreHp ?? 100, shield: run.shield || 0, protocol: run.protocol, cards: new Map(run.cards || []),
      enemies: (run.enemies || []).map((enemy) => ({ ...enemy, type: ENEMY_TYPES[enemy.typeId], dead: false, hitFlash: 0 })),
      projectiles: [], particles: [], floaters: [], lightning: [], shockwaves: [], focus: run.focus ? { ...run.focus } : null,
      focusCooldown: run.focusCooldown || 0, overdrive: run.overdrive || 0, overdriveTime: run.overdriveTime || 0, staticTimer: run.staticTimer || 0,
      arcCount: run.arcCount || 0, phoenixKills: run.phoenixKills || 0, nextEnemyId: run.nextEnemyId || 1, nextProjectileId: run.nextProjectileId || 1,
      saveAccumulator: 0, shake: 0, flash: 0
    });
    state.turrets = TURRET_DATA.map((turret, index) => ({ ...turret, id: index, cooldown: run.turrets?.[index]?.cooldown ?? .1 + index * .09, shotCount: run.turrets?.[index]?.shotCount || 0, recoil: 0, pulse: run.turrets?.[index]?.pulse || Math.random() * TAU }));
    rebuildTags();
    $("#startOverlay").classList.remove("show"); $("#resultOverlay").classList.remove("show"); $("#cardOverlay").classList.remove("show");
    updateBuildUI(); updateUI(true); updateAccountUI(); syncPauseUI();
    if (run.drafting) showDraft();
    else { $("#phaseText").textContent = state.waveEnding ? "本波已肃清" : "存档已恢复"; $("#phaseDetail").textContent = `第 ${state.wave} 波 · 继续上次记录`; showToast(`已加载第 ${state.wave} 波存档`); }
    playSound("start");
  }

  function discardRun() {
    const account = activeAccount();
    if (account) { account.run = null; persistAccountStore(); }
    renderStartChoice(); showToast("上次记录已放弃，可以选择新武装");
  }

  function renderResumePanel() {
    const account = activeAccount(), run = account?.run;
    if (!account || !run) return;
    $("#resumeAccountName").textContent = account.name;
    $("#resumeWave").textContent = String(run.wave || 1).padStart(2, "0");
    $("#resumeTime").textContent = formatTime(run.elapsed || 0);
    $("#resumeScore").textContent = (run.score || 0).toLocaleString();
    $("#resumeCards").textContent = (run.cards || []).reduce((sum, card) => sum + Number(card[1] || 0), 0);
    const counts = {};
    (run.cards || []).forEach(([id, rank]) => CARD_MAP[id]?.tags.forEach((tag) => { counts[tag] = (counts[tag] || 0) + rank; }));
    $("#resumeBuild").innerHTML = Object.entries(counts).sort((a, b) => b[1] - a[1]).map(([tag, count]) => `<span class="build-tag" data-tag="${tag}">${tag}<b>×${count}</b></span>`).join("");
    $("#resumeSavedAt").textContent = `最后保存：${new Date(run.savedAt).toLocaleString("zh-CN", { hour12: false })}`;
  }

  function renderStartChoice() {
    const hasRun = !!activeAccount()?.run;
    $("#resumePanel").classList.toggle("hidden", !hasRun);
    $("#protocolSelect").classList.toggle("hidden", hasRun);
    if (hasRun) renderResumePanel();
  }

  function showStartScreen() {
    if (!state.authenticated) { openAccountPanel(true); return; }
    state.started = false; state.paused = true; state.drafting = false;
    $("#cardOverlay").classList.remove("show"); $("#resultOverlay").classList.remove("show");
    renderStartChoice(); $("#startOverlay").classList.add("show"); updateAccountUI(); syncPauseUI();
  }

  function resetGame(protocol) {
    if (!state.authenticated) { openAccountPanel(true); return; }
    const account = activeAccount(); if (account) account.run = null;
    Object.assign(state, { started: true, paused: false, drafting: false, gameOver: false, wave: 0, waveTarget: 0, waveSpawned: 0, waveResolved: 0, waveEnding: false, elapsed: 0, score: 0, kills: 0, chain: 0, chainTimer: 0, coreHp: 100, shield: 0, protocol, cards: new Map(), tagCounts: {}, enemies: [], projectiles: [], particles: [], floaters: [], lightning: [], shockwaves: [], focus: null, focusCooldown: 0, overdrive: 0, overdriveTime: 0, staticTimer: 0, arcCount: 0, phoenixKills: 0, nextEnemyId: 1, nextProjectileId: 1, rerolled: false, shake: 0, flash: 0 });
    state.turrets = TURRET_DATA.map((turret, index) => ({ ...turret, id: index, cooldown: .1 + index * .09, shotCount: 0, recoil: 0, pulse: Math.random() * TAU }));
    addCard(protocol, true);
    $("#startOverlay").classList.remove("show"); $("#resultOverlay").classList.remove("show");
    startNextWave(); updateBuildUI(); updateUI(true); updateAccountUI(); syncPauseUI(); saveRun(false); playSound("start");
  }

  function addCard(id, silent = false) {
    const card = CARD_MAP[id]; if (!card) return;
    const rank = Math.min(card.max, cardRank(id) + 1); state.cards.set(id, rank); rebuildTags();
    if (card.combo && !silent) showCombo(card);
    if (!silent) { showToast(`${card.name} · ${rank >= card.max ? "已完成" : `等级 ${rank}`}`); playSound(card.combo ? "combo" : "card"); }
  }
  function rebuildTags() {
    state.tagCounts = {};
    for (const [id, rank] of state.cards) CARD_MAP[id].tags.forEach((tag) => { state.tagCounts[tag] = (state.tagCounts[tag] || 0) + rank; });
  }
  function cardEligible(card) {
    if (cardRank(card.id) >= card.max || (card.minWave || 0) > state.wave) return false;
    if (card.req && !card.req.every(hasCard)) return false;
    return !(card.reqRank && cardRank(card.reqRank[0]) < card.reqRank[1]);
  }
  function offerScore(card) {
    let score = Math.random() * 2; const rank = cardRank(card.id);
    if (rank) score += 5.2 + rank * .7;
    card.tags.forEach((tag) => { score += Math.min(4, (state.tagCounts[tag] || 0) * .75); });
    if (card.combo) score += 7; if (card.rarity === "传说") score -= 1;
    return score;
  }
  function generateOffers() {
    const eligible = CARDS.filter(cardEligible);
    const scored = eligible.map((card) => ({ card, score: offerScore(card) })).sort((a, b) => b.score - a.score);
    const offers = [];
    if (scored[0]) offers.push(scored[0].card);
    const relevant = scored.slice(1, 8).filter((item) => !offers.includes(item.card));
    if (relevant.length) offers.push(relevant[Math.floor(Math.random() * Math.min(4, relevant.length))].card);
    const discovery = eligible.filter((card) => !offers.includes(card) && !cardRank(card.id));
    const pool = discovery.length ? discovery : eligible.filter((card) => !offers.includes(card));
    if (pool.length) offers.push(pool[Math.floor(Math.random() * pool.length)]);
    for (const item of scored) { if (offers.length >= 3) break; if (!offers.includes(item.card)) offers.push(item.card); }
    state.currentOffers = offers.slice(0, 3); renderDraft();
  }
  function renderDraft() {
    $("#cardChoices").innerHTML = state.currentOffers.map((card) => {
      const current = cardRank(card.id), color = CARD_COLORS[card.tags[0]] || COLORS.cyan, recommended = card.combo || current > 0;
      return `<button class="draft-card ${recommended ? "recommended" : ""}" data-card="${card.id}" style="--card-color:${color}" type="button"><span class="card-top"><i class="rarity">${card.rarity.toUpperCase()}</i><i class="rank">${current ? `LV.${current} → ${current + 1}` : "NEW"}${card.max > 1 ? ` / ${card.max}` : ""}</i></span><span class="card-glyph">${card.glyph}</span><span class="card-body"><h3>${card.name}</h3><span class="card-tags">${card.tags.map((tag) => `<i>${tag}</i>`).join("")}</span><p>${card.desc(current)}</p><span class="synergy-note"><b>${card.combo ? "组合已就绪" : current ? "延续构筑" : "可能性"}</b> · ${card.note}</span></span></button>`;
    }).join("");
    $$(".draft-card").forEach((button) => button.addEventListener("click", () => chooseCard(button.dataset.card)));
    const comboOffer = state.currentOffers.find((card) => card.combo);
    $("#draftComboHint").textContent = comboOffer ? `可立即点亮「${comboOffer.name}」` : "至少一张卡会延续当前构筑";
  }
  function chooseCard(id) {
    if (!state.drafting) return; addCard(id); state.drafting = false; state.paused = false;
    $("#cardOverlay").classList.remove("show"); repairAfterWave(); startNextWave(); updateBuildUI(); syncPauseUI();
  }
  function repairAfterWave() {
    const rank = cardRank("repair"); if (!rank) return; const amount = 1 + rank * 2;
    if (state.coreHp < state.coreMax) { const healed = Math.min(amount, state.coreMax - state.coreHp); state.coreHp += healed; addFloater(640, 594, `+${healed} 屏障`, COLORS.green, 1.5); }
    else state.shield = Math.min(24, state.shield + amount * .7);
  }
  function showDraft() {
    if (state.gameOver) return; state.drafting = true; state.paused = true; state.rerolled = false;
    $("#clearedWave").textContent = state.wave;
    const tags = Object.entries(state.tagCounts).sort((a, b) => b[1] - a[1]).slice(0, 2).map(([tag]) => tag);
    $("#draftReason").textContent = tags.length ? `牌池正在追踪：${tags.join(" × ")} · 相关组件已提高权重` : "牌池已根据初始武装完成校准";
    $("#rerollButton").disabled = false; generateOffers(); $("#cardOverlay").classList.add("show"); syncPauseUI(); saveRun(false); playSound("wave");
  }

  function startNextWave() {
    state.wave += 1; const risk = hasCard("singularity") ? 1.12 : 1;
    state.waveTarget = Math.floor((10 + state.wave * 3.1 + Math.pow(state.wave, 1.13)) * risk);
    if (state.wave % 10 === 0) state.waveTarget += 1; else if (state.wave % 5 === 0) state.waveTarget += 2;
    Object.assign(state, { waveSpawned: 0, waveResolved: 0, spawnTimer: .45, startDelay: 1.1, waveEnding: false, waveEndTimer: 0 });
    $("#phaseText").textContent = state.wave % 10 === 0 ? "首领信号锁定" : state.wave % 5 === 0 ? "精英星潮逼近" : "星潮正在聚集";
    $("#phaseDetail").textContent = `第 ${state.wave} 波 · 防线全炮位就绪`; updateUI(true); saveRun(false);
  }
  function waveBaseHp() { return 43 * Math.pow(1.145, state.wave - 1) * (1 + Math.max(0, state.wave - 18) * .018); }
  function pickEnemyType(index) {
    if (state.wave % 10 === 0 && index === state.waveTarget - 1) return "boss";
    if (state.wave % 5 === 0 && index >= state.waveTarget - 2) return "elite";
    const roll = Math.random();
    if (state.wave >= 8 && roll < .1) return "splitter";
    if (state.wave >= 6 && roll < .22) return "shield";
    if (state.wave >= 4 && roll < .36) return "tank";
    if (state.wave >= 2 && roll < .58) return "runner";
    return "swarm";
  }
  function spawnEnemy(typeId = null, x = null, y = -35, hpScale = 1, bonus = false) {
    const id = typeId || pickEnemyType(state.waveSpawned), type = ENEMY_TYPES[id];
    const maxHp = waveBaseHp() * type.hp * (type.elite ? 1 + state.wave * .035 : 1) * hpScale;
    const posX = x ?? 62 + Math.random() * (W - 124);
    state.enemies.push({ id: state.nextEnemyId++, typeId: id, type, x: posX, y, hp: maxHp, maxHp, bonus, speed: (39 + Math.min(27, state.wave * .72)) * type.speed, drift: (Math.random() - .5) * 12, sway: 8 + Math.random() * 23, phase: Math.random() * TAU, slow: 0, slowPower: 0, burn: 0, burnDps: 0, freeze: 0, thermalDone: false, shield: type.shield ? maxHp * type.shield : 0, dead: false, hitFlash: 0 });
  }

  function getStats() {
    const caliber = cardRank("caliber"), rapid = cardRank("rapid"), twin = cardRank("twin"), crit = cardRank("crit");
    const singularity = hasCard("singularity") ? 1.22 : 1;
    const overdrive = state.overdriveTime > 0 ? 1 + (.72 + Math.max(0, cardRank("overdrive") - 1) * .12) : 1;
    const damageGrowth = 1 + caliber * .24 + caliber * Math.max(0, caliber - 1) * .015;
    const rateGrowth = 1 + rapid * .18 + rapid * Math.max(0, rapid - 1) * .01;
    const critGrowth = crit * .08 + crit * Math.max(0, crit - 1) * .015;
    return { damage: 18 * damageGrowth * singularity * overdrive, rate: 1.42 * rateGrowth * singularity * overdrive, projectiles: 1 + twin, projectileScale: twin ? (twin > 1 ? .78 : .74) : 1, crit: .06 + critGrowth, critDamage: 1.9, pierce: cardRank("pierce") };
  }

  function update(dt) {
    if (!state.started || state.paused || state.gameOver) return;
    const scaled = Math.min(dt, .05) * state.speed; state.elapsed += scaled;
    state.saveAccumulator += scaled;
    if (state.saveAccumulator >= 8) { state.saveAccumulator = 0; saveRun(false); }
    state.chainTimer = Math.max(0, state.chainTimer - scaled); if (!state.chainTimer) state.chain = 0;
    state.focusCooldown = Math.max(0, state.focusCooldown - scaled); state.overdriveTime = Math.max(0, state.overdriveTime - scaled);
    state.shake = Math.max(0, state.shake - scaled * 16); state.flash = Math.max(0, state.flash - scaled * 3); state.bannerTimer = Math.max(0, state.bannerTimer - scaled);
    if (!state.bannerTimer) $("#comboBanner").classList.remove("show");
    if (state.focus) { state.focus.life -= scaled; state.focus.pulse += scaled * 4; if (state.focus.life <= 0) state.focus = null; }
    if (state.startDelay > 0) state.startDelay -= scaled; else updateSpawns(scaled);
    updateEnemies(scaled); updateTurrets(scaled); updateProjectiles(scaled); updateEffects(scaled);
    if (cardRank("static") && state.focus) { state.staticTimer -= scaled; if (state.staticTimer <= 0) { state.staticTimer = 1.45 - (cardRank("static") - 1) * .2; staticStrike(); } }
    if (!state.waveEnding && state.waveSpawned >= state.waveTarget && state.enemies.length === 0) { state.waveEnding = true; state.waveEndTimer = .72; $("#phaseText").textContent = "本波已肃清"; $("#phaseDetail").textContent = "正在校准下一次进化"; }
    if (state.waveEnding) { state.waveEndTimer -= scaled; if (state.waveEndTimer <= 0) { state.waveEnding = false; showDraft(); } }
  }
  function updateSpawns(dt) {
    if (state.waveEnding || state.waveSpawned >= state.waveTarget) return;
    state.spawnTimer -= dt;
    if (state.spawnTimer <= 0) {
      const type = pickEnemyType(state.waveSpawned); spawnEnemy(type); state.waveSpawned += 1;
      state.spawnTimer = Math.max(.14, .58 - state.wave * .012) * (.72 + Math.random() * .56);
      if (type === "boss") { showToast("主宰级信号穿过大气层"); playSound("boss"); state.shake = 7; }
    }
  }
  function updateEnemies(dt) {
    for (let i = state.enemies.length - 1; i >= 0; i--) {
      const enemy = state.enemies[i]; enemy.hitFlash = Math.max(0, enemy.hitFlash - dt * 7); enemy.slow = Math.max(0, enemy.slow - dt); enemy.freeze = Math.max(0, enemy.freeze - dt);
      if (enemy.burn > 0) { enemy.burn -= dt; damageEnemy(enemy, enemy.burnDps * dt, { dot: true, fire: true }); if (enemy.dead) continue; }
      const factor = enemy.freeze > 0 ? 0 : enemy.slow > 0 ? Math.max(.28, 1 - enemy.slowPower) : 1;
      enemy.y += enemy.speed * factor * dt; enemy.phase += dt; enemy.x += enemy.drift * dt + Math.sin(enemy.phase * 1.9) * enemy.sway * dt * .35;
      enemy.x = Math.max(30, Math.min(W - 30, enemy.x));
      if (enemy.y >= LINE_Y) reachLine(enemy);
    }
  }
  function reachLine(enemy) {
    if (enemy.dead) return; enemy.dead = true; let damage = enemy.type.damage + Math.floor(state.wave / 12);
    if (state.shield > 0) { const absorbed = Math.min(state.shield, damage); state.shield -= absorbed; damage -= absorbed; }
    state.coreHp = Math.max(0, state.coreHp - damage); if (!enemy.bonus) state.waveResolved += 1; removeEnemy(enemy);
    createBurst(enemy.x, LINE_Y, COLORS.danger, 16, 1.4); addShockwave(enemy.x, LINE_Y, COLORS.danger, 70); addFloater(enemy.x, LINE_Y - 32, `-${damage}`, COLORS.danger, 1.2);
    state.shake = Math.max(state.shake, enemy.type.boss ? 15 : 7); state.flash = .5; playSound("damage"); if (state.coreHp <= 0) endGame();
  }

  function selectTarget() {
    const alive = state.enemies.filter((enemy) => !enemy.dead); if (!alive.length) return null;
    if (state.focus) {
      const focused = alive.filter((enemy) => Math.hypot(enemy.x - state.focus.x, enemy.y - state.focus.y) < 150).sort((a, b) => b.y - a.y);
      if (focused.length) return focused[0];
    }
    return alive.sort((a, b) => b.y - a.y)[0];
  }
  function updateTurrets(dt) {
    const stats = getStats();
    for (const turret of state.turrets) {
      turret.recoil = Math.max(0, turret.recoil - dt * 8); turret.pulse += dt * (state.overdriveTime > 0 ? 5 : 1.5); turret.cooldown -= dt * stats.rate * turret.rate;
      if (turret.cooldown <= 0) { const target = selectTarget(); if (target) { fireTurret(turret, target, stats); turret.cooldown += 1; } else turret.cooldown = Math.max(turret.cooldown, -.2); }
    }
  }
  function fireTurret(turret, primary, stats) {
    turret.shotCount += 1; turret.recoil = 1;
    const candidates = state.enemies.filter((enemy) => !enemy.dead).sort((a, b) => b.y - a.y);
    const echo = hasCard("echo") && state.overdriveTime > 0 && turret.shotCount % (5 - (cardRank("echo") - 1)) === 0;
    const count = stats.projectiles + (echo ? 1 : 0);
    for (let i = 0; i < count; i++) {
      const target = i ? (candidates[i % Math.min(candidates.length, count)] || primary) : primary;
      const critBonus = target.slow > 0 ? cardRank("brittle") * .18 + Math.max(0, cardRank("brittle") - 1) * .08 : 0;
      const critical = Math.random() < stats.crit + critBonus;
      let damage = stats.damage * stats.projectileScale * turret.damage; if (critical) damage *= stats.critDamage;
      state.projectiles.push({ id: state.nextProjectileId++, x: turret.x, y: turret.y - 23 * turret.scale, px: turret.x, py: turret.y, targetId: target.id, speed: 560, damage, critical, pierce: stats.pierce, hitIds: new Set(), life: 1.5, color: projectileColor() });
    }
    createBurst(turret.x, turret.y - 25 * turret.scale, projectileColor(), 3, .45); if (Math.random() < .14) playSound("shot");
  }
  function projectileColor() {
    if (state.protocol === "arc") return COLORS.violet; if (state.protocol === "frost") return COLORS.frost; if (state.protocol === "burn") return COLORS.fire; return COLORS.cyan;
  }
  function updateProjectiles(dt) {
    for (let i = state.projectiles.length - 1; i >= 0; i--) {
      const p = state.projectiles[i]; p.life -= dt; if (p.life <= 0) { state.projectiles.splice(i, 1); continue; }
      let target = state.enemies.find((enemy) => enemy.id === p.targetId && !enemy.dead && !p.hitIds.has(enemy.id));
      if (!target) target = nearestEnemy(p.x, p.y, 170, p.hitIds); if (!target) { state.projectiles.splice(i, 1); continue; }
      p.targetId = target.id; p.px = p.x; p.py = p.y; const dx = target.x - p.x, dy = target.y - p.y, dist = Math.hypot(dx, dy) || 1, move = Math.min(dist, p.speed * dt);
      p.x += dx / dist * move; p.y += dy / dist * move;
      if (dist <= target.type.radius + 7) {
        hitEnemy(p, target); p.hitIds.add(target.id);
        if (p.pierce > 0) { p.pierce -= 1; p.damage *= .72; const next = nearestEnemy(p.x, p.y, 170, p.hitIds); if (next) p.targetId = next.id; else state.projectiles.splice(i, 1); }
        else state.projectiles.splice(i, 1);
      }
    }
  }
  function nearestEnemy(x, y, range, excluded = new Set()) { return state.enemies.filter((enemy) => !enemy.dead && !excluded.has(enemy.id) && Math.hypot(enemy.x - x, enemy.y - y) <= range).sort((a, b) => b.y - a.y)[0] || null; }
  function hitEnemy(projectile, enemy) {
    if (hasCard("frost")) { const rank = cardRank("frost"); enemy.slow = Math.max(enemy.slow, 1.8 + (rank - 1) * .35); enemy.slowPower = Math.max(enemy.slowPower, .24 + (rank - 1) * .05); }
    if (hasCard("burn")) { const rank = cardRank("burn"); enemy.burn = Math.max(enemy.burn, 3 + (rank - 1) * .5); enemy.burnDps = Math.max(enemy.burnDps, getStats().damage * (.34 + (rank - 1) * .1)); }
    if (hasCard("thermal") && enemy.slow > 0 && enemy.burn > 0 && !enemy.thermalDone) { enemy.thermalDone = true; damageEnemy(enemy, enemy.maxHp * (enemy.type.boss ? .055 : .12), { combo: true, color: COLORS.gold }); addFloater(enemy.x, enemy.y - 24, "热震", COLORS.gold, .8); addShockwave(enemy.x, enemy.y, COLORS.gold, 38); }
    damageEnemy(enemy, projectile.damage, { critical: projectile.critical, projectile: true, color: projectile.color });
    if (!enemy.dead) tryExecute(enemy); if (!enemy.dead) tryArc(enemy, projectile.damage);
  }
  function tryExecute(enemy) {
    const rank = cardRank("execute"); if (!rank || enemy.burn <= 0) return;
    const threshold = (.15 + (rank - 1) * .07) * (enemy.type.boss ? .5 : 1);
    if (enemy.hp / enemy.maxHp <= threshold) { addFloater(enemy.x, enemy.y - 24, "处决", COLORS.fire, .8); damageEnemy(enemy, enemy.hp + 1, { execute: true, fire: true }); }
  }
  function tryArc(enemy, baseDamage) {
    const rank = cardRank("arc"), chance = rank ? .22 + (rank - 1) * .07 : 0; if (!chance || Math.random() >= chance) return;
    const jumps = 2 + Math.floor(Math.max(0, rank - 1) / 2), range = 145 + cardRank("voltage") * 24;
    const amount = baseDamage * .48 * (1 + cardRank("voltage") * .32 + Math.max(0, cardRank("voltage") - 1) * .14);
    const targets = state.enemies.filter((other) => !other.dead && other.id !== enemy.id && Math.hypot(other.x - enemy.x, other.y - enemy.y) <= range).sort((a, b) => Math.hypot(a.x - enemy.x, a.y - enemy.y) - Math.hypot(b.x - enemy.x, b.y - enemy.y)).slice(0, jumps);
    let from = enemy;
    targets.forEach((target) => { let damage = amount;
      if (hasCard("superconduct")) { if (target.slow > 0) damage *= 1.75; target.slow = Math.max(target.slow, 1.65); target.slowPower = Math.max(target.slowPower, .25); }
      if (hasCard("plasma") && target.burn > 0) { damage += target.burnDps * target.burn * .6; target.burn *= .35; addFloater(target.x, target.y - 22, "等离子", COLORS.fire, .7); }
      addLightning(from.x, from.y, target.x, target.y, hasCard("superconduct") ? COLORS.frost : COLORS.violet); damageEnemy(target, damage, { arc: true, combo: hasCard("superconduct") || hasCard("plasma") }); from = target;
    });
    state.arcCount += 1; if (hasCard("storm") && state.arcCount >= 9) { state.arcCount = 0; triggerStorm(); }
  }
  function staticStrike() {
    if (!state.focus) return; const targets = state.enemies.filter((e) => !e.dead && Math.hypot(e.x - state.focus.x, e.y - state.focus.y) < 160).sort((a, b) => b.y - a.y).slice(0, 6);
    targets.forEach((enemy) => { addLightning(state.focus.x, state.focus.y, enemy.x, enemy.y, COLORS.violet); damageEnemy(enemy, getStats().damage * (.72 + cardRank("static") * .23), { arc: true }); });
  }
  function triggerStorm() {
    [...state.enemies].filter((e) => !e.dead).sort(() => Math.random() - .5).slice(0, 7).forEach((enemy, index) => { addLightning(enemy.x + (Math.random() - .5) * 35, -15, enemy.x, enemy.y, COLORS.violet, .22 + index * .015); damageEnemy(enemy, getStats().damage * 1.35, { arc: true, combo: true }); });
    showToast("雷暴核心 · 全域轰击"); state.flash = .32; state.shake = Math.max(state.shake, 5);
  }

  function damageEnemy(enemy, damage, meta = {}) {
    if (!enemy || enemy.dead || damage <= 0) return;
    if (enemy.shield > 0) { const absorbed = Math.min(enemy.shield, damage); enemy.shield -= absorbed; damage -= absorbed; }
    if (damage <= 0) { enemy.hitFlash = 1; return; }
    enemy.hp -= damage; enemy.hitFlash = 1;
    if (!meta.dot && (meta.critical || damage > enemy.maxHp * .12)) addFloater(enemy.x, enemy.y - enemy.type.radius - 7, `${meta.critical ? "暴击 " : ""}${Math.round(damage)}`, meta.color || (meta.critical ? COLORS.gold : COLORS.ink), meta.critical ? .85 : .55);
    if (meta.critical && hasCard("absolute") && enemy.slow > 0) { enemy.freeze = Math.max(enemy.freeze, .75); addFloater(enemy.x, enemy.y - 28, "冻结", COLORS.frost, .7); }
    if (enemy.hp <= 0) killEnemy(enemy, meta);
  }
  function killEnemy(enemy, meta = {}) {
    if (enemy.dead) return; enemy.dead = true; const hadFrost = enemy.slow > 0 || enemy.freeze > 0, hadBurn = enemy.burn > 0, burnDps = enemy.burnDps;
    state.kills += 1; if (!enemy.bonus) state.waveResolved += 1; state.chain += 1; state.chainTimer = 1.35;
    state.score += Math.round(enemy.type.score * (1 + state.wave * .045) * (1 + Math.min(2, Math.floor(state.chain / 25) * .12)));
    const chargeGain = (1.15 + enemy.type.score * .018) * (1 + cardRank("recycle") * .2 + Math.max(0, cardRank("recycle") - 1) * .15); state.overdrive = Math.min(100, state.overdrive + chargeGain);
    state.shake = Math.max(state.shake, enemy.type.boss ? 13 : enemy.type.elite ? 6 : meta.critical ? 2.5 : 0); createBurst(enemy.x, enemy.y, enemy.type.color, enemy.type.boss ? 34 : enemy.type.elite ? 20 : 9, enemy.type.boss ? 2 : 1);
    if (enemy.type.elite || enemy.type.boss) addShockwave(enemy.x, enemy.y, enemy.type.color, enemy.type.boss ? 130 : 70);
    if (enemy.type.split && !enemy.type.boss) for (let i = 0; i < 2; i++) spawnEnemy("runner", enemy.x + (i ? 12 : -12), enemy.y - 10, .34, true);
    if (hasCard("shatter") && hadFrost) {
      const rank = cardRank("shatter"), radius = 76 + rank * 8, amount = enemy.maxHp * (.08 + (rank - 1) * .03) * (hasCard("absolute") ? 2 : 1);
      state.enemies.filter((other) => !other.dead && Math.hypot(other.x - enemy.x, other.y - enemy.y) < radius).forEach((other) => damageEnemy(other, Math.min(amount, other.maxHp * .3), { combo: true, color: COLORS.frost })); addShockwave(enemy.x, enemy.y, COLORS.frost, radius);
    }
    if (hasCard("wildfire") && hadBurn) state.enemies.filter((other) => !other.dead && Math.hypot(other.x - enemy.x, other.y - enemy.y) < 140).sort((a, b) => Math.hypot(a.x - enemy.x, a.y - enemy.y) - Math.hypot(b.x - enemy.x, b.y - enemy.y)).slice(0, 2 + cardRank("wildfire") - 1).forEach((other) => { other.burn = Math.max(other.burn, 2.8); other.burnDps = Math.max(other.burnDps, burnDps * .8); addLightning(enemy.x, enemy.y, other.x, other.y, COLORS.fire, .18); });
    if (hasCard("phoenix") && (meta.fire || hadBurn)) { state.phoenixKills += 1; if (state.phoenixKills >= 60) { state.phoenixKills = 0; triggerPhoenix(); } }
    removeEnemy(enemy);
  }
  function triggerPhoenix() {
    state.coreHp = Math.min(state.coreMax, state.coreHp + 4); state.enemies.forEach((enemy) => { enemy.burn = Math.max(enemy.burn, 4); enemy.burnDps = Math.max(enemy.burnDps, getStats().damage * .65); });
    for (let x = 90; x < W; x += 170) addLightning(x, LINE_Y, x + 25, 30, COLORS.fire, .45); showToast("余烬重生 · 屏障修复"); state.flash = .3;
  }
  function removeEnemy(enemy) { const index = state.enemies.indexOf(enemy); if (index >= 0) state.enemies.splice(index, 1); }

  function activateFocus(x, y) {
    if (!state.started || state.paused || state.focusCooldown > 0) { if (state.focusCooldown > 0) showToast(`集火标记还需 ${state.focusCooldown.toFixed(1)} 秒`); return; }
    state.focus = { x, y: Math.min(LINE_Y - 35, y), life: 5, pulse: 0 }; state.focusCooldown = 12; state.staticTimer = .15;
    addShockwave(x, Math.min(LINE_Y - 35, y), COLORS.cyan, 95); showToast("集火标记已部署 · 全炮位转向"); playSound("focus");
  }
  function activateOverdrive() {
    if (!state.started || state.paused || state.overdrive < 100 || state.overdriveTime > 0) return;
    state.overdrive = 0; state.overdriveTime = 7 + cardRank("overdrive") * .5; state.flash = .25; state.shake = 4;
    state.turrets.forEach((turret) => { turret.cooldown = Math.min(turret.cooldown, .08); }); showToast(`极限火力 · ${state.overdriveTime.toFixed(1)} 秒`); playSound("combo");
  }

  function updateEffects(dt) {
    for (let i = state.particles.length - 1; i >= 0; i--) { const p = state.particles[i]; p.life -= dt; p.x += p.vx * dt; p.y += p.vy * dt; p.vx *= .985; p.vy *= .985; if (p.life <= 0) state.particles.splice(i, 1); }
    for (let i = state.floaters.length - 1; i >= 0; i--) { const f = state.floaters[i]; f.life -= dt; f.y -= dt * 24; if (f.life <= 0) state.floaters.splice(i, 1); }
    for (let i = state.lightning.length - 1; i >= 0; i--) { state.lightning[i].life -= dt; if (state.lightning[i].life <= 0) state.lightning.splice(i, 1); }
    for (let i = state.shockwaves.length - 1; i >= 0; i--) { const s = state.shockwaves[i]; s.life -= dt; s.r += dt * s.speed; if (s.life <= 0) state.shockwaves.splice(i, 1); }
  }
  function createBurst(x, y, color, count = 8, power = 1) { for (let i = 0; i < count; i++) { const a = Math.random() * TAU, speed = (25 + Math.random() * 75) * power; state.particles.push({ x, y, vx: Math.cos(a) * speed, vy: Math.sin(a) * speed, life: .35 + Math.random() * .45, maxLife: .8, color, size: 1 + Math.random() * 2.8 * power }); } }
  function addFloater(x, y, text, color = COLORS.ink, life = .7) { state.floaters.push({ x, y, text, color, life, maxLife: life }); }
  function addShockwave(x, y, color, max = 55) { state.shockwaves.push({ x, y, color, r: 4, max, speed: max * 2.1, life: .48, maxLife: .48 }); }
  function addLightning(x1, y1, x2, y2, color = COLORS.violet, life = .2) { state.lightning.push({ x1, y1, x2, y2, color, life, maxLife: life, seed: Math.random() * 1000 }); }

  function draw(time) {
    ctx.save(); if (state.shake) ctx.translate((Math.random() - .5) * state.shake, (Math.random() - .5) * state.shake);
    drawBackground(time); drawSpawnField(time); drawBarrier(time); state.turrets.forEach((turret) => drawTurret(turret, time)); state.enemies.forEach((enemy) => drawEnemy(enemy, time)); drawProjectiles(); drawLightningFx(); drawEffects(); drawFocus(time); ctx.restore();
    if (state.flash > 0) { ctx.fillStyle = `rgba(255,105,130,${state.flash * .09})`; ctx.fillRect(0, 0, W, H); }
  }
  function drawBackground(time) {
    const gradient = ctx.createRadialGradient(640, 690, 30, 640, 360, 760); gradient.addColorStop(0, "#102d3e"); gradient.addColorStop(.42, "#091827"); gradient.addColorStop(1, "#040912"); ctx.fillStyle = gradient; ctx.fillRect(0, 0, W, H);
    ctx.strokeStyle = "rgba(110,180,210,.05)"; ctx.lineWidth = 1;
    for (let x = 0; x <= W; x += 64) { ctx.beginPath(); ctx.moveTo(x, 0); ctx.lineTo(x, H); ctx.stroke(); }
    for (let y = 0; y <= H; y += 64) { ctx.beginPath(); ctx.moveTo(0, y); ctx.lineTo(W, y); ctx.stroke(); }
    for (let i = 0; i < 80; i++) { const x = (i * 197.37) % W, y = (i * 83.91 + time * (.006 + (i % 3) * .002)) % H, alpha = .08 + (Math.sin(time * .001 + i) + 1) * .055; ctx.fillStyle = `rgba(190,235,255,${alpha})`; ctx.fillRect(x, y, i % 9 === 0 ? 2 : 1, i % 9 === 0 ? 4 : 2); }
    ctx.fillStyle = "rgba(120,175,198,.38)"; ctx.font = "9px Consolas"; ctx.fillText("LAST ATMOSPHERE / ALT 00", 22, 25); ctx.fillText(`THREAT ${String(state.wave).padStart(3, "0")}`, 1162, 25);
  }
  function drawSpawnField(time) {
    const y = 56; ctx.save(); ctx.strokeStyle = "rgba(255,86,118,.2)"; ctx.setLineDash([4, 11]); ctx.lineDashOffset = time * .02; ctx.beginPath(); ctx.moveTo(30, y); ctx.lineTo(W - 30, y); ctx.stroke(); ctx.setLineDash([]);
    for (let x = 85; x < W; x += 185) { ctx.fillStyle = "rgba(255,86,118,.35)"; ctx.beginPath(); ctx.arc(x, y, 2 + Math.sin(time * .003 + x) * .8, 0, TAU); ctx.fill(); } ctx.restore();
  }
  function drawBarrier(time) {
    ctx.fillStyle = "rgba(4,11,18,.92)"; ctx.fillRect(0, LINE_Y, W, H - LINE_Y);
    const hp = state.coreHp / state.coreMax;
    ctx.strokeStyle = hp > .35 ? "rgba(89,230,255,.65)" : "rgba(255,86,118,.8)"; ctx.shadowColor = hp > .35 ? COLORS.cyan : COLORS.danger; ctx.shadowBlur = 14; ctx.lineWidth = 2; ctx.beginPath(); ctx.moveTo(0, LINE_Y); ctx.lineTo(W, LINE_Y); ctx.stroke(); ctx.shadowBlur = 0;
    ctx.strokeStyle = "rgba(89,230,255,.18)"; ctx.setLineDash([3, 15]); ctx.lineDashOffset = -time * .03; ctx.beginPath(); ctx.moveTo(0, LINE_Y - 8); ctx.lineTo(W, LINE_Y - 8); ctx.stroke(); ctx.setLineDash([]);
    if (state.shield > 0) { ctx.strokeStyle = "rgba(105,240,189,.6)"; ctx.lineWidth = 4; ctx.beginPath(); ctx.moveTo(0, LINE_Y - 5); ctx.lineTo(W * Math.min(1, state.shield / 24), LINE_Y - 5); ctx.stroke(); }
  }
  function drawTurret(turret, time) {
    const color = projectileColor(), s = turret.scale, recoil = turret.recoil * 7 * s; ctx.save(); ctx.translate(turret.x, turret.y); if (state.overdriveTime > 0) { ctx.fillStyle = "rgba(255,209,122,.08)"; ctx.beginPath(); ctx.arc(0, -18 * s, 45 * s + Math.sin(turret.pulse) * 4, 0, TAU); ctx.fill(); }
    ctx.fillStyle = "#0a1927"; ctx.strokeStyle = "rgba(118,185,211,.5)"; ctx.lineWidth = 1.5; ctx.beginPath(); ctx.moveTo(-30*s,0); ctx.lineTo(-21*s,-25*s); ctx.lineTo(21*s,-25*s); ctx.lineTo(30*s,0); ctx.closePath(); ctx.fill(); ctx.stroke();
    ctx.translate(0, recoil); ctx.fillStyle = "#10283a"; ctx.strokeStyle = color; ctx.beginPath(); ctx.rect(-17*s,-43*s,34*s,25*s); ctx.fill(); ctx.stroke();
    ctx.fillStyle = color; ctx.shadowColor = color; ctx.shadowBlur = state.overdriveTime > 0 ? 18 : 8; ctx.fillRect(-5*s,-62*s,10*s,27*s); ctx.beginPath(); ctx.arc(0,-36*s,5*s,0,TAU); ctx.fill(); ctx.shadowBlur=0;
    if (turret.main) { ctx.strokeStyle = `${color}77`; ctx.beginPath(); ctx.arc(0,-35*s,26*s,0,TAU); ctx.stroke(); }
    ctx.restore();
  }
  function drawEnemy(enemy, time) {
    const r = enemy.type.radius; ctx.save(); ctx.translate(enemy.x, enemy.y); ctx.rotate(enemy.phase * .7);
    if (enemy.burn > 0) { ctx.fillStyle = "rgba(255,111,67,.14)"; ctx.beginPath(); ctx.arc(0, 0, r + 8 + Math.sin(time*.008+enemy.id)*2, 0, TAU); ctx.fill(); }
    if (enemy.slow > 0 || enemy.freeze > 0) { ctx.strokeStyle = enemy.freeze > 0 ? "rgba(210,250,255,.9)" : "rgba(166,239,255,.45)"; ctx.setLineDash([3,4]); ctx.beginPath(); ctx.arc(0,0,r+6,0,TAU); ctx.stroke(); ctx.setLineDash([]); }
    if (enemy.shield > 0) { ctx.strokeStyle = "rgba(107,188,255,.72)"; ctx.lineWidth=2; ctx.beginPath(); ctx.arc(0,0,r+6,0,TAU); ctx.stroke(); }
    ctx.fillStyle = enemy.hitFlash > 0 ? "#fff" : enemy.type.color; ctx.strokeStyle = enemy.type.boss || enemy.type.elite ? COLORS.gold : "rgba(255,255,255,.28)"; ctx.lineWidth = enemy.type.boss ? 3 : 1; ctx.shadowColor=enemy.type.color;ctx.shadowBlur=enemy.type.boss?20:7;
    if (enemy.type.boss) { ctx.beginPath(); for(let i=0;i<10;i++){const a=i*TAU/10,rr=i%2?r*.62:r,px=Math.cos(a)*rr,py=Math.sin(a)*rr;i?ctx.lineTo(px,py):ctx.moveTo(px,py);}ctx.closePath();ctx.fill();ctx.stroke(); }
    else if (enemy.typeId === "tank" || enemy.type.elite) { ctx.beginPath(); for(let i=0;i<6;i++){const a=i*TAU/6,px=Math.cos(a)*r,py=Math.sin(a)*r;i?ctx.lineTo(px,py):ctx.moveTo(px,py);}ctx.closePath();ctx.fill();ctx.stroke(); }
    else { ctx.beginPath(); ctx.rect(-r*.7,-r*.7,r*1.4,r*1.4);ctx.fill();ctx.stroke(); }
    ctx.shadowBlur=0;ctx.fillStyle="rgba(4,10,18,.7)";ctx.beginPath();ctx.arc(0,0,r*.34,0,TAU);ctx.fill();ctx.restore();
    if(enemy.hp<enemy.maxHp||enemy.type.elite||enemy.type.boss){const width=enemy.type.boss?74:enemy.type.elite?52:28;ctx.fillStyle="rgba(2,6,10,.8)";ctx.fillRect(enemy.x-width/2,enemy.y-r-13,width,4);ctx.fillStyle=enemy.type.boss?COLORS.danger:enemy.type.color;ctx.fillRect(enemy.x-width/2,enemy.y-r-13,width*Math.max(0,enemy.hp/enemy.maxHp),4);}
  }
  function drawProjectiles() { state.projectiles.forEach((p)=>{ctx.strokeStyle=p.color;ctx.globalAlpha=.45;ctx.lineWidth=p.critical?3:1.5;ctx.beginPath();ctx.moveTo(p.px,p.py);ctx.lineTo(p.x,p.y);ctx.stroke();ctx.globalAlpha=1;ctx.fillStyle=p.critical?COLORS.gold:p.color;ctx.shadowColor=ctx.fillStyle;ctx.shadowBlur=p.critical?13:7;ctx.beginPath();ctx.arc(p.x,p.y,p.critical?4:2.4,0,TAU);ctx.fill();ctx.shadowBlur=0;}); }
  function drawLightningFx() { state.lightning.forEach((b)=>{const alpha=Math.min(1,b.life/b.maxLife*2);ctx.save();ctx.globalAlpha=alpha;ctx.strokeStyle=b.color;ctx.shadowColor=b.color;ctx.shadowBlur=10;ctx.lineWidth=2;ctx.beginPath();ctx.moveTo(b.x1,b.y1);for(let i=1;i<7;i++){const t=i/7,x=b.x1+(b.x2-b.x1)*t,y=b.y1+(b.y2-b.y1)*t,j=Math.sin(b.seed+i*12.31)*7*(1-Math.abs(t-.5));ctx.lineTo(x+j,y-j*.45);}ctx.lineTo(b.x2,b.y2);ctx.stroke();ctx.restore();}); }
  function drawEffects() { state.shockwaves.forEach((s)=>{ctx.globalAlpha=Math.max(0,s.life/s.maxLife);ctx.strokeStyle=s.color;ctx.lineWidth=2;ctx.beginPath();ctx.arc(s.x,s.y,s.r,0,TAU);ctx.stroke();});ctx.globalAlpha=1;state.particles.forEach((p)=>{ctx.globalAlpha=Math.max(0,p.life/p.maxLife);ctx.fillStyle=p.color;ctx.fillRect(p.x-p.size/2,p.y-p.size/2,p.size,p.size);});ctx.globalAlpha=1;ctx.textAlign="center";state.floaters.forEach((f)=>{ctx.globalAlpha=Math.max(0,f.life/f.maxLife);ctx.fillStyle=f.color;ctx.font=f.text.includes("暴击")?"700 13px 'Microsoft YaHei UI'":"700 10px 'Microsoft YaHei UI'";ctx.fillText(f.text,f.x,f.y);});ctx.globalAlpha=1;ctx.textAlign="left"; }
  function drawFocus(time) {
    if (!state.focus) return; const f = state.focus, alpha = Math.min(1, f.life * 1.4); ctx.save(); ctx.translate(f.x, f.y); ctx.globalAlpha = alpha; ctx.strokeStyle=COLORS.cyan;ctx.lineWidth=1.5;ctx.setLineDash([7,7]);ctx.rotate(f.pulse*.5);ctx.beginPath();ctx.arc(0,0,54+Math.sin(f.pulse)*5,0,TAU);ctx.stroke();ctx.setLineDash([]);ctx.rotate(-f.pulse);for(let i=0;i<4;i++){ctx.rotate(Math.PI/2);ctx.beginPath();ctx.moveTo(68,0);ctx.lineTo(43,0);ctx.stroke();}ctx.fillStyle="rgba(89,230,255,.08)";ctx.beginPath();ctx.arc(0,0,145,0,TAU);ctx.fill();ctx.restore();
  }

  function updateUI(force = false) {
    $("#waveText").textContent=String(Math.max(1,state.wave)).padStart(2,"0");$("#timeText").textContent=formatTime(state.elapsed);$("#scoreText").textContent=state.score.toLocaleString();
    const corePct=Math.max(0,state.coreHp/state.coreMax*100);$("#corePercent").innerHTML=`${Math.round(corePct)}<small>%</small>`;$("#coreBar").style.width=`${corePct}%`;$("#coreState").textContent=corePct>70?"稳定":corePct>35?"受损":"危急";$("#coreState").style.color=corePct>70?COLORS.cyan:corePct>35?COLORS.gold:COLORS.danger;
    $("#coreHint").textContent=state.shield>0?`额外护盾 ${state.shield.toFixed(1)} · 将优先吸收漏怪伤害。`:"敌人突破画面底部的最终防线时会直接损伤屏障。";
    const threat=Math.min(100,12+state.wave*3.8);$("#threatBar").style.width=`${threat}%`;$("#threatLabel").textContent=!state.started?"侦测中":state.wave%10===0?"主宰级":state.wave%5===0?"精英级":threat>70?"灾变级":threat>40?"高压":"常规";
    const progress=state.waveTarget?Math.min(100,state.waveResolved/state.waveTarget*100):0;$("#waveBar").style.width=`${progress}%`;$("#waveProgressLabel").textContent=!state.started?"等待启动":state.waveEnding?"本波已肃清":state.startDelay>0?`第 ${state.wave} 波即将接敌`:`第 ${state.wave} 波推进度`;$("#waveEnemyText").textContent=`${Math.max(0,state.waveTarget-state.waveResolved)} 敌军未解决`;
    const chain=$("#killChain");chain.classList.toggle("active",state.chain>=5);chain.querySelector("b").textContent=`×${state.chain}`;
    const focusReady=state.focusCooldown<=0;$("#focusRing").classList.toggle("cooldown",!focusReady);$("#focusText").textContent=focusReady?"标记就绪":`恢复中 ${state.focusCooldown.toFixed(1)}s`;
    const od=$("#overdriveButton"), odPct=state.overdriveTime>0?100:state.overdrive;$("#overdriveFill").style.width=`${odPct}%`;$("#overdriveText").textContent=state.overdriveTime>0?`极限火力 ${state.overdriveTime.toFixed(1)}s`:`极限火力 ${Math.floor(state.overdrive)}%`;od.disabled=state.overdrive<100||state.overdriveTime>0;od.classList.toggle("ready",state.overdrive>=100&&state.overdriveTime<=0);od.classList.toggle("active",state.overdriveTime>0);
    const stats=getStats();$("#weaponDamage").textContent=`${Math.round(stats.damage)} 基础伤害`;$("#weaponRate").textContent=`${stats.rate.toFixed(1)} / 秒`;$("#saveButton").disabled=!state.authenticated||!state.started||state.gameOver;
    if(force){const chips=$$("#enemyPreview .enemy-chip");chips[0]?.classList.add("active");chips[1]?.classList.toggle("active",state.wave>=2);chips[2]?.classList.toggle("active",state.wave>=4);}
  }
  function updateBuildUI() {
    const tags=Object.entries(state.tagCounts).sort((a,b)=>b[1]-a[1]);$("#cardCount").textContent=`${[...state.cards.values()].reduce((a,b)=>a+b,0)} 张`;$("#buildTags").innerHTML=tags.length?tags.map(([tag,count])=>`<span class="build-tag" data-tag="${tag}">${tag}<b>×${count}</b></span>`).join(""):'<span class="empty-build">尚未选择武装</span>';
    const active=COMBOS.filter((combo)=>hasCard(combo.id)).length;$("#comboCount").textContent=`${active} / ${COMBOS.length}`;$("#comboList").innerHTML=COMBOS.map((combo)=>{const card=CARD_MAP[combo.id],on=hasCard(combo.id),ready=!on&&card.req.every(hasCard);return `<div class="combo-item ${on?"active":ready?"ready":""}"><i>${on?combo.glyph:ready?"+":"·"}</i><span><strong>${combo.name}</strong><small>${on?combo.text:ready?"组件齐备 · 等待选牌":card.req.map((id)=>CARD_MAP[id].name).join(" + ")}</small></span></div>`;}).join("");
  }
  function showCombo(card){$("#comboBannerName").textContent=card.name;$("#comboBannerText").textContent=card.note.replace("组合点亮：","");$("#comboBanner").classList.add("show");state.bannerTimer=3.4;}
  function showToast(text){const toast=$("#toast");toast.textContent=text;toast.classList.add("show");clearTimeout(showToast.timer);showToast.timer=setTimeout(()=>toast.classList.remove("show"),2100);}
  function formatTime(seconds){const m=Math.floor(seconds/60),s=Math.floor(seconds%60);return `${String(m).padStart(2,"0")}:${String(s).padStart(2,"0")}`;}
  function togglePause(){if(!state.started||state.gameOver||state.drafting)return;state.paused=!state.paused;syncPauseUI();showToast(state.paused?"推演已暂停":"星潮继续推进");}
  function syncPauseUI(){$("#pauseIcon").textContent=state.paused?"▶":"Ⅱ";$("#pauseButton").classList.toggle("active",state.paused);$("#pauseVeil").classList.toggle("hidden",!state.paused||state.drafting||!state.started);}
  function endGame(){if(state.gameOver)return;state.gameOver=true;state.paused=true;saveBest();const account=activeAccount();if(account){account.run=null;account.lastPlayedAt=Date.now();persistAccountStore();}updateAccountUI();$("#resultWave").textContent=state.wave;$("#resultKills").textContent=state.kills.toLocaleString();$("#resultScore").textContent=state.score.toLocaleString();const combos=COMBOS.filter((combo)=>hasCard(combo.id));$("#resultCombos").textContent=combos.length;$("#resultSummary").textContent=combos.length>=3?"这套构筑已经形成完整循环；下一次可以尝试更少见的跨系组合。":state.wave<6?"先让一种元素成型，再寻找第二种元素完成跨系组合。":"已经找到节奏；进一步集中牌池，会比平均升级走得更远。";$("#resultBuild").innerHTML=Object.entries(state.tagCounts).sort((a,b)=>b[1]-a[1]).map(([tag,count])=>`<span class="build-tag" data-tag="${tag}">${tag}<b>×${count}</b></span>`).join("");setTimeout(()=>$("#resultOverlay").classList.add("show"),650);playSound("end");syncPauseUI();}

  let audioContext=null;
  function playSound(kind){if(!state.sound)return;try{audioContext||=new(window.AudioContext||window.webkitAudioContext)();if(audioContext.state==="suspended")audioContext.resume();const now=audioContext.currentTime,osc=audioContext.createOscillator(),gain=audioContext.createGain();osc.connect(gain);gain.connect(audioContext.destination);const c={shot:[520,.025,"square"],focus:[280,.17,"sine"],card:[620,.22,"triangle"],combo:[330,.45,"sine"],wave:[440,.3,"triangle"],start:[220,.45,"sine"],boss:[95,.4,"sawtooth"],damage:[120,.18,"sawtooth"],end:[110,.65,"triangle"]}[kind]||[380,.08,"sine"];osc.type=c[2];osc.frequency.setValueAtTime(c[0],now);osc.frequency.exponentialRampToValueAtTime(kind==="combo"?880:Math.max(60,c[0]*(kind==="end"?.55:1.35)),now+c[1]);gain.gain.setValueAtTime(.04,now);gain.gain.exponentialRampToValueAtTime(.0001,now+c[1]);osc.start(now);osc.stop(now+c[1]);}catch{/* optional */}}
  function canvasPoint(event){const r=canvas.getBoundingClientRect();return{x:(event.clientX-r.left)*W/r.width,y:(event.clientY-r.top)*H/r.height};}
  function showStart(){if(state.started&&!state.gameOver)saveRun(false);saveBest();showStartScreen();}
  function bindEvents(){
    $$(".protocol-card").forEach((b)=>b.addEventListener("click",()=>resetGame(b.dataset.protocol)));$("#pauseButton").addEventListener("click",togglePause);$("#speedButton").addEventListener("click",()=>{state.speed=state.speed===1?1.5:state.speed===1.5?2:1;$("#speedText").textContent=`${state.speed}×`;showToast(`推演速度 ${state.speed}×`);});$("#soundButton").addEventListener("click",()=>{state.sound=!state.sound;$("#soundIcon").textContent=state.sound?"♪":"×";$("#soundButton").classList.toggle("muted",!state.sound);if(state.sound)playSound("card");});
    $("#saveButton").addEventListener("click",()=>saveRun(true));$("#accountButton").addEventListener("click",()=>openAccountPanel(false));$("#startAccountButton").addEventListener("click",()=>openAccountPanel(false));$("#accountClose").addEventListener("click",closeAccountPanel);$("#loginAccountButton").addEventListener("click",loginSelectedAccount);$("#loginPin").addEventListener("keydown",(event)=>{if(event.key==="Enter")loginSelectedAccount();});$("#createAccountForm").addEventListener("submit",createAccount);$("#logoutButton").addEventListener("click",logoutAccount);$("#continueRunButton").addEventListener("click",loadRun);$("#discardRunButton").addEventListener("click",discardRun);
    $("#helpButton").addEventListener("click",()=>{if(state.started&&!state.gameOver)state.paused=true;$("#helpOverlay").classList.add("show");syncPauseUI();});const closeHelp=()=>{$("#helpOverlay").classList.remove("show");if(state.started&&!state.gameOver&&!state.drafting)state.paused=false;syncPauseUI();};$("#helpClose").addEventListener("click",closeHelp);$("#helpDone").addEventListener("click",closeHelp);
    $("#restartButton").addEventListener("click",showStart);$("#resultRestart").addEventListener("click",showStart);$("#overdriveButton").addEventListener("click",activateOverdrive);$("#rerollButton").addEventListener("click",()=>{if(state.rerolled)return;state.rerolled=true;$("#rerollButton").disabled=true;generateOffers();playSound("card");});
    canvas.addEventListener("pointerdown",(event)=>{const p=canvasPoint(event);activateFocus(p.x,p.y);});canvas.addEventListener("contextmenu",(e)=>e.preventDefault());window.addEventListener("keydown",(event)=>{if(event.code==="Space"){event.preventDefault();togglePause();}if(event.key.toLowerCase()==="r")showStart();});document.addEventListener("visibilitychange",()=>{if(document.hidden&&state.started&&!state.gameOver){saveRun(false);state.paused=true;syncPauseUI();}});window.addEventListener("beforeunload",()=>saveRun(false));window.addEventListener("resize",resizeCanvas);
  }
  function resizeCanvas(){const dpr=Math.min(2,window.devicePixelRatio||1);canvas.width=W*dpr;canvas.height=H*dpr;ctx.setTransform(dpr,0,0,dpr,0,0);}
  let uiAccumulator=0;
  function loop(time){const dt=state.lastTime?(time-state.lastTime)/1000:0;state.lastTime=time;update(dt);draw(time);uiAccumulator+=dt;if(uiAccumulator>.1){uiAccumulator=0;updateUI();}requestAnimationFrame(loop);}
  function init(){state.turrets=TURRET_DATA.map((t,index)=>({...t,id:index,cooldown:.1+index*.09,shotCount:0,recoil:0,pulse:Math.random()*TAU}));resizeCanvas();bindEvents();updateBuildUI();updateUI(true);renderProfiles();updateAccountUI();$("#startOverlay").classList.remove("show");openAccountPanel(true);draw(0);requestAnimationFrame(loop);}
  init();
})();
