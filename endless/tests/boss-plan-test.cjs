const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const vm = require("node:vm");

const root = path.resolve(__dirname, "..");
const game = fs.readFileSync(path.join(root, "game.js"), "utf8");
const renderer = fs.readFileSync(path.join(root, "black-hole-enemy.js"), "utf8");

assert.match(game, /function colossalBossSequenceIndex\(wave=state\.wave\)\{return wave>=10&&\(wave-10\)%2===0/);
assert.match(game, /function blackHoleBossSequenceIndex\(wave=state\.wave\)\{return wave>=11&&\(wave-11\)%2===0/);
assert.match(game, /if\(colossalIndex>=0\)return \[\{type:colossalIndex%2===0\?"boss_red_giant":"boss_red_antares",kind:"final",colossal:true\}\]/);
assert.match(game, /if\(blackHoleIndex>=0\)return \[\{type:waveBossType\(wave\),kind:"final",colossal:false\}\]/);
assert.match(game, /const radius=isBlackHole\?type\.radius\*\(colossal\?4\.2:2\):type\.radius/);
assert.match(renderer, /const MAX_GAME_BOSS_WIDTH = 720/);
assert.match(renderer, /const MAX_COLOSSAL_BOSS_WIDTH = 1320/);
assert.match(game, /function enemyAttackPoint\(enemy\)[\s\S]{0,300}enemy\.y\+halfHeight/);
assert.match(game, /function updateProjectiles\(dt\)[\s\S]{0,420}enemyAttackPoint\(target\)/);
assert.match(game, /const centralBoss=enemy\.type\.bossKind==="redgiant"\|\|enemy\.type\.bossKind==="blackhole"/);
assert.match(game, /function blackHoleEventHorizonHalfHeight\(radius\)/);
assert.match(game, /function triggerBossPaletteSkill\(enemy\)/);
assert.match(game, /palette\.key==="violet"[\s\S]{0,520}type:"ionized"/);
assert.match(game, /!options\.ionLinkCopy&&barrierDebuffPower\(segment,"ionized"\)>0/);
assert.match(game, /ionLinkCopy:true,exactDamage:true/);
assert.match(game, /palette\.key==="gold"[\s\S]{0,900}type:"healBlock"/);
assert.match(game, /palette\.key==="blue"[\s\S]{0,900}type:"weaken"/);
assert.match(game, /赤潮裂变/);
assert.match(game, /enemy\.type\.bossKind==="blackhole"\?"引力深渊威胁":"超巨星威胁"/);

const enduranceSource=game.match(/  function bossEnduranceMultiplier\([^\r\n]+/)?.[0]||"";
const rangeSuppressionSource=game.match(/  function bossRangeSuppressionProfile\([^\r\n]+/)?.[0]||"";
assert(enduranceSource&&rangeSuppressionSource,"可以提取 Boss 久战增压与射程压制数值函数");
const bossMechanicsSandbox={globalThis:null};
bossMechanicsSandbox.globalThis=bossMechanicsSandbox;
vm.runInNewContext(`
  let __difficultyRating=0;
  const difficultyIndex=()=>__difficultyRating;
  const clamp=(value,min,max)=>Math.max(min,Math.min(max,value));
${enduranceSource}
${rangeSuppressionSource}
  globalThis.__setDifficulty=(rating)=>{__difficultyRating=rating;};
  globalThis.__bossEnduranceMultiplier=bossEnduranceMultiplier;
  globalThis.__bossRangeSuppressionProfile=bossRangeSuppressionProfile;
`,bossMechanicsSandbox,{filename:"boss-v149-mechanics-test.js"});
const rangeProfile=(rating,phase)=>{bossMechanicsSandbox.__setDifficulty(rating);const profile=bossMechanicsSandbox.__bossRangeSuppressionProfile(phase);return profile?{power:+profile.power.toFixed(8),duration:profile.duration}:null;};
assert.equal(rangeProfile(9,2),null,"难度索引 10 前不会触发 Boss 射程压制");
assert.equal(rangeProfile(10,1),null,"Boss 第一阶段不压制射程");
assert.deepEqual([2,3,4].map((phase)=>rangeProfile(10,phase)),[
  {power:.10,duration:5},{power:.15,duration:6},{power:.20,duration:7}
],"中高难 Boss 二至四阶段依次压制 10%/15%/20%，持续 5/6/7 秒");
assert.deepEqual([2,3,4].map((phase)=>rangeProfile(15,phase)),[
  {power:.15,duration:6},{power:.20,duration:7},{power:.25,duration:8}
],"最高难度段的阶段压制额外提高 5% 与 1 秒，并严格封顶 25%");
const enduranceAt=(rating,seconds,boss=true)=>{bossMechanicsSandbox.__setDifficulty(rating);return bossMechanicsSandbox.__bossEnduranceMultiplier({type:{boss},bossCombatTime:seconds});};
assert.equal(enduranceAt(14,100),1,"难度索引 15 前 Boss 不获得久战增压");
assert.equal(enduranceAt(15,100,false),1,"普通敌人永不获得久战增压");
assert.equal(enduranceAt(15,9.999),1,"战斗未满 10 秒时不提前增压");
assert.equal(enduranceAt(15,10),1.1,"Boss 有效战斗每满 10 秒攻击倍率提高 10%");
assert.equal(enduranceAt(15,90),1.9,"Boss 战斗 90 秒时攻击倍率为 1.9 倍");
assert.equal(enduranceAt(15,100),2,"Boss 久战增压在 100 秒达到 2 倍上限");
assert.equal(enduranceAt(15,1000),2,"Boss 久战增压不会越过 2 倍硬上限");
assert.match(game,/function applyBossRangeSuppression\(enemy,phase\)[^\n]+power:Math\.max\([^\n]+time:Math\.max\(/,"多名 Boss 连续压制时保留更强幅度与更长剩余时间");
assert.match(game,/updateBossPhase\(enemy\)[\s\S]{0,900}applyBossRangeSuppression\(enemy,phase\)/,"Boss 跨阶段时实际施加射程压制");
assert.match(game,/function activeTurretRangePenalty\(\)[^\n]+clamp\([^\n]+0,\.25\)/,"战斗射程压制入口再次限制在 25% 内");
assert.match(game,/function updateTurretRangeDebuff\(dt\)[^\n]+debuff\.time=Math\.max\(0,[^\n]+if\(debuff\.time<=0\)\{debuff\.power=0;debuff\.label="";/,"射程压制独立倒计时并在到期时彻底清零");
assert.match(game,/turretRangeDebuff:\{\.\.\.\(state\.turretRangeDebuff\|\|\{\}\)\}/,"未结束的 Boss 射程压制会写入战局存档");
assert.match(game,/drawRangeSuppressionStatus\(\)[^\n]+视界压缩 · 射程 -\$\{Math\.round\(debuff\.power\*100\)\}% · \$\{debuff\.time\.toFixed\(1\)\}s/,"战斗底部持续显示射程压制幅度与剩余时间");
assert.match(game,/enemy\.type\.boss&&enemy\.invulnerable<=0&&\(enemy\.type\.bossKind!=="blackhole"\|\|enemy\.bossStage==="casting"\)\)enemy\.bossCombatTime=[^\n]+\+dt/,"久战计时排除首领无敌期与黑洞入场期");
assert.match(game,/function enemyAttackScale\(enemy[^\n]+endurance=boss\?bossEnduranceMultiplier\(enemy\):1[^\n]+phasePower\*endurance\*pressure\.attack/,"久战增压真实进入 Boss 攻击倍率结算");
assert.match(game,/superBossBuffEntries\(enemy\)[^\n]+久战增压 ×\$\{endurance\.toFixed\(1\)\}/,"超大首领状态栏显示当前久战增压倍率");
assert.match(game,/function drawCompactBossEndurance\(enemy,radius\)[^\n]+久战增压 ×\$\{endurance\.toFixed\(1\)\}/,"普通恒星 Boss 的紧凑血条也显示当前久战增压倍率");
assert.match(game,/if\(!centralBoss\)[^\n]+drawCompactBossEndurance\(enemy,radius\);return/,"普通 Boss 血条绘制路径不会漏掉久战增压提示");

const plan = Array.from({length:20}, (_, index) => {
  const wave = 10 + index;
  return {wave, type:wave % 2 === 0 ? "colossal" : "blackhole"};
});
assert.equal(plan.length, 20);
assert(plan.every((entry, index) => entry.type === (index % 2 === 0 ? "colossal" : "blackhole")));

console.log(JSON.stringify({waves:plan, blackHoleScale:2, normalWidth:720, colossalWidth:1320}, null, 2));
