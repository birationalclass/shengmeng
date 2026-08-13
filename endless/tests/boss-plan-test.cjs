const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");

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

const plan = Array.from({length:20}, (_, index) => {
  const wave = 10 + index;
  return {wave, type:wave % 2 === 0 ? "colossal" : "blackhole"};
});
assert.equal(plan.length, 20);
assert(plan.every((entry, index) => entry.type === (index % 2 === 0 ? "colossal" : "blackhole")));

console.log(JSON.stringify({waves:plan, blackHoleScale:2, normalWidth:720, colossalWidth:1320}, null, 2));
