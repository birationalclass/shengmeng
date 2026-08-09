"use strict";

const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const vm = require("node:vm");
const Balance = require("../balance-core.js");

function rng(seed) {
  let value = seed >>> 0;
  return () => {
    value ^= value << 13; value ^= value >>> 17; value ^= value << 5;
    return (value >>> 0) / 4294967296;
  };
}

const gameSource = fs.readFileSync(path.join(__dirname, "..", "game.js"), "utf8");
const blackHoleSource = fs.readFileSync(path.join(__dirname, "..", "black-hole-enemy.js"), "utf8");
const cardStart = gameSource.indexOf("const CARDS = [");
const cardEnd = gameSource.indexOf("\n  ];", cardStart);
assert(cardStart >= 0 && cardEnd > cardStart, "可以读取完整卡牌定义");
const arrayStart = gameSource.indexOf("[", cardStart);
const cards = vm.runInNewContext(`(${gameSource.slice(arrayStart, cardEnd + 4)})`, { rangeCardDesc:() => "射程测试" });

const ids = new Set(cards.map((card) => card.id));
assert.equal(ids.size, cards.length, "所有卡牌 ID 唯一");
for (const card of cards) {
  assert.equal(typeof card.id, "string", "卡牌具有 ID");
  assert.equal(typeof card.name, "string", `${card.id} 具有名称`);
  assert(Array.isArray(card.tags) && card.tags.length, `${card.id} 具有分类`);
  assert(Number.isInteger(card.max) && card.max >= 1 && card.max <= 6, `${card.id} 层数处于安全范围`);
  for (const requirement of [...(card.req || []), ...(card.reqAny || [])]) assert(ids.has(requirement), `${card.id} 前置 ${requirement} 存在`);
  assert.equal(typeof card.desc(0), "string", `${card.id} 首级说明可渲染`);
  assert.equal(typeof card.desc(card.max - 1), "string", `${card.id} 满级说明可渲染`);
}

assert(/const DRAFT_OFFER_COUNT = 4;/.test(gameSource), "所有选卡均为四选一");
assert(/const NEW_RUN_OPENING_DRAFTS = 5;/.test(gameSource), "新局提供五轮开局选卡");
assert(/const NEW_RUN_RANDOM_CARDS = 3;/.test(gameSource), "新局额外直接获得三张随机卡牌");
assert.equal(cards.find((card) => card.id === "global_damage").max, 4, "弹道火控总成最多四级");
assert(/const LOOP_SECONDS = 9\.6;/.test(blackHoleSource), "黑洞默认旋转周期减半为 9.6 秒");
assert(/sample\.index[\s\S]*sample\.next[\s\S]*sample\.mix/.test(blackHoleSource), "黑洞运行时混合相邻帧而非跳帧播放");
assert(!/drawSideLensRims\(ctx, width, height, palette\)/.test(blackHoleSource), "黑洞主体不再叠加额外透镜边框");
assert(!/enemy\.hit[\s\S]{0,500}ctx\.ellipse/.test(blackHoleSource), "黑洞受击不再叠加整圈白色描边");

assert.deepEqual(Balance.FORBIDDEN_INSIGHT_CHANCES, [0, .2, .28, .35, .43, .5], "禁忌洞见由 20% 成长至 50%");
assert.equal(Balance.forbiddenInsightChance(1), .2, "禁忌洞见一级为 20%");
assert.equal(Balance.forbiddenInsightChance(5), .5, "禁忌洞见满级为 50%");
assert.equal(Balance.rollForbiddenInsight(5, () => .49), true, "满级在 50% 内只返回一次布尔触发");
assert.equal(Balance.rollForbiddenInsight(5, () => .5), false, "满级不超过 50% 概率");
const bargainBranch = gameSource.indexOf("if(wasBargainPick)");
const forbiddenRollBranch = gameSource.indexOf("BalanceCore.rollForbiddenInsight");
assert(bargainBranch >= 0 && bargainBranch < forbiddenRollBranch, "追加选择先返回原流程，不会再次触发禁忌洞见");
assert(/state\.bargainDraftsQueued=1/.test(gameSource), "禁忌洞见每次最多只追加一次选择");

assert.deepEqual(Balance.BONUS_BOUNTY_INTERVALS, [0, 20, 15, 10], "奖励敌人判定节点由每 20 个缩短至每 10 个");
assert.equal(Balance.shouldSpawnBonusBounty(1, 20, () => .09), true, "一级每 20 个敌人进行 10% 判定");
assert.equal(Balance.shouldSpawnBonusBounty(1, 19, () => .01), false, "非判定节点不会生成额外奖励敌人");
assert.equal(Balance.shouldSpawnBonusBounty(3, 10, () => .1), false, "额外奖励敌人概率严格保持为 10%");

const families = ["弹道","激光","导弹","冰霜","电弧","支援","特殊"];
const pool = families.flatMap((family) => Array.from({ length:10 }, (_, index) => ({ id:`${family}-${index}`, tags:[family] })));
function offerRates(history, preferenceTag = "", iterations = 30000) {
  const random = rng(0x5eed1234);
  const hits = Object.fromEntries(families.map((family) => [family, 0]));
  for (let index = 0; index < iterations; index += 1) {
    const offers = Balance.generateOffers(pool, { count:4, history, preferenceTag, rng:random });
    assert.equal(offers.length, 4, "每轮正好四张");
    assert.equal(new Set(offers.map((card) => card.id)).size, 4, "同轮不重复");
    for (const family of families) if (offers.some((card) => card.tags.includes(family))) hits[family] += 1;
  }
  return Object.fromEntries(families.map((family) => [family, hits[family] / iterations]));
}

const baseline = offerRates([]);
const afterBullet = offerRates([{ id:"弹道-0", families:["弹道"] }]);
assert(afterBullet["弹道"] < baseline["弹道"] * 0.72, "刚选择的弹道类别下一轮显著降权");
assert(afterBullet["激光"] > baseline["激光"], "未选择类别获得归一化概率补偿");
const preferredAfterBullet = offerRates([{ id:"弹道-0", families:["弹道"] }], "弹道", 5000);
assert.equal(preferredAfterBullet["弹道"], 1, "卡牌偏好仍然保底一张，不被疲劳覆盖");

const baseDps = {
  bullet:15 / .48,
  laser:6 / .3,
  missile:58 / 2.65,
  frost:5 / 1.05,
  arc:(4.4 / .92) * (1 + .8 + .64)
};
assert(baseDps.arc < baseDps.bullet * .45, "电弧基础直接伤害保持辅助定位");
assert(baseDps.missile * 3 > baseDps.bullet * 1.8, "导弹命中三个密集目标时确立 AOE 优势");
assert(baseDps.frost < baseDps.bullet * .2, "冰霜保持低伤害控制定位");

console.log(JSON.stringify({
  cardsAudited:cards.length,
  openingDrafts:5,
  initialRandomCards:3,
  offerCount:4,
  forbiddenInsight:[Balance.forbiddenInsightChance(1), Balance.forbiddenInsightChance(5)],
  bonusBountyIntervals:[Balance.bonusBountyInterval(1), Balance.bonusBountyInterval(3)],
  bulletOfferBaseline:+baseline["弹道"].toFixed(3),
  bulletOfferAfterPick:+afterBullet["弹道"].toFixed(3),
  otherFamilyLift:+(afterBullet["激光"] / baseline["激光"] - 1).toFixed(3),
  baseDps:Object.fromEntries(Object.entries(baseDps).map(([key,value]) => [key,+value.toFixed(2)]))
}, null, 2));
