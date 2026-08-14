((root, factory) => {
  const api = factory();
  if (typeof module === "object" && module.exports) module.exports = api;
  if (root) root.EndlessBalanceCore = api;
})(typeof globalThis === "object" ? globalThis : this, () => {
  "use strict";

  const DRAFT_FAMILIES = new Set(["弹道","激光","导弹","冰霜","电弧","支援","特殊","生存","全局","功能"]);
  const DEFAULT_FATIGUE = [0.38, 0.62, 0.82];
  const SAME_CARD_FATIGUE = [0.45, 0.68, 0.84];
  const FORBIDDEN_INSIGHT_CHANCES = [0, 0.20, 0.28, 0.35, 0.43, 0.50];
  const BONUS_BOUNTY_INTERVALS = [0, 20, 15, 10];
  const BASE_STAR_PROBABILITIES = [0.64, 0.22, 0.085, 0.035, 0.015, 0.005];
  const STAR_BOOST_PER_LEVEL = [0.016, 0.010, 0.005, 0.0025, 0.001];
  const DIFFICULTY_STEP_MULTIPLIER = 1.5;
  const BARRIER_RELIC_UNLOCK_THRESHOLD = 10_000_000;
  const COMBAT_FAMILIES = new Set(["弹道","激光","导弹","冰霜","电弧","支援"]);

  function difficultyStatMultiplier(rating) {
    const steps = Math.max(0, Math.floor(Number(rating) || 0));
    return Math.pow(DIFFICULTY_STEP_MULTIPLIER, steps);
  }

  function hasReachedBarrierRelicThreshold(value) {
    return Number(value) >= BARRIER_RELIC_UNLOCK_THRESHOLD;
  }

  function families(card) {
    const tags = [...new Set((card?.tags || []).filter((tag) => DRAFT_FAMILIES.has(tag)))];
    return tags.length ? tags : ["其他"];
  }

  function offerWeight(card, history = []) {
    const cardFamilies = families(card);
    let weight = 1;
    history.slice(0, DEFAULT_FATIGUE.length).forEach((entry, age) => {
      const priorFamilies = new Set(entry?.families || []);
      if (cardFamilies.some((family) => priorFamilies.has(family))) weight *= DEFAULT_FATIGUE[age];
      if (entry?.id === card.id) weight *= SAME_CARD_FATIGUE[age];
    });
    return Math.max(0.025, weight);
  }

  function chooseIndex(pool, history, rng = Math.random, predicate = () => true) {
    const candidates = [];
    let total = 0;
    pool.forEach((card, index) => {
      if (!predicate(card)) return;
      const weight = offerWeight(card, history);
      total += weight;
      candidates.push({ index, total });
    });
    if (!candidates.length) return -1;
    const roll = Math.max(0, Math.min(0.999999999, rng())) * total;
    return candidates.find((candidate) => roll < candidate.total)?.index ?? candidates[candidates.length - 1].index;
  }

  function takeOne(pool, history, rng, predicate) {
    const index = chooseIndex(pool, history, rng, predicate);
    return index < 0 ? null : pool.splice(index, 1)[0];
  }

  function generateOffers(cards, options = {}) {
    const pool = [...cards];
    const history = options.history || [];
    const rng = options.rng || Math.random;
    const count = Math.max(1, Math.floor(options.count || 4));
    const offers = [];
    if (options.preferenceTag) {
      const preferred = takeOne(pool, history, rng, (card) => (card.tags || []).includes(options.preferenceTag));
      if (preferred) offers.push(preferred);
    }
    while (offers.length < count && pool.length) {
      const card = takeOne(pool, history, rng, () => true);
      if (!card) break;
      offers.push(card);
    }
    for (let index = offers.length - 1; index > 0; index -= 1) {
      const swap = Math.floor(rng() * (index + 1));
      [offers[index], offers[swap]] = [offers[swap], offers[index]];
    }
    return offers;
  }

  function normalizeProbabilities(values) {
    const positive = values.map((value) => Math.max(0, Number(value) || 0));
    const total = positive.reduce((sum, value) => sum + value, 0) || 1;
    return positive.map((value) => value / total);
  }

  function starProbabilities(boostRanks = []) {
    const probabilities = [...BASE_STAR_PROBABILITIES];
    for (let source = 0; source < 5; source += 1) {
      const rank = Math.max(0, Math.min(5, Math.floor(Number(boostRanks[source]) || 0)));
      const gain = STAR_BOOST_PER_LEVEL[source] * rank;
      if (!gain) continue;
      const recipient = source + 1;
      const donors = Array.from({ length:source + 1 }, (_, index) => index);
      const donorTotal = donors.reduce((sum, index) => sum + probabilities[index], 0);
      if (!donorTotal) continue;
      const actualGain = Math.min(gain, donorTotal * 0.92);
      for (const donor of donors) probabilities[donor] -= actualGain * probabilities[donor] / donorTotal;
      probabilities[recipient] += actualGain;
    }
    return normalizeProbabilities(probabilities);
  }

  function rollStar(probabilities = BASE_STAR_PROBABILITIES, rng = Math.random) {
    const normalized = normalizeProbabilities(probabilities);
    const roll = Math.max(0, Math.min(0.999999999, rng()));
    let cursor = 0;
    for (let index = 0; index < normalized.length; index += 1) {
      cursor += normalized[index];
      if (roll < cursor) return index + 1;
    }
    return 6;
  }

  function nearestStarPool(cards, targetStar) {
    const exact = cards.filter((card) => (card.star || 1) === targetStar);
    if (exact.length) return exact;
    for (let distance = 1; distance < 6; distance += 1) {
      const lower = cards.filter((card) => (card.star || 1) === targetStar - distance);
      if (lower.length) return lower;
      const higher = cards.filter((card) => (card.star || 1) === targetStar + distance);
      if (higher.length) return higher;
    }
    return cards;
  }

  function generateStarOffers(cards, options = {}) {
    const pool = [...cards];
    const history = options.history || [];
    const rng = options.rng || Math.random;
    const count = Math.max(1, Math.floor(options.count || 4));
    const probabilities = options.starProbabilities || starProbabilities(options.boostRanks || []);
    const offers = [];
    const takeForStar = (star, predicate = () => true) => {
      const legal = pool.filter(predicate);
      const starPool = nearestStarPool(legal, star);
      const allowed = new Set(starPool.map((card) => card.id));
      return takeOne(pool, history, rng, (card) => predicate(card) && allowed.has(card.id));
    };
    if (options.preferenceTag) {
      const preferred = takeForStar(rollStar(probabilities, rng), (card) => (card.tags || []).includes(options.preferenceTag));
      if (preferred) offers.push(preferred);
    }
    while (offers.length < count && pool.length) {
      const card = takeForStar(rollStar(probabilities, rng));
      if (!card) break;
      offers.push(card);
    }
    for (let index = offers.length - 1; index > 0; index -= 1) {
      const swap = Math.floor(rng() * (index + 1));
      [offers[index], offers[swap]] = [offers[swap], offers[index]];
    }
    return offers;
  }

  function earlyWaveProfile(wave) {
    const value = Math.max(1, Math.floor(Number(wave) || 1));
    if (value <= 5) return {
      countScale:[0, .62, .68, .75, .84, .93][value],
      hpScale:[0, .54, .61, .69, .78, .88][value],
      attackScale:[0, .42, .50, .59, .69, .80][value]
    };
    return { countScale:1, hpScale:1, attackScale:1 };
  }

  function smoothstep(value) {
    const t = Math.max(0, Math.min(1, Number(value) || 0));
    return t * t * (3 - 2 * t);
  }

  function lateWaveProfile(wave) {
    const value = Math.max(1, Number(wave) || 1);
    const phaseA = smoothstep((value - 9) / 11);
    const phaseB = smoothstep((value - 20) / 10);
    const phaseC = smoothstep((value - 30) / 10);
    return {
      hpScale:1 + phaseA * .95 + phaseB * 2.85 + phaseC * 8.2,
      attackScale:1 + phaseA * .42 + phaseB * .92 + phaseC * 1.78,
      barrierScale:1 + phaseA * .18 + phaseB * .42 + phaseC * .8,
      rewardPressure:1 + phaseA * .12 + phaseB * .2 + phaseC * .28
    };
  }

  function waveEnemyPressureMultiplier(wave) {
    const value = Math.max(1, Math.floor(Number(wave) || 1));
    const coefficient = value <= 10
      ? 0.5 + (value - 1) * (0.5 / 9)
      : Math.pow(1.6, value - 10);
    return { hp:coefficient, attack:coefficient };
  }

  function bossHealthBudget(wave, finalBoss = false) {
    const value = Math.max(1, Math.floor(Number(wave) || 1));
    const waveTenHealth = finalBoss ? 100000 : 10000;
    return Math.max(1, Math.round(waveTenHealth * Math.pow(1.6, value - 10)));
  }

  function rankOf(ranks, id) {
    if (ranks instanceof Map) return Number(ranks.get(id)) || 0;
    return Number(ranks?.[id]) || 0;
  }

  function terminalSynergyProfile(cards, ranks, family) {
    let highStarScore = 0;
    let linkScore = 0;
    let apexScore = 0;
    let completed = 0;
    for (const card of cards || []) {
      if (!(card?.tags || []).includes(family) || (card.star || 1) < 4) continue;
      const progress = Math.max(0, Math.min(1, rankOf(ranks, card.id) / Math.max(1, card.max || 1)));
      if (!progress) continue;
      const starWeight = [0,0,0,1,1.75,3][Math.max(0, Math.min(5, (card.star || 1) - 1))];
      highStarScore += starWeight * progress;
      const linkedFamilies = (card.tags || []).filter((tag) => COMBAT_FAMILIES.has(tag));
      if (card.combo && linkedFamilies.length >= 2) linkScore += starWeight * progress;
      if (card.apex) apexScore += progress;
      if (progress >= 1) completed += 1;
    }
    const foundation = 1 + highStarScore * .18;
    const linkage = 1 + linkScore * .07;
    const apex = 1 + apexScore * .08;
    const completion = 1 + Math.max(0, completed - 4) * .008;
    return {
      multiplier:foundation * linkage * apex * completion,
      highStarScore, linkScore, apexScore, completed
    };
  }

  function remember(history, card, limit = 3) {
    return [{ id:card.id, families:families(card) }, ...(history || [])].slice(0, limit);
  }

  function forbiddenInsightChance(rank) {
    const tier = Math.max(0, Math.min(FORBIDDEN_INSIGHT_CHANCES.length - 1, Math.floor(Number(rank) || 0)));
    return FORBIDDEN_INSIGHT_CHANCES[tier];
  }

  function rollForbiddenInsight(rank, rng = Math.random) {
    const chance = forbiddenInsightChance(rank);
    return chance > 0 && rng() < chance;
  }

  function bonusBountyInterval(rank) {
    const tier = Math.max(0, Math.min(BONUS_BOUNTY_INTERVALS.length - 1, Math.floor(Number(rank) || 0)));
    return BONUS_BOUNTY_INTERVALS[tier];
  }

  function shouldSpawnBonusBounty(rank, enemyIndex, rng = Math.random) {
    const interval = bonusBountyInterval(rank);
    return interval > 0 && enemyIndex > 0 && enemyIndex % interval === 0 && rng() < 0.10;
  }

  return {
    DRAFT_FAMILIES, DEFAULT_FATIGUE, SAME_CARD_FATIGUE,
    FORBIDDEN_INSIGHT_CHANCES, BONUS_BOUNTY_INTERVALS,
    BASE_STAR_PROBABILITIES, STAR_BOOST_PER_LEVEL, DIFFICULTY_STEP_MULTIPLIER, BARRIER_RELIC_UNLOCK_THRESHOLD,
    families, offerWeight, generateOffers, generateStarOffers, remember,
    normalizeProbabilities, starProbabilities, rollStar, earlyWaveProfile, lateWaveProfile, waveEnemyPressureMultiplier, bossHealthBudget, terminalSynergyProfile,
    difficultyStatMultiplier, hasReachedBarrierRelicThreshold, forbiddenInsightChance, rollForbiddenInsight, bonusBountyInterval, shouldSpawnBonusBounty
  };
});
