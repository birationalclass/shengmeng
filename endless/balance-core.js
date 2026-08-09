((root, factory) => {
  const api = factory();
  if (typeof module === "object" && module.exports) module.exports = api;
  if (root) root.EndlessBalanceCore = api;
})(typeof globalThis === "object" ? globalThis : this, () => {
  "use strict";

  const DRAFT_FAMILIES = new Set(["弹道","激光","导弹","冰霜","电弧","支援","特殊","生存","全局","功能"]);
  const DEFAULT_FATIGUE = [0.38, 0.62, 0.82];
  const SAME_CARD_FATIGUE = [0.45, 0.68, 0.84];

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

  function remember(history, card, limit = 3) {
    return [{ id:card.id, families:families(card) }, ...(history || [])].slice(0, limit);
  }

  return { DRAFT_FAMILIES, DEFAULT_FATIGUE, SAME_CARD_FATIGUE, families, offerWeight, generateOffers, remember };
});
