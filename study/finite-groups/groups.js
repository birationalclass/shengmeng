function renderRelations(details) {
  if (!details.open || !window.katex) return;
  for (const host of details.querySelectorAll('[data-math]')) {
    katex.render(host.dataset.math, host, {throwOnError:false, strict:'ignore'});
    host.removeAttribute('data-math');
  }
}
for (const details of document.querySelectorAll('.presentation')) {
  details.addEventListener('toggle', () => renderRelations(details));
}
function revealTarget() {
  if (!location.hash) return;
  const target = document.getElementById(decodeURIComponent(location.hash.slice(1)));
  if (!target) return;
  for (let node = target; node; node = node.parentElement) {
    if (node instanceof HTMLDetailsElement) { node.open = true; renderRelations(node); }
  }
  requestAnimationFrame(() => target.scrollIntoView({block:'start',behavior:'instant'}));
}
addEventListener('hashchange', revealTarget);
if (location.hash) revealTarget();
document.addEventListener('click', event => {
  const link = event.target.closest('a[href^="#"]');
  if (link?.hash === location.hash) revealTarget();
});
