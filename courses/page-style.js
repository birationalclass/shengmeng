/* Shared course settings. Apply the fixed palette before stylesheets load. */
(() => {
  'use strict';
  const key = 'shengmeng-course-sand-motion-v1';
  const root = document.documentElement;
  const read = () => { try { return localStorage.getItem(key) !== 'off'; } catch { return true; } };
  let enabled = read(), dialog, toggle, status, trigger, returnFocus, saved = true;
  const t = (zh, en) => window.CourseLanguage?.language === 'en' ? en : zh;
  root.dataset.pageStyle = 'sand';
  root.dataset.sandMotion = enabled ? 'on' : 'off';
  document.querySelector('meta[name="theme-color"]')?.setAttribute('content', '#11100d');
  function labels() {
    if (!dialog) return;
    dialog.querySelector('#pageStyleTitle').textContent = t('设置', 'Settings');
    dialog.querySelector('.page-style-close').setAttribute('aria-label', t('关闭设置', 'Close settings'));
    dialog.querySelector('.page-motion-name').textContent = t('落沙动画', 'Falling sand');
    dialog.querySelector('#pageMotionDescription').textContent = t('开启时，标题沙粒持续飘落；关闭后静态显示。', 'Animate the title with falling sand, or keep it still.');
    dialog.querySelector('.page-motion-memory').textContent = t('课程安排与课件共用此设置。', 'Shared by the course schedule and lessons.');
    toggle.checked = enabled;
    status.textContent = (enabled ? t('已开启', 'On') : t('已关闭', 'Off')) + ' · ' + (saved ? t('自动保存', 'Saved automatically') : t('仅本次有效', 'For this visit only'));
  }
  function apply(value) {
    const changed = enabled !== value;
    enabled = value;
    root.dataset.sandMotion = enabled ? 'on' : 'off';
    labels();
    if (changed) window.dispatchEvent(new Event('course-sand-motion'));
  }
  function setSandMotion(value) {
    saved = true;
    try { localStorage.setItem(key, value ? 'on' : 'off'); } catch { saved = false; }
    apply(Boolean(value));
  }
  window.CourseAppearance = Object.freeze({ get sandMotion() { return enabled; }, setSandMotion });
  function init() {
    trigger = document.querySelector('[data-page-style-open]');
    if (!trigger) return;
    dialog = document.createElement('dialog');
    dialog.id = 'pageStyleSettings';
    dialog.className = 'page-style-dialog';
    dialog.setAttribute('aria-labelledby', 'pageStyleTitle');
    dialog.innerHTML = `
      <div class="page-style-heading"><h2 id="pageStyleTitle"></h2><button type="button" class="page-style-close">×</button></div>
      <label class="page-motion-control">
        <span class="page-motion-name" id="pageMotionLabel"></span>
        <input type="checkbox" id="pageSandMotion" role="switch" aria-labelledby="pageMotionLabel" aria-describedby="pageMotionDescription">
        <span class="page-motion-switch" aria-hidden="true"></span>
      </label>
      <p id="pageMotionDescription"></p>
      <p class="page-motion-memory"></p>
      <p class="page-motion-status" role="status" aria-live="polite"></p>`;
    document.body.append(dialog);
    toggle = dialog.querySelector('#pageSandMotion');
    status = dialog.querySelector('.page-motion-status');
    labels();
    trigger.hidden = false;
    trigger.addEventListener('click', () => {
      returnFocus = document.activeElement;
      dialog.showModal();
      trigger.setAttribute('aria-expanded', 'true');
      toggle.focus();
    });
    dialog.querySelector('.page-style-close').addEventListener('click', () => dialog.close());
    dialog.addEventListener('close', () => {
      trigger.setAttribute('aria-expanded', 'false');
      const target = returnFocus?.isConnected && returnFocus.getClientRects().length ? returnFocus : trigger;
      target.focus({ preventScroll: true });
    });
    let backdropDown = false;
    const outside = event => {
      const r = dialog.getBoundingClientRect();
      return event.clientX < r.left || event.clientX > r.right || event.clientY < r.top || event.clientY > r.bottom;
    };
    dialog.addEventListener('pointerdown', event => { backdropDown = event.target === dialog && outside(event); });
    dialog.addEventListener('click', event => { if (backdropDown && event.target === dialog && outside(event)) dialog.close(); });
    toggle.addEventListener('change', () => setSandMotion(toggle.checked));
  }
  window.addEventListener('course-language', labels);
  window.addEventListener('storage', event => { if (event.key === key || event.key === null) apply(read()); });
  window.addEventListener('pageshow', () => apply(saved ? read() : enabled));
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', init, { once: true });
  else init();
})();
