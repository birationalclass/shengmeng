/* Shared course appearance. Runs before stylesheets to avoid a light-page flash. */
(() => {
  'use strict';
  const key = 'shengmeng-course-page-style-v1';
  const root = document.documentElement;
  const names = { sand: '砂岩金粒', paper: '纸页青绿' };
  const normalize = value => Object.hasOwn(names, value) ? value : 'sand';
  const read = () => { try { return normalize(localStorage.getItem(key)); } catch { return 'sand'; } };
  let dialog, status, trigger;
  function apply(value) {
    const style = normalize(value);
    root.dataset.pageStyle = style;
    document.querySelector('meta[name="theme-color"]')?.setAttribute('content', style === 'sand' ? '#11100d' : '#173e37');
    if (dialog) {
      dialog.querySelectorAll('input[name="page-style"]').forEach(input => { input.checked = input.value === style; });
      status.textContent = `当前：${names[style]} · 选择自动保存`;
    }
  }
  apply(read());
  function init() {
    trigger = document.querySelector('[data-page-style-open]');
    if (!trigger) return;
    dialog = document.createElement('dialog');
    dialog.id = 'pageStyleSettings';
    dialog.className = 'page-style-dialog';
    dialog.setAttribute('aria-labelledby', 'pageStyleTitle');
    dialog.setAttribute('aria-describedby', 'pageStyleDescription');
    dialog.innerHTML = `
      <div class="page-style-heading"><div><p class="page-style-eyebrow">APPEARANCE</p><h2 id="pageStyleTitle">页面风格</h2></div><button type="button" class="page-style-close" aria-label="关闭页面设置">×</button></div>
      <p id="pageStyleDescription">为课程与讲义，选择一种阅读氛围。</p>
      <fieldset class="page-style-choices"><legend class="sr-only">选择页面风格</legend>
        <label class="page-style-choice"><input type="radio" name="page-style" value="sand" aria-label="砂岩金粒"><span class="page-style-card"><span class="page-style-swatch swatch-sand" aria-hidden="true"><i></i><b>Ab</b><em></em></span><span class="page-style-name">砂岩金粒 <small>默认</small><span class="page-style-check" aria-hidden="true">✓</span></span><span class="page-style-detail">暗色砂岩 · 暖金细砂<br>延续开场动画的光与质感</span></span></label>
        <label class="page-style-choice"><input type="radio" name="page-style" value="paper" aria-label="纸页青绿"><span class="page-style-card"><span class="page-style-swatch swatch-paper" aria-hidden="true"><i></i><b>Ab</b><em></em></span><span class="page-style-name">纸页青绿 <small>原版</small><span class="page-style-check" aria-hidden="true">✓</span></span><span class="page-style-detail">温润纸白 · 沉静青绿<br>保留熟悉的纸页阅读风格</span></span></label>
      </fieldset>
      <p class="page-style-memory">课程页与第一讲共用此设置。</p>
      <p class="page-style-status" role="status" aria-live="polite"></p>`;
    document.body.append(dialog);
    status = dialog.querySelector('.page-style-status');
    apply(root.dataset.pageStyle);
    trigger.hidden = false;
    trigger.addEventListener('click', () => {
      dialog.showModal();
      trigger.setAttribute('aria-expanded', 'true');
      dialog.querySelector('input:checked').focus();
    });
    dialog.querySelector('.page-style-close').addEventListener('click', () => dialog.close());
    dialog.addEventListener('close', () => {
      trigger.setAttribute('aria-expanded', 'false');
      trigger.focus({ preventScroll: true });
    });
    // Ignore drag releases originating inside the panel.
    let backdropDown = false;
    const outside = event => {
      const r = dialog.getBoundingClientRect();
      return event.clientX < r.left || event.clientX > r.right || event.clientY < r.top || event.clientY > r.bottom;
    };
    dialog.addEventListener('pointerdown', event => { backdropDown = event.target === dialog && outside(event); });
    dialog.addEventListener('click', event => { if (backdropDown && event.target === dialog && outside(event)) dialog.close(); });
    dialog.addEventListener('change', event => {
      if (!event.target.matches('input[name="page-style"]')) return;
      apply(event.target.value);
      try { localStorage.setItem(key, root.dataset.pageStyle); }
      catch { status.textContent = `当前：${names[root.dataset.pageStyle]} · 此浏览器无法保存偏好`; }
    });
  }
  window.addEventListener('storage', event => { if (event.key === key || event.key === null) apply(read()); });
  window.addEventListener('pageshow', () => apply(read()));
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', init, { once: true });
  else init();
})();
