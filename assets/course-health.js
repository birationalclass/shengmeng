/* Classroom diagnostics: classic ES5, no telemetry, no network probes or input interception. */
(function (w, d) {
  'use strict';
  if (w.CourseHealth) return;
  var boot = d.currentScript, mode = boot && boot.getAttribute('data-health-page') || 'course';
  var items = [], waits = {}, frames = [], notice, observer, timer, stopped = false;
  var scrolls = [], revision = '20260928-health1';
  function lang() { return (w.CourseLanguage && w.CourseLanguage.language || d.documentElement.lang || '').slice(0, 2) === 'en'; }
  function clean(value, limit) { return String(value || '').replace(/[\r\n\t<>]/g, ' ').slice(0, limit || 180); }
  function file(url) {
    var path = String(url || '').split(/[?#]/)[0].replace(/\\/g, '/');
    return clean(path.slice(path.lastIndexOf('/') + 1), 70) || 'resource';
  }
  function origin() { return w.location.protocol + '//' + w.location.host; }
  function forward(action, entry) {
    if (w.parent === w) return;
    try { w.parent.postMessage({type: 'course-health', action: action, entry: entry}, origin()); } catch (_) {}
  }
  function report(code, zh, en, options) {
    options = options || {};
    var entry = {key: clean(options.key || code, 140), code: clean(code, 40), zh: clean(zh, 260), en: clean(en, 300), severity: options.severity === 'warning' ? 'warning' : 'error'};
    var found = false;
    for (var i = 0; i < items.length; i++) if (items[i].key === entry.key) { items[i] = entry; found = true; break; }
    if (!found) { if (items.length >= 16) items.shift(); items.push(entry); }
    if (!options.local) forward('report', entry);
    render();
  }
  function clear(key, local) {
    for (var i = items.length - 1; i >= 0; i--) if (items[i].key === key) items.splice(i, 1);
    if (!local) forward('clear', {key: key});
    render();
  }
  function host() {
    var root = d.fullscreenElement || d.webkitFullscreenElement || d.body;
    var dialogs = d.querySelectorAll('dialog[open]');
    for (var i = dialogs.length - 1; i >= 0; i--) if (root && root.contains(dialogs[i])) return dialogs[i];
    return root;
  }
  function pruneFrames() {
    for (var i = frames.length - 1; i >= 0; i--) if (!d.documentElement.contains(frames[i].element)) {
      var prefix = frames[i].prefix;
      items = items.filter(function (entry) { return entry.key.indexOf(prefix) !== 0; });
      frames.splice(i, 1);
    }
  }
  function render() {
    if (!d.body || stopped) return;
    pruneFrames();
    if (!items.length) { if (notice) notice.style.setProperty('display', 'none', 'important'); return; }
    if (!notice) {
      notice = d.createElement('p'); notice.id = 'course-health-notice';
      notice.setAttribute('role', 'status'); notice.setAttribute('aria-live', 'polite'); notice.setAttribute('aria-atomic', 'true');
      notice.style.cssText = 'position:fixed!important;left:12px!important;right:12px!important;bottom:8px!important;bottom:calc(8px + env(safe-area-inset-bottom,0px))!important;top:auto!important;z-index:2147483646!important;margin:0!important;padding:5px 9px!important;box-sizing:border-box!important;max-height:64px!important;overflow:hidden!important;border:1px solid #b4935166!important;border-radius:4px!important;background:rgba(25,22,16,.94)!important;color:#ead7a9!important;font:12px/1.5 system-ui,"Microsoft YaHei",sans-serif!important;text-align:left!important;letter-spacing:0!important;text-transform:none!important;visibility:visible!important;opacity:1!important;pointer-events:none!important;white-space:normal!important;word-wrap:break-word!important;';
    }
    var target = host(); if (target && notice.parentNode !== target) target.appendChild(notice);
    var sorted = items.slice().sort(function (a, b) { return (a.severity === 'error' ? 0 : 1) - (b.severity === 'error' ? 0 : 1); });
    var entry = sorted[0], english = lang(), extra = sorted.length > 1 ? (english ? ' · +' + (sorted.length - 1) + ' issue(s)' : ' · 另有 ' + (sorted.length - 1) + ' 项') : '';
    var text = (english ? 'Status ' : '运行提示 ') + entry.code + ' · ' + (english ? entry.en : entry.zh) + extra;
    if (notice.textContent !== text) notice.textContent = text;
    notice.setAttribute('data-code', entry.code); notice.setAttribute('data-count', String(items.length));
    notice.title = sorted.map(function (item) { return item.code + ': ' + (english ? item.en : item.zh); }).join('\n');
    notice.style.setProperty('display', 'block', 'important');
  }
  function ready(name) {
    if (waits[name]) w.clearTimeout(waits[name]); delete waits[name]; clear('wait-' + name);
  }
  function expect(name, zh, en, delay) {
    ready(name);
    waits[name] = w.setTimeout(function () {
      delete waits[name];
      report('D-WAIT', zh + '尚未就绪；请刷新，或拍下此提示反馈。', en + ' is not ready yet. Reload, or share a photo of this message.', {key: 'wait-' + name});
    }, delay || 60000);
  }
  function featureChecks() {
    var missing = [], interactive = mode !== 'index';
    if (interactive) {
      if (!w.Promise) missing.push('Promise');
      if (!w.URLSearchParams) missing.push('URLSearchParams');
      if (!w.fetch) missing.push('fetch');
      if (!w.AbortController) missing.push('AbortController');
      if (!w.ResizeObserver) missing.push('ResizeObserver');
      if (typeof d.createElement('dialog').showModal !== 'function') missing.push('dialog');
    }
    if (/^(sudoku|generators|rubik|cards)$/.test(mode) && !('noModule' in d.createElement('script'))) missing.push('JS modules');
    if (mode === 'sudoku') {
      if (!w.structuredClone) missing.push('structuredClone');
      if (!w.crypto || !w.crypto.randomUUID) missing.push('crypto.randomUUID');
    }
    if (missing.length) report('D-COMPAT', '浏览器缺少 ' + missing.join('、') + '；请换用更新的 Edge/Chrome。', 'Browser lacks ' + missing.join(', ') + '. Use a current Edge/Chrome.');
    if (/^(course|lesson)$/.test(mode) && (!w.CSS || !w.CSS.supports || !w.CSS.supports('height', '100dvh'))) {
      report('D-LAYOUT', '浏览器不支持动态视口高度；若内容被裁切或无法滚动，请换用更新的浏览器。', 'Dynamic viewport height is unsupported. If content is clipped or cannot scroll, use a newer browser.', {severity: 'warning'});
    }
    if (w.location.protocol === 'file:') report('D-LOCAL', '当前直接打开本地文件，课件数据或模块可能被浏览器阻止；请使用网站或本地服务器。', 'Opened as a local file: data/modules may be blocked. Use the website or a local server.');
    if (mode === 'sudoku') {
      var key = 'course-health-probe-' + Date.now() + '-' + Math.random();
      try { w.localStorage.setItem(key, '1'); w.localStorage.removeItem(key); }
      catch (_) { report('D-STORAGE', '本机存储不可用，棋局可能无法在关闭后保留。', 'Local storage is unavailable; boards may not survive closing this page.', {severity: 'warning'}); }
    }
  }
  function online() {
    if (w.navigator.onLine === false) report('D-OFFLINE', '浏览器报告当前离线；未缓存内容和服务器同步可能不可用。', 'Browser reports offline. Uncached content and server sync may be unavailable.', {severity: 'warning'});
    else clear('D-OFFLINE');
  }
  function runtime(event) {
    var target = event.target, name, type;
    if (target && target !== w && target.tagName) {
      type = target.tagName.toLowerCase();
      if (type !== 'script' && !(type === 'link' && /stylesheet/.test(target.rel))) return;
      name = file(target.src || target.href);
      report('D-ASSET', '资源加载失败：' + name + '；可能是连接、拦截或文件版本问题。', 'Resource failed: ' + name + '. Connection, filtering or file version may be involved.', {key: 'asset-' + name});
      return;
    }
    if (event.filename && /^(chrome|moz|safari)-extension:/.test(event.filename)) return;
    name = file(event.filename); type = event.error && event.error.name || 'Error';
    report('D-SCRIPT', '脚本执行异常：' + name + (event.lineno ? ':' + event.lineno : '') + '（' + clean(type, 35) + '）；请拍照反馈。', 'Script error: ' + name + (event.lineno ? ':' + event.lineno : '') + ' (' + clean(type, 35) + '). Please share a photo.', {key: 'script-' + name});
  }
  w.addEventListener('error', runtime, true);
  w.addEventListener('unhandledrejection', function (event) {
    if (event.reason && event.reason.name === 'AbortError') return;
    report('D-ASYNC', '异步操作异常（' + clean(event.reason && event.reason.name || 'Error', 35) + '）；请拍照反馈，不一定是网络问题。', 'Async operation failed (' + clean(event.reason && event.reason.name || 'Error', 35) + '). Please share a photo; this is not necessarily a network issue.');
  });
  w.addEventListener('online', online); w.addEventListener('offline', online);
  w.addEventListener('course-language', render);
  d.addEventListener('fullscreenchange', render); d.addEventListener('webkitfullscreenchange', render);
  d.addEventListener('webglcontextlost', function (event) {
    report('D-GRAPHICS', '图形上下文已丢失；三维画面可能停止，请刷新或使用简洁棋盘。', 'Graphics context lost. 3D may stop; reload or use the simple board.', {key: 'graphics-' + (event.target.id || 'canvas')});
  }, true);
  d.addEventListener('webglcontextrestored', function (event) { clear('graphics-' + (event.target.id || 'canvas')); }, true);
  w.addEventListener('message', function (event) {
    if (event.origin !== origin() || !event.data || event.data.type !== 'course-health') return;
    var nodes = d.querySelectorAll('iframe'), frame, record, entry = event.data.entry;
    if (!entry || typeof entry.key !== 'string') return;
    for (var i = 0; i < nodes.length; i++) if (nodes[i].contentWindow === event.source) { frame = nodes[i]; break; }
    if (!frame) return; // Ignore removed/replaced lesson frames and other windows.
    for (i = 0; i < frames.length; i++) if (frames[i].element === frame) record = frames[i];
    if (!record) { record = {element: frame, prefix: 'frame-' + Date.now() + '-' + frames.length + '-'}; frames.push(record); }
    var key = record.prefix + clean(entry.key, 140);
    if (event.data.action === 'clear') clear(key, true);
    else if (event.data.action === 'report' && typeof entry.zh === 'string' && typeof entry.en === 'string') report(entry.code, entry.zh, entry.en, {key: key, severity: entry.severity, local: true});
  });
  function visible(element) {
    if (!element || !element.getClientRects().length) return false;
    var style = w.getComputedStyle(element);
    if (style.display === 'none' || style.visibility === 'hidden') return false;
    var dialog = element.closest && element.closest('dialog');
    return !dialog || dialog.open;
  }
  function scrollRecord(element) {
    for (var i = 0; i < scrolls.length; i++) if (scrolls[i].element === element) return scrolls[i];
    var record = {element: element, key: 'scroll-' + scrolls.length, hits: 0, timer: 0}; scrolls.push(record); return record;
  }
  function checkScroll() {
    if (d.hidden) return;
    var nodes = d.querySelectorAll('#course-scroll-region,.lesson-notebook,.records-scroll');
    for (var i = 0; i < nodes.length; i++) {
      var element = nodes[i], record = scrollRecord(element), key = record.key + '-layout';
      if (!visible(element)) { clear(key); continue; }
      var style = w.getComputedStyle(element), tall = element.scrollHeight > element.clientHeight + 30;
      var collapsed = element.scrollHeight > 100 && element.clientHeight < 36;
      var clipped = tall && /^(hidden|clip)$/.test(style.overflowY);
      if (collapsed || clipped) report('D-SCROLL', '阅读区域可能被压缩或裁切；试用 Ctrl+0 恢复缩放，或更换浏览器。', 'Reading area may be compressed or clipped. Try Ctrl+0 to reset zoom, or another browser.', {key: key, severity: 'warning'});
      else clear(key);
    }
  }
  d.addEventListener('wheel', function (event) {
    if (event.ctrlKey || event.metaKey || !event.deltaY || !event.target.closest || d.hidden) return;
    if (event.target.closest('input,select,textarea,button,canvas,[contenteditable]')) return;
    var element = event.target.closest('#course-scroll-region,.lesson-notebook,.experiment,.records-scroll');
    if (!element && event.target.closest('.course-title-panel')) element = d.getElementById('course-scroll-region');
    if (!visible(element)) return;
    var dialogs = d.querySelectorAll('dialog[open]');
    if (dialogs.length && !dialogs[dialogs.length - 1].contains(event.target)) return;
    var max = element.scrollHeight - element.clientHeight, top = element.scrollTop;
    if (max < 10 || (event.deltaY > 0 ? top >= max - 6 : top <= 6)) return; // Boundary is not a fault.
    var record = scrollRecord(element); if (record.timer) return;
    record.timer = w.setTimeout(function () {
      record.timer = 0;
      if (!visible(element) || d.hidden) return;
      if (Math.abs(element.scrollTop - top) > 1) { record.hits = 0; clear(record.key); return; }
      record.hits++;
      if (record.hits >= 3) report('D-SCROLL', '检测到多次滚轮操作但阅读区域未移动；疑似滚动受阻，可试拖动滚动条或更换浏览器。', 'Repeated wheel input did not move the reading area. Scrolling may be blocked; try dragging its scrollbar or another browser.', {key: record.key, severity: 'warning'});
    }, 450);
  }, {capture: true, passive: true});
  d.addEventListener('scroll', function (event) {
    for (var i = 0; i < scrolls.length; i++) if (scrolls[i].element === event.target) { scrolls[i].hits = 0; clear(scrolls[i].key); }
  }, true);
  function start() {
    featureChecks(); online(); render();
    if (mode !== 'index' && !w.__courseHealthReady) expect('app', mode === 'sudoku' ? '群数独程序' : '页面程序', mode === 'sudoku' ? 'Group Sudoku' : 'Page application');
    if (w.MutationObserver) {
      observer = new w.MutationObserver(function () { render(); });
      observer.observe(d.documentElement, {subtree: true, attributes: true, attributeFilter: ['lang', 'open']});
    }
    timer = w.setInterval(function () { checkScroll(); render(); }, 4000);
    checkScroll();
  }
  w.CourseHealth = {version: revision, report: report, clear: clear, expect: expect, ready: ready, checkScroll: checkScroll, refresh: render, file: file,
    appReady: function () { w.__courseHealthReady = true; ready('app'); },
    snapshot: function () { return items.map(function (entry) { return {code: entry.code, zh: entry.zh, en: entry.en, severity: entry.severity}; }); }};
  w.addEventListener('pagehide', function () { stopped = true; w.clearInterval(timer); if (observer) observer.disconnect(); for (var key in waits) w.clearTimeout(waits[key]); for (var i = 0; i < scrolls.length; i++) w.clearTimeout(scrolls[i].timer); });
  w.addEventListener('pageshow', function (event) { if (event.persisted) { stopped = false; start(); } });
  if (d.readyState === 'loading') d.addEventListener('DOMContentLoaded', start); else start();
})(window, document);
