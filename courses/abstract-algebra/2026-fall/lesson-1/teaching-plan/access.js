/* Decrypt the lesson only after a correct password; never persist the password. */
(() => {
  'use strict';
  const form = document.getElementById('access-form');
  const input = document.getElementById('course-password');
  const button = document.getElementById('access-submit');
  const message = document.getElementById('access-message');
  const bytes = value => Uint8Array.from(atob(value), char => char.charCodeAt(0));
  let busy = false;
  form.addEventListener('submit', async event => {
    event.preventDefault();
    if (busy || !input.value) return;
    if (!window.crypto?.subtle) {
      message.textContent = '请使用支持安全连接的浏览器，通过 HTTPS 打开本页。';
      return;
    }
    busy = true;
    button.disabled = true;
    button.textContent = '正在验证…';
    message.textContent = '';
    input.removeAttribute('aria-invalid');
    let html;
    try {
      const response = await fetch('lesson.enc.json?v=20260913-password-v1', {cache: 'no-store'});
      if (!response.ok) throw new Error('load');
      const payload = await response.json();
      const material = await crypto.subtle.importKey('raw', new TextEncoder().encode(input.value), 'PBKDF2', false, ['deriveKey']);
      const key = await crypto.subtle.deriveKey({name: 'PBKDF2', salt: bytes(payload.salt), iterations: payload.iterations, hash: 'SHA-256'}, material, {name: 'AES-GCM', length: 256}, false, ['decrypt']);
      try {
        const plain = await crypto.subtle.decrypt({name: 'AES-GCM', iv: bytes(payload.iv)}, key, bytes(payload.data));
        html = new TextDecoder().decode(plain);
      } catch {
        input.setAttribute('aria-invalid', 'true');
        message.textContent = '密码不正确，请重新输入。';
        input.focus();
        input.select();
      }
    } catch {
      message.textContent = '教学方案加载失败，请检查网络后重试。';
    } finally {
      busy = false;
      button.disabled = false;
      button.textContent = '阅读方案 →';
    }
    if (html) {
      input.value = '';
      document.open();
      document.write(html);
      document.close();
    }
  });
})();
