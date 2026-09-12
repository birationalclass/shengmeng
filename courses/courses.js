(() => {
  const rows = [...document.querySelectorAll('tbody tr[data-chapter]')];
  if (!rows.length) return;
  const filters = [...document.querySelectorAll('[data-filter]')];
  const search = document.querySelector('#scheduleSearch');
  const count = document.querySelector('#resultCount');
  let chapter = 'all';
  document.querySelector('.filterbar').hidden = false;
  const print = document.querySelector('#printSchedule');
  print.hidden = false;
  print.addEventListener('click', () => window.print());
  const apply = () => {
    const query = search.value.trim().toLocaleLowerCase();
    let visible = 0;
    rows.forEach(row => {
      row.hidden = !((chapter === 'all' || row.dataset.chapter === chapter) && row.textContent.toLocaleLowerCase().includes(query));
      if (!row.hidden) visible++;
    });
    count.textContent = `${visible} 次课 · ${visible * 2} 学时`;
    document.querySelector('.no-results').hidden = visible !== 0;
  };
  filters.forEach(button => button.addEventListener('click', () => {
    chapter = button.dataset.filter;
    filters.forEach(item => item.setAttribute('aria-pressed', String(item === button)));
    apply();
  }));
  search.addEventListener('input', apply);
  const next = rows.find(row => new Date(row.dataset.end).getTime() > Date.now());
  if (next) {
    next.classList.add('upcoming');
    const link = document.querySelector('#nextLesson');
    link.hidden = false;
    link.href = '#' + next.id;
    link.textContent = `下一次课 · ${next.querySelector('time').textContent} ↓`;
    link.addEventListener('click', () => {
      chapter = 'all'; search.value = '';
      filters.forEach(item => item.setAttribute('aria-pressed', String(item.dataset.filter === 'all')));
      apply();
    });
  }
  window.addEventListener('beforeprint', () => { count.textContent = '24 次课 · 48 学时'; });
  window.addEventListener('afterprint', apply);
})();
