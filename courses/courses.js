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
  const describe = (items) => {
    const lessons = items.filter(row => row.dataset.calendar !== 'true').length;
    if (lessons === items.length) return `${lessons} 次课 · ${lessons * 2} 学时`;
    if (!lessons) return `${items.length} 项安排 · 具体时段待定`;
    return `${items.length} 项安排 · ${lessons} 次课 / ${lessons * 2} 学时`;
  };
  const apply = () => {
    const query = search.value.trim().toLocaleLowerCase();
    let visible = 0;
    rows.forEach(row => {
      row.hidden = !((chapter === 'all' || row.dataset.chapter === chapter) && row.textContent.toLocaleLowerCase().includes(query));
      if (!row.hidden) visible++;
    });
    count.textContent = describe(rows.filter(row => !row.hidden));
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
  window.addEventListener('beforeprint', () => { count.textContent = describe(rows); });
  window.addEventListener('afterprint', apply);
})();
