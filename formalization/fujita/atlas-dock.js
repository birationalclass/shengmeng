// Reuse the Refuge's quiet action arc; the existing controls retain their events.
export function installAtlasDock({english}) {
  const panel=document.querySelector('.graph-panel'),toolbar=panel.querySelector('.graph-toolbar');
  const dock=document.createElement('div');dock.className='atlas-dock';
  const inspectorToggle=toolbar.querySelector('.inspector-toggle');
  const inspectorCaption=document.createElement('span');inspectorCaption.className='inspector-caption';
  inspectorCaption.textContent=inspectorToggle.textContent;inspectorToggle.textContent='';
  inspectorToggle.innerHTML='<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.4" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path class="inspector-open-icon" d="M4 4h16v16H4zM14 4v16"/><path class="inspector-close-icon" d="m6 6 12 12M18 6 6 18"/></svg>';
  inspectorToggle.append(inspectorCaption);document.querySelector('.workspace').append(inspectorToggle);
  const syncInspector=()=>inspectorToggle.setAttribute('aria-pressed',String(document.body.classList.contains('inspector-open')));
  new MutationObserver(syncInspector).observe(document.body,{attributes:true,attributeFilter:['class']});syncInspector();
  const views=toolbar.querySelector('.view-switch');dock.append(views);
  const icons={
    scope:'<path d="M4 5h16M7 12h10M10 19h4"/><circle cx="8" cy="5" r="2"/><circle cx="16" cy="12" r="2"/>',
    node:'<rect x="8" y="8" width="8" height="8" rx="2"/><path d="M12 2v4m0 12v4M2 12h4m12 0h4M4 4l3 3m10 10 3 3M20 4l-3 3M7 17l-3 3"/>'
  };
  const actions=[];
  for(const [key,id] of [['scope','scope'],['node','editorSelect']]){
    const select=document.getElementById(id),label=select.parentElement;
    for(const child of label.childNodes){if(child.nodeType===Node.TEXT_NODE)child.textContent='';}
    label.classList.add('dock-action');label.dataset.dockAction=key;
    const orb=document.createElement('span');orb.className='dock-orb';orb.setAttribute('aria-hidden','true');
    orb.innerHTML=`<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.35" stroke-linecap="round" stroke-linejoin="round">${icons[key]}</svg>`;
    label.insertBefore(orb,select);
    const caption=document.createElement('span');caption.className='dock-caption';
    const value=document.createElement('span');value.className='dock-value';
    label.append(caption,value);dock.append(label);
    actions.push({key,select,label,caption,value});
    select.addEventListener('change',()=>refresh(english));
  }
  for(const button of views.querySelectorAll('button')){
    button.classList.add('dock-action');button.dataset.dockAction=button.dataset.view;
    const svg=button.querySelector('svg'),orb=document.createElement('span');orb.className='dock-orb';orb.setAttribute('aria-hidden','true');orb.append(svg);button.prepend(orb);
    button.querySelector('span:not(.dock-orb)').classList.add('dock-caption');
  }
  function refresh(language){
    english=language;
    inspectorToggle.setAttribute('aria-label',english?'Details':'详情');inspectorToggle.title=english?'Details':'详情';
    for(const a of actions){
      const caption=a.key==='scope'?(english?'Scope':'显示范围'):(english?'Locate node':'定位节点');
      a.caption.textContent=caption;a.value.textContent=a.select.selectedOptions[0]?.textContent||'';
      a.select.setAttribute('aria-label',caption);a.select.title=caption+' · '+a.value.textContent;
    }
  }
  panel.append(dock);refresh(english);return {refresh};
}
