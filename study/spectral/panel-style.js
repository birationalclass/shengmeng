// Appearance is independent of reading position, proof tabs and diagram timelines.
const key='spectral-panel-style';
const choices={
 editorial:['A · 墨色书页','A · Editorial notebook','留白与清晰层次 · 推荐','Space and hierarchy · Recommended'],
 instrument:['B · 秩序工作台','B · Ordered workbench','紧凑排版与精细分区','Compact typography and fine rules'],
 glass:['C · 悬浮薄光','C · Quiet glass','柔和表面与轻薄控制台','Soft surfaces and light controls']
};
export function createPanelStyle({language}){
 const root=document.documentElement,dialog=document.querySelector('#motionSettings');
 let current='editorial';try{const value=localStorage.getItem(key);if(choices[value])current=value;}catch{}
 const group=document.createElement('fieldset');group.className='panel-style-setting';
 group.innerHTML='<legend id="panelStyleLabel"></legend><div class="panel-style-choices">'+Object.keys(choices).map(value=>`<label class="panel-style-option" data-style-choice="${value}"><input type="radio" name="panelStyle" value="${value}"><span class="panel-style-mini" aria-hidden="true"><i></i><i></i><i></i></span><span class="panel-style-copy"><strong></strong><small></small></span></label>`).join('')+'</div>';
 dialog.querySelector('.dialog-head').after(group);
 function sync(){const en=language()==='en';group.querySelector('legend').textContent=en?'Main panel':'主面板风格';for(const el of group.querySelectorAll('[data-style-choice]')){const [zh,enName,zhNote,enNote]=choices[el.dataset.styleChoice];el.querySelector('strong').textContent=en?enName:zh;el.querySelector('small').textContent=en?enNote:zhNote;el.querySelector('input').checked=el.dataset.styleChoice===current;}}
 function set(value){if(!choices[value])return;current=value;root.dataset.panelStyle=current;try{localStorage.setItem(key,current);}catch{}sync();}
 root.dataset.panelStyle=current;sync();
 group.addEventListener('change',event=>{if(event.target.matches('[name="panelStyle"]')&&event.target.checked)set(event.target.value);});
 const api={sync,set,value:()=>current,reset:()=>set('editorial')};window.spectralPanelStyle=api;return api;
}
