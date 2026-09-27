// Small, consistent line icons for the destination/action dock.
const paths={
 hall:'<path d="M4 4h16v10H4zM12 14v4M8 20h8M2 18h3m14 0h3"/>',
 floor:'<path d="M3 20h5v-5h5v-5h5V5h3M4 9V3m-2 2 2-2 2 2"/>',
 pavilion:'<path d="m3 9 9-6 9 6M2 10h20M6 11v8m12-8v8M4 20h16M12 3V1M9 10v9m6-9v9"/>',
 sunrise:'<path d="M2 17h20M5 21h14M7 17a5 5 0 0 1 10 0M12 10V2m-3 3 3-3 3 3M3 11l2 2m14 0 2-2"/>',
 sunset:'<path d="M2 17h20M5 21h14M7 17a5 5 0 0 1 10 0M12 2v8m-3-3 3 3 3-3M3 11l2 2m14 0 2-2"/>',
 lower:'<path d="M4 3h16l-2 6H6zM8 9v5h8V9M3 20h18M12 12v6m-3-3 3 3 3-3"/>',
 raise:'<path d="M4 3h16l-2 6H6zM8 9v5h8V9M3 20h18M12 18v-6m-3 3 3-3 3 3"/>',
 book:'<path d="M12 5v15M12 6C9 3 5 3 2 4v15c4-1 7-1 10 1 3-2 6-2 10-1V4c-3-1-7-1-10 2Z"/>',
 coffee:'<path d="M4 8h12v7a5 5 0 0 1-10 0V8m10 1h2a3 3 0 0 1 0 6h-2M3 21h17M7 2v3m5-3v3"/>',
 lounge:'<path d="M5 12V7a3 3 0 0 1 3-3h8a3 3 0 0 1 3 3v5M5 12H3v7h18v-7h-2M5 12v3h14v-3M5 19v2m14-2v2"/>',
 bed:'<path d="M3 20V7m18 13V10H3m2 0V6h6v4m2 0V6h6v4M3 16h18"/>',
 sea:'<path d="M2 15q3-4 6 0t6 0 6 0M2 21q3-4 6 0t6 0 6 0M12 3v8m-5-5 5-3 5 3"/>',
 walk:'<circle cx="14" cy="3" r="2"/><path d="m7 12 3-5 4 1 3 5h4M12 9l-2 6 5 3 1 4M10 15l-4 7"/>',
 home:'<path d="m3 10 9-7 9 7M5 9v12h14V9M9 21v-8h6v8"/>',
 gallery:'<path d="M3 4h18v16H3zM3 16l5-5 4 4 3-3 6 5"/><circle cx="16" cy="8" r="1.5"/>',
 work:'<path d="M3 4h18v13H3zM12 17v4m-4 0h8M8 8l-2 2 2 2m8-4 2 2-2 2"/>'
};
export function renderRoomAction(button,room,{lowered=false,walk=false}={}){
 const name=room.name;
 let icon='home',label=name.split(' · ')[0],badge='';
 if(room.sunEvent){icon=room.sunEvent;label=room.sunEvent==='sunrise'?'日出':'日落';}
 else if(room.lecternLift){icon=lowered?'raise':'lower';label=lowered?'升讲台':'降讲台';}
 else if(name.includes('亭')){icon='pavilion';label='海上亭';}
 else if(/^[二三]层/.test(name)){icon='floor';badge=name[0]==='二'?'2F':'3F';label=name.split(' · ')[1]||name;}
 else if(name.includes('报告厅')||name.includes('教室')||name.includes('讨论')){icon='hall';label=name.includes('KM')?'KM 研读':name.split(' · ').at(-1);if(name.startsWith('一层'))badge='1F';}
 else if(/书|阅览|论文/.test(name))icon='book';
 else if(/咖啡|茶/.test(name))icon='coffee';
 else if(/客厅|会客/.test(name)){icon='lounge';label=name.split(' · ').at(-1);}
 else if(/客房|主卧/.test(name))icon='bed';
 else if(/露台|海岸总览/.test(name))icon='sea';
 else if(walk)icon='walk';
 else if(/展廊/.test(name))icon='gallery';
 else if(/工作室/.test(name))icon='work';
 const title=room.lecternLift?(lowered?'升起讲台':'降下讲台'):name;
 button.type='button';button.className='room-action';button.dataset.actionIcon=icon;
 button.setAttribute('aria-label',title);button.title=title;
 button.innerHTML=`<span class="room-action-orb"><svg viewBox="0 0 24 24" aria-hidden="true" fill="none" stroke="currentColor" stroke-width="1.2" stroke-linecap="round" stroke-linejoin="round">${paths[icon]}</svg><span class="room-action-badge" aria-hidden="true"></span></span><span class="room-action-label" aria-hidden="true"></span>`;
 button.querySelector('.room-action-badge').textContent=badge;
 button.querySelector('.room-action-label').textContent=label;
}
