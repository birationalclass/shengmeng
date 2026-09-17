// Restore appearance before first paint. Unset preferences use the new defaults.
(()=>{try{
 const root=document.documentElement,style=localStorage.getItem('spectral-panel-style'),marks=localStorage.getItem('spectral-statement-marks');
 if(['sand','editorial','instrument','glass'].includes(style))root.dataset.panelStyle=style;
 if(['bare','circle','square'].includes(marks))root.dataset.markStyle=marks;
}catch{}})();
