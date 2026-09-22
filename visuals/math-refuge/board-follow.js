// Manual viewing temporarily owns the teaching camera; tour state is separate.
export class BoardFollow{
  constructor(delay=20,now=()=>performance.now()/1000){this.now=now;this.delay=delay;this.lastInput=-Infinity;this.interacting=false;}
  setDelay(seconds){this.delay=Math.max(5,Math.min(60,Number(seconds)||20));}
  touch(){this.lastInput=this.now();}
  begin(){this.interacting=true;this.touch();}
  end(){this.interacting=false;this.touch();}
  reset(){this.interacting=false;this.lastInput=-Infinity;}
  get remaining(){return this.interacting?this.delay:Math.max(0,this.delay-(this.now()-this.lastInput));}
  get following(){return !this.interacting&&this.remaining===0;}
}
