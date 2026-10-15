// Reading time is wall time, including a manual pause. It never resumes playback.
export const MIN_BOARD_REVIEW_SECONDS=5;
export class BoardReview {
 constructor(now=()=>performance.now()/1000){this.now=now;this.finished=new Map();}
 clear(){this.finished.clear();}
 mark(page){if(!this.finished.has(page))this.finished.set(page,this.now());}
 remaining(page){return Math.max(0,MIN_BOARD_REVIEW_SECONDS-(this.finished.has(page)?this.now()-this.finished.get(page):0));}
}
