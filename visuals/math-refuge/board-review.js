// Reading time is wall time, including a manual pause. It never resumes playback.
export const MIN_BOARD_REVIEW_SECONDS=10;
export class BoardReview {
 constructor(now=()=>performance.now()/1000){this.now=now;this.finished=new Map();}
 clear(){this.finished.clear();}
 reset(page){this.finished.delete(page);}
 mark(page){if(!this.finished.has(page))this.finished.set(page,this.now());}
 remaining(page){return Math.max(0,MIN_BOARD_REVIEW_SECONDS-(this.finished.has(page)?this.now()-this.finished.get(page):0));}
}

// Media-relative time after BOTH the final stroke and the final spoken sentence.
// Cues are local in the reader; lineCues are absolute in the scene transport.
export function boardReviewStart(board){
 if(!board)return 0;
 const seconds=board.seconds??(board.end-board.start),start=board.start||0;
 const cues=board.cues?.length?board.cues:(board.lineCues||[]).map(c=>({...c,audioEnd:c.audioEnd-start}));
 const speech=cues.length?Math.max(0,...cues.map(c=>c.audioEnd||0)):Math.max(0,seconds-(board.boardHoldSeconds||0));
 const ink=Number.isFinite(board.lastStrokeEnd)?board.lastStrokeEnd:Math.max(0,(board.writeEnd||start)-start);
 return Math.max(ink,speech);
}
