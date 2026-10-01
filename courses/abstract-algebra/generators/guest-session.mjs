export const GUEST_SESSION_KEY='generators-guest-session-v1';
export function readGuestSession(read){
 const own=read(GUEST_SESSION_KEY),legacy=read('group-sudoku-guest-session');
 const valid=s=>s?.account?.kind==='guest'&&typeof s.account.id==='string'&&typeof s.sessionToken==='string'&&s.sessionToken;
 return valid(own)?own:valid(legacy)?legacy:null;
}
export function sameReturningGuest(previous,next){return !previous?.account||previous.account.id===next.account?.id;}
