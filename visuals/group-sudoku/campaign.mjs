import {frontier,canEnter} from './journey.mjs?v=journey4';
export const STORAGE_KEY='shengmeng-group-sudoku-campaign-v1';
export const MAP_STYLE_KEY='group-sudoku-map-style';
export function clearLocalData(storage){for(const key of [STORAGE_KEY,MAP_STYLE_KEY])storage?.removeItem(key);}
export class Campaign{
 constructor(model,storage){this.model=model;this.storage=storage;this.boards={};this.finished={};this.persistent=!!storage;try{const data=JSON.parse(storage?.getItem(STORAGE_KEY)||'{}');for(let n=2;n<=9;n++){if(this.valid(n,data.boards?.[n]))this.boards[n]=data.boards[n];if(this.valid(n,data.finished?.[n])&&model.inspect(data.finished[n]).kind==='complete')this.finished[n]=data.finished[n];}}catch{this.persistent=false;}}
 valid(n,v){const clues=this.model.initial(n);return Array.isArray(v)&&v.length===n*n&&v.every((x,i)=>Number.isInteger(x)&&x>=0&&x<=n&&(!clues[i]||clues[i]===x));}
 get completed(){return Object.keys(this.finished).map(Number).sort((a,b)=>a-b);}
 get current(){return frontier(this.completed);}
 canEnter(n){return canEnter(n,this.completed);}
 get identityUnlocked(){return this.completed.includes(3);}
 board(n){return [...(this.boards[n]||this.model.initial(n))];}
 save(n,values){if(!this.valid(n,values))return false;this.boards[n]=[...values];if(this.model.inspect(values).kind==='complete')this.finished[n]=[...values];try{this.storage?.setItem(STORAGE_KEY,JSON.stringify({boards:this.boards,finished:this.finished}));}catch{this.persistent=false;}return true;}
}
