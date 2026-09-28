// Hours on a 24-hour clock. Minimum 0.3 at the event; unchanged beyond ±30 min.
export function twilightCloudFactor(hour,events){
 let nearest=Infinity;
 for(const event of [events.sunrise,events.sunset])if(Number.isFinite(event)){const distance=((hour-event)%24+36)%24-12;nearest=Math.min(nearest,Math.abs(distance));}
 const t=Math.min(1,nearest/.5),ease=t*t*t*(t*(t*6-15)+10);
 return .3+.7*ease;
}
