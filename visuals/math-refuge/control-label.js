// Updating state must keep the visible icon and its accessible name together.
export function controlLabel(button,label){
  if(button.getAttribute('aria-label')===label)return;
  button.setAttribute('aria-label',label);button.setAttribute('title',label);button.setAttribute('data-tip',label);
}
