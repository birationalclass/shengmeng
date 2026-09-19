/* Prose is text, never HTML: inequalities such as i<j must survive insertion.
   Typeset the explicit subscript notation used in the original lesson notes. */
(()=>{
 'use strict';
 const escape=text=>String(text).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
 const sub={'₀':'0','₁':'1','₂':'2','₃':'3','₄':'4','₅':'5','₆':'6','₇':'7','₈':'8','₉':'9','ₐ':'a','ₑ':'e','ₕ':'h','ᵢ':'i','ⱼ':'j','ₖ':'k','ₗ':'l','ₘ':'m','ₙ':'n','ₒ':'o','ₚ':'p','ᵣ':'r','ₛ':'s','ₜ':'t','ᵤ':'u','ᵥ':'v','ₓ':'x'};
 const sup={'⁰':'0','¹':'1','²':'2','³':'3','⁴':'4','⁵':'5','⁶':'6','⁷':'7','⁸':'8','⁹':'9','⁺':'+','⁻':'-','ⁱ':'i','ʲ':'j','ᵏ':'k','ᵐ':'m','ⁿ':'n','ʳ':'r','ˢ':'s','ᵗ':'t'};
 const greek={'λ':'\\lambda','ρ':'\\rho','σ':'\\sigma','ϕ':'\\phi','φ':'\\phi','α':'\\alpha','β':'\\beta'};
 function tex(text){return text.replace(/[₀-₉ₐₑₕᵢⱼₖₗₘₙₒₚᵣₛₜᵤᵥₓ]+/gu,s=>'_{'+[...s].map(c=>sub[c]).join('')+'}').replace(/[⁰¹²³⁴⁵⁶⁷⁸⁹⁺⁻ⁱʲᵏᵐⁿʳˢᵗ]+/gu,s=>'^{'+[...s].map(c=>sup[c]).join('')+'}').replace(/[λρσϕφαβ]/gu,c=>greek[c]+' ');}
 function inline(text){
  text=String(text);let result='',end=0;
  const pattern=/([A-Za-zλρσϕφαβ])_(\([^()]+\)|[A-Za-zλρσϕφαβ0-9]+[₀-₉ₐₑₕᵢⱼₖₗₘₙₒₚᵣₛₜᵤᵥₓ]*)/gu;
  for(const match of text.matchAll(pattern)){
   result+=escape(text.slice(end,match.index));
   const index=match[2].startsWith('(')?match[2].slice(1,-1):match[2];
   result+=window.katex.renderToString(tex(match[1])+'_{'+tex(index)+'}',{throwOnError:true,strict:'ignore',output:'htmlAndMathml'});
   end=match.index+match[0].length;
  }
  return result+escape(text.slice(end));
 }
 window.GroupLessonMath=Object.freeze({escape,inline});
})();
