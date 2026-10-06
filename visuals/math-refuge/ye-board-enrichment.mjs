import {equationLines} from './chalk-layout.mjs';
const R=String.raw;
// Supplemental rows clarify the actual objects and proof steps, not filler prose.
export const enrichedYeRows={
1:[R`E(u)=\sum_{n\ge1}|u_n-u_{n-1}|^2,\quad M(u)=\sum_{n\ge1}|u_n|^2/n^2`,R`E(u)\ge\frac14M(u)`,R`\inf_{u\ne0}\frac{E(u)}{M(u)}=\frac14`],
2:['original',R`|n|^2=n_1^2+\cdots+n_d^2`,R`E_m(u)=\sum_{n\in\mathbb Z^d}|\mathcal D^m u(n)|^2`,R`M_m(u)=\sum_{n\ne0}|u(n)|^2/|n|^{2m}`],
3:['original',R`|\nabla u|^2=\sum_{j=1}^d|\nabla_j u|^2`,R`\sum_n u(n)\Delta u(n)=\sum_n|\nabla u(n)|^2\ge0`],
4:['original',R`\mathcal D^1u=\nabla u,\quad\mathcal D^2u=\Delta u,\quad\mathcal D^3u=\nabla\Delta u`,R`|\mathcal D^{2r+1}u|^2=\sum_{j=1}^d|\nabla_j\Delta^r u|^2`],
5:[R`E_m(u)=\|\mathcal D^m u\|_{\ell^2}^2,\quad M_m(u)=\sum_{n\ne0}|u(n)|^2/|n|^{2m}`,'original',R`E_m(u)\ge aM_m(u)\ (\forall u)\ \Longrightarrow\ \mathcal C_{m,d}\ge a`,R`0\ne v\in\mathcal E(\mathbb Z^d)\ \Longrightarrow\ \mathcal C_{m,d}\le E_m(v)/M_m(v)`],
6:['original',R`m=1:\quad v=\delta_{e_1}-\delta_{-e_1}`,R`M_1(v)=2,\quad E_1(v)=4d,\quad E_1(v)/M_1(v)=2d`],
7:['original',R`\liminf_{d\to\infty}\mathcal C_{m,d}/d^m\ge2^m`,R`\limsup_{d\to\infty}\mathcal C_{m,d}/d^m\le2^m`],
8:['original',R`|1-e^{ix_j}|^2=4\sin^2(x_j/2)`,R`\sum_{j=1}^d|1-e^{ix_j}|^2=4\omega(x)`],
9:[R`a(0)=0,\quad a(n)=u(n)/|n|^{2m}\ (n\ne0)`,R`\Psi=(-i)^m\mathcal Fa,\quad\mathcal Fa=(2\pi)^{-d/2}\sum_n a(n)e^{-in\cdot x}`,R`\int_{\mathbb T^d}\Psi\,dx=0`,'original'],
10:[R`\sum_j|1-e^{ix_j}|^2=4\omega`,'original',R`\frac{E_m(u)}{M_m(u)}=4^m\frac{\int|D^{2m}\Psi|^2\omega^m}{\int|D^m\Psi|^2}`],
11:[R`\int_{\mathbb T^d}\phi\,dx=0,\quad k>\ell\ge0,\quad1\le k-\ell\le\gamma`,'original',R`C_{d,k,\ell,\gamma}=\inf_{\phi\ne0,\ \int\phi=0}\frac{\int|D^k\phi|^2\omega^\gamma}{\int|D^\ell\phi|^2\omega^{\gamma-k+\ell}}`],
12:[R`q=k-\ell\ \text{fixed}`,'original',R`C_{d,j+1,j,\eta}\ge(d/2)(1-o_d(1)),\quad\eta\ge1`,R`\prod_{r=1}^{q}\frac d2(1-\varepsilon_{r,d})=\left(\frac d2\right)^q(1-o_d(1))`],
15:['original',R`\partial_j\rho=\sin x_j/d`,R`\mathbb E_\mu\rho=1,\quad\operatorname{Var}_\mu(\rho)=1/(2d)`],
16:[R`X_j\stackrel{\rm iid}{\sim}\operatorname{Unif}[-\pi,\pi],\quad Y_j=\cos X_j`,R`Y_j\in[-1,1],\quad\mathbb EY_j=0,\quad\rho=1-d^{-1}\sum_jY_j`,'original'],
17:[R`W_0\ge0,\quad s>0,\quad B=\mathbb E_\mu(f^2)>0`,R`g=f^2/B,\quad h=e^{sW_0}/\mathbb E_\mu e^{sW_0}`,R`\mathbb E_\mu g=\mathbb E_\mu h=1,\quad\int g\log(g/h)d\mu\ge0`,'original'],
18:['original',R`\mu=\mu_1^{\otimes d},\quad\operatorname{Ent}_\mu(f^2)\le\sum_{j=1}^d\mathbb E_{\widehat x_j}\operatorname{Ent}_{\mu_1}(f^2)`,R`\sum_{j=1}^d\int|\partial_j f|^2d\mu=\int|\nabla f|^2d\mu`],
20:[R`E_\gamma=\int\omega^\gamma|\nabla\varphi|^2,\quad B_\eta=\int\omega^\eta\varphi^2`,'original',R`\varepsilon_d\to0\quad\text{uniformly over }\varphi`],
21:[R`Q_\gamma=\int\omega^\gamma|\Delta\varphi|^2,\quad E_\eta=\int\omega^\eta|\nabla\varphi|^2`,'original',R`\gamma\ \text{fixed};\quad\varepsilon_d\ \text{independent of }\varphi`],
22:[R`q=k-\ell,\quad\eta_j=\gamma-k+j+1\ge1\quad(\ell\le j<k)`,R`C_{d,k,\ell,\gamma}\ge\prod_{j=\ell}^{k-1}C_{d,j+1,j,\eta_j}`,'original'],
23:['original',R`|D^{2r}\phi_1|^2=\sin^2x_1,\quad|D^{2r+1}\phi_1|^2=\cos^2x_1`,R`\int\sin^2x_1dx=\int\cos^2x_1dx=(2\pi)^d/2`],
24:['original',R`\operatorname{supp}u_1=\{e_1,-e_1\},\quad u_1(0)=0`,R`|e_1|=|-e_1|=1\ \Longrightarrow\ |n|^{-2m}=1\ \text{on the support}`]
};
enrichedYeRows[1200]=[0,1,3,4];
export const formulaRowsForYe=p=>enrichedYeRows[p.editorialIndex]?.flatMap(tex=>typeof tex==='number'?[equationLines(p.tex)[tex]]:tex==='original'?equationLines(p.tex):[tex])||equationLines(p.tex);
