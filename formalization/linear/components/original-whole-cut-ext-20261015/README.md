# Original whole-cut global derived Ext class and coefficient formula

LET f be the original positive-degree surjective homogeneous endomorphism
of projective space over C,V the original integral invariant variety,r<n,
and L0,...,Lr the SAME degree-one forms inducing an injective finite ring
normalization. Let x0=[1:x1:...:xn] be an actual point of V.
Put S=C[X0,...,Xn]/I_V,H_i=f*(w0 L_i-w_i L0),1<=i<=r,
Z_w the WHOLE original projective cut,i:Z_w->V the original embedding,
C=C_w(k) the SAME original native global weighted Koszul complex,
T=i_*native O_Zw(k),M=native O_V(k-r*q).

THEN derive cone dimension r+1,actual chart dimension r,and I_V nonzero
FROM THE SAME chosen finite injective map and original r<n.
Derive ONE NONEMPTY parameter open D(c) BEFORE EVERY integer k.
For every w in D(c) and every integer k,derive an actual e:coker(d1)~=T
and quasi-isomorphic actual quotient augmentation alpha:C->T[0],
alpha_0=pi followed by e.hom. No dimension,nonzero-ideal,source exactness,
desired target comparison,Ext class or desired coefficient law is added
as a premise in this original geometric family.

Construct the ACTUAL original top exterior-basis map phi:C_r~=M and
prove its top cocycle condition from above-rank vanishing. Construct
an actual GLOBAL derived Ext class eps_alpha in Ext_V^r(T,M) in the
actual scheme-module category,using the native derived roof and SAME
original augmentation. Prove for EVERY coefficient module sheaf N and
g:M->N: push_g(eps_alpha) is the class of phi followed by g.
At t=r*q-r-1 the actual coefficient twist is native O_V(-r-1).
The final geometric family retains the derived e,quasiiso and formula,
on ONE NONEMPTY open BEFORE ALL k. c defines the parameter open;
it is NOT original4.2's uniform fixed-degree polynomial Q.

Reuse mathlib Ext.homEquiv,derived Q and actual inverse of Q(alpha),
native toSingle cocycles and n->-n embedding preserving differentials.
Construct standard HasExt/derived category at an abstract boundary.
No global locally free sheaf is assumed projective. Generic arbitrary
HasExt/derived versions retain their explicit API prerequisites.
The explicit standard geometric application has no such added premise.
This is GLOBAL Ext in scheme modules,NOT an internal SHEAF Ext comparison.

40 declarations in18roots:16 ordinary theorem declarations,7 actual
proof-term definitions and17 object/statement constructions=23proofs.
All40 full types,axioms andALL24 definition bodies manually read.
Lean Meta.isProp independently verifies all semantic roles. Only
propext,Classical.choice,Quot.sound are used;one logic theorem uses none.
Object constructions of Ext elements are NOT extra theorem proofs.

OPEN: identification with the manuscript's successive connecting
boundary;internal SHEAF Ext and local support/restriction comparison;
proper duality/canonical theta;canonical geometric augmentation and
ambient pullback-twist comparisons;uniform fixed-m section production.
Original Lemmas4.1/4.2 and main theorem remain OPEN,last whole180.
The authorized temporary unverified4.1 interface is NOT used to label it
proved. Original Setup1<=r<n,d>=2 is preserved;the present bridge needs
only r<n andq>0 of those inequalities. Earlier explicit dimension and
nonzero-ideal inputs are now DISCHARGED for that Setup.

All18 roots actually compiled unchanged via lean_runner.run_file;
full imported type/body/role/axiom audit passed at4905.2MiB.
The seven newly compiled roots have max6417.9MiB;actual geometric
coefficient-law family4935.9MiB. These are observations,not guarantees.
All69holds retained;failed e8a source excluded and never retried.
The changed architecture keeps the SAME original named complex as
source and passes its quasiiso explicitly at an abstract boundary;
it does not convert a concrete augmentation into a differently named
native source while synthesizing HasExt. No caps raised,no new agents.
One8GiBhardJob,2threads,CPU25%,20min. Persistent artifactsD.
Lean4.35.0-rc3;mathlib2a885768dae569d938bb9ff3474da6a8753bb90a.
Non-root dependency bytes match prior public frozen archives. No separate
full replay AFTER freezing,no full-project or remote Lean CI claim.
Original library author/license headers are retained.
