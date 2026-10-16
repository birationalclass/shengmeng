# ORIGINAL Koszul epsilon:ACTUAL iterated native source boundary

LET A be abelian,K an ACTUAL complex with K^j=0 for j>0,
alpha:K->E[0] an ACTUAL quasi-isomorphic augmentation,r>=1,
a:K^(-r)->N with d*a=0. Let Q_j=opcycles(K,j),and let
S_j=(Q_j -> K^(j+1) -> Q_(j+1)),j=-r,...,-1.
THEN source exactness and short exactness of EVERY S_j are DERIVED
from alpha. CONSTRUCT eta:Q_0->E from SAME augmentation and PROVE
it is an isomorphism. Descend SAME top functional to abar:Q_(-r)->N.
For the ACTUAL native contravariant Ext boundaries prove
 delta_(S_-1)^(r-1) ... delta_(S_-r)^0 (Ext.mk0 abar)
   = (Ext.mk0 eta).comp ORIGINAL epsilon_alpha(a).
The implementation retains canonical endpoint equality transport.
No source lift,recurrence,representative,class identity,desired square,
global projectivity or chosen source quotient identification is supplied
in the FINAL identity. A coefficient injective resolution suffices in
the abstract theorem;native enough injectives and standard Ext/derived
prerequisites are constructed for the scheme-module application.

CONSTRUCT the SAME actual representative c and source homotopy t.
Extract top/middle/bottom components and prove the normalization
 b_j = ((-1)^((r+1)*j))*t_j.
It gives POSITIVE lifting equations with SAME original top functional
and SAME terminal cocycle,no residual bottom sign. Construct EVERY
quotient cocycle,prove closure,compute EVERY native Ext.delta and
iterate. The initial actual cocycle represents EXACT native Ext.mk0;
the terminal actual cocycle is EXACT pullback of SAME epsilon.
The native Ext.delta sign convention is preserved,not redefined.

Specialize to SAME ORIGINAL nonnegative chain via native n->-n
embedding and SAME ordered top functional. Apply to SAME original
geometric Koszul complex C_w(k),whole-cut target E=i_*O_Zw(k),and
coefficient N=O_V(k-r*q). For original Setup with 0<r<n,positive
surjective homogeneous f,V integral/invariant,linear normalization
injective/finite,and ACTUAL point x0 on original X0 chart,DERIVE
ONE NONEMPTY parameter open U=D(u) BEFORE ALL integer k.
For every w in U and every k,DERIVE e,alpha,quasiiso,alpha0=pi*e
and SAME original class/native iterated-source equality.
u is a PARAMETER equation,not the final fixed-degree polynomial Q.

54exact declarations:38ordinary theorems,1ACTUAL proof-term definition,
15checked objects/statement definitions(NOT proofs).26individually
compiled roots;ALL full imported types,16definition bodies,standard
axiom closures and semantic roles manually reviewed.Only propext,
Classical.choice,Quot.sound.575nonroot modules byte-match the earlier
PUBLIC E/F/coefficient archives;8native sources match PINNED Git
bytes. Fresh compiler ranges/edges for26newroots;reuse prior PUBLIC
metadata only after live hashes and SAME archived source bytes match.
No whole-project replay or new remote whole-project Lean CI claimed.

This CLOSES the ORIGINAL arbitrary-positive-r source-boundary class
identification after the canonical augmentation quotient iso.
OPEN:connecting square for actual global-to-internal lambda,actual
internal-SHEAF-Ext/local-MODULE-Ext comparison,a|S restriction/support,
global-to-local isomorphism,proper duality/canonical theta,ambient
pullback twist,and UNIFORM fixed m.Original4.1/4.2/main STILL OPEN.
Keep1<=r<n,d>=2,ONE NONEMPTY parameteropen BEFORE ALLintegerk,
and parameteru/c distinct from finalQ.Unverified4.1interface NOTaxiom.
Local freeness is not global projectivity;Hom fullfaithfulness is not
an Ext comparison.GLOBAL Ext,INTERNAL SHEAF Ext,MODULE Ext distinct.

AlltaskfilesD;onecompiler,8GiBWindowsJob,2threads,CPU25%,BelowNormal,
20min,allRAM/commit/disk limits and ALL87holds retained.No extra agents,
raisedlimits or OSchanges.Wholelocalcheckpoint180;181notaccepted.
Lean4.35.0-rc3,pinnedmathlib2a885768dae569d938bb9ff3474da6a8753bb90a.
