# Actual native monomial multiplication is transpose on top Cech homology

Let K be a field, sigma a finite ordered coordinate set with card(sigma)=r+1,
r>=1, and l,m>=0. Let P=Proj K[sigma], T(k) its original integer twist
defined by locally homogeneous fractions, and X^b an actual degree-l
monomial with coefficient1. The original sheaf multiplication
T(-(l+m)-r-1)->T(-m-r-1), passed through the ACTUAL Cech functor, induces
the transpose of actual homogeneous polynomial multiplication
S_m->S_(l+m) under the previously proved native top Cech duality.

The pairing extracts the coefficient complementary to c, with exponent
-c_i-1. Actual monomial Laurent multiplication shifts exponents by b,
so the shifted residue at c equals the original residue at b+c.
The proof starts with actual cochain maps and actual polynomial ring
products. Their compatibility descends through the already proved
actual boundary kernel, the actual quotient map and mathlib homology
functors. No multiplication or homology map is defined by duality
transport. Integer-degree equality transports are explicit and proved.
The original native/Laurent comparison commutes with multiplication
on the full complexes and actual homology, giving the final transpose
square for the originally constructed sheaf multiplication.

This is actual Cech homology, not a comparison with derived sheaf
cohomology. General polynomial extension, finite graded-presentation
duality and actual Koszul connecting-map/restriction compatibility
remain OPEN. Original4.1 canonical normalized-dualizing identification
remains UNVERIFIED. Original4.1/4.2 and the main theorem remain OPEN.
The original manuscript hypotheses and indices are unchanged. No
normality, smoothness or Cohen-Macaulay hypothesis is added to V.

20 new modules; 1039 physical source lines; 65 audited
declarations (46 proofs and 19 definitions).
112 closed modules; 92 older dependencies
match previously frozen bytes. Exact types and transitive axioms are
included: only propext, Classical.choice, Quot.sound. Every compile
and audit uses lean_runner.run_file, one compiler, 8GiB Job memory,
two Lean threads, CPU<=25%, twenty-minute wall timeout. No whole-project
checkpoint/CI verification is asserted; checkpoint180 stays the latest
whole-project locally accepted checkpoint.

Pinned Lean v4.35.0-rc3; mathlib2a885768dae569d938bb9ff3474da6a8753bb90a.
Original manuscript SHA256:
503864b699ae2b315ff857a57f33fb1d722ab53f331040ae6afafcd2e691ef2a.
Compile the closed modules in dependency order, then CheckAxioms.lean.
Linear.lean is the convenience entry. Previous Apache2.0 attribution
is preserved. No downloaded setup program is executed.
