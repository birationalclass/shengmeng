# Checkpoint 107: actual generic linear-section cardinality equals Hilbert degree

Pinned mathlib: `2a885768dae569d938bb9ff3474da6a8753bb90a`.

Online original mathlib documentation was consulted:

- [Finsupp/Multiset](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finsupp/Multiset.html): `Sym.equivNatSumOfFintype`.
- [Polynomial/HilbertPoly](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Polynomial/HilbertPoly.html): pre-Hilbert polynomial coefficients and evaluation.
- The online `Data/Sym/NatCard.html` request failed; the pinned local source supplies `Sym.natCard_sym_eq_choose`. The exact pinned implementations and full hypotheses were read before reuse.

No applicable already combined original-V section/degree entry was found in the focused searches. The uncovered bridges use existing mathlib bases, symmetric-power counts, Hilbert polynomials and polynomial-ratio limits:

1. A slack exponent identifies actual monomials of total degree at most N with a symmetric power. The actual source filtration has dimension `choose(N+s,s)`.
2. Two-sided filtered growth for the **same** actual linear projection forces its generic rank to equal the ratio of actual leading coefficients.
3. The actual cumulative coordinate filtration and actual homogeneous-piece Hilbert polynomial have the same factorial-normalized leading coefficient.
4. `projective_exists_linear_section_hilbert_degree` derives from the original V alone a positive natural d with `d = r! * leadingCoeff(P)` and actual generic section cardinality d.

The equality is proved, not made true by changing the definition of projective degree. Full mathematical types and standard-axiom compiler logs bind each exact private source hash.

Still open: simultaneous original-f good target selection and transversality, global Scheme comparison, actual Section 4 fixed-degree lifting, actual geometric intersection and the full Linearity Theorem.
