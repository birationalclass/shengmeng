# Milestone 17 — actual local evaluation, perfect pairing and fiber determinants

The exact relative Jacobian goal remains proved. The global Linearity Theorem remains UNPROVED. The manuscript is unchanged.

`LocalResidueEvaluation.lean` constructs the actual reduction A/(τ)→ℂ, identifies its kernel with the image of nilrad(A), and proves finite-dimensionality of the actual quotient. From the original finite flat regular complete-intersection hypotheses and any allowed parameter lifts, it constructs a normalized linear functional and a perfect multiplication pairing with

ρ(δ)=1, ρ([h]δ)=constantCoeff(q(h)).

No extra local pairing or socle conclusion is assumed. The functionals constructed here are not claimed to be globally compatible Grothendieck residues. Independent local normalization does not establish an Euler–Jacobi sum theorem.

`LocalFiberJacobian.lean` uses actual mathlib derivations and quotient homomorphisms. If pᵢ∈I and Hᵢ−u⁻¹pᵢ∈I² for a unit u, Leibniz and determinant scaling give

[det(DH)]=[u⁻¹]ᶜ[det(Dp)].

Nonvanishing and annihilation transfer along that unit factor. These first-order equation data are explicit; the smooth-chart/completed local-ring comparison providing them is still open.

The two new modules contain 18 project proofs and 3 definitions. The entire build and exact-type/axiom audit pass without sorryAx or custom axioms. The frozen audit, compiler declaration ranges and exported source hashes provide the actual counts and scopes.

Library reuse and discovery: `Module.Projective.exists_dual_eq_one`, nilpotent-kernel finiteness, actual derivation Leibniz rules, ideal-product induction and `RingHom.map_det`. See `research/GLOBAL_BRIDGE_SEARCH_20261007.md` for pinned source inspection and official-documentation provenance. New local algebra is not substituted for the missing global geometric inputs.

Next obligations remain the canonical global residue and its low-degree sum vanishing, actual projective-fiber comparison, geometric Koszul/proper-duality/Serre lifting, Cartier/Bézout estimates and the exact Scheme/coordinate comparison.
