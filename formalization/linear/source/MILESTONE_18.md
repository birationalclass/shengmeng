# Milestone 18 — global finite polynomial pairing and diagonal normalization

The full Linearity Theorem remains UNPROVED. The exact local Lemma31Goal remains proved. The manuscript has not been changed.

The new theorem `polynomialQuotient_perfectPairing` starts with n+1 regular polynomials over an infinite algebraically closed field and the actual finite-dimensional quotient K[X]/(P). It constructs a perfect multiplication pairing. No local-ring, preselected pairing or socle-generation conclusion is supplied as a hypothesis.

The proof constructs every maximal residue map to K, identifies its kernel with the ideal of translated coordinates, proves a nonzero cyclic maximal socle by the already checked Koszul comparison, and chooses a functional simultaneously nonzero on all the finitely many maximal socles. Every nonzero ideal meets a maximal socle, so multiplication into the dual is injective and hence bijective in finite dimension.

`PolynomialRegular.lean` constructs coordinate translation and its inverse, and proves that the variables and their translates form regular sequences in the actual polynomial ring. `ArtinianGlobalPairing.lean` removes locality from the maximal-socle nonvanishing and pairing construction. These statements use actual mathlib associated primes and vector-space duality.

`PolynomialFiberDiagonal.lean` constructs a difference matrix in the tensor square of the actual polynomial quotient. Its determinant annihilates the actual Kähler diagonal ideal and maps under multiplication to the derivative Jacobian, without assuming regularity, finite-dimensionality or locality.

`DiagonalNormalization.lean` and `GlobalDiagonalNormalization.lean` prove that a diagonal-annihilator tensor with explicit nonzero right reduction at every maximal ideal uniquely determines a normalized functional. A normalized pairing then satisfies the actual algebraic trace identity. The auxiliary starting pairing is used to prove existence and uniqueness, rather than being part of the normalization equation.

Important remaining input: nonzero reductions for the specific constructed polynomial difference tensor have not yet been proved. No low-degree vanishing is claimed, and the normalized functional has not been identified with a global geometric Grothendieck residue. The next steps are the actual tensor nondegeneracy, polynomial degree bounds and Euler–Jacobi relation, followed by the geometric comparison and lifting obligations.

Online and pinned-source reuse inspected: Mathlib.RingTheory.Ideal.AssociatedPrime.Basic and Localization; Algebra.Module.Submodule.Union (`Module.exists_dual_forall_apply_ne_zero`); actual polynomial equivalences and constant-coefficient quotients; IsAlgClosed.algebraMap_bijective_of_isIntegral; tensor/endomorphism equivalences and multiplication trace. Exact types, dependencies, compiler source ranges and allowed axioms are exported by the audit.
