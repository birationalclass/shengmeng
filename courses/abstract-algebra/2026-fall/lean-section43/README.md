# Lean formalization of Section 4.3: Unique factorization domains

This project formalizes the **abstract algebra course's Section 4.3** in
[birationalclass/shengmeng](https://github.com/birationalclass/shengmeng).

The authoritative source used here is
[4.3.json](https://github.com/birationalclass/shengmeng/blob/9731fa5be382757611d4401c9cb5cb7cf66df4d4/courses/abstract-algebra/2026-fall/lesson-groups/sections/4.3.json), at repository commit
`9731fa5be382757611d4401c9cb5cb7cf66df4d4`.
The course entries cite textbook PDF pages 199–209.
No course webpage, textbook source, or pre-existing Lean theorem was changed.

## Files and coverage

There are 60 named theorem declarations across three source files. Familiar general
results reuse mathlib proofs; the concrete quadratic-ring counterexample includes
explicit norm calculations and a norm-descent proof.

| Course entry | Lean declarations | File |
| --- | --- | --- |
| Divisibility, Definition/Theorem 4.3.1 | `divides_iff`, `divides_trans`, `divides_linear_combination` | `Section43/Basic.lean` |
| Associates, Definition/Theorem 4.3.2 | `associated_iff_mutual_divisibility`, `principal_ideals_eq_iff`, `associated_iff_unit_multiple`, `association_equivalence` | `Section43/Basic.lean` |
| Prime implies irreducible, Theorem 4.3.3 | `prime_is_irreducible` | `Section43/Basic.lean` |
| Quadratic norm, Theorem 4.3.4 | `Quadratic.absNorm_formula`, `absNorm_mul`, `absNorm_eq_zero_iff`, `absNorm_eq_one_iff`, `absNorm_dvd_of_dvd` | `Section43/Quadratic.lean` |
| Failure of uniqueness in ℤ[√−3] | `MinusThree.two_factorizations`, all three irreducibility proofs, pairwise nonassociation proofs, `two_not_prime`, `not_uniqueFactorizationMonoid` | `Section43/Quadratic.lean` |
| UFD definitions 4.3.6–4.3.7 | `factorization_exists`, `factorization_unique`, `ufd_iff_unique_factorization`, `standard_factorization_exists` | `Section43/Basic.lean` |
| Irreducible iff prime, Theorem 4.3.5 | `irreducible_iff_prime` | `Section43/Basic.lean` |
| Proper-divisor chains, Theorems 4.3.6–4.3.7 | `no_infinite_proper_divisor_chain`, `ufd_iff_no_infinite_chain_and_prime_irreducibles` | `Section43/Basic.lean` |
| Gcd, Theorem 4.3.8 | `gcd_exists`, `gcd_unique_up_to_association`, `gcd_prime_exponent`, `gcd_zero` | `Section43/Basic.lean` |
| Relatively prime elements, Theorem 4.3.9 | `relatively_prime_iff_unit_gcd`, both divisibility rules, `relatively_prime_gcd_product` | `Section43/Basic.lean` |
| Examples and exercises | Integer/rational divisibility, factorization of 60, gcd(72,120), Gaussian associates, relatively prime 2 and X without Bézout | `Section43/Examples.lean` |

Names in `Basic.lean` have prefix `Section43`. Names in the other files have
prefixes `Section43.Quadratic`, `Section43.MinusThree`, and `Section43.Examples`.
The extra theorem `MinusThree.irreducible_factorization_exists` proves that
factorizations exist in the counterexample ring, although they are not unique.
The ring is explicitly proved to be an integral domain.

## Interpretation of the source

- `UniqueFactorizationMonoid R` with `CommRing R` and `IsDomain R` expresses UFD.
  Its equivalence with existence and uniqueness of irreducible multisets is proved,
  so the course definition is not merely assumed to match the library definition.
- `Associated` means equality up to a unit. Multisets remove the order of factors;
  `Multiset.Rel Associated` expresses matching individual factors up to units.
- `standard_factorization_exists` has a finite set of pairwise nonassociate
  irreducibles, strictly positive exponents, and an explicit unit. A normalization
  is chosen inside the proof; its existence is not an additional hypothesis.
- `Quadratic.absNorm` is `Int.natAbs` of mathlib's signed quadratic norm. The
  zero-norm theorem retains squarefreeness and `d ≠ 1`; the course's `d ≠ 0`
  already follows from squarefreeness.
- `DvdNotUnit a b` means `a ≠ 0` and `b = a*c` for a nonunit `c`. In a domain it
  is equivalent to `a ∣ b` and `¬ b ∣ a`. It permits a unit at the end of a finite
  descending chain, which does not affect the no-infinite-chain criterion.
- `gcd_prime_exponent` uses extended multiplicity `ℕ∞`, so zero arguments are
  handled correctly. For nonzero arguments and an irreducible prime, these
  exponents are finite and give the course's usual minimum formula.
- Coprimality is `IsRelPrime`, meaning every common divisor is a unit. The stronger
  Bézout predicate `IsCoprime` is deliberately distinguished and refuted for the
  example `(2, X)` in `ℤ[X]`.

## Reproduce the checks

The project pins Lean `v4.35.0-rc3` and mathlib commit
`2a885768dae569d938bb9ff3474da6a8753bb90a`.

```sh
lake build
lake env lean Audit.lean
```

Install [elan](https://github.com/leanprover/elan) and make `lake` available on PATH.
The toolchain and complete dependency revisions are pinned in `lean-toolchain`
and `lake-manifest.json`. On a fresh checkout, run `lake exe cache get` before
building. A local dependency-cache symlink used during development is ignored by
Git and is not required on another machine.

`Audit.lean` enumerates every exported declaration under `Section43`, including
definitions, instances, and generated declarations. It fails on any axiom other
than `propext`, `Classical.choice`, or `Quot.sound`. This excludes `sorryAx`, custom
axioms, and compiler-trusting decision axioms. Build and audit outputs are saved
in `verification/build.log` and `verification/axioms.log`. The successful build
completed 1505 jobs; the audit checked 72 declarations. `verification/manifest.json`
records the SHA-256 hashes of the checked Lean sources.

The build may report unused-domain-hypothesis style warnings: these hypotheses
are intentionally retained to match the course's domain setting. They are not
unproved goals. The formal proofs contain no `sorry`, `admit`, `axiom`, or
`native_decide` declarations. Verification concerns the statements listed above;
it does not claim a line-by-line transcription of every informal proof sentence
or independent verification of the textbook page attribution.
