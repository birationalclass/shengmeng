module

/-
Third-party source: Vilin97/Autoformalization, Apache-2.0.
Pinned upstream commit: 09497ebf6ee48ef49c4f3d24501954bc3a2855d6.
Original path: coherent-cohomology-finite/CoherentCohomologyFinite/ProjectiveLaurentCechComplex.lean
Local adaptation: imports relocated to Negativity.External.Laurent.
-/
public import Negativity.External.Laurent.ProjectiveLaurentCechComplexFiniteness
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

@[expose] public section

/-!
# The Laurent Čech differential as a `CochainComplex`

The combinatorial development uses explicit linear maps because that
presentation is convenient for exponentwise calculations.  This file
packages the same data in Mathlib's categorical homological-complex API,
which is the interface used by acyclic-resolution comparison.
-/

open CategoryTheory

set_option autoImplicit false

namespace LeanEval.AlgebraicGeometry.ProjectiveLaurentCech

variable {ι R : Type*} [Fintype ι] [LinearOrder ι]

/-- The explicit Laurent Čech cochains and differential, bundled as a
cochain complex of modules. -/
noncomputable def laurentCechComplex
    [CommRing R] (d : ℤ) :
    CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of
    (fun q => ModuleCat.of R (Cochain (ι := ι) R d q))
    (fun q => ModuleCat.ofHom (differential (ι := ι) (R := R) d q))
    (fun q => by
      apply ModuleCat.hom_ext
      exact differential_comp (ι := ι) (R := R) d q)

@[simp]
lemma laurentCechComplex_X
    [CommRing R] (d : ℤ) (q : ℕ) :
    (laurentCechComplex (ι := ι) (R := R) d).X q =
      ModuleCat.of R (Cochain (ι := ι) R d q) :=
  rfl

@[simp]
lemma laurentCechComplex_d
    [CommRing R] (d : ℤ) (q : ℕ) :
    (laurentCechComplex (ι := ι) (R := R) d).d q (q + 1) =
      ModuleCat.ofHom (differential (ι := ι) (R := R) d q) := by
  simp [laurentCechComplex, CochainComplex.of_d]

@[simp]
lemma laurentCechComplex_d_apply
    [CommRing R] (d : ℤ) (q : ℕ)
    (c : Cochain (ι := ι) R d q) :
    (laurentCechComplex (ι := ι) (R := R) d).d q (q + 1) c =
      differential (ι := ι) (R := R) d q c := by
  rw [laurentCechComplex_d]
  rfl

end LeanEval.AlgebraicGeometry.ProjectiveLaurentCech
