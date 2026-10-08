module
public import Linear.FieldEndomorphismMap
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.Finrank
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy

/-- Actual image-field degrees multiply under composition. The scalar
tower uses the actual inclusion of the composite image in the outer image. -/
theorem fieldEndomorphism_finrank_comp
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (φ ψ : L →ₐ[K] L) :
    Module.finrank (ψ.comp φ).fieldRange L =
      Module.finrank ψ.fieldRange L * Module.finrank φ.fieldRange L := by
  let S := φ.fieldRange
  let E := ψ.fieldRange
  let F := (ψ.comp φ).fieldRange
  have hFE : F ≤ E := by
    rintro z ⟨a, rfl⟩
    exact ⟨φ a, rfl⟩
  let ν := IntermediateField.inclusion hFE
  letI : Algebra F E := ν.toRingHom.toAlgebra
  letI : SMul F E := ν.toRingHom.toAlgebra.toSMul
  letI : Module F E := Algebra.toModule
  letI : IsScalarTower F E L := IsScalarTower.of_algebraMap_eq (fun z => rfl)
  let u : S →ₐ[K] F := (ψ.comp S.val).codRestrict F.toSubalgebra (by
    rintro ⟨z, a, rfl⟩
    exact ⟨a, rfl⟩)
  have hu : Function.Bijective u := by
    refine ⟨u.injective, ?_⟩
    rintro ⟨z, a, rfl⟩
    exact ⟨⟨φ a, ⟨a, rfl⟩⟩, rfl⟩
  let i := AlgEquiv.ofBijective u hu
  let j := ψ.equivFieldRange
  have hc : (algebraMap F E).comp i.toRingEquiv.toRingHom =
      j.toRingEquiv.toRingHom.comp (algebraMap S L) := by
    apply RingHom.ext
    intro z
    apply Subtype.ext
    rfl
  have hr : Module.finrank S L = Module.finrank F E :=
    Algebra.finrank_eq_of_equiv_equiv i.toRingEquiv j.toRingEquiv hc
  calc
    Module.finrank F L = Module.finrank F E * Module.finrank E L :=
      (Module.finrank_mul_finrank F E L).symm
    _ = Module.finrank E L * Module.finrank S L := by rw [← hr, Nat.mul_comm]

theorem fieldEndomorphism_finrank_one
    {K L : Type*} [Field K] [Field L] [Algebra K L] :
    Module.finrank (1 : L →ₐ[K] L).fieldRange L = 1 := by
  let E := (1 : L →ₐ[K] L).fieldRange
  let u : E →ₐ[E] L := Algebra.ofId E L
  have hu : Function.Bijective u := by
    refine ⟨u.injective, ?_⟩
    intro z
    exact ⟨⟨z, ⟨z, rfl⟩⟩, rfl⟩
  let e := AlgEquiv.ofBijective u hu
  exact e.toLinearEquiv.finrank_eq.symm.trans (Module.finrank_self E)

/-- The degree of each ACTUAL iterated field endomorphism, not a
separately supplied extension, is the power of its original degree. -/
theorem fieldEndomorphism_finrank_pow
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (φ : L →ₐ[K] L) (k : ℕ) :
    Module.finrank (φ ^ k).fieldRange L =
      (Module.finrank φ.fieldRange L) ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    exact fieldEndomorphism_finrank_one (K := K) (L := L)
  | succ k ih =>
    rw [pow_succ']
    change Module.finrank (φ.comp (φ ^ k)).fieldRange L = _
    rw [fieldEndomorphism_finrank_comp, ih, pow_succ']

end LinearStudy
