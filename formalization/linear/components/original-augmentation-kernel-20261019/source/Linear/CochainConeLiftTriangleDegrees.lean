module
public import Linear.CochainConeLiftDerivedAllDegrees
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
open CochainComplex.HomComplex
universe u v d
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{d} A]

/-- Keep the specified target degree while transporting the native cone formula. -/
theorem cochainConeLiftTriangle_degrees
    (S : ShortComplex (CochainComplex A ℤ)) (K : CochainComplex A ℤ)
    (q r : ℤ) (hqr : q+1=r)
    (a : Cocycle S.X₁ K q) (b : Cochain S.X₂ K q) (c : Cocycle S.X₃ K r)
    (hb : (Cochain.ofHom S.f).comp b (zero_add q) = a.val)
    (hc : δ q r b = (Cochain.ofHom S.g).comp c.val (zero_add r)) :
    ShiftedHom.map (Cocycle.equivHomShift.symm
      (c.precomp (CochainComplex.mappingCone.descShortComplex S))) DerivedCategory.Q =
      ShiftedHom.map (r.negOnePow • ShiftedHom.comp
        (CochainComplex.mappingCone.triangle S.f).mor₃
        (Cocycle.equivHomShift.symm a) hqr) DerivedCategory.Q := by
  subst r
  exact cochainConeLiftTriangle_allDegrees S K q a b c hb hc

end LinearStudy
