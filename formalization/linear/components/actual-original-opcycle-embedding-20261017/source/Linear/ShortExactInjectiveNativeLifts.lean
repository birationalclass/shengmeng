module
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u v
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- CONSTRUCT actual natural-indexed lifts of EVERY actual coefficient
cocycle. No chosen lift or target class equality is supplied. -/
theorem shortExactInjectiveNativeLifts_exists
    (S : ShortComplex A) (hS : S.ShortExact) {N : A} (I : InjectiveResolution N)
    (q : ℕ) (a : S.X₁ ⟶ I.cocomplex.X q) (ha : a ≫ I.cocomplex.d q (q+1) = 0) :
    ∃ (b : S.X₂ ⟶ I.cocomplex.X q) (c : S.X₃ ⟶ I.cocomplex.X (q+1)),
      S.f ≫ b = a ∧ b ≫ I.cocomplex.d q (q+1) = S.g ≫ c ∧
      c ≫ I.cocomplex.d (q+1) (q+1+1) = 0 := by
  letI : Mono S.f := hS.mono_f
  letI : Epi S.g := hS.epi_g
  let b := Injective.factorThru a S.f
  have hb : S.f ≫ b = a := Injective.comp_factorThru a S.f
  have hz : S.f ≫ (b ≫ I.cocomplex.d q (q+1)) = 0 := by rw [← Category.assoc,hb,ha]
  let c := hS.exact.desc (b ≫ I.cocomplex.d q (q+1)) hz
  have hc : S.g ≫ c = b ≫ I.cocomplex.d q (q+1) := hS.exact.g_desc _ _
  refine ⟨b,c,hb,hc.symm,?_⟩
  apply (cancel_epi S.g).1
  rw [← Category.assoc,hc,Category.assoc,I.cocomplex.d_comp_d,comp_zero,comp_zero]

end LinearStudy
