module
public import Linear.ShortExactInjectiveBoundaryComponents
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u v w
variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]

/-- Compute native Ext.delta on SAME natural-indexed coefficient cocycles;
retain the actual native injective-resolution Ext.extMk constructor. -/
theorem shortExactInjectiveExtBoundary_nativeComponents
    (S : ShortComplex A) (hS : S.ShortExact) {N : A} (I : InjectiveResolution N)
    (q : ℕ) (a : S.X₁ ⟶ I.cocomplex.X q) (ha : a ≫ I.cocomplex.d q (q+1) = 0)
    (b : S.X₂ ⟶ I.cocomplex.X q)
    (c : S.X₃ ⟶ I.cocomplex.X (q+1)) (hc : c ≫ I.cocomplex.d (q+1) (q+1+1) = 0)
    (hb : S.f ≫ b = a) (hbc : b ≫ I.cocomplex.d q (q+1) = S.g ≫ c) :
    Ext.δ hS q (q+1) rfl (I.extMk a (q+1) rfl ha) = I.extMk c (q+1+1) rfl hc := by
  dsimp only [InjectiveResolution.extMk]
  apply shortExactInjectiveExtBoundary_components S hS I q _ _
    (b ≫ (I.cochainComplexXIso (q : ℤ) q rfl).inv) _ _
  · simp only [← Category.assoc,hb]
  · simp only [I.cochainComplex_d (q : ℤ) ((q+1 : ℕ) : ℤ) q (q+1) rfl rfl,
      Category.assoc,Iso.inv_hom_id_assoc]
    simpa only [Category.assoc] using congrArg
      (fun z => z ≫ (I.cochainComplexXIso ((q+1 : ℕ) : ℤ) (q+1) rfl).inv) hbc

end LinearStudy
