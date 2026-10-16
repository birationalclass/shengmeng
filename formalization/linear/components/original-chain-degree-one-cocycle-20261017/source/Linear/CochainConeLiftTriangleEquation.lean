module
public import Linear.CochainConeLiftDerivedBridge
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
open CochainComplex.HomComplex
universe u v d
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{d} A]

/-- Compute the ACTUAL native cone triangle map from actual cochain lift equations.
The MINUS is proved;no desired Ext-class identity or replacement boundary is a premise. -/
theorem cochainConeLiftTriangleEquation
    (S : ShortComplex (CochainComplex A ℤ)) (K : CochainComplex A ℤ)
    (a : S.X₁ ⟶ K) (b : Cochain S.X₂ K 0) (c : Cocycle S.X₃ K 1)
    (hb : (Cochain.ofHom S.f).comp b (zero_add 0) = Cochain.ofHom a)
    (hc : δ 0 1 b = (Cochain.ofHom S.g).comp c.val (zero_add 1)) :
    DerivedCategory.Q.map (CochainComplex.mappingCone.triangle S.f).mor₃ ≫
        (Functor.commShiftIso DerivedCategory.Q (1 : ℤ)).hom.app S.X₁ ≫
        (shiftFunctor (DerivedCategory A) (1 : ℤ)).map (DerivedCategory.Q.map a) =
      -(DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex S)) ≫
        ShiftedHom.map (Cocycle.equivHomShift.symm c) DerivedCategory.Q := by
  have h := cochainConeLiftDerivedBridge S K (Cocycle.ofHom a) b c hb hc
  simp only [Cocycle.homOf_ofHom_eq_self,Cocycle.equivHomShift_symm_postcomp,
    Cocycle.equivHomShift_symm_precomp,ShiftedHom.map,
    CategoryTheory.Functor.map_comp,Category.assoc] at h
  erw [(Functor.commShiftIso DerivedCategory.Q (1 : ℤ)).hom.naturality a] at h
  rw [cochainConeTriangle_mor3_neg_fst]
  simp only [map_neg,CategoryTheory.Functor.map_neg,Preadditive.neg_comp,
    ShiftedHom.map,Category.assoc]
  exact congrArg (fun f => -f) h

end LinearStudy
