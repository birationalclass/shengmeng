module
public import Linear.AffineKoszulActualSheafExtTop
public import Linear.SchemeModuleOriginalTopExtClassIsoLaw
public import Linear.AffineKoszulHomGeometricCokernel
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 5000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local irreducible] schemeModuleHomPrecompose schemeModuleHomModuleSheaf
  affineKoszulHomGeometricCokernelIso
/-- SAME original quotient-cofork and actual derived SHEAF Ext, computed
by SAME original top differential-Hom cokernel. All positive source-term
Ext vanishings and above-rank zero are DERIVED from original Koszul bases.
I is any actual coefficient injective resolution, not an Ext comparison. -/
def affineKoszulOriginalSheafExtCokernelIso (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (p : ℕ) (H : Fin (p+1) → R)
    (he : ∀ j : ℕ,0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j)
    (I : InjectiveResolution (tilde N)) :
    schemeModuleInternalExt (tildeKoszulOriginalCutCokernelCofork R H).pt (tilde N) (p+1) ≅
      cokernel (schemeModuleHomPrecompose (X:=Spec R) (N:=tilde N)
        ((tildeFunctionKoszulComplex R H).d (p+1) p)) :=
  schemeModuleOriginalWholeTopCokernelIso (tildeFunctionKoszulComplex R H) (tilde N) p
    (originalChainCoforkAugmentation (tildeFunctionKoszulComplex R H)
      (tildeKoszulOriginalCutCokernelCofork R H))
    (tildeKoszulCoforkAugmentation_quasiIso_of_exact R H he) I
    (tildeFunctionKoszul_sourceInternalExtAcyclic R H (tilde N))
    (tildeFunctionKoszul_isZero_above_rank R H (p+2) (by omega))
/-- Prove the exact all-representative law for SAME original affine
quotient roof and SAME constructed Ext/cokernel iso. The named law keeps
concrete module-sheaf category reductions bounded; its full body records
the actual canonical lambda and original class for every functional. -/
theorem affineKoszulOriginalSheafExtCokernelIso_classLaw (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (p : ℕ) (H : Fin (p+1) → R)
    (he : ∀ j : ℕ,0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j)
    (I : InjectiveResolution (tilde N)) :
    schemeModuleOriginalTopExtClassIsoLaw (tildeFunctionKoszulComplex R H) (p+1)
      (originalChainCoforkAugmentation (tildeFunctionKoszulComplex R H)
        (tildeKoszulOriginalCutCokernelCofork R H))
      (tildeKoszulCoforkAugmentation_quasiIso_of_exact R H he)
      (affineKoszulOriginalSheafExtCokernelIso R N p H he I)
      (cokernel.π (schemeModuleHomPrecompose (X:=Spec R) (N:=tilde N)
        ((tildeFunctionKoszulComplex R H).d (p+1) p))) :=
  schemeModuleOriginalTopExtClassIsoLaw_wholeCokernel (tildeFunctionKoszulComplex R H) p
    (originalChainCoforkAugmentation (tildeFunctionKoszulComplex R H)
      (tildeKoszulOriginalCutCokernelCofork R H))
    (tildeKoszulCoforkAugmentation_quasiIso_of_exact R H he) I
    (tildeFunctionKoszul_sourceInternalExtAcyclic R H (tilde N))
    (tildeFunctionKoszul_isZero_above_rank R H (p+2) (by omega))
/-- SAME actual categorical Koszul differential equals its original
explicit exterior differential by the native library d_eq_d theorem. -/
theorem tildeFunctionKoszulComplex_d_next (R : CommRingCat.{u})
    {r : ℕ} (H : Fin r → R) (p : ℕ) :
    (tildeFunctionKoszulComplex R H).d (p+1) p =
      (tilde.functor R).map (ModuleCat.ofHom (koszulComplex.d (Fintype.linearCombination R H) p)) := by
  change (tilde.functor R).map ((koszulComplex (Fintype.linearCombination R H)).d (p+1) p) = _
  rw [koszulComplex.d_eq_d]
/-- Preserve the actual chain differential when passing to SAME original
explicit geometric Hom-cokernel calculation. Equality is transported by
mathlib cokernelIsoOfEq, not assumed definitionally. -/
def affineKoszulOriginalTopHomCokernelGeometricIso (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (p : ℕ) (H : Fin (p+1) → R) :
    cokernel (schemeModuleHomPrecompose (X:=Spec R) (N:=tilde N)
      ((tildeFunctionKoszulComplex R H).d (p+1) p)) ≅
        (affineKoszulHomGeometricRestrictionPresentation R N p H).X₃ :=
  cokernelIsoOfEq (f:=schemeModuleHomPrecompose (X:=Spec R) (N:=tilde N)
      ((tildeFunctionKoszulComplex R H).d (p+1) p))
    (g:=schemeModuleHomPrecompose (X:=Spec R) (N:=tilde N)
      ((tilde.functor R).map (ModuleCat.ofHom (koszulComplex.d (Fintype.linearCombination R H) p))))
    (by rw [tildeFunctionKoszulComplex_d_next]) ≪≫
      affineKoszulHomGeometricCokernelIso R N p H
/-- The original categorical-differential cokernel projection is exactly
the actual geometric restriction, retaining the original ordered frame. -/
theorem affineKoszulOriginalTopHomCokernelGeometricIso_projection (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (p : ℕ) (H : Fin (p+1) → R) :
    cokernel.π (schemeModuleHomPrecompose (X:=Spec R) (N:=tilde N)
        ((tildeFunctionKoszulComplex R H).d (p+1) p)) ≫
      (affineKoszulOriginalTopHomCokernelGeometricIso R N p H).hom =
        (affineKoszulHomGeometricRestrictionPresentation R N p H).g := by
  dsimp only [affineKoszulOriginalTopHomCokernelGeometricIso,Iso.trans_hom]
  rw [π_comp_cokernelIsoOfEq_hom_assoc,affineKoszulHomGeometricCokernelIso_projection]
/-- Actual derived SHEAF Ext of SAME original quotient-cut structure
sheaf is SAME geometric pullback-pushforward coefficient. N is arbitrary;
only exactness of the ORIGINAL source Koszul is required. -/
def affineKoszulOriginalSheafExtGeometricIso (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (p : ℕ) (H : Fin (p+1) → R)
    (he : ∀ j : ℕ,0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j)
    (I : InjectiveResolution (tilde N)) :
    schemeModuleInternalExt (tildeKoszulOriginalCutCokernelCofork R H).pt (tilde N) (p+1) ≅
      (affineKoszulHomGeometricRestrictionPresentation R N p H).X₃ :=
  affineKoszulOriginalSheafExtCokernelIso R N p H he I ≪≫
    affineKoszulOriginalTopHomCokernelGeometricIso R N p H
/-- SAME original global Ext class maps to SAME geometric restriction of
its original functional. This is a proved morphism law for ALL original
representatives,not just an isomorphism of objects. -/
theorem affineKoszulOriginalSheafExtGeometricIso_classLaw (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (p : ℕ) (H : Fin (p+1) → R)
    (he : ∀ j : ℕ,0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j)
    (I : InjectiveResolution (tilde N)) :
    schemeModuleOriginalTopExtClassIsoLaw (tildeFunctionKoszulComplex R H) (p+1)
      (originalChainCoforkAugmentation (tildeFunctionKoszulComplex R H)
        (tildeKoszulOriginalCutCokernelCofork R H))
      (tildeKoszulCoforkAugmentation_quasiIso_of_exact R H he)
      (affineKoszulOriginalSheafExtGeometricIso R N p H he I)
      (affineKoszulHomGeometricRestrictionPresentation R N p H).g := by
  have h := schemeModuleOriginalTopExtClassIsoLaw_postcompose
    (tildeFunctionKoszulComplex R H) (p+1)
    (originalChainCoforkAugmentation (tildeFunctionKoszulComplex R H)
      (tildeKoszulOriginalCutCokernelCofork R H))
    (tildeKoszulCoforkAugmentation_quasiIso_of_exact R H he)
    (affineKoszulOriginalSheafExtCokernelIso R N p H he I)
    (cokernel.π (schemeModuleHomPrecompose (X:=Spec R) (N:=tilde N)
      ((tildeFunctionKoszulComplex R H).d (p+1) p)))
    (affineKoszulOriginalSheafExtCokernelIso_classLaw R N p H he I)
    (affineKoszulOriginalTopHomCokernelGeometricIso R N p H)
  rw [affineKoszulOriginalTopHomCokernelGeometricIso_projection] at h
  exact h
end LinearStudy
