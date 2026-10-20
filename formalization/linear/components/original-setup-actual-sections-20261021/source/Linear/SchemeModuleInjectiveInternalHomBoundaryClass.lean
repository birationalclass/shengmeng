module
public import Linear.SchemeModuleInternalExtSourceBoundary
public import Linear.SchemeModuleInjectiveInternalHomCycles
public import Linear.SchemeModuleHomUnitSourceNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u
variable {X : Scheme.{u}}

/-- Compute SAME actual internal-Hom snake boundary on SAME curried
injective cocycles. Reuse native HomologySequence.ShortExact.delta_eq;
no desired connecting square or class equality is a premise. -/
theorem schemeModuleInjectiveInternalHomClassMap_boundary
    (S : ShortComplex X.Modules) (hS : S.ShortExact) {N : X.Modules}
    (I : InjectiveResolution N) (q : ℕ)
    (a : injectiveCocycleGroup I S.X₁ q)
    (b : S.X₂ ⟶ I.cocomplex.X q)
    (c : injectiveCocycleGroup I S.X₃ (q+1))
    (hb : S.f ≫ b = a.val)
    (hbc : b ≫ I.cocomplex.d q (q+1) = S.g ≫ c.val) :
    schemeModuleInjectiveInternalHomClassMap I S.X₁ q a ≫
      (schemeModuleHomSourceShortComplex_shortExact S hS I.cocomplex).δ q (q+1) rfl =
      schemeModuleInjectiveInternalHomClassMap I S.X₃ (q+1) c := by
  let T := schemeModuleHomSourceShortComplex S I.cocomplex
  have hT : T.ShortExact := schemeModuleHomSourceShortComplex_shortExact S hS I.cocomplex
  have ha : a.val ≫ I.cocomplex.d q (q+1) = 0 := a.property
  have hca : (schemeModuleHomUnitAddEquiv S.X₁ (I.cocomplex.X q)).symm a.val ≫
      T.X₃.d q (q+1) = 0 := by
    change (schemeModuleHomUnitAddEquiv S.X₁ (I.cocomplex.X q)).symm a.val ≫
      schemeModuleHomPostcompose (I.cocomplex.d q (q+1)) = 0
    rw [← schemeModuleHomUnitAddEquiv_symm_postcompose,ha,map_zero]
  have hcb : (schemeModuleHomUnitAddEquiv S.X₂ (I.cocomplex.X q)).symm b ≫ T.g.f q =
      (schemeModuleHomUnitAddEquiv S.X₁ (I.cocomplex.X q)).symm a.val := by
    change _ ≫ schemeModuleHomPrecompose S.f = _
    rw [← schemeModuleHomUnitAddEquiv_symm_precompose,hb]
  have hcc : (schemeModuleHomUnitAddEquiv S.X₃ (I.cocomplex.X (q+1))).symm c.val ≫ T.f.f (q+1) =
      (schemeModuleHomUnitAddEquiv S.X₂ (I.cocomplex.X q)).symm b ≫ T.X₂.d q (q+1) := by
    change _ ≫ schemeModuleHomPrecompose S.g = _ ≫ schemeModuleHomPostcompose (I.cocomplex.d q (q+1))
    rw [← schemeModuleHomUnitAddEquiv_symm_precompose,← schemeModuleHomUnitAddEquiv_symm_postcompose,hbc]
  have h := hT.δ_eq q (q+1) rfl
    ((schemeModuleHomUnitAddEquiv S.X₁ (I.cocomplex.X q)).symm a.val) hca
    ((schemeModuleHomUnitAddEquiv S.X₂ (I.cocomplex.X q)).symm b) hcb
    ((schemeModuleHomUnitAddEquiv S.X₃ (I.cocomplex.X (q+1))).symm c.val) hcc
    (q+1+1) (by simp)
  dsimp only [schemeModuleInjectiveInternalHomClassMap,schemeModuleInjectiveInternalHomCycleMap,DFunLike.coe]
  convert! h using 1 <;> rfl

end LinearStudy
