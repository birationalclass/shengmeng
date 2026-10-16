module
public import Linear.SchemeModuleInternalExtZero
public import Linear.SchemeModuleInternalExtSourceMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- Actual zero SHEAF Ext comparison preserves the SAME source map,
not only coefficient naturality. -/
theorem schemeModuleInternalExtZeroIso_source_inv {A B : X.Modules}
    (f : A ⟶ B) (N : X.Modules) :
    schemeModuleHomPrecompose (N := N) f ≫
        ((schemeModuleInternalExtZeroIso A).app N).inv =
      ((schemeModuleInternalExtZeroIso B).app N).inv ≫
        schemeModuleInternalExtSourceMap f N 0 := by
  let I := injectiveResolution N
  have hc : schemeModuleHomPrecompose (N := N) f ≫
      I.toRightDerivedZero' (schemeModuleInternalHomCoefficientFunctor X A) =
      I.toRightDerivedZero' (schemeModuleInternalHomCoefficientFunctor X B) ≫
        HomologicalComplex.cyclesMap (schemeModuleHomCoefficientComplexMap f I.cocomplex) 0 := by
    apply (cancel_mono (HomologicalComplex.iCycles _ 0)).1
    dsimp only [schemeModuleHomCoefficientComplex]
    erw [Category.assoc,InjectiveResolution.toRightDerivedZero'_comp_iCycles,
      Category.assoc,HomologicalComplex.cyclesMap_i,
      InjectiveResolution.toRightDerivedZero'_comp_iCycles_assoc]
    exact (schemeModuleInternalHomSourceNatTrans f).naturality (I.ι.f 0)
  rw [schemeModuleInternalExtZeroIso_inv_app,schemeModuleInternalExtZeroIso_inv_app,
    I.toRightDerivedZero_eq,I.toRightDerivedZero_eq,
    schemeModuleInternalExtSourceMap_resolution f N 0 I]
  dsimp only [schemeModuleInternalExtInjectiveResolutionIso]
  simp only [Category.assoc,Iso.inv_hom_id_assoc]
  rw [reassoc_of% hc]
  exact congrArg (fun z => I.toRightDerivedZero'
      (schemeModuleInternalHomCoefficientFunctor X B) ≫ z ≫
      (I.isoRightDerivedObj (schemeModuleInternalHomCoefficientFunctor X A) 0).inv)
    (HomologicalComplex.homologyπ_naturality (schemeModuleHomCoefficientComplexMap f I.cocomplex) 0).symm

/-- Forward actual Ext^0~=Hom comparison commutes with SAME precomposition. -/
theorem schemeModuleInternalExtZeroIso_source {A B : X.Modules}
    (f : A ⟶ B) (N : X.Modules) :
    schemeModuleInternalExtSourceMap f N 0 ≫
        ((schemeModuleInternalExtZeroIso A).app N).hom =
      ((schemeModuleInternalExtZeroIso B).app N).hom ≫
        schemeModuleHomPrecompose (N := N) f := by
  apply (cancel_epi ((schemeModuleInternalExtZeroIso B).app N).inv).1
  rw [← Category.assoc,← schemeModuleInternalExtZeroIso_source_inv f N]
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id,Iso.inv_hom_id_assoc]

end LinearStudy
