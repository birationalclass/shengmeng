module
public import Linear.SchemeModuleInternalHomSourceShortExact
public import Linear.SchemeModuleDerivedInternalHom
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- The ACTUAL derived SHEAF Ext map in the source variable,obtained
from native derived natural transformation of SAME precomposition. -/
def schemeModuleInternalExtSourceMap {A B : X.Modules} (f : A ⟶ B)
    (N : X.Modules) (q : ℕ) :
    schemeModuleInternalExt B N q ⟶ schemeModuleInternalExt A N q :=
  (NatTrans.rightDerived (schemeModuleInternalHomSourceNatTrans f) q).app N

theorem schemeModuleInternalExtSourceMap_id (A N : X.Modules) (q : ℕ) :
    schemeModuleInternalExtSourceMap (𝟙 A) N q = 𝟙 _ := by
  unfold schemeModuleInternalExtSourceMap
  rw [schemeModuleInternalHomSourceNatTrans_id,NatTrans.rightDerived_id]
  rfl

theorem schemeModuleInternalExtSourceMap_comp {A B C : X.Modules}
    (f : A ⟶ B) (g : B ⟶ C) (N : X.Modules) (q : ℕ) :
    schemeModuleInternalExtSourceMap (f ≫ g) N q =
      schemeModuleInternalExtSourceMap g N q ≫
        schemeModuleInternalExtSourceMap f N q := by
  simp [schemeModuleInternalExtSourceMap,schemeModuleInternalHomSourceNatTrans_comp]

/-- ANY actual injective resolution computes the SAME source map. -/
theorem schemeModuleInternalExtSourceMap_resolution {A B : X.Modules}
    (f : A ⟶ B) (N : X.Modules) (q : ℕ) (I : InjectiveResolution N) :
    schemeModuleInternalExtSourceMap f N q =
      (schemeModuleInternalExtInjectiveResolutionIso B N q I).hom ≫
        HomologicalComplex.homologyMap (schemeModuleHomCoefficientComplexMap f I.cocomplex) q ≫
          (schemeModuleInternalExtInjectiveResolutionIso A N q I).inv :=
  I.rightDerived_app_eq (schemeModuleInternalHomSourceNatTrans f) q

/-- The actual Ext source map and SAME actual Hom-complex map commute
under the original native injective-resolution comparison. -/
theorem schemeModuleInternalExtSourceMap_resolution_square {A B : X.Modules}
    (f : A ⟶ B) (N : X.Modules) (q : ℕ) (I : InjectiveResolution N) :
    schemeModuleInternalExtSourceMap f N q ≫
        (schemeModuleInternalExtInjectiveResolutionIso A N q I).hom =
      (schemeModuleInternalExtInjectiveResolutionIso B N q I).hom ≫
        HomologicalComplex.homologyMap (schemeModuleHomCoefficientComplexMap f I.cocomplex) q := by
  rw [schemeModuleInternalExtSourceMap_resolution f N q I]
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]

/-- Zero in the original source stays zero on the SAME coefficient complex. -/
theorem schemeModuleHomCoefficientComplexMap_zero (A B : X.Modules)
    (K : CochainComplex X.Modules ℕ) :
    schemeModuleHomCoefficientComplexMap (0 : A ⟶ B) K = 0 := by
  ext j : 1
  exact schemeModuleHomPrecompose_zero A B (K.X j)

/-- The actual derived source map preserves the zero morphism. -/
theorem schemeModuleInternalExtSourceMap_zero (A B N : X.Modules) (q : ℕ) :
    schemeModuleInternalExtSourceMap (0 : A ⟶ B) N q = 0 := by
  rw [schemeModuleInternalExtSourceMap_resolution (0 : A ⟶ B) N q (injectiveResolution N),
    schemeModuleHomCoefficientComplexMap_zero,HomologicalComplex.homologyMap_zero]
  dsimp only [schemeModuleHomCoefficientComplex]
  simp only [zero_comp,comp_zero]

end LinearStudy
