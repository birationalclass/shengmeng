module
public import Linear.SchemeModuleHomUnitCurry
public import Linear.SchemeModuleDerivedInternalHom
public import Linear.InjectiveCocycleExtPresentation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X : Scheme.{u}} {N : X.Modules} (I : InjectiveResolution N) (P : X.Modules)

/-- The ACTUAL internal-Hom complex of the SAME coefficient injective
resolution used to compute derived SHEAF Ext. -/
def schemeModuleInjectiveInternalHomComplex : CochainComplex X.Modules ℕ :=
  ((schemeModuleInternalHomCoefficientFunctor X P).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj I.cocomplex

/-- Curry the SAME actual injective cocycle to an ACTUAL sheaf cycle. -/
def schemeModuleInjectiveInternalHomCycleMap (q : ℕ) :
    injectiveCocycleGroup I P q →+
      (SheafOfModules.unit X.ringCatSheaf ⟶
        (schemeModuleInjectiveInternalHomComplex I P).cycles q) := by
  let K := schemeModuleInjectiveInternalHomComplex I P
  refine {
    toFun := fun f => K.liftCycles ((schemeModuleHomUnitAddEquiv P (I.cocomplex.X q)).symm f.val)
      (q+1) (by simp) (by
        change (schemeModuleHomUnitAddEquiv P (I.cocomplex.X q)).symm f.val ≫
          schemeModuleHomPostcompose (I.cocomplex.d q (q+1)) = 0
        rw [← schemeModuleHomUnitAddEquiv_symm_postcompose,f.property,map_zero])
    map_zero' := ?_
    map_add' := ?_ }
  · apply (cancel_mono (K.iCycles q)).mp
    simp only [HomologicalComplex.liftCycles_i,Limits.zero_comp]
    change (schemeModuleHomUnitAddEquiv P (I.cocomplex.X q)).symm (0 : P ⟶ I.cocomplex.X q) = 0
    exact map_zero _
  · intro f g
    apply (cancel_mono (K.iCycles q)).mp
    simp only [HomologicalComplex.liftCycles_i,Preadditive.add_comp]
    exact (schemeModuleHomUnitAddEquiv P (I.cocomplex.X q)).symm.map_add f.val g.val

/-- Class of the SAME actual cycle in ACTUAL internal-Hom cohomology. -/
def schemeModuleInjectiveInternalHomClassMap (q : ℕ) :
    injectiveCocycleGroup I P q →+
      (SheafOfModules.unit X.ringCatSheaf ⟶
        (schemeModuleInjectiveInternalHomComplex I P).homology q) where
  toFun f := schemeModuleInjectiveInternalHomCycleMap I P q f ≫
    (schemeModuleInjectiveInternalHomComplex I P).homologyπ q
  map_zero' := by simp
  map_add' f g := by simp [Preadditive.add_comp]

/-- An ACTUAL boundary in the SAME injective resolution has zero class
in the ACTUAL internal-Hom cohomology sheaf. No desired descent or
comparison square is a premise. -/
theorem schemeModuleInjectiveInternalHomClassMap_boundary_zero (n : ℕ)
    (f : injectiveCocycleGroup I P (n+1)) (g : P ⟶ I.cocomplex.X n)
    (hg : g ≫ I.cocomplex.d n (n+1) = f.val) :
    schemeModuleInjectiveInternalHomClassMap I P (n+1) f = 0 := by
  let K := schemeModuleInjectiveInternalHomComplex I P
  have h : (schemeModuleHomUnitAddEquiv P (I.cocomplex.X (n+1))).symm f.val =
      (schemeModuleHomUnitAddEquiv P (I.cocomplex.X n)).symm g ≫ K.d n (n+1) := by
    rw [← hg]
    exact schemeModuleHomUnitAddEquiv_symm_postcompose P g (I.cocomplex.d n (n+1))
  exact K.liftCycles_homologyπ_eq_zero_of_boundary _ (n+1+1) (by simp)
    ((schemeModuleHomUnitAddEquiv P (I.cocomplex.X n)).symm g) h

end LinearStudy
