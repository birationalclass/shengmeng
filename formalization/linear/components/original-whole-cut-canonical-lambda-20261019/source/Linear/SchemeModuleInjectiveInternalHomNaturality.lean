module
public import Linear.SchemeModuleInjectiveInternalHomCycles
public import Linear.InjectiveCocycleTransport
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X : Scheme.{u}} {N N' : X.Modules} (I : InjectiveResolution N)
  (J : InjectiveResolution N') (P : X.Modules)

/-- The original actual cycle inclusion retains the SAME curried cocycle. -/
theorem schemeModuleInjectiveInternalHomCycleMap_i (q : ℕ)
    (f : injectiveCocycleGroup I P q) :
    schemeModuleInjectiveInternalHomCycleMap I P q f ≫
        (schemeModuleInjectiveInternalHomComplex I P).iCycles q =
      (schemeModuleHomUnitAddEquiv P (I.cocomplex.X q)).symm f.val :=
by
  let K := schemeModuleInjectiveInternalHomComplex I P
  have hf : (schemeModuleHomUnitAddEquiv P (I.cocomplex.X q)).symm f.val ≫
      K.d q (q+1) = 0 := by
    change (schemeModuleHomUnitAddEquiv P (I.cocomplex.X q)).symm f.val ≫
      schemeModuleHomPostcompose (I.cocomplex.d q (q+1)) = 0
    rw [← schemeModuleHomUnitAddEquiv_symm_postcompose,f.property,map_zero]
  exact HomologicalComplex.liftCycles_i K _ (q+1) (by simp) hf

/-- SAME cocycle transported along SAME actual resolution map gives
SAME actual cycle map,not merely isomorphic cohomology objects. -/
theorem schemeModuleInjectiveInternalHomCycleMap_naturality (q : ℕ)
    (phi : I.cocomplex ⟶ J.cocomplex) (f : injectiveCocycleGroup I P q) :
    schemeModuleInjectiveInternalHomCycleMap J P q (injectiveCocycleTransport I J P q phi f) =
      schemeModuleInjectiveInternalHomCycleMap I P q f ≫
        HomologicalComplex.cyclesMap
          (((schemeModuleInternalHomCoefficientFunctor X P).mapHomologicalComplex
            (ComplexShape.up ℕ)).map phi) q := by
  apply (cancel_mono ((schemeModuleInjectiveInternalHomComplex J P).iCycles q)).mp
  erw [schemeModuleInjectiveInternalHomCycleMap_i,Category.assoc,
    HomologicalComplex.cyclesMap_i,← Category.assoc,schemeModuleInjectiveInternalHomCycleMap_i]
  exact schemeModuleHomUnitAddEquiv_symm_postcompose P f.val (phi.f q)

/-- The SAME actual class is natural under original resolution maps. -/
theorem schemeModuleInjectiveInternalHomClassMap_naturality (q : ℕ)
    (phi : I.cocomplex ⟶ J.cocomplex) (f : injectiveCocycleGroup I P q) :
    schemeModuleInjectiveInternalHomClassMap J P q (injectiveCocycleTransport I J P q phi f) =
      schemeModuleInjectiveInternalHomClassMap I P q f ≫
        HomologicalComplex.homologyMap
          (((schemeModuleInternalHomCoefficientFunctor X P).mapHomologicalComplex
            (ComplexShape.up ℕ)).map phi) q := by
  change (_ ≫ (schemeModuleInjectiveInternalHomComplex J P).homologyπ q) =
    (_ ≫ (schemeModuleInjectiveInternalHomComplex I P).homologyπ q) ≫ _
  erw [schemeModuleInjectiveInternalHomCycleMap_naturality,Category.assoc,
    ← HomologicalComplex.homologyπ_naturality,← Category.assoc]

end LinearStudy
