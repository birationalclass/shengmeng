module
public import Linear.SchemeModuleGlobalExtActualHZeroCalibration
public import Linear.PointedExactFunctorExtMapIsIso
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
universe u
/-- The canonical GLOBAL unit-Ext to actual native SHEAF H map is bijective in EVERY degree. -/
theorem schemeModuleGlobalExtActualHMap_bijective (X : Scheme.{u})
    (M : X.Modules) (n : ℕ) : Function.Bijective (schemeModuleGlobalExtActualHMap X M n) :=
  pointedExactFunctorExtMap_bijective (schemeModuleToAdditiveSheaf X)
    (schemeModuleIntegerToUnderlyingUnit X)
    (fun N => by
      change Function.Bijective (schemeModuleGlobalExtActualHMap X N 0)
      have hmap : ⇑(schemeModuleGlobalExtActualHMap X N 0) =
          ⇑(schemeModuleGlobalExtZeroActualHAddEquiv X N) :=
        funext (schemeModuleGlobalExtActualHMap_zero X N)
      rw [hmap]
      exact (schemeModuleGlobalExtZeroActualHAddEquiv X N).bijective)
    (fun I _ j => schemeModule_injective_actualHigherCohomology_vanish X I j) M n

/-- Canonical additive comparison with NATIVE actual SHEAF H in EVERY degree. -/
def schemeModuleGlobalExtActualHAddEquiv (X : Scheme.{u}) (M : X.Modules) (n : ℕ) :
    Ext.{u} (SheafOfModules.unit X.ringCatSheaf) M n ≃+
      schemeModuleActualCohomology X M n :=
  AddEquiv.ofBijective (schemeModuleGlobalExtActualHMap X M n)
    (schemeModuleGlobalExtActualHMap_bijective X M n)

/-- The EVERY-degree canonical equivalence is natural in each original coefficient morphism. -/
theorem schemeModuleGlobalExtActualHAddEquiv_naturality (X : Scheme.{u})
    {M N : X.Modules} (f : M ⟶ N) (n : ℕ)
    (x : Ext.{u} (SheafOfModules.unit X.ringCatSheaf) M n) :
    schemeModuleGlobalExtActualHAddEquiv X N n (x.comp (Ext.mk₀ f) (add_zero n)) =
      CategoryTheory.Sheaf.H.map ((schemeModuleToActualAbelianSheaf X).map f) n
        (schemeModuleGlobalExtActualHAddEquiv X M n x) :=
  schemeModuleGlobalExtActualHMap_naturality X f n x

/-- The canonical equivalence retains the SAME actual covariant connecting class. -/
theorem schemeModuleGlobalExtActualHAddEquiv_boundary (X : Scheme.{u})
    {S : ShortComplex X.Modules} (hS : S.ShortExact) (n : ℕ)
    (x : Ext.{u} (SheafOfModules.unit X.ringCatSheaf) S.X₃ n) :
    schemeModuleGlobalExtActualHAddEquiv X S.X₁ (n+1) (x.comp hS.extClass rfl) =
      (schemeModuleGlobalExtActualHAddEquiv X S.X₃ n x).comp
        (schemeModuleShortExact_underlyingAdditiveSheaf S hS).extClass rfl :=
  schemeModuleGlobalExtActualHMap_boundary X hS n x

/-- Degree zero agrees with the SAME previously verified evaluation-at1 equivalence. -/
theorem schemeModuleGlobalExtActualHAddEquiv_zero (X : Scheme.{u}) (M : X.Modules) :
    schemeModuleGlobalExtActualHAddEquiv X M 0 = schemeModuleGlobalExtZeroActualHAddEquiv X M := by
  ext x
  exact schemeModuleGlobalExtActualHMap_zero X M x
end LinearStudy
