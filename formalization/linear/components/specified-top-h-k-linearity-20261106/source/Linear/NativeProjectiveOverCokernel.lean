module
public import Linear.NativeProjectiveDegreeZeroMap
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite Limits
universe u
variable {K S : Type u} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]

/-- Actual native restriction is additive, by its actual section map. -/
@[instance] def nativeSheafOverFunctor_additive
    (U : Opens (ProjectiveSpectrum.top 𝓑)) :
    (SheafOfModules.overFunctor (AlgebraicGeometry.Proj 𝓑).ringCatSheaf U).Additive where
  map_add {X Y f g} := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

/-- The actual native restriction has mathlib's constructed right
adjoint on the original open site; it consequently preserves colimits. -/
@[instance] def nativeSheafOverFunctor_isLeftAdjoint
    (U : Opens (ProjectiveSpectrum.top 𝓑)) :
    (SheafOfModules.overFunctor (AlgebraicGeometry.Proj 𝓑).ringCatSheaf U).IsLeftAdjoint :=
  (SheafOfModules.overPushforwardOverAdj
    (R := (AlgebraicGeometry.Proj 𝓑).ringCatSheaf) U).isLeftAdjoint

/-- An actual native cokernel presentation restricts to the actual
native open-site cokernel, with its actual induced maps. -/
def nativeSheafOverCokernelIsColimit
    {E F M : SheafOfModules (AlgebraicGeometry.Proj 𝓑).ringCatSheaf}
    (a : E ⟶ F) (b : F ⟶ M) (h : a ≫ b = 0)
    (hc : IsColimit (CokernelCofork.ofπ b h))
    (U : Opens (ProjectiveSpectrum.top 𝓑)) :
    IsColimit (CokernelCofork.ofπ (b.over U)
      (show a.over U ≫ b.over U = 0 by
        rw [← CategoryTheory.Functor.map_comp, h,
          CategoryTheory.Functor.map_zero])) :=
  CokernelCofork.mapIsColimit _ hc
    (SheafOfModules.overFunctor (AlgebraicGeometry.Proj 𝓑).ringCatSheaf U)

end LinearStudy
