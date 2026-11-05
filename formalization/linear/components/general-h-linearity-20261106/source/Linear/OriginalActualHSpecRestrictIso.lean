module
public import Linear.OriginalActualHSpecModuleObject
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u

/-- Apply the canonical restriction of scalars to a comparison with the
independently defined original Γ-module on actual H. -/
def originalActualHSpecRestrictIso
    {K : Type u} [CommRing K] {X : Scheme.{u}}
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) (n : ℕ)
    {C : ModuleCat.{u} Γ(Spec (CommRingCat.of K),⊤)}
    (I : C ≅ originalActualHBaseModuleObject pi M n) :
    (ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).obj C ≅
      originalActualHSpecModuleObject pi M n :=
  (ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).mapIso I

theorem originalActualHSpecRestrictIso_forget_hom
    {K : Type u} [CommRing K] {X : Scheme.{u}}
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) (n : ℕ)
    {C : ModuleCat.{u} Γ(Spec (CommRingCat.of K),⊤)}
    (I : C ≅ originalActualHBaseModuleObject pi M n) :
    (forget₂ (ModuleCat.{u} K) AddCommGrpCat.{u}).map
      (originalActualHSpecRestrictIso pi M n I).hom =
    (forget₂ (ModuleCat.{u} Γ(Spec (CommRingCat.of K),⊤)) AddCommGrpCat.{u}).map I.hom :=
  ModuleCat.forget₂_map_restrictScalars (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom I.hom

end LinearStudy
#check LinearStudy.originalActualHSpecRestrictIso
#print axioms LinearStudy.originalActualHSpecRestrictIso
#check LinearStudy.originalActualHSpecRestrictIso_forget_hom
#print axioms LinearStudy.originalActualHSpecRestrictIso_forget_hom
