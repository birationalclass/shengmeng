module
public import Linear.OverOpenUnitZeroSheafMono
public import Linear.ModuleSheafificationCounitHomEquiv
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory
universe u
variable {C : Type u} [Preorder C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u}) (U : C)
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Precompiled actual source binding keeps open-unit type comparisons separate. -/
def overOpenUnitZeroBoundPresheaf : PresheafOfModules.{u} R.obj :=
  (overOpenZeroPresheafFunctor R.obj U).obj
    ((SheafOfModules.forget (R.over U)).obj (SheafOfModules.unit (R.over U)))

/-- The same original inclusion,with source and restricted-scalar target bound explicitly. -/
def overOpenUnitZeroBoundPresheafToUnit :
    overOpenUnitZeroBoundPresheaf R U ⟶
      (PresheafOfModules.restrictScalars (𝟙 R.obj)).obj
        (SheafOfModules.unit R).val :=
  overOpenUnitZeroPresheafToUnit R.obj U

/-- The same bound original presheaf map is mono. -/
theorem overOpenUnitZeroBoundPresheafToUnit_mono :
    Mono (overOpenUnitZeroBoundPresheafToUnit R U) :=
  overOpenUnitZeroPresheafToUnit_mono R.obj U

/-- Hom equivalence of the actual bound map,without expanding the open source. -/
theorem overOpenUnitZeroBoundPresheafToUnit_homEquiv :
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv
      (overOpenUnitZeroBoundPresheaf R U) (SheafOfModules.unit R)
      ((PresheafOfModules.sheafification (𝟙 R.obj)).map
        (overOpenUnitZeroBoundPresheafToUnit R U) ≫
          (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit.app
            (SheafOfModules.unit R)) = overOpenUnitZeroBoundPresheafToUnit R U :=
  moduleSheafification_homEquiv_map_counit R
    (overOpenUnitZeroBoundPresheaf R U) (SheafOfModules.unit R)
    (overOpenUnitZeroBoundPresheafToUnit R U)
end LinearStudy
