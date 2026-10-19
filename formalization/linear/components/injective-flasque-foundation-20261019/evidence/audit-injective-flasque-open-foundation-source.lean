module
import all Linear.AdjunctionCounitHomEquiv
import all Linear.ModuleSheafificationCounitHomEquiv
import all Linear.OverOpenUnitZeroPresheafMono
import all Linear.OverOpenUnitZeroSheafMono
import all Linear.OverOpenUnitZeroSheafBinding
import all Linear.OverOpenUnitZeroSheafAdjoint
import all Linear.OverOpenInjectiveUnitExtension
set_option maxHeartbeats 50000
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.adjunction_homEquiv_map_counit
#print axioms LinearStudy.adjunction_homEquiv_map_counit
#check @LinearStudy.moduleSheafification_homEquiv_map_counit
#print axioms LinearStudy.moduleSheafification_homEquiv_map_counit
#check @LinearStudy.overOpenUnitZeroPresheafToUnit
#print axioms LinearStudy.overOpenUnitZeroPresheafToUnit
#check @LinearStudy.overOpenUnitZeroPresheafToUnit_lof
#print axioms LinearStudy.overOpenUnitZeroPresheafToUnit_lof
#check @LinearStudy.overOpenUnitZeroPresheafToUnit_mono
#print axioms LinearStudy.overOpenUnitZeroPresheafToUnit_mono
#check @LinearStudy.overOpenUnitZeroSheafToUnit
#print axioms LinearStudy.overOpenUnitZeroSheafToUnit
#check @LinearStudy.overOpenUnitZeroSheafToUnit_mono
#print axioms LinearStudy.overOpenUnitZeroSheafToUnit_mono
#check @LinearStudy.overOpenUnitZeroBoundPresheaf
#print axioms LinearStudy.overOpenUnitZeroBoundPresheaf
#check @LinearStudy.overOpenUnitZeroBoundPresheafToUnit
#print axioms LinearStudy.overOpenUnitZeroBoundPresheafToUnit
#check @LinearStudy.overOpenUnitZeroBoundPresheafToUnit_mono
#print axioms LinearStudy.overOpenUnitZeroBoundPresheafToUnit_mono
#check @LinearStudy.overOpenUnitZeroBoundPresheafToUnit_homEquiv
#print axioms LinearStudy.overOpenUnitZeroBoundPresheafToUnit_homEquiv
#check @LinearStudy.overOpenZeroSheafHomEquiv_val
#print axioms LinearStudy.overOpenZeroSheafHomEquiv_val
#check @LinearStudy.overOpenUnitZeroSheafToUnit_presheafAdjoint
#print axioms LinearStudy.overOpenUnitZeroSheafToUnit_presheafAdjoint
#check @LinearStudy.overOpenUnitZeroSheafToUnit_adjoint
#print axioms LinearStudy.overOpenUnitZeroSheafToUnit_adjoint
#check @LinearStudy.overOpenUnitHom_extend_of_injective
#print axioms LinearStudy.overOpenUnitHom_extend_of_injective
#print LinearStudy.overOpenUnitZeroPresheafToUnit
#print LinearStudy.overOpenUnitZeroSheafToUnit
#print LinearStudy.overOpenUnitZeroBoundPresheaf
#print LinearStudy.overOpenUnitZeroBoundPresheafToUnit
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.adjunction_homEquiv_map_counit,true),(`LinearStudy.moduleSheafification_homEquiv_map_counit,true),(`LinearStudy.overOpenUnitZeroPresheafToUnit,false),(`LinearStudy.overOpenUnitZeroPresheafToUnit_lof,true),(`LinearStudy.overOpenUnitZeroPresheafToUnit_mono,true),(`LinearStudy.overOpenUnitZeroSheafToUnit,false),(`LinearStudy.overOpenUnitZeroSheafToUnit_mono,true),(`LinearStudy.overOpenUnitZeroBoundPresheaf,false),(`LinearStudy.overOpenUnitZeroBoundPresheafToUnit,false),(`LinearStudy.overOpenUnitZeroBoundPresheafToUnit_mono,true),(`LinearStudy.overOpenUnitZeroBoundPresheafToUnit_homEquiv,true),(`LinearStudy.overOpenZeroSheafHomEquiv_val,true),(`LinearStudy.overOpenUnitZeroSheafToUnit_presheafAdjoint,true),(`LinearStudy.overOpenUnitZeroSheafToUnit_adjoint,true),(`LinearStudy.overOpenUnitHom_extend_of_injective,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
