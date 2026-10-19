module
import all Linear.PointedExactFunctorExtMap
import all Linear.PointedExactFunctorExtMapIsIso
import all Linear.PointedExactFunctorExtZero
import all Linear.SchemeModuleCohomologyPointedSource
import all Linear.SchemeModuleGlobalExtActualHMap
import all Linear.SchemeModuleGlobalExtActualHZeroCalibration
import all Linear.SchemeModuleGlobalExtActualHCohomology
set_option maxHeartbeats 50000
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.pointedExactFunctorExtMap
#print axioms LinearStudy.pointedExactFunctorExtMap
#check @LinearStudy.pointedExactFunctorExtMap_postcompose
#print axioms LinearStudy.pointedExactFunctorExtMap_postcompose
#check @LinearStudy.pointedExactFunctorExtMap_boundary
#print axioms LinearStudy.pointedExactFunctorExtMap_boundary
#check @LinearStudy.pointedExactFunctorExtMap_bijective
#print axioms LinearStudy.pointedExactFunctorExtMap_bijective
#check @LinearStudy.pointedExactFunctorExtMap_zero_homEquiv
#print axioms LinearStudy.pointedExactFunctorExtMap_zero_homEquiv
#check @LinearStudy.schemeModuleToAdditiveSheaf_additive
#print axioms LinearStudy.schemeModuleToAdditiveSheaf_additive
#check @LinearStudy.schemeModuleToAdditiveSheaf_preservesFiniteColimits
#print axioms LinearStudy.schemeModuleToAdditiveSheaf_preservesFiniteColimits
#check @LinearStudy.schemeModuleIntegerToUnderlyingUnit
#print axioms LinearStudy.schemeModuleIntegerToUnderlyingUnit
#check @LinearStudy.schemeModuleIntegerToUnderlyingUnit_section
#print axioms LinearStudy.schemeModuleIntegerToUnderlyingUnit_section
#check @LinearStudy.schemeModuleGlobalExtActualHMap
#print axioms LinearStudy.schemeModuleGlobalExtActualHMap
#check @LinearStudy.schemeModuleGlobalExtActualHMap_naturality
#print axioms LinearStudy.schemeModuleGlobalExtActualHMap_naturality
#check @LinearStudy.schemeModuleGlobalExtActualHMap_boundary
#print axioms LinearStudy.schemeModuleGlobalExtActualHMap_boundary
#check @LinearStudy.schemeModuleGlobalExtActualHMap_zero
#print axioms LinearStudy.schemeModuleGlobalExtActualHMap_zero
#check @LinearStudy.schemeModuleGlobalExtActualHMap_bijective
#print axioms LinearStudy.schemeModuleGlobalExtActualHMap_bijective
#check @LinearStudy.schemeModuleGlobalExtActualHAddEquiv
#print axioms LinearStudy.schemeModuleGlobalExtActualHAddEquiv
#check @LinearStudy.schemeModuleGlobalExtActualHAddEquiv_naturality
#print axioms LinearStudy.schemeModuleGlobalExtActualHAddEquiv_naturality
#check @LinearStudy.schemeModuleGlobalExtActualHAddEquiv_boundary
#print axioms LinearStudy.schemeModuleGlobalExtActualHAddEquiv_boundary
#check @LinearStudy.schemeModuleGlobalExtActualHAddEquiv_zero
#print axioms LinearStudy.schemeModuleGlobalExtActualHAddEquiv_zero
#print LinearStudy.pointedExactFunctorExtMap
#print LinearStudy.schemeModuleIntegerToUnderlyingUnit
#print LinearStudy.schemeModuleGlobalExtActualHMap
#print LinearStudy.schemeModuleGlobalExtActualHAddEquiv
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.pointedExactFunctorExtMap,false),(`LinearStudy.pointedExactFunctorExtMap_postcompose,true),(`LinearStudy.pointedExactFunctorExtMap_boundary,true),(`LinearStudy.pointedExactFunctorExtMap_bijective,true),(`LinearStudy.pointedExactFunctorExtMap_zero_homEquiv,true),(`LinearStudy.schemeModuleToAdditiveSheaf_additive,true),(`LinearStudy.schemeModuleToAdditiveSheaf_preservesFiniteColimits,true),(`LinearStudy.schemeModuleIntegerToUnderlyingUnit,false),(`LinearStudy.schemeModuleIntegerToUnderlyingUnit_section,true),(`LinearStudy.schemeModuleGlobalExtActualHMap,false),(`LinearStudy.schemeModuleGlobalExtActualHMap_naturality,true),(`LinearStudy.schemeModuleGlobalExtActualHMap_boundary,true),(`LinearStudy.schemeModuleGlobalExtActualHMap_zero,true),(`LinearStudy.schemeModuleGlobalExtActualHMap_bijective,true),(`LinearStudy.schemeModuleGlobalExtActualHAddEquiv,false),(`LinearStudy.schemeModuleGlobalExtActualHAddEquiv_naturality,true),(`LinearStudy.schemeModuleGlobalExtActualHAddEquiv_boundary,true),(`LinearStudy.schemeModuleGlobalExtActualHAddEquiv_zero,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
