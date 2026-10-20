module
import all Linear.AcyclicChainOpcycleSequence
import all Linear.AcyclicChainHomExtension
import all Linear.AcyclicChainExtVanishing
import all Linear.AcyclicResolutionExtVanishing
import all Linear.FiniteCoproductExtAcyclic
import all Linear.TopOpenAbelianSheafRestriction
import all Linear.TopOpenRestrictionHomSections
import all Linear.PointedExactFunctorExtZeroHomEquiv
import all Linear.TopOpenRestrictionPointedSource
import all Linear.TopOpenRestrictionActualCohomology
import all Linear.TopCechFiniteFreeSheafTerms
import all Linear.TopCechLocalAcyclicTerms
import all Linear.TopCechNativeHVanishingCriterion
set_option maxHeartbeats 50000
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.chainOpcycleSequence
#print axioms LinearStudy.chainOpcycleSequence
#check @LinearStudy.chainOpcycleSequenceIsCokernel
#print axioms LinearStudy.chainOpcycleSequenceIsCokernel
#check @LinearStudy.chainOpcycleSequence_shortExact
#print axioms LinearStudy.chainOpcycleSequence_shortExact
#check @LinearStudy.chainActualHomCochain
#print axioms LinearStudy.chainActualHomCochain
#check @LinearStudy.chainActualHomExact_opcycle_extension
#print axioms LinearStudy.chainActualHomExact_opcycle_extension
#check @LinearStudy.acyclicChainOpcycle_ext_subsingleton
#print axioms LinearStudy.acyclicChainOpcycle_ext_subsingleton
#check @LinearStudy.chainResolutionOpcycleZeroIso
#print axioms LinearStudy.chainResolutionOpcycleZeroIso
#check @LinearStudy.acyclicResolution_ext_subsingleton
#print axioms LinearStudy.acyclicResolution_ext_subsingleton
#check @LinearStudy.ext_subsingleton_of_source_iso
#print axioms LinearStudy.ext_subsingleton_of_source_iso
#check @LinearStudy.finiteCoproduct_ext_subsingleton
#print axioms LinearStudy.finiteCoproduct_ext_subsingleton
#check @LinearStudy.topOpenAbelianSheafRestriction
#print axioms LinearStudy.topOpenAbelianSheafRestriction
#check @LinearStudy.topOpenAbelianSheafRestriction_additive
#print axioms LinearStudy.topOpenAbelianSheafRestriction_additive
#check @LinearStudy.topOpenAbelianSheafRestriction_preservesFiniteLimits
#print axioms LinearStudy.topOpenAbelianSheafRestriction_preservesFiniteLimits
#check @LinearStudy.topOpenAbelianSheafRestriction_preservesColimits
#print axioms LinearStudy.topOpenAbelianSheafRestriction_preservesColimits
#check @LinearStudy.topOpenAbelianSheafRestriction_isFlasque
#print axioms LinearStudy.topOpenAbelianSheafRestriction_isFlasque
#check @LinearStudy.topOpenRestrictionGlobalSectionsIso
#print axioms LinearStudy.topOpenRestrictionGlobalSectionsIso
#check @LinearStudy.topOpenRestrictionGlobalSectionsIso_naturality
#print axioms LinearStudy.topOpenRestrictionGlobalSectionsIso_naturality
#check @LinearStudy.topOpenRestrictionHomAddEquiv
#print axioms LinearStudy.topOpenRestrictionHomAddEquiv
#check @LinearStudy.topOpenRestrictionHomAddEquiv_postcompose
#print axioms LinearStudy.topOpenRestrictionHomAddEquiv_postcompose
#check @LinearStudy.pointedExactFunctorExtMap_zero_bijective_of_homEquiv
#print axioms LinearStudy.pointedExactFunctorExtMap_zero_bijective_of_homEquiv
#check @LinearStudy.topOpenRestrictionIntegerPoint
#print axioms LinearStudy.topOpenRestrictionIntegerPoint
#check @LinearStudy.topOpenRestrictionIntegerPoint_comp
#print axioms LinearStudy.topOpenRestrictionIntegerPoint_comp
#check @LinearStudy.topOpenRestrictionPointedExt_zero_bijective
#print axioms LinearStudy.topOpenRestrictionPointedExt_zero_bijective
#check @LinearStudy.topOpenFreeSheafExtActualHAddEquiv
#print axioms LinearStudy.topOpenFreeSheafExtActualHAddEquiv
#check @LinearStudy.topOpenFreeSheafExt_subsingleton_of_actualH
#print axioms LinearStudy.topOpenFreeSheafExt_subsingleton_of_actualH
#check @LinearStudy.topCechFiniteFreeSheafTermIso
#print axioms LinearStudy.topCechFiniteFreeSheafTermIso
#check @LinearStudy.topCechFiniteFreeSheafTerm_ext_subsingleton
#print axioms LinearStudy.topCechFiniteFreeSheafTerm_ext_subsingleton
#check @LinearStudy.topFiniteCech_actualHigherH_vanish_of_localAcyclic
#print axioms LinearStudy.topFiniteCech_actualHigherH_vanish_of_localAcyclic
#print LinearStudy.chainOpcycleSequence
#print LinearStudy.chainOpcycleSequenceIsCokernel
#print LinearStudy.chainActualHomCochain
#print LinearStudy.chainResolutionOpcycleZeroIso
#print LinearStudy.topOpenAbelianSheafRestriction
#print LinearStudy.topOpenAbelianSheafRestriction_additive
#print LinearStudy.topOpenAbelianSheafRestriction_preservesFiniteLimits
#print LinearStudy.topOpenAbelianSheafRestriction_preservesColimits
#print LinearStudy.topOpenRestrictionGlobalSectionsIso
#print LinearStudy.topOpenRestrictionHomAddEquiv
#print LinearStudy.topOpenRestrictionIntegerPoint
#print LinearStudy.topOpenFreeSheafExtActualHAddEquiv
#print LinearStudy.topCechFiniteFreeSheafTermIso
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.chainOpcycleSequence,false),(`LinearStudy.chainOpcycleSequenceIsCokernel,false),(`LinearStudy.chainOpcycleSequence_shortExact,true),(`LinearStudy.chainActualHomCochain,false),(`LinearStudy.chainActualHomExact_opcycle_extension,true),(`LinearStudy.acyclicChainOpcycle_ext_subsingleton,true),(`LinearStudy.chainResolutionOpcycleZeroIso,false),(`LinearStudy.acyclicResolution_ext_subsingleton,true),(`LinearStudy.ext_subsingleton_of_source_iso,true),(`LinearStudy.finiteCoproduct_ext_subsingleton,true),(`LinearStudy.topOpenAbelianSheafRestriction,false),(`LinearStudy.topOpenAbelianSheafRestriction_additive,true),(`LinearStudy.topOpenAbelianSheafRestriction_preservesFiniteLimits,true),(`LinearStudy.topOpenAbelianSheafRestriction_preservesColimits,true),(`LinearStudy.topOpenAbelianSheafRestriction_isFlasque,true),(`LinearStudy.topOpenRestrictionGlobalSectionsIso,false),(`LinearStudy.topOpenRestrictionGlobalSectionsIso_naturality,true),(`LinearStudy.topOpenRestrictionHomAddEquiv,false),(`LinearStudy.topOpenRestrictionHomAddEquiv_postcompose,true),(`LinearStudy.pointedExactFunctorExtMap_zero_bijective_of_homEquiv,true),(`LinearStudy.topOpenRestrictionIntegerPoint,false),(`LinearStudy.topOpenRestrictionIntegerPoint_comp,true),(`LinearStudy.topOpenRestrictionPointedExt_zero_bijective,true),(`LinearStudy.topOpenFreeSheafExtActualHAddEquiv,false),(`LinearStudy.topOpenFreeSheafExt_subsingleton_of_actualH,true),(`LinearStudy.topCechFiniteFreeSheafTermIso,false),(`LinearStudy.topCechFiniteFreeSheafTerm_ext_subsingleton,true),(`LinearStudy.topFiniteCech_actualHigherH_vanish_of_localAcyclic,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
