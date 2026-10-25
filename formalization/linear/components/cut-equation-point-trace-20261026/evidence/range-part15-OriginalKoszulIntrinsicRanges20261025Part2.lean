module
import all Linear.CochainConeLiftDerivedBridge
import all Linear.CochainConeLiftTriangleDegrees
import all Linear.CochainKInjectiveDerivedCocycle
import all Linear.CochainOpcycleInjectiveBoundaryComponents
import all Linear.CochainOpcycleIteratedBoundary
import all Linear.CochainOpcycleSourceSequence
import all Linear.CochainResolutionExtClass
import all Linear.CochainResolutionInjectiveCocycle
import all Linear.CochainResolutionIteratedSourceBoundary
import all Linear.CochainResolutionSourceBoundaryClass
import all Linear.CochainResolutionSourceBoundaryFamily
import all Linear.CochainResolutionSourceLiftEquations
import all Linear.CochainResolutionTopExtNaturality
import all Linear.CochainResolutionTopHomotopyEquations
import all Linear.CochainSingleSupportComponents
import all Linear.CochainSourceLiftClasses
import all Linear.CochainSourceLiftComponentRecurrence
import all Linear.CochainSourceLiftFamily
import all Linear.CochainSourceLiftInitialClass
import all Linear.CochainSourceLiftRecurrence
import all Linear.CochainSourceLiftSigns
import all Linear.CochainSourceLiftTerminalClass
import all Linear.CommonNormalCoordinates
import all Linear.CommonPolynomialCoordinates
import all Linear.CompleteIntersectionChange
import all Linear.CompletionCongr
import all Linear.CompletionLocalization
import all Linear.CompletionQuotient
import all Linear.ConormalGenerators
import all Linear.ContractionPairing
import all Linear.CoordinateRatioField
import all Linear.CutLocalRegularSequence
import all Linear.DeterminantAnnihilator
import all Linear.DiagonalNonzero
import all Linear.DiagonalNormalization
import all Linear.DiagonalTrace
import all Linear.DiscreteClosedMapSupportFlasque
import all Linear.DiscreteSheafCohomology
import all Linear.DiscreteSheafFlasque
import all Linear.DiscreteSheafPushforwardCohomology
import all Linear.DiscreteSheafPushforwardExact
import all Linear.DiscreteSheafSectionsExact
import all Linear.DoublePoint
import all Linear.Duality
import all Linear.ExtendScalarsActualTensor
import all Linear.FieldEndomorphismMap
import all Linear.FilteredIdeal
import all Linear.FiniteCutArtinianTopology
import all Linear.FiniteCutPrimeCoordinates
import all Linear.FiniteLinearProjectionGoodOpen
import all Linear.FiniteNormalizationFilteredBound
import all Linear.FinitePresentationHomCodomainLocalization
import all Linear.FiniteProjectionTensorFibers
import all Linear.FiniteRationalPoints
import all Linear.FiniteReducedAlgebraPoints
import all Linear.FiniteReducedClosedBaseChange
import all Linear.FiniteReducedLocalCut
import all Linear.FiniteSpecialization
import all Linear.FiniteTypeFieldEndomorphism
import all Linear.FiniteTypeRationalPoint
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 50000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.CochainConeLiftDerivedBridge","Linear.CochainConeLiftTriangleDegrees","Linear.CochainKInjectiveDerivedCocycle","Linear.CochainOpcycleInjectiveBoundaryComponents","Linear.CochainOpcycleIteratedBoundary","Linear.CochainOpcycleSourceSequence","Linear.CochainResolutionExtClass","Linear.CochainResolutionInjectiveCocycle","Linear.CochainResolutionIteratedSourceBoundary","Linear.CochainResolutionSourceBoundaryClass","Linear.CochainResolutionSourceBoundaryFamily","Linear.CochainResolutionSourceLiftEquations","Linear.CochainResolutionTopExtNaturality","Linear.CochainResolutionTopHomotopyEquations","Linear.CochainSingleSupportComponents","Linear.CochainSourceLiftClasses","Linear.CochainSourceLiftComponentRecurrence","Linear.CochainSourceLiftFamily","Linear.CochainSourceLiftInitialClass","Linear.CochainSourceLiftRecurrence","Linear.CochainSourceLiftSigns","Linear.CochainSourceLiftTerminalClass","Linear.CommonNormalCoordinates","Linear.CommonPolynomialCoordinates","Linear.CompleteIntersectionChange","Linear.CompletionCongr","Linear.CompletionLocalization","Linear.CompletionQuotient","Linear.ConormalGenerators","Linear.ContractionPairing","Linear.CoordinateRatioField","Linear.CutLocalRegularSequence","Linear.DeterminantAnnihilator","Linear.DiagonalNonzero","Linear.DiagonalNormalization","Linear.DiagonalTrace","Linear.DiscreteClosedMapSupportFlasque","Linear.DiscreteSheafCohomology","Linear.DiscreteSheafFlasque","Linear.DiscreteSheafPushforwardCohomology","Linear.DiscreteSheafPushforwardExact","Linear.DiscreteSheafSectionsExact","Linear.DoublePoint","Linear.Duality","Linear.ExtendScalarsActualTensor","Linear.FieldEndomorphismMap","Linear.FilteredIdeal","Linear.FiniteCutArtinianTopology","Linear.FiniteCutPrimeCoordinates","Linear.FiniteLinearProjectionGoodOpen","Linear.FiniteNormalizationFilteredBound","Linear.FinitePresentationHomCodomainLocalization","Linear.FiniteProjectionTensorFibers","Linear.FiniteRationalPoints","Linear.FiniteReducedAlgebraPoints","Linear.FiniteReducedClosedBaseChange","Linear.FiniteReducedLocalCut","Linear.FiniteSpecialization","Linear.FiniteTypeFieldEndomorphism","Linear.FiniteTypeRationalPoint"]
  let isOwn := fun (n : Lean.Name) => match env.getModuleIdxFor? n with
    | none => false
    | some idx => (env.header.moduleNames[idx]!).toString.startsWith "Linear."
  let mut count : Nat := 0
  for (name,info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[idx]!
    unless selected.contains modName.toString do continue
    let deps := String.intercalate "," (info.getUsedConstantsAsSet.toArray.toList.filter isOwn |>.map toString)
    Lean.logInfo m!"SOURCE_DEPENDENCIES|{name}|{modName}|{deps}"
    let some ranges ← Lean.findDeclarationRanges? name | continue
    let q := ranges.range
    Lean.logInfo m!"SOURCE_RANGE|{name}|{modName}|{q.pos.line}|{q.pos.column}|{q.endPos.line}|{q.endPos.column}|{deps}"
    count := count+1
  Lean.logInfo m!"SOURCE_RANGE_COUNT|{count}"
