module
import all Linear.CompletionCongr
import all Linear.CompletionLocalization
import all Linear.CompletionQuotient
import all Linear.ConcreteAdditiveEquivSquare
import all Linear.ContractionPairing
import all Linear.CoordinateNativeCechHomologyModel
import all Linear.CoordinateRatioField
import all Linear.CoverGeneratedTerminalPresheaf
import all Linear.DeterminantAnnihilator
import all Linear.DiagonalNonzero
import all Linear.DiagonalNormalization
import all Linear.DiagonalTrace
import all Linear.DiscreteSheafCohomology
import all Linear.DiscreteSheafFlasque
import all Linear.DiscreteSheafPushforwardCohomology
import all Linear.DiscreteSheafPushforwardExact
import all Linear.DiscreteSheafSectionsExact
import all Linear.DoublePoint
import all Linear.Duality
import all Linear.ExtZeroHomCoefficientNaturality
import all Linear.ExtendScalarsActualTensor
import all Linear.FieldCoextensionRankOne
import all Linear.FieldEndomorphismMap
import all Linear.FilteredIdeal
import all Linear.FiniteBiproductDualCoordinates
import all Linear.FiniteBiproductMatrixDuality
import all Linear.FiniteCoextensionModule
import all Linear.FiniteCoextensionTorsionFree
import all Linear.FiniteCoextensionUpper
import all Linear.FiniteCoextensionUpperModule
import all Linear.FiniteCoproductExtAcyclic
import all Linear.FiniteCutArtinianTopology
import all Linear.FiniteDomainDualNonzero
import all Linear.FiniteFunctionalLocalization
import all Linear.FiniteFunctionalLocalizationEquiv
import all Linear.FiniteGradedNormalizationIrrelevantRadical
import all Linear.FiniteNativeCoextensionLocalization
import all Linear.FiniteNormalizationCoordinateCover
import all Linear.FinitePiDualEquiv
import all Linear.FiniteSpecialization
import all Linear.FiniteTypeFieldEndomorphism
import all Linear.FiniteTypeHomogeneousChartNoetherian
import all Linear.FiniteTypeNativeProjActualCohomology
import all Linear.FirstJet
import all Linear.FirstSyzygy
import all Linear.FormalCechFormalEvaluation
import all Linear.FormalCechPresheafResolution
import all Linear.FormalCechScalarIdentity
import all Linear.FormalCechSimplicialResolution
import all Linear.FormalCechYonedaAdjunction
import all Linear.FormalCoproductContravariantCoefficientNaturality
import all Linear.FormalCoproductContravariantEvaluation
import all Linear.FormalCoproductCovariantEvaluation
import all Linear.FormalCoproductFunctorMap
import all Linear.FormalProductCoefficientNaturality
import all Linear.FormalProductEvaluationWhiskering
import all Linear.FreeOpenHomCoefficientNaturality
import all Linear.FullCechZeroRelations
import all Linear.FullFreePresheafValueCech
import all Linear.FunctionalSourceLocalization
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 50000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.CompletionCongr","Linear.CompletionLocalization","Linear.CompletionQuotient","Linear.ConcreteAdditiveEquivSquare","Linear.ContractionPairing","Linear.CoordinateNativeCechHomologyModel","Linear.CoordinateRatioField","Linear.CoverGeneratedTerminalPresheaf","Linear.DeterminantAnnihilator","Linear.DiagonalNonzero","Linear.DiagonalNormalization","Linear.DiagonalTrace","Linear.DiscreteSheafCohomology","Linear.DiscreteSheafFlasque","Linear.DiscreteSheafPushforwardCohomology","Linear.DiscreteSheafPushforwardExact","Linear.DiscreteSheafSectionsExact","Linear.DoublePoint","Linear.Duality","Linear.ExtZeroHomCoefficientNaturality","Linear.ExtendScalarsActualTensor","Linear.FieldCoextensionRankOne","Linear.FieldEndomorphismMap","Linear.FilteredIdeal","Linear.FiniteBiproductDualCoordinates","Linear.FiniteBiproductMatrixDuality","Linear.FiniteCoextensionModule","Linear.FiniteCoextensionTorsionFree","Linear.FiniteCoextensionUpper","Linear.FiniteCoextensionUpperModule","Linear.FiniteCoproductExtAcyclic","Linear.FiniteCutArtinianTopology","Linear.FiniteDomainDualNonzero","Linear.FiniteFunctionalLocalization","Linear.FiniteFunctionalLocalizationEquiv","Linear.FiniteGradedNormalizationIrrelevantRadical","Linear.FiniteNativeCoextensionLocalization","Linear.FiniteNormalizationCoordinateCover","Linear.FinitePiDualEquiv","Linear.FiniteSpecialization","Linear.FiniteTypeFieldEndomorphism","Linear.FiniteTypeHomogeneousChartNoetherian","Linear.FiniteTypeNativeProjActualCohomology","Linear.FirstJet","Linear.FirstSyzygy","Linear.FormalCechFormalEvaluation","Linear.FormalCechPresheafResolution","Linear.FormalCechScalarIdentity","Linear.FormalCechSimplicialResolution","Linear.FormalCechYonedaAdjunction","Linear.FormalCoproductContravariantCoefficientNaturality","Linear.FormalCoproductContravariantEvaluation","Linear.FormalCoproductCovariantEvaluation","Linear.FormalCoproductFunctorMap","Linear.FormalProductCoefficientNaturality","Linear.FormalProductEvaluationWhiskering","Linear.FreeOpenHomCoefficientNaturality","Linear.FullCechZeroRelations","Linear.FullFreePresheafValueCech","Linear.FunctionalSourceLocalization"]
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
