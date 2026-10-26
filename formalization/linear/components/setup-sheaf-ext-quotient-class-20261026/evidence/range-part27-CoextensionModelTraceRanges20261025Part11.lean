module
import all Linear.ProjectiveLaurentInitialGenerators
import all Linear.ProjectiveLaurentInitialRestriction
import all Linear.ProjectiveLaurentNatExponent
import all Linear.ProjectiveLaurentNoninitialRestriction
import all Linear.ProjectiveLaurentPositiveBoundary
import all Linear.ProjectiveLaurentReindexShift
import all Linear.ProjectiveLaurentScaledSectionShift
import all Linear.ProjectiveLaurentSectionShift
import all Linear.ProjectiveLaurentShiftCoefficients
import all Linear.ProjectiveLaurentShiftComplex
import all Linear.ProjectiveLaurentShiftLinear
import all Linear.ProjectiveLaurentShiftProduct
import all Linear.ProjectiveLaurentTopWeight
import all Linear.ProjectiveLaurentWeight
import all Linear.ProjectiveLaurentWeightAssembly
import all Linear.ProjectiveLaurentWeightComponents
import all Linear.ProjectiveLaurentWeightShift
import all Linear.ProjectiveLaurentZeroCycle
import all Linear.ProjectiveMonomialDualTranspose
import all Linear.ProjectiveMonomialFullHomologyNaturality
import all Linear.ProjectiveMonomialResidueDuality
import all Linear.ProjectiveMonomialResidueNaturality
import all Linear.ProjectiveMonomialTopHomologyNaturality
import all Linear.ProjectiveMonomialTopQuotientNaturality
import all Linear.ProjectiveNegativeWeightComplement
import all Linear.ProjectiveOriginalGradedPolynomialMultiply
import all Linear.ProjectivePositiveMonomialWeight
import all Linear.ProjectiveRatioChartKernel
import all Linear.ProjectiveRationalChart
import all Linear.ProjectiveRationalInvariance
import all Linear.ProjectiveSpaceChart
import all Linear.ProjectiveStandardIntersectionRing
import all Linear.QuasicoherentAffineOpenSections
import all Linear.RadicalProjMap
import all Linear.Reduction
import all Linear.RegularGeneratorsFree
import all Linear.RegularSpecialization
import all Linear.RelativeJacobian
import all Linear.RelativeJacobianTrace
import all Linear.ResiduePairing
import all Linear.SchemeModuleActualAbelianScalarValue
import all Linear.SchemeModuleActualCohomologyGroup
import all Linear.SchemeModuleActualHBaseScalars
import all Linear.SchemeModuleActualHFunctorCalibration
import all Linear.SchemeModuleActualHGlobalSectionsModule
import all Linear.SchemeModuleActualHLinearCoefficientMap
import all Linear.SchemeModuleActualHScalarRingHom
import all Linear.SchemeModuleActualHSpecScalars
import all Linear.SchemeModuleAdditiveSheafColimits
import all Linear.SchemeModuleCohomologyPointedSource
import all Linear.SchemeModuleFiniteSupportCohomology
import all Linear.SchemeModuleFlasqueExtAcyclic
import all Linear.SchemeModuleFlasqueKernelSectionLifting
import all Linear.SchemeModuleFlasqueShortExact
import all Linear.SchemeModuleGlobalExtActualHCohomology
import all Linear.SchemeModuleGlobalExtActualHMap
import all Linear.SchemeModuleGlobalExtActualHZero
import all Linear.SchemeModuleGlobalExtActualHZeroCalibration
import all Linear.SchemeModuleGlobalSectionMorphism
import all Linear.SchemeModuleHomEvaluationRestriction
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 50000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.ProjectiveLaurentInitialGenerators","Linear.ProjectiveLaurentInitialRestriction","Linear.ProjectiveLaurentNatExponent","Linear.ProjectiveLaurentNoninitialRestriction","Linear.ProjectiveLaurentPositiveBoundary","Linear.ProjectiveLaurentReindexShift","Linear.ProjectiveLaurentScaledSectionShift","Linear.ProjectiveLaurentSectionShift","Linear.ProjectiveLaurentShiftCoefficients","Linear.ProjectiveLaurentShiftComplex","Linear.ProjectiveLaurentShiftLinear","Linear.ProjectiveLaurentShiftProduct","Linear.ProjectiveLaurentTopWeight","Linear.ProjectiveLaurentWeight","Linear.ProjectiveLaurentWeightAssembly","Linear.ProjectiveLaurentWeightComponents","Linear.ProjectiveLaurentWeightShift","Linear.ProjectiveLaurentZeroCycle","Linear.ProjectiveMonomialDualTranspose","Linear.ProjectiveMonomialFullHomologyNaturality","Linear.ProjectiveMonomialResidueDuality","Linear.ProjectiveMonomialResidueNaturality","Linear.ProjectiveMonomialTopHomologyNaturality","Linear.ProjectiveMonomialTopQuotientNaturality","Linear.ProjectiveNegativeWeightComplement","Linear.ProjectiveOriginalGradedPolynomialMultiply","Linear.ProjectivePositiveMonomialWeight","Linear.ProjectiveRatioChartKernel","Linear.ProjectiveRationalChart","Linear.ProjectiveRationalInvariance","Linear.ProjectiveSpaceChart","Linear.ProjectiveStandardIntersectionRing","Linear.QuasicoherentAffineOpenSections","Linear.RadicalProjMap","Linear.Reduction","Linear.RegularGeneratorsFree","Linear.RegularSpecialization","Linear.RelativeJacobian","Linear.RelativeJacobianTrace","Linear.ResiduePairing","Linear.SchemeModuleActualAbelianScalarValue","Linear.SchemeModuleActualCohomologyGroup","Linear.SchemeModuleActualHBaseScalars","Linear.SchemeModuleActualHFunctorCalibration","Linear.SchemeModuleActualHGlobalSectionsModule","Linear.SchemeModuleActualHLinearCoefficientMap","Linear.SchemeModuleActualHScalarRingHom","Linear.SchemeModuleActualHSpecScalars","Linear.SchemeModuleAdditiveSheafColimits","Linear.SchemeModuleCohomologyPointedSource","Linear.SchemeModuleFiniteSupportCohomology","Linear.SchemeModuleFlasqueExtAcyclic","Linear.SchemeModuleFlasqueKernelSectionLifting","Linear.SchemeModuleFlasqueShortExact","Linear.SchemeModuleGlobalExtActualHCohomology","Linear.SchemeModuleGlobalExtActualHMap","Linear.SchemeModuleGlobalExtActualHZero","Linear.SchemeModuleGlobalExtActualHZeroCalibration","Linear.SchemeModuleGlobalSectionMorphism","Linear.SchemeModuleHomEvaluationRestriction"]
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
