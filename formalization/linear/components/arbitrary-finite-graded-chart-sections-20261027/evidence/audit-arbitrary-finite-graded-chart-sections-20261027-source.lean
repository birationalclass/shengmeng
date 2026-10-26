module
import all Linear.ActualChartQuotientZero
import all Linear.LocalizedOriginalKernelCoefficientZero
import all Linear.NativeGradedWeightedSurjection
import all Linear.NativeChartKernelQuotientInjective
import all Linear.NativeFiniteGradedTorsionChartSections
import all Linear.NativeFiniteGradedTorsionBaseSourceSections
import all Linear.NativeGeneralSourceAmbientCechSections
set_option maxHeartbeats 5000
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.actualChartQuotient_zero
#print axioms LinearStudy.actualChartQuotient_zero
#check @LinearStudy.localizedOriginalKernelCoefficient_comp_zero
#print axioms LinearStudy.localizedOriginalKernelCoefficient_comp_zero
#check @LinearStudy.nativeGradedModuleAwayDegreeZeroCoefficientMap_surjective
#print axioms LinearStudy.nativeGradedModuleAwayDegreeZeroCoefficientMap_surjective
#check @LinearStudy.nativeGradedModuleAwayDegreeZeroCoefficientMap_kernel_zero
#print axioms LinearStudy.nativeGradedModuleAwayDegreeZeroCoefficientMap_kernel_zero
#check @LinearStudy.nativeProjectiveChartDegreeZeroSectionMap_zero_of_kernel
#print axioms LinearStudy.nativeProjectiveChartDegreeZeroSectionMap_zero_of_kernel
#check @LinearStudy.nativeProjectiveChartDegreeZeroSectionMap_injective_of_kernel
#print axioms LinearStudy.nativeProjectiveChartDegreeZeroSectionMap_injective_of_kernel
#check @LinearStudy.nativeFiniteGradedIndependentCechProductSectionMap_injective_general
#print axioms LinearStudy.nativeFiniteGradedIndependentCechProductSectionMap_injective_general
#check @LinearStudy.nativeFiniteGradedIndependentCechProductSectionMap_bijective_general
#print axioms LinearStudy.nativeFiniteGradedIndependentCechProductSectionMap_bijective_general
#check @LinearStudy.nativeFiniteGradedIndependentSourceCechProductSectionMap_bijective_general
#print axioms LinearStudy.nativeFiniteGradedIndependentSourceCechProductSectionMap_bijective_general
#check @LinearStudy.nativeIndependentSourceAmbientCechSectionAddEquiv_general
#print axioms LinearStudy.nativeIndependentSourceAmbientCechSectionAddEquiv_general
#print LinearStudy.nativeIndependentSourceAmbientCechSectionAddEquiv_general
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool × Bool) := [(`LinearStudy.actualChartQuotient_zero,true,true),(`LinearStudy.localizedOriginalKernelCoefficient_comp_zero,true,true),(`LinearStudy.nativeGradedModuleAwayDegreeZeroCoefficientMap_surjective,true,true),(`LinearStudy.nativeGradedModuleAwayDegreeZeroCoefficientMap_kernel_zero,true,true),(`LinearStudy.nativeProjectiveChartDegreeZeroSectionMap_zero_of_kernel,true,true),(`LinearStudy.nativeProjectiveChartDegreeZeroSectionMap_injective_of_kernel,true,true),(`LinearStudy.nativeFiniteGradedIndependentCechProductSectionMap_injective_general,true,true),(`LinearStudy.nativeFiniteGradedIndependentCechProductSectionMap_bijective_general,true,true),(`LinearStudy.nativeFiniteGradedIndependentSourceCechProductSectionMap_bijective_general,true,true),(`LinearStudy.nativeIndependentSourceAmbientCechSectionAddEquiv_general,false,false)]
  let env ← Lean.getEnv
  for (n,want,wantTheorem) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
    let kernelKind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | _ => "other"
    unless kernelKind == (if wantTheorem then "theorem" else "definition") do
      throwError m!"Incorrect kernel declaration kind: {n}"
    Lean.logInfo m!"KINDCHECK:{n}:{kernelKind}"
