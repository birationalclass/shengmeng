module
import all Linear.RelativeAcyclicCovariantBoundary
import all Linear.ExtUnitSmulComposition
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.relativeAcyclicCovariantBoundary_surjective
#print axioms LinearStudy.relativeAcyclicCovariantBoundary_surjective
#check @LinearStudy.relativeAcyclicCovariantBoundary_injective
#print axioms LinearStudy.relativeAcyclicCovariantBoundary_injective
#check @LinearStudy.ext_comp_unit_smul
#print axioms LinearStudy.ext_comp_unit_smul
#check @LinearStudy.ext_unit_smul_comp
#print axioms LinearStudy.ext_unit_smul_comp
#check @LinearStudy.ext_comp_unit_smul_zero_iff
#print axioms LinearStudy.ext_comp_unit_smul_zero_iff
#check @LinearStudy.ext_postcomp_unit_smul_surjective
#print axioms LinearStudy.ext_postcomp_unit_smul_surjective
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.relativeAcyclicCovariantBoundary_surjective,true),(`LinearStudy.relativeAcyclicCovariantBoundary_injective,true),(`LinearStudy.ext_comp_unit_smul,true),(`LinearStudy.ext_unit_smul_comp,true),(`LinearStudy.ext_comp_unit_smul_zero_iff,true),(`LinearStudy.ext_postcomp_unit_smul_surjective,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
