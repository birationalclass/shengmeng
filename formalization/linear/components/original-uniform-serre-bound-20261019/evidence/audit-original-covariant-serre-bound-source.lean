module
import all Linear.ProjectivePulledOriginalCovariantSerreBound
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.projectivePulledOriginalStructureTwistSerreBoundStatement
#print axioms LinearStudy.projectivePulledOriginalStructureTwistSerreBoundStatement
#check @LinearStudy.projectivePulledOriginalCovariantAtSerreTwistStatement
#print axioms LinearStudy.projectivePulledOriginalCovariantAtSerreTwistStatement
#check @LinearStudy.projectivePulledOriginalCovariantAtSerreTwistStatement_of_Serre
#print axioms LinearStudy.projectivePulledOriginalCovariantAtSerreTwistStatement_of_Serre
#check @LinearStudy.projectivePulledOriginal_uniformCovariantExact_from_Serre
#print axioms LinearStudy.projectivePulledOriginal_uniformCovariantExact_from_Serre
#check @LinearStudy.projectivePulledOriginal_uniformCovariantExact_above_from_Serre
#print axioms LinearStudy.projectivePulledOriginal_uniformCovariantExact_above_from_Serre
#print LinearStudy.projectivePulledOriginalStructureTwistSerreBoundStatement
#print LinearStudy.projectivePulledOriginalCovariantAtSerreTwistStatement
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.projectivePulledOriginalStructureTwistSerreBoundStatement,false),(`LinearStudy.projectivePulledOriginalCovariantAtSerreTwistStatement,false),(`LinearStudy.projectivePulledOriginalCovariantAtSerreTwistStatement_of_Serre,true),(`LinearStudy.projectivePulledOriginal_uniformCovariantExact_from_Serre,true),(`LinearStudy.projectivePulledOriginal_uniformCovariantExact_above_from_Serre,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
