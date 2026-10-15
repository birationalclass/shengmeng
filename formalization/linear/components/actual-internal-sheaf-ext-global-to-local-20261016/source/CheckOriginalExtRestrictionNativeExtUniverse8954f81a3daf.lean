module
import all Linear.NativeExtUniverseTransport
set_option pp.deepTerms true
set_option pp.funBinderTypes true
set_option pp.universes true
#check @LinearStudy.nativeExtUniverseEquiv
#print axioms LinearStudy.nativeExtUniverseEquiv
#check @LinearStudy.nativeExtUniverseEquiv_hom
#print axioms LinearStudy.nativeExtUniverseEquiv_hom
#check @LinearStudy.nativeExtUniverseAddEquiv
#print axioms LinearStudy.nativeExtUniverseAddEquiv
#check @LinearStudy.nativeExtUniverseEquiv_comp
#print axioms LinearStudy.nativeExtUniverseEquiv_comp
#check @LinearStudy.nativeExtUniverseEquiv_mk₀
#print axioms LinearStudy.nativeExtUniverseEquiv_mk₀
#print LinearStudy.nativeExtUniverseEquiv
#print LinearStudy.nativeExtUniverseAddEquiv
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.nativeExtUniverseEquiv,false),(`LinearStudy.nativeExtUniverseEquiv_hom,true),(`LinearStudy.nativeExtUniverseAddEquiv,false),(`LinearStudy.nativeExtUniverseEquiv_comp,true),(`LinearStudy.nativeExtUniverseEquiv_mk₀,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
