module
import all Linear.OverOpenZeroPresheaf
import all Linear.OverOpenZeroPresheafFunctor
import all Linear.OverOpenZeroPresheafAdjunction
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.overOpenZeroObj
#print axioms LinearStudy.overOpenZeroObj
#check @LinearStudy.overOpenZeroMap
#print axioms LinearStudy.overOpenZeroMap
#check @LinearStudy.overOpenZeroMap_lof
#print axioms LinearStudy.overOpenZeroMap_lof
#check @LinearStudy.overOpenZeroMap_id
#print axioms LinearStudy.overOpenZeroMap_id
#check @LinearStudy.overOpenZeroMap_comp
#print axioms LinearStudy.overOpenZeroMap_comp
#check @LinearStudy.overOpenZeroPresheaf
#print axioms LinearStudy.overOpenZeroPresheaf
#check @LinearStudy.overOpenZeroPresheafHom
#print axioms LinearStudy.overOpenZeroPresheafHom
#check @LinearStudy.overOpenZeroPresheafFunctor
#print axioms LinearStudy.overOpenZeroPresheafFunctor
#check @LinearStudy.overOpenZeroPresheafFunctor_preservesMonomorphisms
#print axioms LinearStudy.overOpenZeroPresheafFunctor_preservesMonomorphisms
#check @LinearStudy.overOpenZeroHomRestrict
#print axioms LinearStudy.overOpenZeroHomRestrict
#check @LinearStudy.overOpenZeroHomExtend
#print axioms LinearStudy.overOpenZeroHomExtend
#check @LinearStudy.overOpenZeroHomExtend_lof
#print axioms LinearStudy.overOpenZeroHomExtend_lof
#check @LinearStudy.overOpenZeroHomEquiv
#print axioms LinearStudy.overOpenZeroHomEquiv
#check @LinearStudy.overOpenZeroPresheafAdjunction
#print axioms LinearStudy.overOpenZeroPresheafAdjunction
#print LinearStudy.overOpenZeroObj
#print LinearStudy.overOpenZeroMap
#print LinearStudy.overOpenZeroPresheaf
#print LinearStudy.overOpenZeroPresheafHom
#print LinearStudy.overOpenZeroPresheafFunctor
#print LinearStudy.overOpenZeroHomRestrict
#print LinearStudy.overOpenZeroHomExtend
#print LinearStudy.overOpenZeroHomEquiv
#print LinearStudy.overOpenZeroPresheafAdjunction
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.overOpenZeroObj,false),(`LinearStudy.overOpenZeroMap,false),(`LinearStudy.overOpenZeroMap_lof,true),(`LinearStudy.overOpenZeroMap_id,true),(`LinearStudy.overOpenZeroMap_comp,true),(`LinearStudy.overOpenZeroPresheaf,false),(`LinearStudy.overOpenZeroPresheafHom,false),(`LinearStudy.overOpenZeroPresheafFunctor,false),(`LinearStudy.overOpenZeroPresheafFunctor_preservesMonomorphisms,true),(`LinearStudy.overOpenZeroHomRestrict,false),(`LinearStudy.overOpenZeroHomExtend,false),(`LinearStudy.overOpenZeroHomExtend_lof,true),(`LinearStudy.overOpenZeroHomEquiv,false),(`LinearStudy.overOpenZeroPresheafAdjunction,false)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
