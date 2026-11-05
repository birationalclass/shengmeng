module
public import Linear.NativeGeneralModuleHScalarProof
public import Linear.NativeOriginalPublicScalarIntrinsic
public import Lean
@[expose] public section
set_option maxHeartbeats 5000
open Lean Meta Elab Command

/-- Specialize the independently checked scalar calibration at the
exact target operator of the general module-valued comparison square. -/
elab "check_general_public_h_intrinsic_witness " target:ident : command => do
  let stx ← getRef
  withExporting (isExporting := true) <| liftTermElabM do
    let square ← getConstInfo
      ``LinearStudy.nativeFiniteNormalization_generalModuleCechActualH_baseScalar_proof
    let calibration ← getConstInfo
      ``LinearStudy.nativeOriginalActualHPublicScalarOperator_heq_intrinsic
    let levels := square.levelParams.map Level.param
    unless calibration.levelParams.length == levels.length do
      throwError "The square and calibration universes disagree"
    let arity ← forallTelescope calibration.type fun xs _ => pure xs.size
    forallTelescope square.type fun xs prop => do
      let mut eq := prop
      while eq.isLet do
        eq := eq.letBody!.instantiate1 eq.letValue!
      unless eq.isAppOfArity ``Eq 3 do
        throwError "Expected the exact original scalar square"
      let rhs := eq.getAppArgs.back!
      let some op := rhs.find? (fun e =>
          e.isAppOfArity ``LinearStudy.nativeOriginalActualHPublicScalarOperator arity) |
        throwError "The target of the square is not the literal public operator"
      let proof := mkAppN (mkConst calibration.name levels) op.getAppArgs
      let ht ← inferType proof
      unless ht.isAppOfArity ``HEq 4 && ht.getAppArgs[1]! == op do
        throwError "The intrinsic witness changed the exact operator"
      let type ← mkForallFVars xs ht
      let value ← mkLambdaFVars xs proof
      addDecl (.thmDecl {name := target.getId, levelParams := square.levelParams, type, value})
        (forceExpose := true)
  addDeclarationRangesFromSyntax target.getId stx target

check_general_public_h_intrinsic_witness LinearStudy.nativeGeneralModuleH_publicOperator_heq_intrinsic
#check LinearStudy.nativeGeneralModuleH_publicOperator_heq_intrinsic
#print axioms LinearStudy.nativeGeneralModuleH_publicOperator_heq_intrinsic
