module
public import Linear.NativeOriginalHScalarCachedOperator
public import Lean
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 5000
open Lean Meta Elab Command

/-- Specialize the existing mathlib functorH_map theorem with the
literal site, instances and coefficient map of the original operator.
The ordinary kernel checks the resulting equality. -/
elab "check_native_original_scalar_map_formula " target:ident : command => do
  let stx ← getRef
  withExporting (isExporting := true) <| liftTermElabM do
    let d ← getConstInfoDefn ``LinearStudy.nativeOriginalActualHScalarOperator
    unless d.safety == .safe do throwError "Expected safe original operator"
    let levels := d.levelParams.map Level.param
    forallTelescope d.type fun xs _ => do
      let original := (mkAppN d.value xs).headBeta
      unless original.isAppOf ``CategoryTheory.Functor.map do
        throwError "Expected the literal original coefficient functor map"
      let args := original.getAppArgs
      unless args.size == 8 do throwError "Unexpected functor map arity"
      let F := args[4]!
      unless F.isAppOf ``CategoryTheory.Sheaf.functorH do
        throwError "Expected actual sheaf H"
      let proof := mkAppN
        (mkConst ``CategoryTheory.Sheaf.functorH_map F.getAppFn.constLevels!)
        (F.getAppArgs ++ args.extract 5 8)
      let pt ← inferType proof
      unless pt.isAppOfArity ``Eq 3 do throwError "Expected map equality"
      let eqArgs := pt.getAppArgs
      unless eqArgs[1]! == original do throwError "The original map is not the left side"
      let folded := mkApp3 pt.getAppFn eqArgs[0]! (mkAppN (mkConst d.name levels) xs) eqArgs[2]!
      let type ← mkForallFVars xs folded
      let value ← mkLambdaFVars xs proof
      addDecl (.thmDecl {name := target.getId, levelParams := d.levelParams, type, value})
        (forceExpose := true)
  addDeclarationRangesFromSyntax target.getId stx target

check_native_original_scalar_map_formula LinearStudy.nativeOriginalActualHScalarOperator_eq_rawMap
#check LinearStudy.nativeOriginalActualHScalarOperator_eq_rawMap
#print axioms LinearStudy.nativeOriginalActualHScalarOperator_eq_rawMap
