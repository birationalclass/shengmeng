module
public import Linear.OriginalNativeScalarPackageAction
public import Lean
@[expose] public section
set_option maxHeartbeats 5000
open Lean Meta Elab Command

/-- State the checked native action with the dependent package projection
type itself, so subsequent compositions share the exact same middle type. -/
elab "check_original_native_scalar_package_refold " target:ident : command => do
  let stx ← getRef
  withExporting (isExporting := true) <| liftTermElabM do
    let q ← getConstInfo ``LinearStudy.originalNativeScalarPackageAction_heq
    let levels := q.levelParams.map Level.param
    forallTelescope q.type fun xs prop => do
      unless prop.isAppOfArity ``HEq 4 do throwError "Expected native package action"
      let args := prop.getAppArgs
      let leftType ← inferType args[1]!
      let statement := mkAppN prop.getAppFn #[leftType,args[1]!,args[2]!,args[3]!]
      let type ← mkForallFVars xs statement
      let value ← mkLambdaFVars xs (mkAppN (mkConst q.name levels) xs)
      addDecl (.thmDecl {name := target.getId, levelParams := q.levelParams, type, value})
        (forceExpose := true)
  addDeclarationRangesFromSyntax target.getId stx target

check_original_native_scalar_package_refold LinearStudy.originalNativeScalarPackageAction_refold_heq
#check LinearStudy.originalNativeScalarPackageAction_refold_heq
#print axioms LinearStudy.originalNativeScalarPackageAction_refold_heq
