module
public import Linear.NativeOriginalScalarPackages
public import Linear.OriginalNativeScalarPackageActionRefold
public import Lean
@[expose] public section
set_option maxHeartbeats 5000
open Lean Meta Elab Command

/-- Specialize the checked native package action while preserving the
exact dependent type of its middle projection. -/
elab "check_native_original_package_action_refold " target:ident : command => do
  let stx ← getRef
  withExporting (isExporting := true) <| liftTermElabM do
    let p ← getConstInfo ``LinearStudy.nativeOriginalActualHScalarOperator_eq_rawMap
    let levels := p.levelParams.map Level.param
    forallTelescope p.type fun xs pt => do
      let args ← nativeOriginalScalarContext pt.getAppArgs.back!.getAppArgs.back! xs.back!
      let h := mkAppN (mkConst ``LinearStudy.originalNativeScalarPackageAction_refold_heq levels) args
      let type ← mkForallFVars xs (← inferType h)
      let value ← mkLambdaFVars xs h
      addDecl (.thmDecl {name := target.getId, levelParams := p.levelParams, type, value})
        (forceExpose := true)
  addDeclarationRangesFromSyntax target.getId stx target

check_native_original_package_action_refold LinearStudy.nativeOriginalScalarPackageAction_refold_heq
#check LinearStudy.nativeOriginalScalarPackageAction_refold_heq
#print axioms LinearStudy.nativeOriginalScalarPackageAction_refold_heq
