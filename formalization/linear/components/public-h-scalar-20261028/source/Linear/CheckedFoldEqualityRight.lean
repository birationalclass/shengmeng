module
public import Lean
@[expose] public section
set_option maxHeartbeats 5000
open Lean Meta Elab Command
/-- Fold the right side of a checked equality using a safe public definition.
Only the existing binder arguments are supplied;the normal kernel checks
both the new full equality and its existing proof. -/
elab "checked_fold_equality_right " source:ident " with " cached:ident
    " as " target:ident : command => do
  let stx ← getRef
  withExporting (isExporting := true) <| liftTermElabM do
    let ci ← getConstInfo source.getId
    unless ci.isTheorem do throwError "Expected ordinary theorem"
    let di ← getConstInfoDefn cached.getId
    unless di.safety == .safe do throwError "Expected safe definition"
    unless ci.levelParams == di.levelParams do throwError "Universe mismatch"
    let levels := ci.levelParams.map Level.param
    forallTelescope ci.type fun xs prop => do
      let prop ← whnf prop
      let some _ ← matchEq? prop | throwError "Expected equality"
      let right := mkAppN (mkConst cached.getId levels) xs
      let newProp := mkAppN prop.getAppFn (prop.getAppArgs.set! 2 right)
      let type ← mkForallFVars xs newProp
      let value := mkConst source.getId levels
      addDecl (.thmDecl {name := target.getId,levelParams := ci.levelParams,type,value})
        (forceExpose := true)
  addDeclarationRangesFromSyntax target.getId stx target
