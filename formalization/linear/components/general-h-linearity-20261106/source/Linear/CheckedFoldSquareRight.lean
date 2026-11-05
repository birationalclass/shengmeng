module
public import Lean
public import Mathlib.CategoryTheory.Functor.Basic
@[expose] public section
set_option maxHeartbeats 5000
open Lean Meta Elab Command
/-- Fold only the literal final scalar map in a checked square.
The existing public map has exactly the same arguments and the ordinary
kernel checks the complete resulting proof. No equality is postulated. -/
elab "checked_fold_square_right " source:ident " with " cached:ident
    " as " target:ident : command => do
  let stx ← getRef
  withExporting (isExporting := true) <| liftTermElabM do
    let ci ← getConstInfo source.getId
    unless ci.isTheorem do throwError "Expected an existing ordinary theorem"
    let di ← getConstInfoDefn cached.getId
    unless di.safety == .safe do throwError "Expected a safe cached map"
    unless ci.levelParams == di.levelParams do throwError "Universe parameters must match"
    let levels := ci.levelParams.map Level.param
    forallTelescope ci.type fun xs prop => do
      let prop ← whnf prop
      let some (_,_,rhs) ← matchEq? prop | throwError "Expected an equality"
      unless rhs.isAppOf ``CategoryTheory.CategoryStruct.comp do throwError "Expected right composition"
      let args := rhs.getAppArgs
      let map := mkAppN (mkConst cached.getId levels) xs
      let rhs2 := mkAppN rhs.getAppFn (args.set! (args.size-1) map)
      let pargs := prop.getAppArgs
      let newProp := mkAppN prop.getAppFn (pargs.set! 2 rhs2)
      let type ← mkForallFVars xs newProp
      let value := mkConst source.getId levels
      addDecl (.thmDecl {name := target.getId,levelParams := ci.levelParams,type,value})
        (forceExpose := true)
  addDeclarationRangesFromSyntax target.getId stx target
