module
public import Lean
@[expose] public section
set_option maxHeartbeats 5000
open Lean Meta Elab Command
/-- Give an existing safe proof its EXACT original type as an ordinary
opaque theorem. No type is inferred again or changed. The ordinary
kernel checks the supplied proof constant against that identical type. -/
elab "checked_opaque_proof " source:ident " as " target:ident : command => do
  let stx ← getRef
  withExporting (isExporting := true) <| liftTermElabM do
    let ci ← getConstInfo source.getId
    match ci with
    | .defnInfo d => unless d.safety == .safe do throwError "Only safe proof definitions are accepted"
    | .thmInfo _ => pure ()
    | _ => throwError "Expected an existing safe proof"
    unless (← isProp ci.type) do throwError "The existing constant must be a proof"
    let value := mkConst source.getId (ci.levelParams.map Level.param)
    addDecl (.thmDecl {name := target.getId,levelParams := ci.levelParams,type := ci.type,value})
      (forceExpose := true)
  addDeclarationRangesFromSyntax target.getId stx target
