module
public import Lean
@[expose] public section
set_option maxHeartbeats 5000
open Lean Meta Elab Command
/-- Cache the literal right morphism of a checked equality with the exact
nominal Hom type carried by that equality. Ordinary kernel checking stays on. -/
elab "cache_checked_equality_right " source:ident " as " target:ident : command => do
  let stx ← getRef
  withExporting (isExporting := true) <| liftTermElabM do
    let ci ← getConstInfo source.getId
    unless ci.isTheorem do throwError "Expected ordinary theorem"
    forallTelescope ci.type fun xs prop => do
      let prop ← whnf prop
      let some (homTy,_,rhs) ← matchEq? prop | throwError "Expected equality"
      let type ← mkForallFVars xs homTy
      let value ← mkLambdaFVars xs rhs
      addDecl (.defnDecl {
        name := target.getId
        levelParams := ci.levelParams
        type := type
        value := value
        hints := ReducibilityHints.abbrev
        safety := DefinitionSafety.safe
      }) (forceExpose := true)
      modifyEnv (addNoncomputable · target.getId)
  addDeclarationRangesFromSyntax target.getId stx target
