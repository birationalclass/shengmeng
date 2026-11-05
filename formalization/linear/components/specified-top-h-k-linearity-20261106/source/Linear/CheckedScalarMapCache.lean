module
public import Lean
public import Mathlib.CategoryTheory.Functor.Basic
@[expose] public section
set_option maxHeartbeats 5000
open Lean Meta Elab Command
/-- Cache the EXISTING right-hand endomorphism in a checked scalar
square. The value must be a literal functor map. Its endomorphism type
uses the EXACT target object in that checked square. This defines an
object only,never a proof,and never transports an action by an iso. -/
elab "cache_original_scalar_map " source:ident " as " target:ident : command => do
  let stx ← getRef
  withExporting (isExporting := true) <| liftTermElabM do
    let ci ← getConstInfo source.getId
    unless ci.isTheorem do throwError "Expected an existing ordinary theorem"
    let levels := ci.levelParams.map Level.param
    forallTelescope ci.type fun xs prop => do
      let prop ← whnf prop
      let some (homTy,_,rhs) ← matchEq? prop | throwError "Expected an equality"
      unless homTy.isAppOfArity ``Quiver.Hom 4 do throwError "Expected a categorical square"
      unless rhs.isAppOf ``CategoryTheory.CategoryStruct.comp do throwError "Expected right-hand composition"
      let map := rhs.getAppArgs.back!
      unless map.isAppOf ``CategoryTheory.Functor.map do throwError "Expected the ORIGINAL functor map"
      let args := homTy.getAppArgs
      let obj := args[3]!
      let endTy := mkAppN homTy.getAppFn #[args[0]!,args[1]!,obj,obj]
      let type ← mkForallFVars xs endTy
      let value ← mkLambdaFVars xs map
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
