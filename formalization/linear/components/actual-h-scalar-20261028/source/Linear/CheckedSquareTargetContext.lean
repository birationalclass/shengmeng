module
public import Lean
public import Mathlib.CategoryTheory.Functor.Basic
@[expose] public section
set_option maxHeartbeats 5000
open Lean Meta Elab Command
/-- Cache the exact target of an original scalar square,with the scalar
binder removed. This only names the original object. -/
elab "cache_square_target_context " source:ident " as " target:ident : command => do
  let stx ← getRef
  withExporting (isExporting := true) <| liftTermElabM do
    let ci ← getConstInfo source.getId
    unless ci.isTheorem do throwError "Expected ordinary theorem"
    forallTelescope ci.type fun xs prop => do
      let prop ← whnf prop
      let some (homTy,_,_) ← matchEq? prop | throwError "Expected equality"
      unless homTy.isAppOfArity ``Quiver.Hom 4 do throwError "Expected Hom"
      let args := homTy.getAppArgs
      let obj := args[3]!
      unless !(obj.containsFVar xs.back!.fvarId!) do throwError "Object depends on scalar"
      let type ← mkForallFVars xs.pop args[0]!
      let value ← mkLambdaFVars xs.pop obj
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
/-- Replace occurrences of one exact original target by its safe public
abbreviation. The normal kernel checks the full statement and proof. -/
elab "checked_fold_square_target " source:ident " with " cached:ident
    " as " target:ident : command => do
  let stx ← getRef
  withExporting (isExporting := true) <| liftTermElabM do
    let ci ← getConstInfo source.getId
    unless ci.isTheorem do throwError "Expected ordinary theorem"
    let di ← getConstInfoDefn cached.getId
    unless di.safety == .safe do throwError "Expected safe object definition"
    unless ci.levelParams == di.levelParams do throwError "Universe mismatch"
    let levels := ci.levelParams.map Level.param
    forallTelescope ci.type fun xs prop => do
      let prop ← whnf prop
      let some (homTy,_,_) ← matchEq? prop | throwError "Expected equality"
      unless homTy.isAppOfArity ``Quiver.Hom 4 do throwError "Expected Hom"
      let obj := homTy.getAppArgs[3]!
      let obj2 := mkAppN (mkConst cached.getId levels) xs.pop
      let newProp := prop.replace fun e => if e == obj then some obj2 else none
      if newProp == prop then throwError "No exact target occurrence"
      let type ← mkForallFVars xs newProp
      let value := mkConst source.getId levels
      addDecl (.thmDecl {name := target.getId,levelParams := ci.levelParams,type,value})
        (forceExpose := true)
  addDeclarationRangesFromSyntax target.getId stx target
