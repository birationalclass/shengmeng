module
public import Lean
public import Mathlib.CategoryTheory.Functor.Basic
@[expose] public section
set_option maxHeartbeats 5000
open Lean Meta Elab Command
/-- Cache the literal scalar operator in a checked square on the exact
public codomain of an independently calibrated comparison morphism. -/
elab "cache_square_right_on_codomain " source:ident " of " comparison:ident
    " as " target:ident : command => do
  let stx ← getRef
  withExporting (isExporting := true) <| liftTermElabM do
    let ci ← getConstInfo source.getId
    unless ci.isTheorem do throwError "Expected ordinary theorem"
    let di ← getConstInfoDefn comparison.getId
    unless di.safety == .safe do throwError "Expected safe comparison"
    unless ci.levelParams == di.levelParams do throwError "Universe mismatch"
    let levels := ci.levelParams.map Level.param
    forallTelescope ci.type fun xs prop => do
      let prop ← whnf prop
      let some (_,_,rhs) ← matchEq? prop | throwError "Expected equality"
      unless rhs.isAppOf ``CategoryTheory.CategoryStruct.comp do throwError "Expected square"
      let pubHom := mkAppN (mkConst comparison.getId levels) xs.pop
      let pubTy ← inferType pubHom
      unless pubTy.isAppOfArity ``Quiver.Hom 4 do throwError "Expected nominal public Hom type"
      let ha := pubTy.getAppArgs
      let obj := ha[3]!
      let endTy := mkAppN pubTy.getAppFn ((ha.set! 2 obj).set! 3 obj)
      let type ← mkForallFVars xs endTy
      let value ← mkLambdaFVars xs rhs.getAppArgs.back!
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
/-- Name the target of a checked scalar square by the exact codomain
of its calibrated public comparison. Normal kernel conversion is required. -/
elab "checked_square_on_codomain " source:ident " of " comparison:ident
    " as " target:ident : command => do
  let stx ← getRef
  withExporting (isExporting := true) <| liftTermElabM do
    let ci ← getConstInfo source.getId
    unless ci.isTheorem do throwError "Expected ordinary theorem"
    let di ← getConstInfoDefn comparison.getId
    unless di.safety == .safe do throwError "Expected safe comparison"
    unless ci.levelParams == di.levelParams do throwError "Universe mismatch"
    let levels := ci.levelParams.map Level.param
    forallTelescope ci.type fun xs prop => do
      let prop ← whnf prop
      let some (homTy,_,_) ← matchEq? prop | throwError "Expected equality"
      unless homTy.isAppOfArity ``Quiver.Hom 4 do throwError "Expected Hom"
      let obj := homTy.getAppArgs[3]!
      let pubHom := mkAppN (mkConst comparison.getId levels) xs.pop
      let pubTy ← inferType pubHom
      unless pubTy.isAppOfArity ``Quiver.Hom 4 do throwError "Expected public Hom"
      let pubObj := pubTy.getAppArgs[3]!
      let newProp := prop.replace fun e => if e == obj then some pubObj else none
      let type ← mkForallFVars xs newProp
      let value := mkConst source.getId levels
      addDecl (.thmDecl {name := target.getId,levelParams := ci.levelParams,type,value})
        (forceExpose := true)
  addDeclarationRangesFromSyntax target.getId stx target
