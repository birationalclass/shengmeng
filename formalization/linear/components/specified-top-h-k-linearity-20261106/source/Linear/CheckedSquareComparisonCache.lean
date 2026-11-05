module
public import Lean
public import Mathlib.CategoryTheory.Functor.Basic
@[expose] public section
set_option maxHeartbeats 5000
open Lean Meta Elab Command
/-- Cache the literal comparison morphism in an original scalar square.
The last scalar argument is removed; its occurrence would be rejected. -/
elab "cache_original_square_comparison " source:ident " as " target:ident : command => do
  let stx ← getRef
  withExporting (isExporting := true) <| liftTermElabM do
    let ci ← getConstInfo source.getId
    unless ci.isTheorem do throwError "Expected an ordinary theorem"
    forallTelescope ci.type fun xs prop => do
      let prop ← whnf prop
      let some (homTy,lhs,_) ← matchEq? prop | throwError "Expected equality"
      unless lhs.isAppOf ``CategoryTheory.CategoryStruct.comp do throwError "Expected composition"
      let hom := lhs.getAppArgs.back!
      unless homTy.isAppOfArity ``Quiver.Hom 4 do throwError "Expected categorical Hom"
      unless !(hom.containsFVar xs.back!.fvarId!) do throwError "Comparison depends on scalar"
      let type ← mkForallFVars xs.pop homTy
      let value ← mkLambdaFVars xs.pop hom
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
/-- Fold just the same comparison on both sides of a proved scalar square.
The ordinary kernel checks the new theorem against the original proof. -/
elab "checked_fold_square_comparison " source:ident " with " cached:ident
    " as " target:ident : command => do
  let stx ← getRef
  withExporting (isExporting := true) <| liftTermElabM do
    let ci ← getConstInfo source.getId
    unless ci.isTheorem do throwError "Expected ordinary theorem"
    let di ← getConstInfoDefn cached.getId
    unless di.safety == .safe do throwError "Expected safe comparison"
    unless ci.levelParams == di.levelParams do throwError "Universe mismatch"
    let levels := ci.levelParams.map Level.param
    forallTelescope ci.type fun xs prop => do
      let prop ← whnf prop
      let some (_,lhs,rhs) ← matchEq? prop | throwError "Expected equality"
      unless lhs.isAppOf ``CategoryTheory.CategoryStruct.comp && rhs.isAppOf ``CategoryTheory.CategoryStruct.comp do
        throwError "Expected coefficient square"
      let hom := mkAppN (mkConst cached.getId levels) xs.pop
      let la := lhs.getAppArgs
      let ra := rhs.getAppArgs
      let lhs2 := mkAppN lhs.getAppFn (la.set! (la.size-1) hom)
      let rhs2 := mkAppN rhs.getAppFn (ra.set! (ra.size-2) hom)
      let pa := prop.getAppArgs
      let newProp := mkAppN prop.getAppFn ((pa.set! 1 lhs2).set! 2 rhs2)
      let type ← mkForallFVars xs newProp
      let value := mkConst source.getId levels
      addDecl (.thmDecl {name := target.getId,levelParams := ci.levelParams,type,value})
        (forceExpose := true)
  addDeclarationRangesFromSyntax target.getId stx target
