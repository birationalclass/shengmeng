module
public import Lean
@[expose] public section
set_option maxHeartbeats 5000
open Lean Meta Elab Command
/-- Generate ONLY the reflexive identity between an existing definition
and its single delta expansion. addDecl performs the ordinary kernel
check on the generated theorem; no trust or resource option is changed. -/
elab "checked_unfold_identity " src:ident " as " dst:ident : command => do
  let stx ← getRef
  withExporting (isExporting := true) <| liftTermElabM do
    let ci ← getConstInfoDefn src.getId
    let levels := ci.levelParams.map Level.param
    forallTelescope ci.type fun xs _ => do
      let lhs := mkAppN (mkConst ci.name levels) xs
      let rhs := (mkAppN ci.value xs).headBeta
      let ty ← inferType lhs
      let .sort u ← whnf (← inferType ty) | throwError "Expected an ordinary type"
      let equality := mkApp3 (mkConst ``Eq [u]) ty lhs rhs
      let type ← mkForallFVars xs equality
      let value ← mkLambdaFVars xs (← mkEqRefl lhs)
      addDecl (.thmDecl {name := dst.getId,levelParams := ci.levelParams,type,value})
        (forceExpose := true)
  addDeclarationRangesFromSyntax dst.getId stx dst
