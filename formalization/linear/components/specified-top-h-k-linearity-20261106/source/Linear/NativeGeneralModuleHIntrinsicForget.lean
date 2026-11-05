module
public import Linear.NativeGeneralModuleHIntrinsicExactIso
public import Lean
@[expose] public section
set_option maxHeartbeats 5000
open Lean Meta Elab Command

/-- After the exact target-object identification, the Γ-linear lift has
the same additive morphism as the original general comparison. -/
elab "check_general_module_intrinsic_forget " target:ident : command => do
  let stx ← getRef
  withExporting (isExporting := true) <| liftTermElabM do
    let d ← getConstInfoDefn
      ``LinearStudy.nativeIndependentFiniteNormalization_moduleCechActualHigherHIntrinsicIso_general
    let levels := d.levelParams.map Level.param
    forallTelescope d.type fun xs _ => do
      let exactIso := mkAppN (mkConst d.name levels) xs
      let body := (mkAppN d.value xs).headBeta
      unless body.isAppOf ``LinearStudy.originalScalarSquareModuleIso_literal do
        throwError "Expected the exact scalar-square lift"
      let proof := mkAppN
        (mkConst ``LinearStudy.originalScalarSquareModuleIso_literal_forget_hom
          body.getAppFn.constLevels!)
        body.getAppArgs
      let pt ← inferType proof
      unless pt.isAppOfArity ``Eq 3 do throwError "Expected the original morphism equality"
      let some old := pt.find? (· == body) |
        throwError "Expected the expanded exact lift in the forgotten morphism"
      let prop := pt.replace (fun e => if e == old then some exactIso else none)
      let type ← mkForallFVars xs prop
      let value ← mkLambdaFVars xs proof
      addDecl (.thmDecl {name := target.getId, levelParams := d.levelParams, type, value})
        (forceExpose := true)
  addDeclarationRangesFromSyntax target.getId stx target

check_general_module_intrinsic_forget LinearStudy.nativeIndependentFiniteNormalization_moduleCechActualHigherHIntrinsicIso_general_forget_hom
#check LinearStudy.nativeIndependentFiniteNormalization_moduleCechActualHigherHIntrinsicIso_general_forget_hom
#print axioms LinearStudy.nativeIndependentFiniteNormalization_moduleCechActualHigherHIntrinsicIso_general_forget_hom
