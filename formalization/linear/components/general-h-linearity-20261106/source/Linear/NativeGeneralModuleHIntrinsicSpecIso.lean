module
public import Linear.NativeGeneralModuleHIntrinsicForget
public import Linear.OriginalActualHSpecRestrictIso
public import Lean
@[expose] public section
set_option maxHeartbeats 5000
open Lean Meta Elab Command

/-- Restrict the exact general Γ-linear comparison along the original
canonical coefficient map, with the independently defined K-target. -/
elab "check_general_module_intrinsic_spec_iso " target:ident : command => do
  let stx ← getRef
  withExporting (isExporting := true) <| liftTermElabM do
    let d ← getConstInfoDefn
      ``LinearStudy.nativeIndependentFiniteNormalization_moduleCechActualHigherHIntrinsicIso_general
    let levels := d.levelParams.map Level.param
    forallTelescope d.type fun xs prop => do
      unless prop.isAppOf ``CategoryTheory.Iso do throwError "Expected the Γ-linear isomorphism"
      let args := prop.getAppArgs
      let c := args[args.size-2]!
      let g := args.back!
      unless g.isAppOfArity ``LinearStudy.originalActualHBaseModuleObject 5 do
        throwError "Expected the independent original Γ-module"
      let ga := g.getAppArgs
      let k := xs[0]!
      let some kRing := ga[1]!.find? (fun t =>
          t.isAppOfArity ``CommRingCat.of 2 && t.getAppArgs[0]! == k) |
        throwError "Expected the original Spec K"
      let iso := mkAppN (mkConst d.name levels) xs
      let body := mkAppN (mkConst ``LinearStudy.originalActualHSpecRestrictIso levels)
        #[k,kRing.getAppArgs[1]!,ga[0]!,ga[2]!,ga[3]!,ga[4]!,c,iso]
      let type ← mkForallFVars xs (← inferType body)
      let value ← mkLambdaFVars xs body
      addDecl (.defnDecl {
        name := target.getId
        levelParams := d.levelParams
        type := type
        value := value
        hints := .regular 1
        safety := .safe
      }) (forceExpose := true)
      modifyEnv (addNoncomputable · target.getId)
  addDeclarationRangesFromSyntax target.getId stx target

check_general_module_intrinsic_spec_iso LinearStudy.nativeIndependentFiniteNormalization_moduleCechActualHigherHSpecIso_general
#check LinearStudy.nativeIndependentFiniteNormalization_moduleCechActualHigherHSpecIso_general
#print axioms LinearStudy.nativeIndependentFiniteNormalization_moduleCechActualHigherHSpecIso_general
