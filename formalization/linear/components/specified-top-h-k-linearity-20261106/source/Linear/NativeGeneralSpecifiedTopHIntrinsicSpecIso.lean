module
public import Linear.NativeGeneralModuleHIntrinsicSpecForget
public import Linear.NativeGeneralSpecifiedNormalizationTopDuality
public import Linear.CoordinateNativeCechHomologyModel
public import Lean
@[expose] public section
set_option maxHeartbeats 5000
open Lean Meta Elab Command

/-- Lift the specified top-H duality by reusing its original coordinate
cover and presentation-data factor with the checked general K-linear comparison. -/
elab "check_general_specified_top_h_spec_iso " target:ident : command => do
  let stx ← getRef
  withExporting (isExporting := true) <| liftTermElabM do
    let old ← getConstInfoDefn ``LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualIso_general
    let general ← getConstInfoDefn
      ``LinearStudy.nativeIndependentFiniteNormalization_moduleCechActualHigherHSpecIso_general
    forallTelescope old.type fun xs _ => do
      let mut body := (mkAppN old.value xs).headBeta
      while body.isLet do
        body := body.letBody!.instantiate1 body.letValue!
      unless body.isAppOf ``CategoryTheory.Iso.trans do
        throwError "Expected the specified comparison's original two factors"
      let sides := body.getAppArgs
      let inverse := sides[sides.size-2]!
      let dual := sides.back!
      unless inverse.isAppOf ``CategoryTheory.Iso.symm &&
          dual.isAppOf ``CategoryTheory.Functor.mapIso do
        throwError "Expected the original inverse comparison and presentation-data factor"
      let orig := inverse.getAppArgs.back!
      unless orig.isAppOf ``LinearStudy.nativeIndependentFiniteNormalization_moduleCechActualHigherHIso_general do
        throwError "Expected the original general comparison"
      let origArgs := orig.getAppArgs
      let cut := origArgs.size-6
      let levels := orig.getAppFn.constLevels!
      let lift := mkAppN (mkConst general.name levels)
        (origArgs.extract 0 cut ++ origArgs.extract (cut+2) origArgs.size)
      let dualK := dual.getAppArgs.back!
      let invK ← mkAppM ``CategoryTheory.Iso.symm #[lift]
      let lt ← inferType invK
      let dt ← inferType dualK
      unless lt.isAppOfArity ``CategoryTheory.Iso 4 && dt.isAppOfArity ``CategoryTheory.Iso 4 do
        throwError "Expected the exact K-linear factors"
      let la := lt.getAppArgs
      let da := dt.getAppArgs
      let valueBody := mkAppN (mkConst ``CategoryTheory.Iso.trans lt.getAppFn.constLevels!)
        #[la[0]!,la[1]!,la[2]!,la[3]!,da[3]!,invK,dualK]
      let type ← mkForallFVars xs (← inferType valueBody)
      let value ← mkLambdaFVars xs valueBody
      addDecl (.defnDecl {
        name := target.getId
        levelParams := old.levelParams
        type := type
        value := value
        hints := .regular 1
        safety := .safe
      }) (forceExpose := true)
      modifyEnv (addNoncomputable · target.getId)
  addDeclarationRangesFromSyntax target.getId stx target

check_general_specified_top_h_spec_iso LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualKLinearIso_general
#check LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualKLinearIso_general
#print axioms LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualKLinearIso_general
