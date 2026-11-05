module
public import Linear.OriginalActualHBaseScalarRawMorphism
public import Linear.OriginalSheafHRawMapPackage
public import Lean
@[expose] public section
set_option maxHeartbeats 5000
open Lean Meta Elab Command

/-- Split the native package projection from the equality that folds the
existing native carrier and additive-group definitions. -/
elab "check_native_raw_scalar_package_right " part:str " as " target:ident : command => do
  let stx ← getRef
  withExporting (isExporting := true) <| liftTermElabM do
    let q ← getConstInfo ``LinearStudy.originalActualHBaseScalarRawMorphism
    let p ← getConstInfoDefn ``LinearStudy.originalSheafHRawMapPackage
    forallTelescope q.type fun xs qt => do
      unless qt.isAppOfArity ``Eq 3 do throwError "Expected original scalar formula"
      let raw := qt.getAppArgs.back!
      let m := raw.getAppArgs.back!
      unless m.isAppOfArity ``CategoryTheory.Sheaf.H.map 9 do
        throwError "Expected native H.map"
      let pa := m.getAppArgs
      let levels := m.getAppFn.constLevels!
      let args := pa.extract 0 6 ++ pa.extract 7 9
      let pack := mkAppN (mkConst p.name levels) args
      let mut body := (mkAppN (p.value.instantiateLevelParams p.levelParams levels) args).headBeta
      while body.isLet do
        body := body.letBody!.instantiate1 body.letValue!
      unless body.isAppOf ``Sigma.mk do throwError "Expected original raw H package"
      let expanded := body.getAppArgs.back!
      unless expanded.getAppArgs.back! == m do throwError "Expected the same literal H.map"
      let (left,right) ←
        if part.getString == "projection" then pure (← mkAppM ``Sigma.snd #[pack], expanded)
        else if part.getString == "carrier" then pure (expanded,raw)
        else throwError "Expected projection or carrier"
      let prop := mkApp3 qt.getAppFn (← inferType expanded) left right
      let type ← mkForallFVars xs prop
      let value ← mkLambdaFVars xs (← mkEqRefl expanded)
      addDecl (.thmDecl {name := target.getId, levelParams := q.levelParams, type, value})
        (forceExpose := true)
  addDeclarationRangesFromSyntax target.getId stx target

check_native_raw_scalar_package_right "projection" as LinearStudy.originalRawScalarNativePackage_projection
check_native_raw_scalar_package_right "carrier" as LinearStudy.originalRawScalarNativePackage_carrier_fold
#check LinearStudy.originalRawScalarNativePackage_projection
#print axioms LinearStudy.originalRawScalarNativePackage_projection
#check LinearStudy.originalRawScalarNativePackage_carrier_fold
#print axioms LinearStudy.originalRawScalarNativePackage_carrier_fold
