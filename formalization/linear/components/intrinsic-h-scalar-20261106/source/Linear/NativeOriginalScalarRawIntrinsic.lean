module
public import Linear.NativeOriginalScalarEndPackageCalibration
public import Lean
@[expose] public section
set_option maxHeartbeats 5000
open Lean Meta Elab Command

/-- Restore one original endpoint at a time from the checked package
calibration. Neither endpoint map is changed. -/
elab "unfold_native_original_scalar_endpoint " source:ident " at " side:str
    " from " endpoint:ident " as " target:ident : command => do
  let stx ← getRef
  withExporting (isExporting := true) <| liftTermElabM do
    let p ← getConstInfo source.getId
    let levels := p.levelParams.map Level.param
    forallTelescope p.type fun xs pt => do
      let q ← inferType (mkAppN (mkConst endpoint.getId levels) xs)
      unless pt.isAppOfArity ``HEq 4 && q.isAppOfArity ``HEq 4 do
        throwError "Expected checked heterogeneous equalities"
      let pa := pt.getAppArgs
      let qa := q.getAppArgs
      let args ←
        if side.getString == "left" then pure (qa.extract 0 2 ++ pa.extract 2 4)
        else if side.getString == "right" then pure (pa.extract 0 2 ++ qa.extract 2 4)
        else throwError "Expected left or right"
      let type ← mkForallFVars xs (mkAppN pt.getAppFn args)
      let value ← mkLambdaFVars xs (mkAppN (mkConst p.name levels) xs)
      addDecl (.thmDecl {name := target.getId, levelParams := p.levelParams, type, value})
        (forceExpose := true)
  addDeclarationRangesFromSyntax target.getId stx target

unfold_native_original_scalar_endpoint LinearStudy.nativeOriginalScalarEndPackages_heq_intrinsic
  at "left" from LinearStudy.nativeOriginalRawScalar_toPackage_heq
  as LinearStudy.nativeOriginalScalarRawToIntrinsicPackage_heq
unfold_native_original_scalar_endpoint LinearStudy.nativeOriginalScalarRawToIntrinsicPackage_heq
  at "right" from LinearStudy.nativeOriginalScalarPackageAction_refold_heq
  as LinearStudy.nativeOriginalActualHScalarOperator_heq_intrinsic
#check LinearStudy.nativeOriginalScalarRawToIntrinsicPackage_heq
#print axioms LinearStudy.nativeOriginalScalarRawToIntrinsicPackage_heq
#check LinearStudy.nativeOriginalActualHScalarOperator_heq_intrinsic
#print axioms LinearStudy.nativeOriginalActualHScalarOperator_heq_intrinsic
