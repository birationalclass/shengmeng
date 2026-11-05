module
public import Linear.NativeOriginalScalarPackages
public import Linear.OriginalNativeScalarPackageAction
public import Lean
@[expose] public section
set_option maxHeartbeats 5000
open Lean Meta Elab Command

/-- Identify the original projective coefficient map with the
independently defined native base scalar action through the checked
package interfaces. The ordinary kernel verifies the proof. -/
elab "check_native_original_raw_scalar_piece " part:str " as " target:ident : command => do
  let stx ← getRef
  withExporting (isExporting := true) <| liftTermElabM do
    let p ← getConstInfo ``LinearStudy.nativeOriginalActualHScalarOperator_eq_rawMap
    let levels := p.levelParams.map Level.param
    forallTelescope p.type fun xs pt => do
      let nativeArgs ← nativeOriginalScalarContext pt.getAppArgs.back!.getAppArgs.back! xs.back!
      let literal := mkAppN (mkConst p.name levels) xs
      let left := mkAppN (mkConst ``LinearStudy.nativeOriginalScalarPackageLeft_eq levels) xs
      let packs := mkAppN (mkConst ``LinearStudy.nativeOriginalScalarPackageMaps_heq levels) xs
      let right := mkAppN (mkConst ``LinearStudy.originalNativeScalarPackageAction_heq levels) nativeArgs
      let proof ←
        if part.getString == "left" then do
          let h ← mkAppM ``heq_of_eq_of_heq #[← mkAppM ``Eq.symm #[left],packs]
          mkAppM ``heq_of_eq_of_heq #[literal,h]
        else if part.getString == "right" then pure right
        else throwError "Expected left or right"
      let type ← mkForallFVars xs (← inferType proof)
      let value ← mkLambdaFVars xs proof
      addDecl (.thmDecl {name := target.getId, levelParams := p.levelParams, type, value})
        (forceExpose := true)
  addDeclarationRangesFromSyntax target.getId stx target

check_native_original_raw_scalar_piece "left" as LinearStudy.nativeOriginalRawScalar_toPackage_heq
check_native_original_raw_scalar_piece "right" as LinearStudy.nativeOriginalRawScalar_fromPackage_heq
#check LinearStudy.nativeOriginalRawScalar_toPackage_heq
#print axioms LinearStudy.nativeOriginalRawScalar_toPackage_heq
#check LinearStudy.nativeOriginalRawScalar_fromPackage_heq
#print axioms LinearStudy.nativeOriginalRawScalar_fromPackage_heq
