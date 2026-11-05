module
public import Linear.NativeOriginalScalarRawIntrinsic
public import Linear.NativePublicHScalarOperatorIdentity
public import Lean
@[expose] public section
set_option maxHeartbeats 5000
open Lean Meta Elab Command

/-- Align the checked raw action with the original public coefficient
operator while keeping the exact intrinsic group package shared. -/
elab "check_original_public_scalar_intrinsic " part:str " as " target:ident : command => do
  let stx ← getRef
  withExporting (isExporting := true) <| liftTermElabM do
    let p ← getConstInfo ``LinearStudy.nativeOriginalActualHPublicScalarOperator_eq_raw
    let levels := p.levelParams.map Level.param
    forallTelescope p.type fun xs pt => do
      unless pt.isAppOfArity ``Eq 3 do throwError "Expected the published map identity"
      let pa := pt.getAppArgs
      let (prop,proof) ←
        if part.getString == "refold" then do
          let h := mkAppN (mkConst ``LinearStudy.nativeOriginalScalarRawToIntrinsicPackage_heq levels) xs
          let ht ← inferType h
          unless ht.isAppOfArity ``HEq 4 && ht.getAppArgs[1]! == pa[2]! do
            throwError "Expected the same raw operator"
          let a := ht.getAppArgs
          pure (mkAppN ht.getAppFn #[pa[0]!,pa[2]!,a[2]!,a[3]!],h)
        else if part.getString == "public" then do
          let h ← mkAppM ``heq_of_eq_of_heq #[
            mkAppN (mkConst p.name levels) xs,
            mkAppN (mkConst (Name.str (Name.str .anonymous "LinearStudy")
              "nativeOriginalRawScalarOnPublicGroup_heq") levels) xs]
          pure (← inferType h,h)
        else throwError "Expected refold or public"
      let type ← mkForallFVars xs prop
      let value ← mkLambdaFVars xs proof
      addDecl (.thmDecl {name := target.getId, levelParams := p.levelParams, type, value})
        (forceExpose := true)
  addDeclarationRangesFromSyntax target.getId stx target

check_original_public_scalar_intrinsic "refold" as LinearStudy.nativeOriginalRawScalarOnPublicGroup_heq
check_original_public_scalar_intrinsic "public" as LinearStudy.nativeOriginalPublicScalarToIntrinsicPackage_heq
unfold_native_original_scalar_endpoint LinearStudy.nativeOriginalPublicScalarToIntrinsicPackage_heq
  at "right" from LinearStudy.nativeOriginalScalarPackageAction_refold_heq
  as LinearStudy.nativeOriginalActualHPublicScalarOperator_heq_intrinsic
#check LinearStudy.nativeOriginalRawScalarOnPublicGroup_heq
#print axioms LinearStudy.nativeOriginalRawScalarOnPublicGroup_heq
#check LinearStudy.nativeOriginalPublicScalarToIntrinsicPackage_heq
#print axioms LinearStudy.nativeOriginalPublicScalarToIntrinsicPackage_heq
#check LinearStudy.nativeOriginalActualHPublicScalarOperator_heq_intrinsic
#print axioms LinearStudy.nativeOriginalActualHPublicScalarOperator_heq_intrinsic
