module
public import Linear.NativeOriginalScalarEndPackages
public import Lean
@[expose] public section
set_option maxHeartbeats 5000
open Lean Meta Elab Command

/-- Refold a checked edge using its exact group-and-map packages. -/
elab "refold_native_original_scalar_edge " source:ident " from " left:ident " to " right:ident
    " as " target:ident : command => do
  let stx ← getRef
  withExporting (isExporting := true) <| liftTermElabM do
    let ci ← getConstInfo source.getId
    unless ci.isTheorem do throwError "Expected a checked scalar edge"
    let levels := ci.levelParams.map Level.param
    forallTelescope ci.type fun xs prop => do
      unless prop.isAppOfArity ``HEq 4 do throwError "Expected heterogeneous equality"
      let l ← mkAppM ``Sigma.snd #[mkAppN (mkConst left.getId levels) xs]
      let r ← mkAppM ``Sigma.snd #[mkAppN (mkConst right.getId levels) xs]
      let type ← mkForallFVars xs (mkAppN prop.getAppFn #[← inferType l,l,← inferType r,r])
      let value ← mkLambdaFVars xs (mkAppN (mkConst ci.name levels) xs)
      addDecl (.thmDecl {name := target.getId, levelParams := ci.levelParams, type, value})
        (forceExpose := true)
  addDeclarationRangesFromSyntax target.getId stx target

refold_native_original_scalar_edge LinearStudy.nativeOriginalRawScalar_toPackage_heq
  from LinearStudy.nativeOriginalRawScalarEndPackage to LinearStudy.nativeOriginalMiddleScalarEndPackage
  as LinearStudy.nativeOriginalScalarEndPackageLeft_heq
refold_native_original_scalar_edge LinearStudy.nativeOriginalScalarPackageAction_refold_heq
  from LinearStudy.nativeOriginalMiddleScalarEndPackage to LinearStudy.nativeOriginalIntrinsicScalarEndPackage
  as LinearStudy.nativeOriginalScalarEndPackageRight_heq
#check LinearStudy.nativeOriginalScalarEndPackageLeft_heq
#print axioms LinearStudy.nativeOriginalScalarEndPackageLeft_heq
#check LinearStudy.nativeOriginalScalarEndPackageRight_heq
#print axioms LinearStudy.nativeOriginalScalarEndPackageRight_heq
