module
public import Linear.NativeOriginalScalarEndPackageEdges
public import Lean
@[expose] public section
set_option maxHeartbeats 5000
open Lean Meta Elab Command

/-- Compose the checked scalar edges on their exact shared group packages. -/
elab "check_original_scalar_end_package_chain " target:ident : command => do
  let stx ← getRef
  withExporting (isExporting := true) <| liftTermElabM do
    let l ← getConstInfo ``LinearStudy.nativeOriginalScalarEndPackageLeft_heq
    let levels := l.levelParams.map Level.param
    forallTelescope l.type fun xs _ => do
      let p := mkAppN (mkConst l.name levels) xs
      let q := mkAppN (mkConst ``LinearStudy.nativeOriginalScalarEndPackageRight_heq levels) xs
      let h ← mkAppM ``HEq.trans #[p,q]
      let type ← mkForallFVars xs (← inferType h)
      let value ← mkLambdaFVars xs h
      addDecl (.thmDecl {name := target.getId, levelParams := l.levelParams, type, value})
        (forceExpose := true)
  addDeclarationRangesFromSyntax target.getId stx target

check_original_scalar_end_package_chain LinearStudy.nativeOriginalScalarEndPackages_heq_intrinsic
#check LinearStudy.nativeOriginalScalarEndPackages_heq_intrinsic
#print axioms LinearStudy.nativeOriginalScalarEndPackages_heq_intrinsic
