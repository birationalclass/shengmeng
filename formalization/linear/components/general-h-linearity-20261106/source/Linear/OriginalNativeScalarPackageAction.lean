module
public import Linear.OriginalRawScalarPackageRightInterface
public import Lean
@[expose] public section
set_option maxHeartbeats 5000
open Lean Meta Elab Command

/-- Compose the already checked native package projection, group fold,
and intrinsic scalar formula. The normal kernel checks the full proof. -/
elab "check_original_native_scalar_package_action " target:ident : command => do
  let stx ← getRef
  withExporting (isExporting := true) <| liftTermElabM do
    let q ← getConstInfo ``LinearStudy.originalActualHBaseScalarRawMorphism
    let levels := q.levelParams.map Level.param
    forallTelescope q.type fun xs _ => do
      let projection := mkAppN (mkConst ``LinearStudy.originalRawScalarNativePackage_projection levels) xs
      let fold := mkAppN (mkConst ``LinearStudy.originalRawScalarNativePackage_carrier_fold levels) xs
      let raw := mkAppN (mkConst q.name levels) xs
      let h ← mkAppM ``Eq.trans #[projection,fold]
      let h₁ ← mkAppM ``heq_of_eq #[h]
      let h₂ ← mkAppM ``Eq.symm #[raw]
      let proof ← mkAppM ``heq_of_heq_of_eq #[h₁,h₂]
      let type ← mkForallFVars xs (← inferType proof)
      let value ← mkLambdaFVars xs proof
      addDecl (.thmDecl {name := target.getId, levelParams := q.levelParams, type, value})
        (forceExpose := true)
  addDeclarationRangesFromSyntax target.getId stx target

check_original_native_scalar_package_action LinearStudy.originalNativeScalarPackageAction_heq
#check LinearStudy.originalNativeScalarPackageAction_heq
#print axioms LinearStudy.originalNativeScalarPackageAction_heq
