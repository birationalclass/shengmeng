module
public import Linear.NativeGeneralModuleHIntrinsicSpecIso
public import Lean
@[expose] public section
set_option maxHeartbeats 5000
open Lean Meta Elab Command

/-- The K-linear lift retains the exact underlying comparison morphism
after the same target additive-group identification. -/
elab "check_general_module_intrinsic_spec_forget " target:ident : command => do
  let stx ← getRef
  withExporting (isExporting := true) <| liftTermElabM do
    let d ← getConstInfoDefn
      ``LinearStudy.nativeIndependentFiniteNormalization_moduleCechActualHigherHSpecIso_general
    let levels := d.levelParams.map Level.param
    forallTelescope d.type fun xs _ => do
      let iso := mkAppN (mkConst d.name levels) xs
      let body := (mkAppN d.value xs).headBeta
      unless body.isAppOf ``LinearStudy.originalActualHSpecRestrictIso do
        throwError "Expected the original restriction of scalars"
      let restrict := mkAppN
        (mkConst ``LinearStudy.originalActualHSpecRestrictIso_forget_hom levels) body.getAppArgs
      let gamma := mkAppN (mkConst
        ``LinearStudy.nativeIndependentFiniteNormalization_moduleCechActualHigherHIntrinsicIso_general_forget_hom
        levels) xs
      let rt ← inferType restrict
      let gt ← inferType gamma
      unless rt.isAppOfArity ``Eq 3 && gt.isAppOfArity ``Eq 3 do
        throwError "Expected the two exact additive equalities"
      let left := gt.getAppArgs[1]!
      unless left.isAppOfArity ``CategoryTheory.CategoryStruct.comp 7 &&
          left.getAppArgs[5]! == rt.getAppArgs[2]! do
        throwError "Expected the same exact middle additive map"
      let proof ← withLocalDeclD `f rt.getAppArgs[0]! fun f => do
        let compose := mkAppN left.getAppFn (left.getAppArgs.set! 5 f)
        let map ← mkLambdaFVars #[f] compose
        let h ← mkAppM ``congrArg #[map,restrict]
        mkAppM ``Eq.trans #[h,gamma]
      let pt ← inferType proof
      unless (pt.find? (· == body)).isSome do
        throwError "Expected the expanded K-linear lift"
      let prop := pt.replace (fun e => if e == body then some iso else none)
      let type ← mkForallFVars xs prop
      let value ← mkLambdaFVars xs proof
      addDecl (.thmDecl {name := target.getId, levelParams := d.levelParams, type, value})
        (forceExpose := true)
  addDeclarationRangesFromSyntax target.getId stx target

check_general_module_intrinsic_spec_forget LinearStudy.nativeIndependentFiniteNormalization_moduleCechActualHigherHSpecIso_general_forget_hom
#check LinearStudy.nativeIndependentFiniteNormalization_moduleCechActualHigherHSpecIso_general_forget_hom
#print axioms LinearStudy.nativeIndependentFiniteNormalization_moduleCechActualHigherHSpecIso_general_forget_hom
