module
public import Linear.NativeOriginalRawScalarIntrinsicPieces
public import Linear.NativeOriginalScalarPackageActionRefold
public import Lean
@[expose] public section
set_option maxHeartbeats 5000
open Lean Meta Elab Command

/-- Recover the group of a literal endomorphism space without reducing
the cohomology construction. -/
meta def nativeOriginalEndGroup (type : Expr) : MetaM Expr := do
  let t ← if type.isAppOf ``CategoryTheory.End then do
    let d ← getConstInfoDefn ``CategoryTheory.End
    pure ((mkAppN (d.value.instantiateLevelParams d.levelParams type.getAppFn.constLevels!)
      type.getAppArgs).headBeta)
  else pure type
  unless t.isAppOfArity ``Quiver.Hom 4 do throwError "Expected an endomorphism space"
  let args := t.getAppArgs
  unless args[2]! == args[3]! do throwError "Expected equal endomorphism endpoints"
  return args[2]!

/-- Give the three exact group-and-map pairs short names. This only names
existing objects. The inner maps are the original maps on each group. -/
elab "name_native_original_scalar_end_package " part:str " as " target:ident : command => do
  let stx ← getRef
  withExporting (isExporting := true) <| liftTermElabM do
    let l ← getConstInfo ``LinearStudy.nativeOriginalRawScalar_toPackage_heq
    let levels := l.levelParams.map Level.param
    forallTelescope l.type fun xs lt => do
      let rt ← inferType (mkAppN (mkConst ``LinearStudy.nativeOriginalScalarPackageAction_refold_heq levels) xs)
      let la := lt.getAppArgs
      let ra := rt.getAppArgs
      unless lt.isAppOfArity ``HEq 4 && rt.isAppOfArity ``HEq 4 &&
          la[2]! == ra[0]! && la[3]! == ra[1]! && la[3]!.isAppOf ``Sigma.snd do
        throwError "Expected matching checked scalar packages"
      let middle := la[3]!.getAppArgs.back!
      let sig ← inferType middle
      unless sig.isAppOfArity ``Sigma 2 do throwError "Expected the group-endomorphism package"
      let pair := mkConst ``Sigma.mk sig.getAppFn.constLevels!
      let body ←
        if part.getString == "left" then
          pure (mkAppN pair (sig.getAppArgs ++ #[← nativeOriginalEndGroup la[0]!,la[1]!]))
        else if part.getString == "middle" then pure middle
        else if part.getString == "right" then
          pure (mkAppN pair (sig.getAppArgs ++ #[← nativeOriginalEndGroup ra[2]!,ra[3]!]))
        else throwError "Expected left, middle or right"
      let type ← mkForallFVars xs sig
      let value ← mkLambdaFVars xs body
      addDecl (.defnDecl {
        name := target.getId
        levelParams := l.levelParams
        type := type
        value := value
        hints := .regular 1
        safety := .safe
      }) (forceExpose := true)
      modifyEnv (addNoncomputable · target.getId)
  addDeclarationRangesFromSyntax target.getId stx target

name_native_original_scalar_end_package "left" as LinearStudy.nativeOriginalRawScalarEndPackage
name_native_original_scalar_end_package "middle" as LinearStudy.nativeOriginalMiddleScalarEndPackage
name_native_original_scalar_end_package "right" as LinearStudy.nativeOriginalIntrinsicScalarEndPackage
#check LinearStudy.nativeOriginalRawScalarEndPackage
#print axioms LinearStudy.nativeOriginalRawScalarEndPackage
#check LinearStudy.nativeOriginalMiddleScalarEndPackage
#print axioms LinearStudy.nativeOriginalMiddleScalarEndPackage
#check LinearStudy.nativeOriginalIntrinsicScalarEndPackage
#print axioms LinearStudy.nativeOriginalIntrinsicScalarEndPackage
