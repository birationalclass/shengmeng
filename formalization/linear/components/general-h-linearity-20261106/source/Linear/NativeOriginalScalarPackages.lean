module
public import Linear.NativeOriginalScalarMapFormula
public import Linear.OriginalActualHBaseScalarRawMorphism
public import Linear.OriginalSheafHRawMapPackage
public import Lean
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 5000
open Lean Meta Elab Command

/-- Recover only the literal original scalar map and its scheme map from
the type of a verified formula. -/
meta def nativeOriginalScalarContext (hmap r : Expr) : MetaM (Array Expr) := do
  unless hmap.isAppOfArity ``CategoryTheory.Sheaf.H.map 9 do
    throwError "Expected actual sheaf H.map"
  let args := hmap.getAppArgs
  let f := args[7]!
  unless f.isAppOfArity ``CategoryTheory.Functor.map 8 do
    throwError "Expected original additive sheaf coefficient map"
  let scalar := f.getAppArgs.back!
  unless scalar.isAppOfArity ``LinearStudy.originalGlobalModuleScalar 3 do
    throwError "Expected original global module scalar"
  let scalarArgs := scalar.getAppArgs
  let sectionValue := scalarArgs[1]!
  unless sectionValue.getAppArgs.back! == r do throwError "Expected the original scalar argument"
  let some appTop := sectionValue.find? (fun e =>
    e.isAppOfArity ``AlgebraicGeometry.Scheme.Hom.appTop 3) |
    throwError "Expected original global sections scheme map"
  let pi := appTop.getAppArgs
  unless pi[0]! == scalarArgs[0]! do throwError "Scheme map source disagrees with coefficient"
  return #[pi[0]!,pi[1]!,pi[2]!,scalarArgs[2]!,args[8]!,r]

meta def nativeOriginalRawMapPackageExpr (hmap : Expr) : Expr :=
  let args := hmap.getAppArgs
  mkAppN (mkConst ``LinearStudy.originalSheafHRawMapPackage hmap.getAppFn.constLevels!)
    (args.extract 0 6 ++ args.extract 7 9)

/-- Verify separately the agreement of the raw map packages and the
left projection. The normal kernel checks each complete declaration. -/
elab "check_native_original_scalar_package " part:str " as " target:ident : command => do
  let stx ← getRef
  withExporting (isExporting := true) <| liftTermElabM do
    let p ← getConstInfo ``LinearStudy.nativeOriginalActualHScalarOperator_eq_rawMap
    let levels := p.levelParams.map Level.param
    forallTelescope p.type fun xs pt => do
      unless pt.isAppOfArity ``Eq 3 do throwError "Expected original coefficient formula"
      let raw := pt.getAppArgs.back!
      let pMap := raw.getAppArgs.back!
      let nativeArgs ← nativeOriginalScalarContext pMap xs.back!
      let pPack := nativeOriginalRawMapPackageExpr pMap
      let (prop,proof) ←
        if part.getString == "left" then do
          let proj ← mkAppM ``Sigma.snd #[pPack]
          pure (mkApp3 pt.getAppFn (← inferType raw) proj raw, ← mkEqRefl raw)
        else if part.getString == "packages" then do
          let q ← inferType (mkAppN (mkConst ``LinearStudy.originalActualHBaseScalarRawMorphism levels) nativeArgs)
          unless q.isAppOfArity ``Eq 3 do throwError "Expected intrinsic coefficient formula"
          let qMap := q.getAppArgs.back!.getAppArgs.back!
          unless qMap.isAppOfArity ``CategoryTheory.Sheaf.H.map 9 do throwError "Expected native H.map"
          let qPack := nativeOriginalRawMapPackageExpr qMap
          let h := mkAppN
            (mkConst ``LinearStudy.originalSheafHRawMapPackage_snd_heq [levels.head!])
            #[pPack,qPack,← mkEqRefl pPack]
          pure (← inferType h,h)
        else throwError "Expected left or packages"
      let type ← mkForallFVars xs prop
      let value ← mkLambdaFVars xs proof
      addDecl (.thmDecl {name := target.getId, levelParams := p.levelParams, type, value})
        (forceExpose := true)
  addDeclarationRangesFromSyntax target.getId stx target

check_native_original_scalar_package "left" as LinearStudy.nativeOriginalScalarPackageLeft_eq
check_native_original_scalar_package "packages" as LinearStudy.nativeOriginalScalarPackageMaps_heq
#check LinearStudy.nativeOriginalScalarPackageLeft_eq
#print axioms LinearStudy.nativeOriginalScalarPackageLeft_eq
#check LinearStudy.nativeOriginalScalarPackageMaps_heq
#print axioms LinearStudy.nativeOriginalScalarPackageMaps_heq
