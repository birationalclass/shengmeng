module
public import Linear.NativeGeneralPublicHIntrinsicWitness
public import Linear.OriginalActualHBaseModuleForgetting
public import Linear.OriginalOrderedModuleHomologyScalarMorphism
public import Linear.OriginalScalarSquareModuleIsoLiteral
public import Lean
@[expose] public section
set_option maxHeartbeats 5000
open Lean Meta Elab Command

/-- Assemble the Γ-linear lift from the exact objects and maps in the
previously checked additive comparison square. -/
elab "check_general_module_intrinsic_iso " target:ident : command => do
  let stx ← getRef
  withExporting (isExporting := true) <| liftTermElabM do
    let q ← getConstInfo
      ``LinearStudy.nativeFiniteNormalization_generalModuleCechActualH_baseScalar_proof
    let levels := q.levelParams.map Level.param
    unless levels.length == 1 do throwError "Expected the original common universe"
    let u := levels.head!
    forallTelescope q.type fun xs prop => do
      unless prop.isAppOfArity ``Eq 3 do throwError "Expected the original scalar square"
      let r := xs.back!
      let ls := prop.getAppArgs[1]!
      let rs := prop.getAppArgs[2]!
      unless ls.isAppOfArity ``CategoryTheory.CategoryStruct.comp 7 &&
          rs.isAppOfArity ``CategoryTheory.CategoryStruct.comp 7 do
        throwError "Expected the two original composites"
      let a := ls.getAppArgs[5]!
      let d := rs.getAppArgs[6]!
      let h := rs.getAppArgs[5]!
      unless h.isAppOf ``CategoryTheory.Iso.hom do
        throwError "Expected the original comparison isomorphism"
      let i := h.getAppArgs.back!
      let it ← inferType i
      unless it.isAppOf ``CategoryTheory.Iso do throwError "Expected an additive iso"
      let ia := it.getAppArgs
      let x := ia[ia.size-2]!
      let y := ia.back!
      unless x.isAppOf ``CategoryTheory.Functor.obj do
        throwError "Expected the original forgotten module-valued homology"
      let c := x.getAppArgs.back!
      let ct ← inferType c
      unless ct.isAppOfArity ``ModuleCat 2 do throwError "Expected the source module type"
      let w := mkAppN (mkConst q.name levels) xs
      let hd := mkAppN (mkConst ``LinearStudy.nativeGeneralModuleH_publicOperator_heq_intrinsic levels) xs
      let ht ← inferType hd
      unless ht.isAppOfArity ``HEq 4 && ht.getAppArgs[1]! == d do
        throwError "Expected the same original target operator"
      let some g := ht.getAppArgs[3]!.find? (fun t =>
          t.isAppOfArity ``LinearStudy.originalActualHBaseModuleObject 5) |
        throwError "Expected the independent original target module"
      let e0 := mkAppN (mkConst ``LinearStudy.originalActualHBaseModuleObject_forget levels) g.getAppArgs
      let e ← mkAppM ``Eq.symm #[e0]
      let some coeff := a.find? (fun t =>
          t.isAppOfArity ``LinearStudy.orderedBaseCechActualCoefficientMap 9) |
        throwError "Expected the original source coefficient map"
      let ca := coeff.getAppArgs
      let some hm := a.find? (fun t =>
          t.isAppOf ``HomologicalComplex.homologyMap && t.getAppArgs.back!.isAppOf ``HAdd.hAdd) |
        throwError "Expected the original coefficient homology map"
      let n := hm.getAppArgs.back!
      let ha := mkAppN (mkConst ``LinearStudy.originalOrderedModuleHomologyScalarMorphism levels)
        #[ca[0]!,ca[1]!,ca[2]!,ca[3]!,r,ca[6]!,ca[7]!,ca[8]!,n]
      let af ← mkLambdaFVars #[r] a
      let df ← mkLambdaFVars #[r] d
      let haf ← mkLambdaFVars #[r] ha
      let hdf ← mkLambdaFVars #[r] hd
      let wf ← mkLambdaFVars #[r] w
      let valueBody := mkAppN (mkConst ``LinearStudy.originalScalarSquareModuleIso_literal [u,u])
        (ct.getAppArgs ++ #[c,g,y,i,e,af,df,haf,hdf,wf])
      let params := xs.extract 0 (xs.size-1)
      let type ← mkForallFVars params (← inferType valueBody)
      let value ← mkLambdaFVars params valueBody
      addDecl (.defnDecl {
        name := target.getId
        levelParams := q.levelParams
        type := type
        value := value
        hints := .regular 1
        safety := .safe
      }) (forceExpose := true)
      modifyEnv (addNoncomputable · target.getId)
  addDeclarationRangesFromSyntax target.getId stx target

check_general_module_intrinsic_iso LinearStudy.nativeIndependentFiniteNormalization_moduleCechActualHigherHIntrinsicIso_general
#check LinearStudy.nativeIndependentFiniteNormalization_moduleCechActualHigherHIntrinsicIso_general
#print axioms LinearStudy.nativeIndependentFiniteNormalization_moduleCechActualHigherHIntrinsicIso_general
