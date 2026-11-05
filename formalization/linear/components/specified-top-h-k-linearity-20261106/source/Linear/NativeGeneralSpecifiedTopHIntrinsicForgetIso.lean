module
public import Linear.NativeGeneralSpecifiedTopHIntrinsicSpecIso
public import Linear.OriginalInverseCompositeForgetIso
public import Lean
@[expose] public section
set_option maxHeartbeats 5000
open Lean Meta Elab Command

/-- The specified K-linear top-H duality forgets to its original named
additive isomorphism, via the exact original actual-H group identification. -/
elab "check_general_specified_top_h_forget_iso " target:ident : command => do
  let stx ← getRef
  withExporting (isExporting := true) <| liftTermElabM do
    let d ← getConstInfoDefn ``LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualKLinearIso_general
    let old ← getConstInfoDefn ``LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualIso_general
    let levels := d.levelParams.map Level.param
    forallTelescope d.type fun xs _ => do
      let body := (mkAppN d.value xs).headBeta
      let mut ob := (mkAppN old.value xs).headBeta
      while ob.isLet do
        ob := ob.letBody!.instantiate1 ob.letValue!
      unless body.isAppOfArity ``CategoryTheory.Iso.trans 7 &&
          ob.isAppOfArity ``CategoryTheory.Iso.trans 7 do
        throwError "Expected the original two-factor dualities"
      let ba := body.getAppArgs
      let oa := ob.getAppArgs
      let i := ba[5]!.getAppArgs.back!
      let j := oa[5]!.getAppArgs.back!
      let b := ba[6]!
      let f := oa[6]!.getAppArgs[4]!
      unless oa[6]!.isAppOfArity ``CategoryTheory.Functor.mapIso 8 &&
          oa[6]!.getAppArgs.back! == b &&
          i.isAppOf ``LinearStudy.nativeIndependentFiniteNormalization_moduleCechActualHigherHSpecIso_general &&
          j.isAppOf ``LinearStudy.nativeIndependentFiniteNormalization_moduleCechActualHigherHIso_general do
        throwError "The original comparison factors disagree"
      let h := mkAppN (mkConst
        ``LinearStudy.nativeIndependentFiniteNormalization_moduleCechActualHigherHSpecIso_general_forget_hom
        i.getAppFn.constLevels!) i.getAppArgs
      let ht ← inferType h
      unless ht.isAppOfArity ``Eq 3 do throwError "Expected the checked forward map equality"
      let cast := ht.getAppArgs[1]!.getAppArgs.back!
      unless cast.isAppOf ``CategoryTheory.eqToHom do throwError "Expected the exact target identification"
      let e := cast.getAppArgs.back!
      let p ← mkAppM ``LinearStudy.originalInverseCompositeForgetIso #[f,i,j,b,e,h]
      let pt ← inferType p
      unless pt.isAppOfArity ``Eq 3 do throwError "Expected the exact inverse-composition equality"
      let pa := pt.getAppArgs
      let lift := mkAppN (mkConst d.name levels) xs
      let additive := mkAppN (mkConst old.name levels) xs
      let mapped := pa[1]!.getAppArgs.back!
      let original := mapped.getAppArgs.back!
      unless mapped.isAppOfArity ``CategoryTheory.Functor.mapIso 8 &&
          original.isAppOfArity ``CategoryTheory.Iso.trans 7 &&
          original.getAppArgs[5]!.getAppArgs.back! == i &&
          original.getAppArgs[6]! == b do
        throwError "Expected the two unchanged K-linear factors"
      let left := pa[1]!.replace (fun t => if t == original then some lift else none)
      let prop := mkApp3 pt.getAppFn pa[0]! left additive
      let type ← mkForallFVars xs prop
      let value ← mkLambdaFVars xs p
      addDecl (.thmDecl {name := target.getId, levelParams := d.levelParams, type, value})
        (forceExpose := true)
  addDeclarationRangesFromSyntax target.getId stx target

check_general_specified_top_h_forget_iso LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualKLinearIso_general_forget
#check LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualKLinearIso_general_forget
#print axioms LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualKLinearIso_general_forget
