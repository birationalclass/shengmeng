import OAI.AlgebraicGeometry.PlaneCurves.Nagata
import Lean.DeclarationRange
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms

open Lean Elab Command

run_cmd do
  let env ← getEnv
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[idx]!
    if !modName.toString.startsWith "OAI.AlgebraicGeometry.PlaneCurves." then continue
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom"
      | .quotInfo _ => "quotient"
    let ty ← liftTermElabM <| Meta.ppExpr info.type
    let (inputs, result) ← liftTermElabM <| Meta.forallTelescope info.type fun args body => do
      let inputs ← args.toList.mapM fun arg => do
        let parameter ← arg.fvarId!.getDecl
        let t ← Meta.ppExpr parameter.type
        return parameter.userName.toString ++ " : " ++ t.pretty
      let result ← Meta.ppExpr body
      return (inputs, result.pretty)
    let axs ← collectAxioms name
    let deps := info.getUsedConstantsAsSet.toArray.map toString
    let range ← match (← findDeclarationRanges? name) with
      | none => pure Json.null
      | some rs => pure <| Json.mkObj [
          ("startLine", toJson rs.range.pos.line),
          ("endLine", toJson (rs.range.endPos.line - if rs.range.endPos.column == 0 then 1 else 0))]
    let data := Json.mkObj [
      ("name", toJson name.toString), ("module", toJson modName.toString),
      ("kind", toJson kind), ("type", toJson ty.pretty),
      ("inputs", toJson inputs), ("result", toJson result),
      ("axioms", toJson (axs.map toString)), ("dependencies", toJson deps), ("range", range)]
    logInfo m!"LEAN_RECORD|{data.compress}"
