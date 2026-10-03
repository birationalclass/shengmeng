import Section43
import Lean.Util.CollectAxioms

/-! Audit every exported declaration in the formalization, including instances and definitions. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.toList.map Prod.fst |>.filter (fun n ↦ (`Section43).isPrefixOf n)
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for n in names do
    let axioms ← Lean.collectAxioms n
    let bad := axioms.filter (!allowed.contains ·)
    unless bad.isEmpty do
      throwError "{n} has forbidden axioms: {bad}"
    logInfo m!"{n}: {axioms}"
  logInfo m!"AUDIT PASSED: {names.length} declarations; only standard axioms."
