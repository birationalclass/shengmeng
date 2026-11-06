module
import all Linear.GradedIdealContractionByDegrees
import all Linear.OriginalDegreeVeroneseAllHomogeneousOpen
import all Linear.OriginalDegreeVeroneseBasicOpen
import all Linear.OriginalDegreeVeronesePrimeAnnihilator
import all Linear.OriginalDegreeVeronesePrimeContraction
import all Linear.OriginalDegreeVeronesePrimeDenominator
import all Linear.OriginalDegreeVeronesePrimeFractionEquiv
import all Linear.OriginalDegreeVeronesePrimeFractionSets
import all Linear.OriginalDegreeVeronesePrimeLocalization
import all Linear.OriginalDegreeVeronesePrimeReflect
import all Linear.OriginalDegreeVeronesePrimeRepresent
import all Linear.OriginalDegreeVeronesePrimeSameShift
import all Linear.OriginalDegreeVeronesePromotedFraction
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 5000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.GradedIdealContractionByDegrees","Linear.OriginalDegreeVeroneseAllHomogeneousOpen","Linear.OriginalDegreeVeroneseBasicOpen","Linear.OriginalDegreeVeronesePrimeAnnihilator","Linear.OriginalDegreeVeronesePrimeContraction","Linear.OriginalDegreeVeronesePrimeDenominator","Linear.OriginalDegreeVeronesePrimeFractionEquiv","Linear.OriginalDegreeVeronesePrimeFractionSets","Linear.OriginalDegreeVeronesePrimeLocalization","Linear.OriginalDegreeVeronesePrimeReflect","Linear.OriginalDegreeVeronesePrimeRepresent","Linear.OriginalDegreeVeronesePrimeSameShift","Linear.OriginalDegreeVeronesePromotedFraction"]
  let isOwn := fun (n : Lean.Name) => match env.getModuleIdxFor? n with
    | none => false
    | some idx => (env.header.moduleNames[idx]!).toString.startsWith "Linear."
  let mut count : Nat := 0
  let mut seen : Lean.NameSet := {}
  for i in [:env.header.moduleData.size] do
    let owner := env.header.moduleNames[i]!
    unless selected.contains owner.toString do continue
    let data := env.header.moduleData[i]!
    for name in data.constNames ++ data.extraConstNames do
      if seen.contains name then continue
      seen := seen.insert name
      let some info := env.find? name | continue
      let some idx := env.getModuleIdxFor? name | continue
      let modName := env.header.moduleNames[idx]!
      unless selected.contains modName.toString do continue
      let deps := String.intercalate "," (info.getUsedConstantsAsSet.toArray.toList.filter isOwn |>.map toString)
      Lean.logInfo m!"SOURCE_DEPENDENCIES|{name}|{modName}|{deps}"
      let some ranges ← Lean.findDeclarationRanges? name | continue
      let q := ranges.range
      Lean.logInfo m!"SOURCE_RANGE|{name}|{modName}|{q.pos.line}|{q.pos.column}|{q.endPos.line}|{q.endPos.column}|{deps}"
      count := count+1
  Lean.logInfo m!"SOURCE_RANGE_COUNT|{count}"
