module
import all Linear.GradedModuleProjection
import all Linear.GradedSubalgebraDecomposition
import all Linear.GradedSubmoduleDecomposition
import all Linear.OriginalDegreeVeroneseAlgebra
import all Linear.OriginalDegreeVeroneseAmbientCover
import all Linear.OriginalDegreeVeroneseChartInjectivity
import all Linear.OriginalDegreeVeroneseChartMapSquare
import all Linear.OriginalDegreeVeroneseChartRange
import all Linear.OriginalDegreeVeroneseChartRefinement
import all Linear.OriginalDegreeVeroneseChartRingEquiv
import all Linear.OriginalDegreeVeroneseChartRingEquivMk
import all Linear.OriginalDegreeVeroneseChartValues
import all Linear.OriginalDegreeVeroneseGrading
import all Linear.OriginalDegreeVeroneseProductChartCompat
import all Linear.OriginalDegreeVeroneseProductValueLeft
import all Linear.OriginalDegreeVeroneseProductValueRight
import all Linear.OriginalRingEquivOfEqualImages
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 5000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.GradedModuleProjection","Linear.GradedSubalgebraDecomposition","Linear.GradedSubmoduleDecomposition","Linear.OriginalDegreeVeroneseAlgebra","Linear.OriginalDegreeVeroneseAmbientCover","Linear.OriginalDegreeVeroneseChartInjectivity","Linear.OriginalDegreeVeroneseChartMapSquare","Linear.OriginalDegreeVeroneseChartRange","Linear.OriginalDegreeVeroneseChartRefinement","Linear.OriginalDegreeVeroneseChartRingEquiv","Linear.OriginalDegreeVeroneseChartRingEquivMk","Linear.OriginalDegreeVeroneseChartValues","Linear.OriginalDegreeVeroneseGrading","Linear.OriginalDegreeVeroneseProductChartCompat","Linear.OriginalDegreeVeroneseProductValueLeft","Linear.OriginalDegreeVeroneseProductValueRight","Linear.OriginalRingEquivOfEqualImages"]
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
