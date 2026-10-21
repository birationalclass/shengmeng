module
import all Linear.AcyclicChainExtVanishing
import all Linear.AcyclicChainHomExtension
import all Linear.AcyclicChainOpcycleSequence
import all Linear.AcyclicGlobalExtCoefficientNaturality
import all Linear.AcyclicGlobalExtIteratedCoefficientNaturality
import all Linear.AcyclicHomCokernelCoefficientNaturality
import all Linear.AcyclicResolutionExtVanishing
import all Linear.AcyclicResolutionGlobalExtCokernel
import all Linear.AcyclicResolutionGlobalExtHomology
import all Linear.AcyclicResolutionGlobalExtShift
import all Linear.AcyclicResolutionHomologyCoefficientNaturality
import all Linear.AcyclicResolutionOpcycleCoefficientNaturality
import all Linear.ChainActualHomCoefficientNaturality
import all Linear.ChainActualHomCycles
import all Linear.ChainActualHomHomologyCoefficientNaturality
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 50000
run_cmd do
  let env ← Lean.getEnv
  let isOwn := fun (n : Lean.Name) => match env.getModuleIdxFor? n with
    | none => false
    | some idx => (env.header.moduleNames[idx]!).toString.startsWith "Linear."
  for n in [`TopCat.LocalPredicate.mk.congr_simp,`TopCat.PrelocalPredicate.mk.congr_simp,`TopCat.LocalPredicate.mk,`TopCat.PrelocalPredicate.mk] do
    let owner := match env.getModuleIdxFor? n with
      | none => "not-imported"
      | some idx => (env.header.moduleNames[idx]!).toString
    Lean.logInfo m!"SPECIAL_ORIGIN|{n}|{owner}"
  let mut count : Nat := 0
  for (name,info) in env.constants.toList do
    unless isOwn name do continue
    let some idx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[idx]!
    let deps := String.intercalate "," (info.getUsedConstantsAsSet.toArray.toList.filter isOwn |>.map toString)
    Lean.logInfo m!"SOURCE_DEPENDENCIES|{name}|{modName}|{deps}"
    let some ranges ← Lean.findDeclarationRanges? name | continue
    let r := ranges.range
    Lean.logInfo m!"SOURCE_RANGE|{name}|{modName}|{r.pos.line}|{r.pos.column}|{r.endPos.line}|{r.endPos.column}|{deps}"
    count := count+1
  if count < 18 then throwError "Current complete source ranges missing"
  Lean.logInfo m!"SOURCE_RANGE_COUNT|{count}"
