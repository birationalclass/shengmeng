module
public meta import Lean.Elab.Command
import all Linear.OriginalDegreeVeroneseSpecChartRingSquare
import all Linear.OriginalDegreeVeroneseSpecChart
import all Linear.OriginalDegreeVeroneseAffineCover
import all Linear.OriginalDegreeVeroneseAffineOverlap
import all Linear.OriginalDegreeVeroneseOverlapProjection
import all Linear.OriginalDegreeVeroneseAffineOverlapIso
import all Linear.OriginalDegreeVeroneseGlueCompatibility
import all Linear.OriginalDegreeVeroneseProjGlue
import all Linear.OriginalDegreeVeroneseProjIso
set_option maxHeartbeats 5000
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.originalDegreeVeroneseBundledChart
#print axioms LinearStudy.originalDegreeVeroneseBundledChart
#check @LinearStudy.originalDegreeVeroneseBundledAmbientChart
#print axioms LinearStudy.originalDegreeVeroneseBundledAmbientChart
#check @LinearStudy.originalDegreeVeroneseBundledChartIso
#print axioms LinearStudy.originalDegreeVeroneseBundledChartIso
#check @LinearStudy.originalDegreeVeroneseBundledChartRes
#print axioms LinearStudy.originalDegreeVeroneseBundledChartRes
#check @LinearStudy.originalDegreeVeroneseBundledAmbientRes
#print axioms LinearStudy.originalDegreeVeroneseBundledAmbientRes
#check @LinearStudy.originalDegreeVeroneseChartCommRingCatSquare
#print axioms LinearStudy.originalDegreeVeroneseChartCommRingCatSquare
#check @LinearStudy.originalDegreeVeroneseSpecChartIso
#print axioms LinearStudy.originalDegreeVeroneseSpecChartIso
#check @LinearStudy.originalDegreeVeroneseSpecChartSquare
#print axioms LinearStudy.originalDegreeVeroneseSpecChartSquare
#check @LinearStudy.originalDegreeVeroneseAmbientAwayImm
#print axioms LinearStudy.originalDegreeVeroneseAmbientAwayImm
#check @LinearStudy.originalDegreeVeroneseAmbientAwayImmOpen
#print axioms LinearStudy.originalDegreeVeroneseAmbientAwayImmOpen
#check @LinearStudy.originalDegreeVeroneseAmbientAwayImm_opensRange
#print axioms LinearStudy.originalDegreeVeroneseAmbientAwayImm_opensRange
#check @LinearStudy.originalDegreeVeroneseAmbientIndex_exists
#print axioms LinearStudy.originalDegreeVeroneseAmbientIndex_exists
#check @LinearStudy.originalDegreeVeroneseAmbientAffineCover
#print axioms LinearStudy.originalDegreeVeroneseAmbientAffineCover
#check @LinearStudy.originalDegreeVeroneseRegradedAffineCover
#print axioms LinearStudy.originalDegreeVeroneseRegradedAffineCover
#check @LinearStudy.originalDegreeVeroneseAffineCover_sameIndex
#print axioms LinearStudy.originalDegreeVeroneseAffineCover_sameIndex
#check @LinearStudy.originalDegreeVeroneseIndexedAffineIso
#print axioms LinearStudy.originalDegreeVeroneseIndexedAffineIso
#check @LinearStudy.originalDegreeVeroneseAmbientOverlap
#print axioms LinearStudy.originalDegreeVeroneseAmbientOverlap
#check @LinearStudy.originalDegreeVeroneseRegradedOverlap
#print axioms LinearStudy.originalDegreeVeroneseRegradedOverlap
#check @LinearStudy.originalDegreeVeroneseAmbientOverlap_inv_fst
#print axioms LinearStudy.originalDegreeVeroneseAmbientOverlap_inv_fst
#check @LinearStudy.originalDegreeVeroneseAmbientOverlap_inv_snd
#print axioms LinearStudy.originalDegreeVeroneseAmbientOverlap_inv_snd
#check @LinearStudy.originalDegreeVeroneseRegradedOverlap_inv_fst
#print axioms LinearStudy.originalDegreeVeroneseRegradedOverlap_inv_fst
#check @LinearStudy.originalDegreeVeroneseRegradedOverlap_inv_snd
#print axioms LinearStudy.originalDegreeVeroneseRegradedOverlap_inv_snd
#check @LinearStudy.originalDegreeVeroneseAffineOverlapIso
#print axioms LinearStudy.originalDegreeVeroneseAffineOverlapIso
#check @LinearStudy.originalDegreeVeroneseAffineOverlapIso_hom_fst
#print axioms LinearStudy.originalDegreeVeroneseAffineOverlapIso_hom_fst
#check @LinearStudy.originalDegreeVeroneseAffineOverlapIso_hom_snd
#print axioms LinearStudy.originalDegreeVeroneseAffineOverlapIso_hom_snd
#check @LinearStudy.originalDegreeVeroneseAffineOverlapIso_inv_fst
#print axioms LinearStudy.originalDegreeVeroneseAffineOverlapIso_inv_fst
#check @LinearStudy.originalDegreeVeroneseAffineOverlapIso_inv_snd
#print axioms LinearStudy.originalDegreeVeroneseAffineOverlapIso_inv_snd
#check @LinearStudy.originalDegreeVeroneseForwardChartCompatibility
#print axioms LinearStudy.originalDegreeVeroneseForwardChartCompatibility
#check @LinearStudy.originalDegreeVeroneseInverseChartCompatibility
#print axioms LinearStudy.originalDegreeVeroneseInverseChartCompatibility
#check @LinearStudy.originalDegreeVeroneseProjHom
#print axioms LinearStudy.originalDegreeVeroneseProjHom
#check @LinearStudy.originalDegreeVeroneseProjInv
#print axioms LinearStudy.originalDegreeVeroneseProjInv
#check @LinearStudy.originalDegreeVeroneseProjHom_onChart
#print axioms LinearStudy.originalDegreeVeroneseProjHom_onChart
#check @LinearStudy.originalDegreeVeroneseProjInv_onChart
#print axioms LinearStudy.originalDegreeVeroneseProjInv_onChart
#check @LinearStudy.originalDegreeVeroneseProjHom_comp_Inv
#print axioms LinearStudy.originalDegreeVeroneseProjHom_comp_Inv
#check @LinearStudy.originalDegreeVeroneseProjInv_comp_Hom
#print axioms LinearStudy.originalDegreeVeroneseProjInv_comp_Hom
#check @LinearStudy.originalDegreeVeroneseProjIso
#print axioms LinearStudy.originalDegreeVeroneseProjIso
#check @LinearStudy.originalDegreeVeroneseProjIso_hom_onChart
#print axioms LinearStudy.originalDegreeVeroneseProjIso_hom_onChart
#check @LinearStudy.originalDegreeVeroneseProjIso_inv_onChart
#print axioms LinearStudy.originalDegreeVeroneseProjIso_inv_onChart
#print LinearStudy.originalDegreeVeroneseBundledChart
#print LinearStudy.originalDegreeVeroneseBundledAmbientChart
#print LinearStudy.originalDegreeVeroneseBundledChartIso
#print LinearStudy.originalDegreeVeroneseBundledChartRes
#print LinearStudy.originalDegreeVeroneseBundledAmbientRes
#print LinearStudy.originalDegreeVeroneseSpecChartIso
#print LinearStudy.originalDegreeVeroneseAmbientAwayImm
#print LinearStudy.originalDegreeVeroneseAmbientAwayImmOpen
#print LinearStudy.originalDegreeVeroneseAmbientAffineCover
#print LinearStudy.originalDegreeVeroneseRegradedAffineCover
#print LinearStudy.originalDegreeVeroneseIndexedAffineIso
#print LinearStudy.originalDegreeVeroneseAmbientOverlap
#print LinearStudy.originalDegreeVeroneseRegradedOverlap
#print LinearStudy.originalDegreeVeroneseAffineOverlapIso
#print LinearStudy.originalDegreeVeroneseProjHom
#print LinearStudy.originalDegreeVeroneseProjInv
#print LinearStudy.originalDegreeVeroneseProjIso
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool × Bool) := [(`LinearStudy.originalDegreeVeroneseBundledChart,false,false),(`LinearStudy.originalDegreeVeroneseBundledAmbientChart,false,false),(`LinearStudy.originalDegreeVeroneseBundledChartIso,false,false),(`LinearStudy.originalDegreeVeroneseBundledChartRes,false,false),(`LinearStudy.originalDegreeVeroneseBundledAmbientRes,false,false),(`LinearStudy.originalDegreeVeroneseChartCommRingCatSquare,true,true),(`LinearStudy.originalDegreeVeroneseSpecChartIso,false,false),(`LinearStudy.originalDegreeVeroneseSpecChartSquare,true,true),(`LinearStudy.originalDegreeVeroneseAmbientAwayImm,false,false),(`LinearStudy.originalDegreeVeroneseAmbientAwayImmOpen,true,true),(`LinearStudy.originalDegreeVeroneseAmbientAwayImm_opensRange,true,true),(`LinearStudy.originalDegreeVeroneseAmbientIndex_exists,true,true),(`LinearStudy.originalDegreeVeroneseAmbientAffineCover,false,false),(`LinearStudy.originalDegreeVeroneseRegradedAffineCover,false,false),(`LinearStudy.originalDegreeVeroneseAffineCover_sameIndex,true,true),(`LinearStudy.originalDegreeVeroneseIndexedAffineIso,false,false),(`LinearStudy.originalDegreeVeroneseAmbientOverlap,false,false),(`LinearStudy.originalDegreeVeroneseRegradedOverlap,false,false),(`LinearStudy.originalDegreeVeroneseAmbientOverlap_inv_fst,true,true),(`LinearStudy.originalDegreeVeroneseAmbientOverlap_inv_snd,true,true),(`LinearStudy.originalDegreeVeroneseRegradedOverlap_inv_fst,true,true),(`LinearStudy.originalDegreeVeroneseRegradedOverlap_inv_snd,true,true),(`LinearStudy.originalDegreeVeroneseAffineOverlapIso,false,false),(`LinearStudy.originalDegreeVeroneseAffineOverlapIso_hom_fst,true,true),(`LinearStudy.originalDegreeVeroneseAffineOverlapIso_hom_snd,true,true),(`LinearStudy.originalDegreeVeroneseAffineOverlapIso_inv_fst,true,true),(`LinearStudy.originalDegreeVeroneseAffineOverlapIso_inv_snd,true,true),(`LinearStudy.originalDegreeVeroneseForwardChartCompatibility,true,true),(`LinearStudy.originalDegreeVeroneseInverseChartCompatibility,true,true),(`LinearStudy.originalDegreeVeroneseProjHom,false,false),(`LinearStudy.originalDegreeVeroneseProjInv,false,false),(`LinearStudy.originalDegreeVeroneseProjHom_onChart,true,true),(`LinearStudy.originalDegreeVeroneseProjInv_onChart,true,true),(`LinearStudy.originalDegreeVeroneseProjHom_comp_Inv,true,true),(`LinearStudy.originalDegreeVeroneseProjInv_comp_Hom,true,true),(`LinearStudy.originalDegreeVeroneseProjIso,false,false),(`LinearStudy.originalDegreeVeroneseProjIso_hom_onChart,true,true),(`LinearStudy.originalDegreeVeroneseProjIso_inv_onChart,true,true)]
  let env ← Lean.getEnv
  for (n,want,wantTheorem) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
    let kernelKind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | _ => "other"
    unless kernelKind == (if wantTheorem then "theorem" else "definition") do
      throwError m!"Incorrect kernel declaration kind: {n}"
    Lean.logInfo m!"KINDCHECK:{n}:{kernelKind}"
