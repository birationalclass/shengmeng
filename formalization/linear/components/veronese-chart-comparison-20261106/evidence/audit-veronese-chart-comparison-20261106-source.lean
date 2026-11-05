module
public meta import Lean.Elab.Command
import all Linear.OriginalDegreeVeroneseAlgebra
import all Linear.OriginalDegreeVeroneseGrading
import all Linear.OriginalRingEquivOfEqualImages
import all Linear.OriginalDegreeVeroneseChartValues
import all Linear.OriginalDegreeVeroneseChartRange
import all Linear.OriginalDegreeVeroneseChartInjectivity
import all Linear.OriginalDegreeVeroneseChartRingEquiv
import all Linear.OriginalDegreeVeroneseChartRingEquivMk
import all Linear.OriginalDegreeVeroneseProductChartCompat
import all Linear.OriginalDegreeVeroneseProductValueLeft
import all Linear.OriginalDegreeVeroneseProductValueRight
import all Linear.OriginalDegreeVeroneseChartRefinement
import all Linear.OriginalDegreeVeroneseChartMapSquare
import all Linear.OriginalDegreeVeroneseAmbientCover
set_option maxHeartbeats 5000
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.originalDegreeVeroneseAlgebra
#print axioms LinearStudy.originalDegreeVeroneseAlgebra
#check @LinearStudy.originalDegreeVeroneseAlgebra_mem_of_mem
#print axioms LinearStudy.originalDegreeVeroneseAlgebra_mem_of_mem
#check @LinearStudy.originalDegreeVeronesePiece
#print axioms LinearStudy.originalDegreeVeronesePiece
#check @LinearStudy.originalDegreeVeronesePiece_one_iff
#print axioms LinearStudy.originalDegreeVeronesePiece_one_iff
#check @LinearStudy.originalDegreeVeronesePiece_independent
#print axioms LinearStudy.originalDegreeVeronesePiece_independent
#check @LinearStudy.originalDegreeVeronesePiece_total
#print axioms LinearStudy.originalDegreeVeronesePiece_total
#check @LinearStudy.originalDegreeVeroneseGrading
#print axioms LinearStudy.originalDegreeVeroneseGrading
#check @LinearStudy.originalRingEquivOfEqualImages
#print axioms LinearStudy.originalRingEquivOfEqualImages
#check @LinearStudy.originalRingEquivOfEqualImages_apply
#print axioms LinearStudy.originalRingEquivOfEqualImages_apply
#check @LinearStudy.originalDegreeVeroneseChartValue
#print axioms LinearStudy.originalDegreeVeroneseChartValue
#check @LinearStudy.originalDegreeVeroneseChartValue_mk
#print axioms LinearStudy.originalDegreeVeroneseChartValue_mk
#check @LinearStudy.originalDegreeVeroneseChartValue_range
#print axioms LinearStudy.originalDegreeVeroneseChartValue_range
#check @LinearStudy.originalDegreeVeroneseAwayMap_injective
#print axioms LinearStudy.originalDegreeVeroneseAwayMap_injective
#check @LinearStudy.originalDegreeVeroneseChartValue_injective
#print axioms LinearStudy.originalDegreeVeroneseChartValue_injective
#check @LinearStudy.originalDegreeVeroneseChartRingEquiv
#print axioms LinearStudy.originalDegreeVeroneseChartRingEquiv
#check @LinearStudy.originalDegreeVeroneseChartRingEquiv_val
#print axioms LinearStudy.originalDegreeVeroneseChartRingEquiv_val
#check @LinearStudy.originalDegreeVeroneseChartRingEquiv_mk
#print axioms LinearStudy.originalDegreeVeroneseChartRingEquiv_mk
#check @LinearStudy.originalDegreeVeroneseChartRestrict
#print axioms LinearStudy.originalDegreeVeroneseChartRestrict
#check @LinearStudy.originalDegreeVeroneseAmbientChartRestrict
#print axioms LinearStudy.originalDegreeVeroneseAmbientChartRestrict
#check @LinearStudy.originalDegreeVeroneseChartRestrict_mk
#print axioms LinearStudy.originalDegreeVeroneseChartRestrict_mk
#check @LinearStudy.originalDegreeVeroneseAmbientChartRestrict_mk
#print axioms LinearStudy.originalDegreeVeroneseAmbientChartRestrict_mk
#check @LinearStudy.originalDegreeVeroneseProductValueLeft_mk
#print axioms LinearStudy.originalDegreeVeroneseProductValueLeft_mk
#check @LinearStudy.originalDegreeVeroneseProductValueRight_mk
#print axioms LinearStudy.originalDegreeVeroneseProductValueRight_mk
#check @LinearStudy.originalDegreeVeroneseChartRingEquiv_awayMap
#print axioms LinearStudy.originalDegreeVeroneseChartRingEquiv_awayMap
#check @LinearStudy.originalDegreeVeroneseChartRingHomSquare
#print axioms LinearStudy.originalDegreeVeroneseChartRingHomSquare
#check @LinearStudy.OriginalDegreeVeroneseChartIndex
#print axioms LinearStudy.OriginalDegreeVeroneseChartIndex
#check @LinearStudy.originalDegreeVeroneseAmbientCover
#print axioms LinearStudy.originalDegreeVeroneseAmbientCover
#print LinearStudy.originalDegreeVeroneseAlgebra
#print LinearStudy.originalDegreeVeronesePiece
#print LinearStudy.originalDegreeVeroneseGrading
#print LinearStudy.originalRingEquivOfEqualImages
#print LinearStudy.originalDegreeVeroneseChartValue
#print LinearStudy.originalDegreeVeroneseChartRingEquiv
#print LinearStudy.originalDegreeVeroneseChartRestrict
#print LinearStudy.originalDegreeVeroneseAmbientChartRestrict
#print LinearStudy.OriginalDegreeVeroneseChartIndex
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool × Bool) := [(`LinearStudy.originalDegreeVeroneseAlgebra,false,false),(`LinearStudy.originalDegreeVeroneseAlgebra_mem_of_mem,true,true),(`LinearStudy.originalDegreeVeronesePiece,false,false),(`LinearStudy.originalDegreeVeronesePiece_one_iff,true,true),(`LinearStudy.originalDegreeVeronesePiece_independent,true,true),(`LinearStudy.originalDegreeVeronesePiece_total,true,true),(`LinearStudy.originalDegreeVeroneseGrading,false,false),(`LinearStudy.originalRingEquivOfEqualImages,false,false),(`LinearStudy.originalRingEquivOfEqualImages_apply,true,true),(`LinearStudy.originalDegreeVeroneseChartValue,false,false),(`LinearStudy.originalDegreeVeroneseChartValue_mk,true,true),(`LinearStudy.originalDegreeVeroneseChartValue_range,true,true),(`LinearStudy.originalDegreeVeroneseAwayMap_injective,true,true),(`LinearStudy.originalDegreeVeroneseChartValue_injective,true,true),(`LinearStudy.originalDegreeVeroneseChartRingEquiv,false,false),(`LinearStudy.originalDegreeVeroneseChartRingEquiv_val,true,true),(`LinearStudy.originalDegreeVeroneseChartRingEquiv_mk,true,true),(`LinearStudy.originalDegreeVeroneseChartRestrict,false,false),(`LinearStudy.originalDegreeVeroneseAmbientChartRestrict,false,false),(`LinearStudy.originalDegreeVeroneseChartRestrict_mk,true,true),(`LinearStudy.originalDegreeVeroneseAmbientChartRestrict_mk,true,true),(`LinearStudy.originalDegreeVeroneseProductValueLeft_mk,true,true),(`LinearStudy.originalDegreeVeroneseProductValueRight_mk,true,true),(`LinearStudy.originalDegreeVeroneseChartRingEquiv_awayMap,true,true),(`LinearStudy.originalDegreeVeroneseChartRingHomSquare,true,true),(`LinearStudy.OriginalDegreeVeroneseChartIndex,false,false),(`LinearStudy.originalDegreeVeroneseAmbientCover,true,true)]
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
