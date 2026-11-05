module
public import Mathlib.Algebra.Ring.Subring.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
universe u v w
variable {A : Type u} {B : Type v} {T : Type w} [Ring A] [Ring B] [Ring T]

/-- Two rings embedded in a common ring with equal images have the
unique ring equivalence respecting both embeddings. -/
def originalRingEquivOfEqualImages
    (r : A →+* T) (s : B →+* T) (hr : Function.Injective r) (hs : Function.Injective s)
    (h : r.range = s.range) : A ≃+* B :=
  let er := RingEquiv.ofLeftInverse hr.hasLeftInverse.choose_spec
  let es := RingEquiv.ofLeftInverse hs.hasLeftInverse.choose_spec
  er.trans ((RingEquiv.subringCongr h).trans es.symm)

theorem originalRingEquivOfEqualImages_apply
    (r : A →+* T) (s : B →+* T) (hr : Function.Injective r) (hs : Function.Injective s)
    (h : r.range = s.range) (a : A) :
    s (originalRingEquivOfEqualImages r s hr hs h a) = r a := by
  let er := RingEquiv.ofLeftInverse hr.hasLeftInverse.choose_spec
  let es := RingEquiv.ofLeftInverse hs.hasLeftInverse.choose_spec
  let z := RingEquiv.subringCongr h (er a)
  change s (es.symm z) = r a
  calc
    _ = ((es (es.symm z) : s.range) : T) := rfl
    _ = (z : T) := congrArg Subtype.val (es.apply_symm_apply z)
    _ = r a := rfl

end LinearStudy
#check LinearStudy.originalRingEquivOfEqualImages
#print axioms LinearStudy.originalRingEquivOfEqualImages
#check LinearStudy.originalRingEquivOfEqualImages_apply
#print axioms LinearStudy.originalRingEquivOfEqualImages_apply
