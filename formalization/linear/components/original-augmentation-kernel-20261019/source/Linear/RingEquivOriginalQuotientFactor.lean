module
public import Mathlib.RingTheory.Ideal.Quotient.Operations
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
variable {B R C T : Type*} [CommRing B] [CommRing R] [CommRing C] [CommRing T]

/-- Transport an ACTUAL original quotient isomorphism through supplied
actual coordinate-ring isomorphisms. The ideal equality is explicit. -/
def ringEquivOriginalQuotientFactor (J : Ideal B) (I : Ideal R)
    (eB : B ≃+* R) (eC : C ≃+* T) (eQ : (B ⧸ J) ≃+* C)
    (hI : I = J.map eB.toRingHom) : (R ⧸ I) ≃+* T :=
  (Ideal.quotientEquiv J I eB hI).symm.trans (eQ.trans eC)

/-- If both supplied actual ring isomorphisms preserve their ORIGINAL
quotient maps,the transported isomorphism preserves the SAME original
map on EVERY element. All compatibility inputs are explicit here. -/
theorem ringEquivOriginalQuotientFactor_mk (J : Ideal B) (I : Ideal R)
    (eB : B ≃+* R) (eC : C ≃+* T) (eQ : (B ⧸ J) ≃+* C)
    (hI : I = J.map eB.toRingHom) (g : B →+* C) (f : R →+* T)
    (hQ : ∀ x : B,eQ (Ideal.Quotient.mk J x) = g x)
    (hn : ∀ x : B,f (eB x) = eC (g x)) (x : R) :
    ringEquivOriginalQuotientFactor J I eB eC eQ hI (Ideal.Quotient.mk I x) = f x := by
  obtain ⟨y,rfl⟩ := eB.surjective x
  change eC (eQ (Ideal.Quotient.mk J (eB.symm (eB y)))) = f (eB y)
  rw [eB.symm_apply_apply,hQ]
  exact (hn y).symm

end LinearStudy
