module
public import Linear.GenericUnramifiedOpen
public import Mathlib.RingTheory.Localization.AtPrime.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy

theorem localRingHom_equiv_comp
    {R C A : Type*} [CommRing R] [CommRing C] [CommRing A]
    (φ : R →+* C) (E : C ≃+* A) (P : Ideal A) [P.IsPrime] :
    let p := P.comap E.toRingHom
    let q := p.comap φ
    (Localization.localRingEquiv p P E rfl).toRingHom.comp
      (Localization.localRingHom q p φ rfl) =
        Localization.localRingHom q P (E.toRingHom.comp φ) (by ext r; rfl) := by
  intro p q
  apply IsLocalization.ringHom_ext q.primeCompl
  apply RingHom.ext
  intro r
  change Localization.localRingEquiv p P E rfl
      (Localization.localRingHom q p φ rfl (algebraMap R (Localization.AtPrime q) r)) =
        Localization.localRingHom q P (E.toRingHom.comp φ) (by ext a; rfl)
          (algebraMap R (Localization.AtPrime q) r)
  rw [Localization.localRingHom_to_map, Localization.localRingHom_to_map]
  exact Localization.localRingHom_to_map p P E.toRingHom rfl (φ r)

/-- Unramification is carried through the actual source-local ring equivalence. -/
theorem localRingHom_formallyUnramified_of_equiv_comp
    {R C A : Type*} [CommRing R] [CommRing C] [CommRing A]
    (φ : R →+* C) (E : C ≃+* A) (P : Ideal A) [P.IsPrime]
    (h : let p := P.comap E.toRingHom
      let q := p.comap φ
      (Localization.localRingHom q P (E.toRingHom.comp φ) (by ext r; rfl)).FormallyUnramified) :
    let p := P.comap E.toRingHom
    let q := p.comap φ
    (Localization.localRingHom q p φ rfl).FormallyUnramified := by
  intro p q
  let L := Localization.localRingEquiv p P E rfl
  let Ψ := Localization.localRingHom q p φ rfl
  have he := localRingHom_equiv_comp φ E P
  change L.toRingHom.comp Ψ = Localization.localRingHom q P (E.toRingHom.comp φ) _ at he
  change (Localization.localRingHom q P (E.toRingHom.comp φ) (by ext r; rfl)).FormallyUnramified at h
  rw [← he] at h
  have hs : L.symm.toRingHom.FormallyUnramified := RingHom.FormallyUnramified.of_surjective L.symm.surjective
  have hc := h.comp hs
  have hh : L.symm.toRingHom.comp (L.toRingHom.comp Ψ) = Ψ := by
    ext a
    exact L.symm_apply_apply (Ψ a)
  rwa [hh] at hc

end LinearStudy
