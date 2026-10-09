module
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Ideal.Quotient.Operations
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace LinearStudy

/-- The actual map between quotients by an ideal and its extended ideal. -/
def quotientBaseChangeMap {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (I : Ideal R) : R ⧸ I →+* S ⧸ I.map φ :=
  Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map

theorem quotientBaseChangeMap_mk {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (I : Ideal R) (a : R) :
    quotientBaseChangeMap φ I (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk (I.map φ) (φ a) := rfl

/-- Extension of an ideal gives the ring-theoretic pushout, without a
reducedness assumption and without replacing either ideal by its radical. -/
theorem quotientBaseChange_isPushout {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (I : Ideal R) :
    IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom (Ideal.Quotient.mk I))
      (CommRingCat.ofHom (Ideal.Quotient.mk (I.map φ)))
      (CommRingCat.ofHom (quotientBaseChangeMap φ I)) := by
  let f := CommRingCat.ofHom φ
  let g := CommRingCat.ofHom (Ideal.Quotient.mk I)
  let inl := CommRingCat.ofHom (Ideal.Quotient.mk (I.map φ))
  let inr := CommRingCat.ofHom (quotientBaseChangeMap φ I)
  have hw : f ≫ inl = g ≫ inr := by
    ext a
    rfl
  have hkill (s : PushoutCocone f g) : I.map φ ≤ RingHom.ker s.inl.hom := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change s.inl.hom (φ a) = 0
    have he := congrArg (fun h => h.hom a) s.condition
    change s.inl.hom (φ a) = s.inr.hom (Ideal.Quotient.mk I a) at he
    rw [he, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  let desc (s : PushoutCocone f g) := CommRingCat.ofHom
    (Ideal.Quotient.lift (I.map φ) s.inl.hom (fun a ha => hkill s ha))
  refine IsPushout.of_isColimit (c := PushoutCocone.mk inl inr hw) ?_
  refine PushoutCocone.IsColimit.mk hw desc ?_ ?_ ?_
  · intro s
    ext a
    rfl
  · intro s
    ext a
    have he := congrArg (fun h => h.hom a) s.condition
    change s.inl.hom (φ a) = s.inr.hom (Ideal.Quotient.mk I a) at he
    exact he
  · intro s m hm _
    ext a
    exact congrArg (fun h => h.hom a) hm

/-- The closed zero scheme of the extended ideal is the actual scheme
fiber product. The statement retains all nilpotent structure. -/
theorem quotientBaseChange_isPullback {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (I : Ideal R) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map φ))))
      (Spec.map (CommRingCat.ofHom (quotientBaseChangeMap φ I)))
      (Spec.map (CommRingCat.ofHom φ))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (quotientBaseChange_isPushout φ I)

/-- The same closed base change, with a proved equality to an explicitly
presented ideal. No quotient has been reduced or supplied as an input. -/
theorem quotientBaseChange_isPullback_of_eq {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (I : Ideal R) (J : Ideal S) (hJ : I.map φ = J) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
      (Spec.map (CommRingCat.ofHom
        (Ideal.quotientMap J φ (hJ ▸ Ideal.le_comap_map))))
      (Spec.map (CommRingCat.ofHom φ))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) := by
  subst J
  exact quotientBaseChange_isPullback φ I

end LinearStudy
