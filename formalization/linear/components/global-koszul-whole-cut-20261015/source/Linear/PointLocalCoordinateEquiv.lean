module
public import Linear.LocalGeneratorsEquiv
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy

def pointLocalCoordinateEquiv {R T : Type*} [CommRing R] [CommRing T]
    (I P : Ideal R) [P.IsPrime] (Q : Ideal T) [Q.IsPrime]
    (e : R ≃+* T) (hP : P = Q.comap e) :
    (Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P))) ≃+*
      (Localization.AtPrime Q ⧸ (I.map e.toRingHom).map (algebraMap T (Localization.AtPrime Q))) := by
  have hm : P.primeCompl.map e = Q.primeCompl := by
    simpa only [← hP] using e.map_primeCompl_comap_eq Q
  let L := IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime P) (Localization.AtPrime Q) e hm
  have hc : L.toRingHom.comp (algebraMap R (Localization.AtPrime P)) =
      (algebraMap T (Localization.AtPrime Q)).comp e.toRingHom := by
    apply RingHom.ext
    intro a
    exact IsLocalization.ringEquivOfRingEquiv_eq (j := e) hm a
  have hi : (I.map e.toRingHom).map (algebraMap T (Localization.AtPrime Q)) =
      (I.map (algebraMap R (Localization.AtPrime P))).map L.toRingHom := by
    rw [Ideal.map_map, Ideal.map_map, hc]
  exact Ideal.quotientEquiv _ _ L hi

theorem pointLocalCoordinateEquiv_mk {R T : Type*} [CommRing R] [CommRing T]
    (I P : Ideal R) [P.IsPrime] (Q : Ideal T) [Q.IsPrime]
    (e : R ≃+* T) (hP : P = Q.comap e) (a : R) :
    pointLocalCoordinateEquiv I P Q e hP
      (Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime P) a)) =
        Ideal.Quotient.mk _ (algebraMap T (Localization.AtPrime Q) (e a)) := by
  unfold pointLocalCoordinateEquiv
  rw [Ideal.quotientEquiv_mk]
  congr 1
  exact IsLocalization.ringEquivOfRingEquiv_eq (j := e) _ a

theorem pointLocalCoordinateEquiv_symm_mk {R T : Type*} [CommRing R] [CommRing T]
    (I P : Ideal R) [P.IsPrime] (Q : Ideal T) [Q.IsPrime]
    (e : R ≃+* T) (hP : P = Q.comap e) (a : T) :
    (pointLocalCoordinateEquiv I P Q e hP).symm
      (Ideal.Quotient.mk _ (algebraMap T (Localization.AtPrime Q) a)) =
        Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime P) (e.symm a)) := by
  apply (pointLocalCoordinateEquiv I P Q e hP).injective
  rw [RingEquiv.apply_symm_apply, pointLocalCoordinateEquiv_mk, e.apply_symm_apply]

theorem actual_point_parameters_transport_under_coordinates
    {R T ι : Type*} [CommRing R] [CommRing T]
    (I P : Ideal R) [P.IsPrime] (Q : Ideal T) [Q.IsPrime]
    (e : R ≃+* T) (hP : P = Q.comap e)
    [IsLocalRing (Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P)))]
    [IsLocalRing (Localization.AtPrime Q ⧸ (I.map e.toRingHom).map (algebraMap T (Localization.AtPrime Q)))]
    (a : ι → T)
    (ha : Ideal.span (Set.range (fun i => Ideal.Quotient.mk _
      (algebraMap T (Localization.AtPrime Q) (a i)))) =
        IsLocalRing.maximalIdeal
          (Localization.AtPrime Q ⧸ (I.map e.toRingHom).map (algebraMap T (Localization.AtPrime Q)))) :
    Ideal.span (Set.range (fun i => Ideal.Quotient.mk _
      (algebraMap R (Localization.AtPrime P) (e.symm (a i))))) =
        IsLocalRing.maximalIdeal
          (Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P))) := by
  let E := pointLocalCoordinateEquiv I P Q e hP
  have hh := congrArg (fun J => J.map E.symm.toRingHom) ha
  rw [Ideal.map_span, ← Set.range_comp] at hh
  have hh' := hh.trans (IsLocalRing.map_ringEquiv_maximalIdeal E.symm)
  have he : (E.symm.toRingHom ∘ fun i => Ideal.Quotient.mk _
      (algebraMap T (Localization.AtPrime Q) (a i))) =
      (fun i => Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime P) (e.symm (a i)))) := by
    funext i
    exact pointLocalCoordinateEquiv_symm_mk I P Q e hP (a i)
  rwa [he] at hh'
end LinearStudy
