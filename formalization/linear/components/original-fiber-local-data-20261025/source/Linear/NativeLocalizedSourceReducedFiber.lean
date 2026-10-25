module
public import Linear.NativeLocalizedUpperAlgebra
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.LocalProperties.Reduced
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
universe u
/-- Reducedness of the ORIGINAL closed fiber derives reducedness of the
ACTUAL closed fiber after base localization. No finite/free/flat input. -/
theorem nativeLocalizedSourceClosedFiber_reduced
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (m : Ideal R) [m.IsPrime]
    [IsReduced (S ⧸ m.map (algebraMap R S))] :
    let Q := Localization.AtPrime m
    let A := LocalizedModule m.primeCompl S
    letI : Module Q A := LocalizedModule.moduleOfIsLocalization
    letI : Algebra Q A := LocalizedModule.algebraOfIsLocalization (S:=m.primeCompl) Q
    IsReduced (A ⧸ (IsLocalRing.maximalIdeal Q).map (algebraMap Q A)) := by
  let Q := Localization.AtPrime m
  let A := LocalizedModule m.primeCompl S
  letI : Module Q A := LocalizedModule.moduleOfIsLocalization
  letI : Algebra Q A := LocalizedModule.algebraOfIsLocalization (S:=m.primeCompl) Q
  letI : Algebra S A := nativeLocalizedUpperAlgebra (S:=S) m.primeCompl
  let N := Algebra.algebraMapSubmonoid S m.primeCompl
  letI : IsLocalization N A := nativeLocalizedUpperAlgebra_isLocalization (S:=S) m.primeCompl
  let I := m.map (algebraMap R S)
  have hi : I.map (algebraMap S A)=
      (IsLocalRing.maximalIdeal Q).map (algebraMap Q A) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    change (m.map (algebraMap R S)).map (algebraMap S A)=_
    rw [Ideal.map_map,Ideal.map_map]
    congr 1
    ext a
    exact IsScalarTower.algebraMap_apply R Q A a
  letI : IsReduced (A ⧸ I.map (algebraMap S A)) :=
    isReduced_localizationPreserves (Algebra.algebraMapSubmonoid (S ⧸ I) N) _ inferInstance
  change IsReduced (A ⧸ (IsLocalRing.maximalIdeal Q).map (algebraMap Q A))
  rw [← hi]
  infer_instance
end LinearStudy
