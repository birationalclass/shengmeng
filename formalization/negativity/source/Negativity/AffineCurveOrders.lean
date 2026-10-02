module

public import Negativity.CurveFunctionField
public import Negativity.NormalSections
public import Negativity.DvrAdicOrders
public import Negativity.ValuationOrderTransport
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory IsDedekindDomain TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false

/-- Actual coordinate rings of nonempty normal curve charts are Dedekind. -/
theorem normal_curve_affine_dedekind (C : Scheme.{u}) [IsIntegral C]
    [IsLocallyNoetherian C]
    (hn : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (hd : Order.krullDim C ≤ 1) (U : C.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    IsDedekindDomain Γ(C, U) := by
  have : IsNoetherianRing Γ(C, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : IsIntegrallyClosed Γ(C, U) := normal_affine_sections C hn U hU
  have : Ring.KrullDimLE 1 Γ(C, U) := curve_affine_chart_dimension C hd U hU
  have : Ring.DimensionLEOne Γ(C, U) := ⟨fun hp hprime => hprime.isMaximal_of_ne_bot hp⟩
  exact { (inferInstance : IsDomain Γ(C, U)),
    (inferInstance : IsNoetherianRing Γ(C, U)),
    (inferInstance : Ring.DimensionLEOne Γ(C, U)),
    (inferInstance : IsIntegrallyClosed Γ(C, U)) with }

theorem curve_affine_prime_coheight (C : Scheme.{u}) [IsIntegral C]
    (U : C.Opens) (hU : IsAffineOpen U) [IsDedekindDomain Γ(C, U)]
    (p : HeightOneSpectrum Γ(C, U)) :
    Order.coheight (hU.fromSpec ⟨p.asIdeal, inferInstance⟩) = 1 := by
  rw [coheight_eq_of_isOpenImmersion, ← idealHeight_eq_coheight]
  apply le_antisymm
  · have hle := Ideal.height_le_ringKrullDim_of_ne_top p.isPrime.ne_top
    exact WithBot.coe_le_coe.mp (hle.trans (Ring.krullDimLE_iff.mp inferInstance))
  · exact Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr p.ne_bot)

/-- Final theorem: the normalized coordinate-ring order at an actual
affine chart prime equals the actual curve-stalk order at that prime's
geometric point, including poles. The stalk and adic valuation ring are
identified as actual localizations, and their fraction-field maps are
proved compatible; neither an order equality nor an arbitrary weight is
supplied as an input. -/
theorem normal_curve_affine_prime_order
    (C : Scheme.{u}) [IsIntegral C] [IsLocallyNoetherian C]
    (hn : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (U : C.Opens) (hU : IsAffineOpen U) [Nonempty U]
    [IsDedekindDomain Γ(C, U)]
    (p : HeightOneSpectrum Γ(C, U)) (a : C.functionFieldˣ) :
    letI := functionField_isFractionRing_of_isAffineOpen C U hU
    heightOneOrder C.functionField p a =
      schemeRationalOrder C hn (hU.fromSpec ⟨p.asIdeal, inferInstance⟩)
        (curve_affine_prime_coheight C U hU p) a := by
  have := functionField_isFractionRing_of_isAffineOpen C U hU
  let x := hU.fromSpec ⟨p.asIdeal, inferInstance⟩
  have hxU : x ∈ U := (hU.isoSpec.inv ⟨p.asIdeal, inferInstance⟩).2
  let T := C.presheaf.stalk x
  let V := p.valuationSubringAtPrime C.functionField
  let : Algebra Γ(C, U) T := C.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have : IsLocalization.AtPrime T p.asIdeal := hU.isLocalization_stalk' _ hxU
  have : IsScalarTower Γ(C, U) T C.functionField :=
    functionField_isScalarTower C U ⟨x, hxU⟩
  have := hn x
  have hx : Order.coheight x = 1 := curve_affine_prime_coheight C U hU p
  have : IsDiscreteValuationRing T := normal_codimensionOne_stalk_isDVR C x hx
  have hV : V = (p.valuation C.functionField).valuationSubring :=
    p.valuationSubringAtPrime_eq_valuationSubring
  have : IsDiscreteValuationRing V := by rw [hV]; infer_instance
  let e : T ≃ₐ[Γ(C, U)] V := IsLocalization.algEquiv p.asIdeal.primeCompl T V
  have he : (algebraMap V C.functionField).comp e.toRingHom =
      algebraMap T C.functionField := by
    apply IsLocalization.ringHom_ext p.asIdeal.primeCompl
    ext r
    change algebraMap V C.functionField (e (algebraMap Γ(C, U) T r)) =
      algebraMap T C.functionField (algebraMap Γ(C, U) T r)
    rw [e.commutes, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have ho := dvr_rationalOrder_commonField_ringEquiv e.toRingEquiv he a
  change heightOneOrder C.functionField p a = DvrRationalOrder T C.functionField a
  rw [← ho]
  have hv := dedekind_prime_order_eq_valuationRing_order Γ(C, U) C.functionField p a
  let e' : V ≃+* (p.valuation C.functionField).valuationSubring :=
    RingEquiv.ofBijective (ValuationSubring.inclusion V (p.valuation C.functionField).valuationSubring hV.le) ⟨
      fun v w h => Subtype.ext (congrArg
        (fun z : (p.valuation C.functionField).valuationSubring => (z : C.functionField)) h),
      fun w => ⟨⟨w, hV.symm ▸ w.2⟩, rfl⟩⟩
  exact hv.trans (dvr_rationalOrder_commonField_ringEquiv e' rfl a)

end Negativity


