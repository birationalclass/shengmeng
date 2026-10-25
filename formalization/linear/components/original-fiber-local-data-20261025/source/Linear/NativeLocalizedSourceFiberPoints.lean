module
public import Linear.NativeLocalizedSourcePoint
public import Linear.FiniteReducedFiberLocalFree
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
/-- EVERY actual maximal source point after base localization contracts
to the SAME original base point;the fiber condition is derived. -/
theorem nativeLocalizedSourcePoint_base_comap
    (m : Ideal R) [m.IsPrime]
    (p : Ideal (LocalizedModule m.primeCompl S)) [p.IsMaximal] :
    (p.comap (LocalizedModule.numeratorRingHom (S:=m.primeCompl) (A:=S))).comap
      (algebraMap R S)=m := by
  let Q := Localization.AtPrime m
  let A := LocalizedModule m.primeCompl S
  letI : Module Q A := LocalizedModule.moduleOfIsLocalization
  letI : Algebra Q A := LocalizedModule.algebraOfIsLocalization (S:=m.primeCompl) Q
  letI : Module.Finite Q A := Module.Finite.of_isLocalizedModule m.primeCompl
    (Rₚ:=Q) (LocalizedModule.mkLinearMap m.primeCompl S)
  have hc : p.comap (algebraMap Q A)=IsLocalRing.maximalIdeal Q :=
    IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R:=Q) (S:=A) p)
  have ht : (LocalizedModule.numeratorRingHom (S:=m.primeCompl) (A:=S)).comp
      (algebraMap R S)=(algebraMap Q A).comp (algebraMap R Q) := by
    ext a
    exact IsScalarTower.algebraMap_apply R Q A a
  rw [Ideal.comap_comap,ht,← Ideal.comap_comap,hc]
  exact Localization.AtPrime.under_maximalIdeal
/-- If the ORIGINAL base point is maximal,EVERY actual maximal point of
the localized finite source is an ORIGINAL maximal source point. -/
theorem nativeLocalizedSourcePoint_original_maximal
    (m : Ideal R) [m.IsMaximal]
    (p : Ideal (LocalizedModule m.primeCompl S)) [p.IsMaximal] :
    (p.comap (LocalizedModule.numeratorRingHom (S:=m.primeCompl) (A:=S))).IsMaximal := by
  let q := p.comap (LocalizedModule.numeratorRingHom (S:=m.primeCompl) (A:=S))
  apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R:=R) (S:=S) q
  change (q.comap (algebraMap R S)).IsMaximal
  rw [nativeLocalizedSourcePoint_base_comap m p]
  infer_instance
end LinearStudy
