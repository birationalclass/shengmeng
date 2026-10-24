module
public import Linear.OriginRegular
public import Linear.PolynomialLocalParameters
public import Linear.LocalFiber
public import Linear.KoszulFunctionResolution
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open RingTheory.Sequence

/-- At a parameter cut in a CM local ambient ring, the actual cut equations
are regular after quotienting by the actual normal equations. This is a
local ambient statement; it imposes no CM assumption on the whole variety. -/
theorem local_cut_regular_of_ambient_parameters
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsCohenMacaulayLocalRing R]
    (normal cut : List R)
    (hgen : Ideal.ofList (normal ++ cut) = IsLocalRing.maximalIdeal R)
    (hlen : (normal ++ cut).length = ringKrullDim R) :
    IsRegular (R ⧸ Ideal.ofList normal) (cut.map (Ideal.Quotient.mk (Ideal.ofList normal))) := by
  have hreg := isRegular_of_maximalIdeal_mem_ofList_minimalPrimes (normal ++ cut)
    (by rw [hgen,Ideal.minimalPrimes_eq_subsingleton_self];exact Set.mem_singleton _) hlen
  have hnormal : Ideal.ofList normal ≤ IsLocalRing.maximalIdeal R := by
    rw [← hgen,Ideal.ofList_append]
    exact le_sup_left
  have hproper : Ideal.ofList normal ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top hnormal
  letI : Nontrivial (R ⧸ Ideal.ofList normal) := Ideal.Quotient.nontrivial_iff.mpr hproper
  letI : IsLocalRing (R ⧸ Ideal.ofList normal) := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  letI : IsLocalHom (Ideal.Quotient.mk (Ideal.ofList normal)) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hw := ((isWeaklyRegular_append_iff' R normal cut).mp hreg.1).2
  let e := (Submodule.quotEquivOfEq _ _ (ideal_smul_top_self (Ideal.ofList normal))).toAddEquiv
  have he : List.Forall₂ (fun (a b : R ⧸ Ideal.ofList normal) => ∀ x,e (a • x)=b • e x)
      (cut.map (Ideal.Quotient.mk (Ideal.ofList normal)))
      (cut.map (Ideal.Quotient.mk (Ideal.ofList normal))) := by
    apply List.forall₂_same.mpr
    intro a ha x
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b,rfl⟩ := Submodule.mkQ_surjective _ x
    rfl
  have hw' := (e.isWeaklyRegular_congr he).mp hw
  apply IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal (R ⧸ Ideal.ofList normal) ?_ hw'
  intro a ha
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  apply map_nonunit (Ideal.Quotient.mk (Ideal.ofList normal)) b
  rw [← hgen]
  exact Ideal.subset_span (List.mem_append_right normal hb)

end LinearStudy
