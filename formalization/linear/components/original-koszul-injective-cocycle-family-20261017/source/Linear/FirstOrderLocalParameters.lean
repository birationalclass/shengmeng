module
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Noetherian.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy

/-- Nakayama turns actual first-order normal equations into generators of
the maximal ideal modulo the original ideal. -/
theorem firstOrder_normal_equations_and_tangents_generate
    {R α β : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R)
    (v : α ⊕ β → R)
    (hv : Ideal.span (Set.range v) = IsLocalRing.maximalIdeal R)
    (G : β → R) (hG : ∀ i, G i ∈ I)
    (hfirst : ∀ i, G i - v (Sum.inr i) ∈ (IsLocalRing.maximalIdeal R) ^ 2) :
    I ⊔ Ideal.span (Set.range (fun i => v (Sum.inl i))) = IsLocalRing.maximalIdeal R := by
  let m := IsLocalRing.maximalIdeal R
  let J := I ⊔ Ideal.span (Set.range (fun i => v (Sum.inl i)))
  have hJ : J ≤ m := by
    refine sup_le hI (Ideal.span_le.mpr ?_)
    rintro _ ⟨i, rfl⟩
    change v (Sum.inl i) ∈ IsLocalRing.maximalIdeal R
    rw [← hv]
    exact Ideal.mem_span_range_self (x := Sum.inl i)
  have happrox : m ≤ J ⊔ m ^ 2 := by
    change IsLocalRing.maximalIdeal R ≤ J ⊔ m ^ 2
    rw [← hv]
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    cases i with
    | inl i =>
      exact (le_sup_left : J ≤ J ⊔ m ^ 2)
        (Submodule.mem_sup_right (Ideal.mem_span_range_self (x := i)))
    | inr i =>
      have hgi : G i ∈ J := (show I ≤ J from le_sup_left) (hG i)
      have hi : G i ∈ J ⊔ m ^ 2 := (show J ≤ J ⊔ m ^ 2 from le_sup_left) hgi
      have he : G i - v (Sum.inr i) ∈ J ⊔ m ^ 2 :=
        (show m ^ 2 ≤ J ⊔ m ^ 2 from le_sup_right) (hfirst i)
      have hh := (J ⊔ m ^ 2).sub_mem hi he
      simpa only [sub_sub_cancel, SetLike.mem_coe] using hh
  have hn : m ≤ J := by
    apply Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian m)
      (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R))
    simpa only [Ideal.smul_eq_mul, pow_two] using happrox
  exact le_antisymm hJ hn

/-- The actual quotient local ring needs only the tangent coordinates as
parameters once first-order normal equations are known in the source local ring. -/
theorem firstOrder_tangents_generate_quotient_maximalIdeal
    {R α β : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R)
    (v : α ⊕ β → R)
    (hv : Ideal.span (Set.range v) = IsLocalRing.maximalIdeal R)
    (G : β → R) (hG : ∀ i, G i ∈ I)
    (hfirst : ∀ i, G i - v (Sum.inr i) ∈ (IsLocalRing.maximalIdeal R) ^ 2) :
    letI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top hI)
    letI : IsLocalRing (R ⧸ I) := IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
    Ideal.span (Set.range (fun i => Ideal.Quotient.mk I (v (Sum.inl i)))) =
      IsLocalRing.maximalIdeal (R ⧸ I) := by
  let : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top hI)
  let : IsLocalRing (R ⧸ I) := IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective
  have h := congrArg (fun J : Ideal R => J.map (Ideal.Quotient.mk I))
    (firstOrder_normal_equations_and_tangents_generate I hI v hv G hG hfirst)
  rw [Ideal.map_sup, Ideal.map_span, ← Set.range_comp,
    Ideal.map_quotient_self, bot_sup_eq,
    IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective] at h
  exact h
end LinearStudy
