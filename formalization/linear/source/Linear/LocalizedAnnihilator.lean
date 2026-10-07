module
public import Linear.PointDecomposition
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.Tactic
/-! Finite-generated ideal annihilators commute with actual localization. Local nilradical-socle generators give a global generator by maximal localization. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {R : Type*} [CommRing R] (M : Submonoid R)
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization M S]
include M

theorem localization_map_principal_annihilator (x : R) :
    ((Ideal.span {x}).annihilator).map (algebraMap R S) =
      (Ideal.span {algebraMap R S x}).annihilator := by
  ext z
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq M z
  rw [IsLocalization.mk'_mem_map_algebraMap_iff M S,
    IsLocalization.mk'_mem_iff]
  simp only [Submodule.mem_annihilator_span_singleton, smul_eq_mul]
  change (∃ m ∈ M, (m * r) * x = 0) ↔ algebraMap R S r * algebraMap R S x = 0
  rw [← map_mul, IsLocalization.map_eq_zero_iff M S]
  constructor
  · rintro ⟨m, hm, hz⟩
    exact ⟨⟨m, hm⟩, by simpa only [mul_assoc] using hz⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, m.property, by simpa only [mul_assoc] using hm⟩

theorem localization_map_finite_span_annihilator (s : Finset R) :
    ((Ideal.span (s : Set R)).annihilator).map (algebraMap R S) =
      ((Ideal.span (s : Set R)).map (algebraMap R S)).annihilator := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Submodule.annihilator_bot, Ideal.map_top]
  | @insert x s hx ih =>
    rw [Finset.coe_insert, ← Set.singleton_union, Ideal.span_union,
      Submodule.annihilator_sup, IsLocalization.map_inf M S,
      Ideal.map_sup, Submodule.annihilator_sup, ih]
    congr 1
    rw [Ideal.map_span, Set.image_singleton]
    exact localization_map_principal_annihilator M S x

theorem localization_map_annihilator_of_fg (I : Ideal R) (hI : I.FG) :
    I.annihilator.map (algebraMap R S) = (I.map (algebraMap R S)).annihilator := by
  obtain ⟨s, hs⟩ := hI
  rw [← hs]
  exact localization_map_finite_span_annihilator M S s

omit M S in
theorem nilradical_annihilator_generator_of_localizations [IsNoetherianRing R]
    (theta : R)
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      (nilradical (Localization.AtPrime P)).annihilator =
        Ideal.span {algebraMap R (Localization.AtPrime P) theta}) :
    (nilradical R).annihilator = Ideal.span {theta} := by
  apply Ideal.eq_of_localization_maximal
  intro P hP
  let S := Localization.AtPrime P
  rw [localization_map_annihilator_of_fg P.primeCompl S (nilradical R)
    (nilradical R).fg_of_isNoetherianRing, Ideal.map_span, Set.image_singleton]
  have hn : (nilradical R).map (algebraMap R S) = nilradical S := by
    change (⊥ : Ideal R).radical.map (algebraMap R S) = (⊥ : Ideal S).radical
    simpa only [Ideal.map_bot] using
      IsLocalization.map_radical P.primeCompl S (⊥ : Ideal R)
  rw [hn]
  exact h P

end LinearStudy
