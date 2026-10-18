module
public import Linear.Primitive
public import Linear.ParameterQuotient
/-!
# Changing the parameter-base action on an annihilator

Two actual algebra structures and compatible reduction maps induce the same
annihilator action through an explicit reduced-base equivalence. An element
that scalar-generates the old annihilator has unit functional coefficient for
any perfect pairing over the new base, and survives every proper extended
new-base parameter ideal. The new algebra action and its perfect pairing are
explicit inputs: constructing them from arbitrary parameter lifts remains an
unfinished power-series/finite-flat obligation. No claim of the full relative
Jacobian lemma is made here.
-/
@[expose] public section
namespace LinearStudy
variable {B C A : Type*} [CommRing B] [CommRing C] [CommRing A]
  [Algebra B A] [Algebra C A]

theorem annihilator_scalar_action_baseChange
    (q : A →ₐ[B] B) (q' : A →ₐ[C] C) (e : B ≃+* C)
    (hq' : RingHom.ker q'.toRingHom = nilradical A)
    (he : ∀ a, q' a = e (q a))
    {delta : A} (hd : Annihilates (nilradical A) delta) (b : B) :
    b • delta = e b • delta := by
  have hq'zero : ∀ a, q' a = 0 ↔ a ∈ nilradical A := by
    intro a
    change a ∈ RingHom.ker q'.toRingHom ↔ _
    rw [hq']
  rw [Algebra.smul_def (R := B)]
  rw [multiplication_factors_through_reduction q' hq'zero hd]
  rw [he, q.commutes]
  exact (Algebra.smul_def (R := C) _ _).symm

theorem annihilator_generator_coefficient_unit_after_baseChange
    (q : A →ₐ[B] B) (q' : A →ₐ[C] C) (e : B ≃+* C)
    (hq' : RingHom.ker q'.toRingHom = nilradical A)
    (he : ∀ a, q' a = e (q a))
    (delta : A) (hd : Annihilates (nilradical A) delta)
    (hgen : ∀ x : A, Annihilates (nilradical A) x → ∃ b : B, x = b • delta)
    (p' : PerfectMultiplicationPairing (B := C) (A := A)) :
    IsUnit (p'.functional delta) := by
  have hdual : Annihilates (nilradical A) (dualGenerator q' p') := by
    rw [← hq']
    exact dualGenerator_annihilates q' p'
  obtain ⟨b, hb⟩ := hgen _ hdual
  rw [annihilator_scalar_action_baseChange q q' e hq' he hd b] at hb
  have h := dualGenerator_functional q' p'
  rw [hb, map_smul, smul_eq_mul] at h
  exact ⟨⟨p'.functional delta, e b, by simpa only [mul_comm] using h, h⟩, rfl⟩

theorem annihilator_generator_survives_new_parameterIdeal
    (q : A →ₐ[B] B) (q' : A →ₐ[C] C) (e : B ≃+* C)
    (hq' : RingHom.ker q'.toRingHom = nilradical A)
    (he : ∀ a, q' a = e (q a))
    (delta : A) (hd : Annihilates (nilradical A) delta)
    (hgen : ∀ x : A, Annihilates (nilradical A) x → ∃ b : B, x = b • delta)
    (p' : PerfectMultiplicationPairing (B := C) (A := A))
    {ι : Type*} (T : ι → C) (m : Ideal C) (hm : m ≠ ⊤) (hT : ∀ i, T i ∈ m) :
    Ideal.Quotient.mk (Ideal.span (Set.range (fun i => algebraMap C A (T i)))) delta ≠ 0 := by
  have hu := annihilator_generator_coefficient_unit_after_baseChange
    q q' e hq' he delta hd hgen p'
  intro hz
  have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hz
  have hmap : ∀ x ∈ Ideal.span (Set.range (fun i => algebraMap C A (T i))),
      ∀ a : A, p'.functional (a * x) ∈ m := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      intro a
      have hscalar : p'.functional (a * algebraMap C A (T i)) = T i * p'.functional a := by
        have h := p'.functional.map_smul (T i) a
        simpa only [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply,
          mul_comm a, smul_eq_mul] using h
      rw [hscalar]
      exact Ideal.mul_mem_right _ _ (hT i)
    | zero => intro a; simp
    | add y z hy hz hfy hfz =>
      intro a
      simpa only [mul_add, map_add] using m.add_mem (hfy a) (hfz a)
    | smul a y hy hfy =>
      intro b
      simpa only [smul_eq_mul, mul_assoc] using hfy (b * a)
  have hvalue : p'.functional delta ∈ m := by simpa using hmap _ hmem 1
  exact hm (Ideal.eq_top_of_isUnit_mem _ hvalue hu)
end LinearStudy
