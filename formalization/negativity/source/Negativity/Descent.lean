module

public import Negativity.Interfaces
import Mathlib.Tactic

@[expose] public section
namespace Negativity

/-- Coefficient pushforward respects composition of strict transforms. -/
theorem push_comp {I J K : Type*} (s : J → I) (t : K → J)
    (hs : Function.Injective s) (ht : Function.Injective t) (d : I →₀ ℝ) :
    birationalPush t ht (birationalPush s hs d) =
      birationalPush (s ∘ t) (hs.comp ht) d := by
  ext k
  rfl

/-- Zero pushforward is exactly support on exceptional indices. -/
theorem push_zero_iff_exceptional_support {I J : Type*} (s : J → I)
    (hs : Function.Injective s) (d : I →₀ ℝ) :
    birationalPush s hs d = 0 ↔ ∀ i, d i ≠ 0 → ExceptionalIndex s i := by
  constructor
  · intro h i hi
    rintro ⟨j, rfl⟩
    have hj := congrArg (fun z : J →₀ ℝ => z j) h
    exact hi (by simpa using hj)
  · intro h
    ext j
    by_contra hn
    have hd : d (s j) ≠ 0 := by simpa using hn
    exact h (s j) hd ⟨j, rfl⟩

/-- If a vector and its negative are effective, all coefficients vanish. -/
theorem effective_both_signs_iff_zero {I : Type*} (d : I →₀ ℝ) :
    Effective d ∧ Effective (-d) ↔ d = 0 := by
  constructor
  · rintro ⟨hp, hn⟩
    ext i
    have hpi := hp i
    have hni := hn i
    simp only [Finsupp.neg_apply] at hni
    simpa using (le_antisymm (by linarith : d i ≤ 0) hpi)
  · rintro rfl
    constructor <;> intro i <;> simp

/-- Nonnegative scalar multiples preserve the nonpositive curve-degree condition. -/
theorem nonpositive_smul {V C : Type*} [AddCommGroup V] [Module ℝ V]
    (degree : C → V →ₗ[ℝ] ℝ) (D : V) (a : ℝ) (ha : 0 ≤ a)
    (hD : ∀ c, degree c D ≤ 0) : ∀ c, degree c (a • D) ≤ 0 := by
  intro c
  simpa using mul_nonpos_of_nonneg_of_nonpos ha (hD c)

/-- Projection-formula transport, allowing curves contracted by the modification
itself to have degree zero instead of requiring a nonexistent image curve. -/
theorem nonpositive_pullback {V W C C' : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (pull : V →ₗ[ℝ] W) (degree : C → V →ₗ[ℝ] ℝ)
    (degree' : C' → W →ₗ[ℝ] ℝ) (D : V)
    (hD : ∀ c, degree c D ≤ 0)
    (hprojection : ∀ c', degree' c' (pull D) = 0 ∨
      ∃ c r, 0 ≤ r ∧ degree' c' (pull D) = r * degree c D) :
    ∀ c', degree' c' (pull D) ≤ 0 := by
  intro c'
  rcases hprojection c' with hzero | ⟨c, r, hr, h⟩
  · exact le_of_eq hzero
  · rw [h]
    exact mul_nonpos_of_nonneg_of_nonpos hr (hD c)

/-- Effective pullback descends when pushforward preserves effectivity and is
left inverse to pullback. These map properties remain geometric inputs. -/
theorem effective_descends {V W : Type*} (eff : V → Prop) (eff' : W → Prop)
    (pull : V → W) (push : W → V) (D : V)
    (hleft : push (pull D) = D)
    (hpush : ∀ B, eff' B → eff (push B)) (hD : eff' (pull D)) : eff D := by
  simpa only [hleft] using hpush (pull D) hD

/-- The logical proper-to-projective reduction, with all projection and
modification hypotheses explicit. No Chow existence theorem is asserted. -/
theorem negativity_descends {V W Z : Type*}
    (eff : V → Prop) (eff' : W → Prop) (effBase : Z → Prop)
    (nef : V → Prop) (nef' : W → Prop)
    (pull : V → W) (push : W → V) (fpush : V → Z) (gpush : W → Z)
    (hleft : ∀ D, push (pull D) = D)
    (hpush : ∀ B, eff' B → eff (push B))
    (hbase : ∀ D, eff D → effBase (fpush D))
    (hcommute : ∀ D, gpush (pull D) = fpush D)
    (hnefpull : ∀ D, nef D → nef' (pull D))
    (hprojective : ∀ B, nef' B → effBase (gpush B) → eff' B)
    (D : V) (hD : nef D) : eff D ↔ effBase (fpush D) := by
  constructor
  · exact hbase D
  · intro h
    apply effective_descends eff eff' pull push D (hleft D) hpush
    apply hprojective (pull D) (hnefpull D hD)
    simpa only [hcommute D] using h

/-- Surjectivity is sufficient to descend subset relations of preimages. -/
theorem subset_iff_preimage_subset {X X' : Type*} (p : X' → X)
    (hp : Function.Surjective p) (A B : Set X) :
    A ⊆ B ↔ p ⁻¹' A ⊆ p ⁻¹' B := by
  constructor
  · intro h x hx
    exact h hx
  · intro h x hx
    obtain ⟨x', rfl⟩ := hp x
    exact h hx

/-- A fiber meets a support downstairs iff their preimages meet upstairs. -/
theorem disjoint_iff_preimage_disjoint {X X' : Type*} (p : X' → X)
    (hp : Function.Surjective p) (A B : Set X) :
    Disjoint A B ↔ Disjoint (p ⁻¹' A) (p ⁻¹' B) := by
  simp only [Set.disjoint_left]
  constructor
  · intro h x hx hy
    exact h hx hy
  · intro h x hx hy
    obtain ⟨x', rfl⟩ := hp x
    exact h hx hy

/-- Support dichotomy descends through any surjective map with exact support
pullback. This is a fully proved set-theoretic step, not a geometry assumption. -/
theorem support_dichotomy_descends {X X' : Type*} (p : X' → X)
    (hp : Function.Surjective p) (fiber supp : Set X)
    (h : Disjoint (p ⁻¹' fiber) (p ⁻¹' supp) ∨ p ⁻¹' fiber ⊆ p ⁻¹' supp) :
    Disjoint fiber supp ∨ fiber ⊆ supp := by
  rcases h with h | h
  · exact Or.inl ((disjoint_iff_preimage_disjoint p hp fiber supp).mpr h)
  · exact Or.inr ((subset_iff_preimage_subset p hp fiber supp).mpr h)

/-- The fiber of a composite is exactly the preimage of a fiber. -/
theorem composite_fiber {X X' Y : Type*} (p : X' → X) (f : X → Y) (y : Y) :
    {x' | f (p x') = y} = p ⁻¹' {x | f x = y} := rfl

/-- If every fiber upstairs satisfies the support alternative, so does every
fiber downstairs, provided p is surjective and the support is its preimage. -/
theorem fiber_dichotomy_descends {X X' Y : Type*}
    (p : X' → X) (hp : Function.Surjective p) (f : X → Y) (supp : Set X)
    (h : ∀ y, Disjoint {x' | f (p x') = y} (p ⁻¹' supp) ∨
      {x' | f (p x') = y} ⊆ p ⁻¹' supp) :
    ∀ y, Disjoint {x | f x = y} supp ∨ {x | f x = y} ⊆ supp := by
  intro y
  exact support_dichotomy_descends p hp _ supp (h y)


/-- Inserting coefficients at their strict transforms is a section of pushforward.
This is a coefficient-model identity, not the geometric Cartier pullback. -/
theorem push_embDomain {I J : Type*} (s : J → I)
    (hs : Function.Injective s) (d : J →₀ ℝ) :
    birationalPush s hs (Finsupp.embDomain ⟨s, hs⟩ d) = d := by
  ext j
  exact Finsupp.embDomain_apply_self ⟨s, hs⟩ d j

/-- Adding exceptional coefficients does not change pushforward. -/
theorem push_add_exceptional {I J : Type*} (s : J → I)
    (hs : Function.Injective s) (d e : I →₀ ℝ)
    (he : ∀ i, e i ≠ 0 → ExceptionalIndex s i) :
    birationalPush s hs (d + e) = birationalPush s hs d := by
  have hz := (push_zero_iff_exceptional_support s hs e).mpr he
  ext j
  have hj := congrArg (fun z : J →₀ ℝ => z j) hz
  simpa [birationalPush] using hj

/-- Effectivity descends in the coefficient model without assuming separately
that pushforward preserves effectivity; that property is already proved. -/
theorem effective_descends_coefficients {I J : Type*} (s : J → I)
    (hs : Function.Injective s) (d : J →₀ ℝ) (lifted : I →₀ ℝ)
    (hleft : birationalPush s hs lifted = d) (h : Effective lifted) :
    Effective d := by
  simpa only [hleft] using effective_push s hs h

end Negativity
