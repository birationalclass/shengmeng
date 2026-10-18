module
public import Mathlib.Algebra.MvPolynomial.Funext
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
universe u v
/-- Intersect two genuinely nonempty polynomial parameter opens. The SAME
product open precedes all quantifiers already inside P and Q. Existing
dependent witnesses in P are retained, rather than rebuilt. -/
theorem parameterPolynomialFamily_intersection
    {R : Type u} [CommRing R] [IsDomain R] [Infinite R] {s : Type v}
    {P Q : (s → R) → Prop}
    (hP : ∃ c : MvPolynomial s R, c ≠ 0 ∧
      (∃ w : s → R, MvPolynomial.eval w c ≠ 0) ∧
      ∀ w : s → R, MvPolynomial.eval w c ≠ 0 → P w)
    (hQ : ∃ c : MvPolynomial s R, c ≠ 0 ∧
      (∃ w : s → R, MvPolynomial.eval w c ≠ 0) ∧
      ∀ w : s → R, MvPolynomial.eval w c ≠ 0 → Q w) :
    ∃ c : MvPolynomial s R, c ≠ 0 ∧
      (∃ w : s → R, MvPolynomial.eval w c ≠ 0) ∧
      ∀ w : s → R, MvPolynomial.eval w c ≠ 0 → P w ∧ Q w := by
  classical
  obtain ⟨cP,hcP,_,hgoodP⟩ := hP
  obtain ⟨cQ,hcQ,_,hgoodQ⟩ := hQ
  have hc : cP*cQ ≠ 0 := mul_ne_zero hcP hcQ
  have hex : ∃ w : s → R, MvPolynomial.eval w (cP*cQ) ≠ 0 := by
    by_contra h
    push Not at h
    apply hc
    apply MvPolynomial.funext
    intro w
    rw [map_zero]
    exact h w
  refine ⟨cP*cQ,hc,hex,?_⟩
  intro w hw
  rw [map_mul] at hw
  obtain ⟨hwP,hwQ⟩ := mul_ne_zero_iff.mp hw
  exact ⟨hgoodP w hwP,hgoodQ w hwQ⟩
end LinearStudy

