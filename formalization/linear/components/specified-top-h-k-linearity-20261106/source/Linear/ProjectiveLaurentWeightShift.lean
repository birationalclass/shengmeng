module
public import Linear.ProjectiveLaurentNoninitialRestriction
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
open AlgebraicGeometry
universe u
variable {σ : Type} {d l : ℤ}

/-- Addition of a nonnegative homogeneous exponent preserves allowance on
every coordinate intersection. -/
def homogeneousLaurentAllowedShift {n : ℕ} (a : Fin (n+1) → σ)
    (b : HomogeneousLaurentExponent σ l) (hb : ∀ i, 0 ≤ b.1 i) :
    {e : HomogeneousLaurentExponent σ d // e.IsAllowedOn a} →
      {e : HomogeneousLaurentExponent σ (d+l) // e.IsAllowedOn a} :=
  fun e => ⟨⟨e.1.1+b.1, by rw [map_add, e.1.property, b.property]⟩, by
    intro i hi
    apply e.2
    change e.1.1 i < 0
    change (e.1.1+b.1) i < 0 at hi
    simp only [Finsupp.add_apply] at hi
    have := hb i
    omega⟩

/-- Exponent shift commutes with every coface, including the initial one. -/
theorem homogeneousLaurentAllowedShift_delete [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n+1))
    (k : Fin (n+2)) (b : HomogeneousLaurentExponent σ l) (hb : ∀ i, 0 ≤ b.1 i)
    (e : {e : HomogeneousLaurentExponent σ d //
      e.IsAllowedOn (fun j => ((a.delete k).1 j).down)}) :
    coordinateLaurentExponentDeleteEmbedding a k (d+l)
      (homogeneousLaurentAllowedShift _ b hb e) =
    homogeneousLaurentAllowedShift _ b hb
      (coordinateLaurentExponentDeleteEmbedding a k d e) := by
  rfl
end MvPolynomial
