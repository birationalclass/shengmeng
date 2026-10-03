module

public import Negativity.RelativeKernelWeighted
public import Negativity.ReesFractionField
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace Polynomial
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem integral_of_all_valuation_subrings
    (A F : Type*) [CommRing A] [Field F] [Algebra A F] (x : F)
    (hx : ∀ V : ValuationSubring F,
      (∀ a : A, algebraMap A F a ∈ V) → x ∈ V) : IsIntegral A x := by
  by_contra hn
  have hn' : x ∉ (integralClosure A F).toSubring := hn
  obtain ⟨V, hV, hxV⟩ :=
    Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hn'
  exact hxV (hx V fun a => hV ((integralClosure A F).algebraMap_mem a))

/-- Final theorem: every actual kernel coefficient r, placed in its
homogeneous degree n, is integral over the actual base-ideal Rees
algebra. Proper birational lifts supply membership in every valuation
subring; mathlib's intersection-of-valuation-rings criterion then proves
integrality. No graded finite-generation or uniform bound is assumed. -/
theorem actual_relative_kernel_monomial_integral
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsAffine Y]
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    (I : Y.IdealSheafData) (n : ℕ)
    (r : Γ(Y, ⊤)) (hr : r ∈ actualRelativeKernelIdeal f I n) :
    IsIntegral (reesAlgebra (I.ideal ⟨⊤, isAffineOpen_top Y⟩))
      (algebraMap (Polynomial Γ(Y, ⊤)) (FractionRing (Polynomial Γ(Y, ⊤)))
        (monomial n r)) := by
  let R := Γ(Y, ⊤)
  let J := I.ideal ⟨⊤, isAffineOpen_top Y⟩
  let F := FractionRing (Polynomial R)
  let ρ := algebraMap (Polynomial R) F
  let φ : R →+* F := ρ.comp Polynomial.C
  apply integral_of_all_valuation_subrings (reesAlgebra J) F
  intro V hV
  have hφ (s : R) : φ s ∈ V :=
    hV ⟨Polynomial.C s, (reesAlgebra J).algebraMap_mem s⟩
  let g : R →+* V := {
    toFun s := ⟨φ s, hφ s⟩
    map_zero' := Subtype.ext (map_zero φ)
    map_one' := Subtype.ext (map_one φ)
    map_add' s t := Subtype.ext (map_add φ s t)
    map_mul' s t := Subtype.ext (map_mul φ s t) }
  have hg : Function.Injective g := by
    intro s t hst
    exact ((IsFractionRing.injective (Polynomial R) F).comp Polynomial.C_injective)
      (congrArg Subtype.val hst)
  have hJ (s : R) (hs : s ∈ J) : (g s : F) * ρ Polynomial.X ∈ V := by
    change ρ (Polynomial.C s) * ρ Polynomial.X ∈ V
    have hm := hV ⟨monomial 1 s, reesAlgebra.monomial_mem.mpr (by simpa using hs)⟩
    change ρ (monomial 1 s) ∈ V at hm
    simpa only [← C_mul_X_pow_eq_monomial, pow_one, map_mul] using hm
  have hw := actual_relative_kernel_weighted_valuation_mem f hf I n F V g hg
    (ρ Polynomial.X) hJ r hr
  change ρ (Polynomial.C r) * (ρ Polynomial.X) ^ n ∈ V at hw
  simpa only [← C_mul_X_pow_eq_monomial, map_mul, map_pow] using hw

end
end Negativity
