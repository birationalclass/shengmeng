module

public import Negativity.RelativeKernelIntegral
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace Polynomial
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem: the actual kernel filtration has a finite graded Rees
module over a nonzero base ideal on an affine finite-type variety over a
perfect field. Its polynomials embed into the proved finite integral
closure of the Rees algebra; actual proper valuative lifts prove every
coefficient's homogeneous integrality. No finite-generation input is used. -/
theorem actual_relative_kernel_rees_module_finite
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsAffine Y]
    (k : Type u) [Field k] [PerfectField k]
    [Algebra k Γ(Y, ⊤)] [Algebra.FiniteType k Γ(Y, ⊤)]
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    (I : Y.IdealSheafData) (hI : I.ideal ⟨⊤, isAffineOpen_top Y⟩ ≠ ⊥) :
    Module.Finite (reesAlgebra (I.ideal ⟨⊤, isAffineOpen_top Y⟩))
      (actualRelativeKernelFiltration f I).submodule := by
  let R := Γ(Y, ⊤)
  let J := I.ideal ⟨⊤, isAffineOpen_top Y⟩
  let A := reesAlgebra J
  let F := FractionRing (Polynomial R)
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  have : Algebra.FiniteType k A := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType k R) (inferInstance : Algebra.FiniteType R A)
  have : IsFractionRing A F := rees_algebra_polynomial_fraction_field J hI
  have : Module.Finite A (integralClosure A F) :=
    finiteType_perfectField_integralClosure_finite k A F F
  let N := (actualRelativeKernelFiltration f I).submodule
  let e := (PolynomialModule.equivPolynomialSelf (R := R)).restrictScalars A
  let l : N →ₗ[A] F := ((Algebra.linearMap (Polynomial R) F).restrictScalars A).comp
    (e.toLinearMap.comp N.subtype)
  have hl (p : N) : l p ∈ (integralClosure A F).toSubmodule := by
    let q := e p.1
    change IsIntegral A (algebraMap (Polynomial R) F q)
    rw [q.as_sum_support, map_sum]
    apply IsIntegral.sum
    intro n _hn
    have hp : q.coeff n ∈ actualRelativeKernelIdeal f I n := by
      change p.1.coeff n ∈ (actualRelativeKernelFiltration f I).N n
      exact p.property n
    exact actual_relative_kernel_monomial_integral f hf I n (q.coeff n) hp
  let lc := l.codRestrict (integralClosure A F).toSubmodule hl
  apply Module.Finite.of_injective lc
  intro p q hpq
  apply Subtype.ext
  apply e.injective
  apply IsFractionRing.injective (Polynomial R) F
  exact congrArg Subtype.val hpq

end
end Negativity
