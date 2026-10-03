module
public import Negativity.ActualRelativeCechKernelScalarVanishing

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
open scoped DirectSum
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem actual_relative_cech_kernel_transition_zero_of_bounded_generators
    {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) [QuasiCompact f]
    (I : Y.IdealSheafData) {ι : Type v} (U : ι → X.affineOpens)
    (hU : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1)) (c : ℕ)
    (hgen : letI := actualRelativeCechForgetKernelDirectSumModule f I U hU
      Submodule.span (⨁ n : ℕ, ↥((I.ideal ⟨⊤, isAffineOpen_top Y⟩) ^ n))
        {x : ⨁ n : ℕ, ↥(actualRelativeCechForgetKernel f I U n) |
          ∃ d : ℕ, d ≤ c ∧ ∃ a : ↥(actualRelativeCechForgetKernel f I U d),
            x = DirectSum.of (fun n : ℕ => ↥(actualRelativeCechForgetKernel f I U n)) d a}
        = ⊤)
    (D t : ℕ) (hD : t + c ≤ D)
    (j : ((I ^ t).comap f).subscheme ⟶ ((I ^ D).comap f).subscheme)
    (hj : j ≫ ((I ^ D).comap f).subschemeι = ((I ^ t).comap f).subschemeι)
    (q : actualClosedCechHOne ((I ^ D).comap f).subschemeι (fun k => (U k).1))
    (hq : actualClosedCechForget ((I ^ D).comap f).subschemeι
      (fun k => (U k).1) q = 0) :
    actualClosedCechHOneTransition j ((I ^ D).comap f).subschemeι
      (fun k => (U k).1) q = 0 := by
  letI := actualRelativeCechHOneGradedModule f I U hU
  letI := actualRelativeCechForgetKernelGradedModule f I U hU
  letI := actualRelativeCechForgetKernelDirectSumModule f I U hU
  let M := fun n : ℕ => ↥(actualRelativeCechForgetKernel f I U n)
  let T : M D →+ actualClosedCechHOne (j ≫ ((I ^ D).comap f).subschemeι)
      (fun k => (U k).1) :=
    (actualClosedCechHOneTransition j ((I ^ D).comap f).subschemeι
      (fun k => (U k).1)).comp (actualRelativeCechForgetKernel f I U D).subtype
  have hT : ∀ a : M D, T a = 0 := by
    apply actual_graded_component_vanishing_of_bounded_generators c D T hgen
    intro i d r a hd
    by_cases he : i + d = D
    · subst D
      rw [DirectSum.of_eq_same]
      change actualClosedCechHOneTransition j ((I ^ (i + d)).comap f).subschemeι
        (fun k => (U k).1) (actualRelativeCechGradedHOne f I U hU i d r.1 r.2 a.1) = 0
      exact actual_relative_cech_kernel_scalar_transition_zero f I U hU i d t
        (by omega) r.1 r.2 a.1 a.2 j hj
    · have hz (b : M (i + d)) : (DirectSum.of M (i + d) b) D = 0 := by
        simp only [DirectSum.of_apply, he, ↓reduceDIte]
      rw [hz, map_zero]
  exact hT ⟨q, hq⟩

/-- Once the genuine summed H¹ is finite over the actual polynomial Rees
algebra, the actual cohomology kernel transitions vanish with one uniform
shift. The shift is derived from finite generation, not supplied as an input. -/
theorem actual_relative_cech_kernel_vanishing_of_hone_finite
    {X Y : Scheme.{u}} [IsAffine Y] [IsNoetherianRing Γ(Y, ⊤)]
    (f : X ⟶ Y) [QuasiCompact f] (I : Y.IdealSheafData)
    {ι : Type v} (U : ι → X.affineOpens)
    (hU : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1))
    (hfinite : letI := actualRelativeCechHOnePolynomialReesModule f I U hU
      Module.Finite (reesAlgebra (I.ideal ⟨⊤, isAffineOpen_top Y⟩))
        (⨁ n : ℕ, actualClosedCechHOne ((I ^ n).comap f).subschemeι
          (fun j => (U j).1))) :
    ∃ c : ℕ, ActualRelativeCechKernelVanishing f I U c := by
  letI := actualRelativeCechForgetKernelGradedModule f I U hU
  letI := actualRelativeCechForgetKernelDirectSumModule f I U hU
  letI : Module.Finite (⨁ n : ℕ, ↥((I.ideal ⟨⊤, isAffineOpen_top Y⟩) ^ n))
      (⨁ n : ℕ, ↥(actualRelativeCechForgetKernel f I U n)) :=
    actual_relative_cech_forget_kernel_finite_of_hone_finite f I U hU hfinite
  obtain ⟨c, hc⟩ := actual_finite_graded_module_generator_bound
    (R := ⨁ n : ℕ, ↥((I.ideal ⟨⊤, isAffineOpen_top Y⟩) ^ n))
    (M := fun n : ℕ => ↥(actualRelativeCechForgetKernel f I U n))
  refine ⟨c, ?_⟩
  intro n q hq
  apply actual_relative_cech_kernel_transition_zero_of_bounded_generators
    f I U hU c hc (n + c + 1) (n + 1) (by omega)
      (actualRelativePowerInclusion f I (Nat.le_add_right n c)) ?_ q hq
  exact IdealSheafData.inclusion_subschemeι _

#print axioms actual_relative_cech_kernel_transition_zero_of_bounded_generators
#print axioms actual_relative_cech_kernel_vanishing_of_hone_finite
end
end Negativity
