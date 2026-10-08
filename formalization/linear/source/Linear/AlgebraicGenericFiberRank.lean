module
public import Linear.AlgebraicFiniteTypeAway
public import Linear.GenericFiberRankOpen
public import Linear.LocalizedAlgebraFiber
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace LinearStudy
universe u

/-- The ACTUAL fibers of a finite-type algebraic map over a Noetherian
domain have its generic rank on a constructed nonempty target open.
Neither module finiteness nor freeness is assumed for the original map. -/
theorem algebraic_finiteType_exists_generic_rank_fibers
    {R A : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing A] [Algebra R A] [Algebra.FiniteType R A] [Algebra.IsAlgebraic R A]
    {K : Type*} [Field K] :
    ∃ p : R, p ≠ 0 ∧ ∀ ρ : R →+* K, ρ p ≠ 0 →
      (letI : Algebra R K := ρ.toAlgebra
       Module.finrank K (K ⊗[R] A) = Module.finrank R A) := by
  obtain ⟨b, hb, hfinite⟩ := algebraic_finiteType_exists_finite_away (R := R) (S := A)
  let Rb := Localization.Away b
  let Ab := Localization.Away (algebraMap R A b)
  let ψ := Localization.awayMapₐ (Algebra.ofId R A) b
  letI : Algebra Rb Ab := ψ.toRingHom.toAlgebra
  letI : SMul Rb Ab := ψ.toRingHom.toAlgebra.toSMul
  letI : Module Rb Ab := Algebra.toModule
  letI : IsDomain Rb := Localization.Away.isDomain hb
  letI : Module.Finite Rb Ab := hfinite
  obtain ⟨c, hc, hfree, _⟩ := finiteModule_exists_free_away (R := Rb) (M := Ab)
  let a := (IsLocalization.Away.sec b c).1
  let k := (IsLocalization.Away.sec b c).2
  have hsec : c * algebraMap R Rb (b ^ k) = algebraMap R Rb a :=
    IsLocalization.Away.sec_spec b c
  have ha : a ≠ 0 := by
    intro ha0
    have hc0 : c * algebraMap R Rb (b ^ k) = 0 := by rw [hsec, ha0, map_zero]
    exact (mul_ne_zero hc (IsLocalization.Away.algebraMap_pow_isUnit b k).ne_zero)
      (by simpa only [map_pow] using hc0)
  refine ⟨b * a, mul_ne_zero hb ha, ?_⟩
  intro ρ hp
  have hbK : ρ b ≠ 0 := (mul_ne_zero_iff.mp (by simpa only [map_mul] using hp)).1
  have haK : ρ a ≠ 0 := (mul_ne_zero_iff.mp (by simpa only [map_mul] using hp)).2
  letI : Algebra R K := ρ.toAlgebra
  let τ : Rb →+* K := IsLocalization.Away.lift b (isUnit_iff_ne_zero.mpr hbK)
  letI : Algebra Rb K := τ.toAlgebra
  have hτ (z : R) : τ (algebraMap R Rb z) = ρ z :=
    IsLocalization.Away.lift_eq (S := Rb) b (isUnit_iff_ne_zero.mpr hbK) z
  have hcK : τ c ≠ 0 := by
    intro hc0
    have he := congrArg τ hsec
    rw [map_mul, hc0, zero_mul, hτ] at he
    exact haK he.symm
  letI := hfree
  obtain ⟨e⟩ := localizedAlgebra_fiber_equiv (R := R) (A := A) b hbK
  calc
    Module.finrank K (K ⊗[R] A) = Module.finrank K (K ⊗[Rb] Ab) := e.finrank_eq.symm
    _ = Module.finrank Rb Ab := module_tensor_finrank_eq_of_free_away c hc hcK
    _ = Module.finrank R A := localizedAlgebra_finrank_eq b hb

end LinearStudy
