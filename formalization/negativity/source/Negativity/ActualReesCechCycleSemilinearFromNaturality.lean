module
public import Negativity.ActualReesCechCycleScalars

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
open scoped DirectSum
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 100000
noncomputable section
variable {R : Type u} [CommRing R] {X : Scheme.{u}}

theorem actual_rees_cech_cycle_target_homogeneous_scalars
    (f : X ⟶ Spec (.of R)) [QuasiCompact f] (I : Ideal R)
    {ι : Type u} [Fintype ι] (U : ι → X.affineOpens)
    (hpair : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1))
    (m n : ℕ) (r : ↥(I ^ m))
    (a : actualClosedCechCocycles
      (((actualSpecIdealSheaf I) ^ n).comap f).subschemeι (fun j => (U j).1)) :
    letI := actualRelativeCechOneModule f (fun j => (U j).1)
    letI := actualRelativeCechCyclePolynomialReesModule f (actualSpecIdealSheaf I) U hpair
    actualSpecReesScalarEquiv I (actualReesPowerMonomial I m r) • DirectSum.of (fun d => actualRelativeCechCycleModule f (actualSpecIdealSheaf I) (fun j => (U j).1) d) n a =
      DirectSum.of (fun d => actualRelativeCechCycleModule f (actualSpecIdealSheaf I) (fun j => (U j).1) d) (m + n)
        (actualRelativeCechGradedCycle f (actualSpecIdealSheaf I) U hpair m n
          ((Scheme.ΓSpecIso (.of R)).inv r.1) (by
            rw [actual_spec_ideal_sheaf_top, ← Ideal.map_pow]
            exact Ideal.mem_map_of_mem _ r.2) a) := by
  let J := actualSpecIdealSheaf I
  letI := actualRelativeCechOneModule f (fun j => (U j).1)
  letI := actualRelativeCechCycleGradedSMul f J (fun j => (U j).1) hpair
  letI := actualRelativeCechCyclePolynomialReesModule f J U hpair
  rw [actualSpecReesScalarEquiv_monomial, actualPolynomialReesModule_monomial_smul]
  let r' : ↥((J.ideal ⟨⊤, isAffineOpen_top _⟩) ^ m) :=
    ⟨(Scheme.ΓSpecIso (.of R)).inv r.1, by
      rw [actual_spec_ideal_sheaf_top, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ r.2⟩
  have hact : GradedMonoid.GSMul.smul
      (A := fun d : ℕ => ↥((J.ideal ⟨⊤, isAffineOpen_top _⟩) ^ d))
      (M := fun d : ℕ => actualRelativeCechCycleModule f J (fun j => (U j).1) d)
        r' a = actualRelativeCechGradedCycle f J U hpair m n r'.1 r'.2 a := by
    rfl
  simpa only [DirectSum.lof_eq_of, vadd_eq_add, hact] using
    (DirectSum.Gmodule.of_smul_of
      (fun d : ℕ => ↥((J.ideal ⟨⊤, isAffineOpen_top _⟩) ^ d))
      (fun d : ℕ => actualRelativeCechCycleModule f J (fun j => (U j).1) d)
      r' a)

/-- The actual chart comparison respects all genuine Rees scalars, by
finite homogeneous decomposition on both scalar and cochain sides. -/
def actualReesCechCycleSemilinearFromNaturality
    (f : X ⟶ Spec (.of R)) [QuasiCompact f] (I : Ideal R)
    (hnat : ActualReesCoordinateRestrictionCompatibility f I)
    {ι : Type u} [Fintype ι] (U : ι → X.affineOpens)
    (hpair : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1))
    (htriple : ∀ j k l, IsAffineOpen (((U j).1 ⊓ (U k).1) ⊓ (U l).1)) :
    letI := actualReesCechCycleScalarModule f I U
    letI := actualRelativeCechOneModule f (fun j => (U j).1)
    letI := actualRelativeCechCyclePolynomialReesModule f (actualSpecIdealSheaf I) U hpair
    actualCechCocycles (actualRelativeReesScheme f I)
        (fun j => (actualReesCechCover f I U j).1) →ₛₗ[(actualSpecReesScalarEquiv I).toRingHom]
      ⨁ n : ℕ, actualRelativeCechCycleModule f (actualSpecIdealSheaf I) (fun j => (U j).1) n := by
  letI := actualReesCechCycleScalarModule f I U
  letI := actualRelativeCechOneModule f (fun j => (U j).1)
  letI := actualRelativeCechCyclePolynomialReesModule f (actualSpecIdealSheaf I) U hpair
  let e : actualCechCocycles (actualRelativeReesScheme f I)
      (fun j => (actualReesCechCover f I U j).1) ≃+
      ⨁ n : ℕ, actualRelativeCechCycleModule f (actualSpecIdealSheaf I) (fun j => (U j).1) n :=
    actualReesCechCycleEquivFromNaturality f I hnat U hpair htriple
  refine { e.toAddMonoidHom with map_smul' := ?_ }
  intro p x
  change e (p • x) = actualSpecReesScalarEquiv I p • e x
  obtain ⟨r, rfl⟩ := (actualReesDirectSumAlgEquiv I).surjective p
  revert x
  refine DirectSum.induction_on r ?_ (fun m r => ?_) (fun r s hr hs => ?_)
  · intro x
    simp only [map_zero, zero_smul]
  · intro x
    obtain ⟨a, rfl⟩ := e.symm.surjective x
    refine DirectSum.induction_on a ?_ (fun n a => ?_) (fun a b ha hb => ?_)
    · simp only [map_zero, smul_zero]
    · have hm : actualReesDirectSumAlgEquiv I (DirectSum.of _ m r) =
          actualReesPowerMonomial I m r :=
        actualReesDirectSumAlgEquiv_lof I m r
      rw [hm, e.apply_symm_apply]
      exact (actual_rees_cech_cycle_homogeneous_scalars f I hnat U hpair htriple m n r a).trans
        (actual_rees_cech_cycle_target_homogeneous_scalars f I U hpair m n r a).symm
    · rw [e.symm.map_add, smul_add, e.map_add, e.map_add, smul_add, ha, hb]
  · intro x
    rw [map_add, add_smul, e.map_add, map_add, add_smul, hr, hs]

#print axioms actualReesCechCycleSemilinearFromNaturality
end
end Negativity

