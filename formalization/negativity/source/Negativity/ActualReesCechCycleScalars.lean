module
public import Negativity.ActualReesCechCyclesFromNaturality
public import Negativity.ActualAffineOpenReesBaseScalars
public import Negativity.ActualSpecReesScalarCoordinates

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

@[instance_reducible]
def actualReesCechCycleScalarModule (f : X ⟶ Spec (.of R)) (I : Ideal R)
    {ι : Type u} (U : ι → X.affineOpens) :
    Module (reesAlgebra I) (actualCechCocycles (actualRelativeReesScheme f I)
      (fun j => (actualReesCechCover f I U j).1)) := by
  letI := actualCechCycleGlobalModule (actualRelativeReesScheme f I)
    (fun j => (actualReesCechCover f I U j).1)
  exact Module.compHom _ ((actualRelativeReesToBase f I).appTop.hom.comp
    (Scheme.ΓSpecIso (.of (reesAlgebra I))).inv.hom)

theorem actualReesCechCycleScalarModule_apply (f : X ⟶ Spec (.of R)) (I : Ideal R)
    {ι : Type u} (U : ι → X.affineOpens) (p : reesAlgebra I)
    (a : actualCechCocycles (actualRelativeReesScheme f I)
      (fun j => (actualReesCechCover f I U j).1)) (j k : ι) :
    letI := actualReesCechCycleScalarModule f I U
    (p • a).1 j k =
      actualSectionRestriction (actualRelativeReesScheme f I) le_top
        ((actualRelativeReesToBase f I).appTop
          ((Scheme.ΓSpecIso (.of (reesAlgebra I))).inv p)) * a.1 j k := rfl

theorem actual_affine_open_coefficient_scalar (f : X ⟶ Spec (.of R))
    (V : X.Opens) (r : R) :
    actualAffineOpenCoefficientMap f V r =
      actualSectionRestriction X le_top (f.appTop ((Scheme.ΓSpecIso (.of R)).inv r)) := by
  have h := ConcreteCategory.congr_hom (actual_appTop_restriction f V)
    ((Scheme.ΓSpecIso (.of R)).inv r)
  exact h.symm

theorem actualReesCechCycleEquivFromNaturality_symm_coeff
    (f : X ⟶ Spec (.of R)) (I : Ideal R)
    (hnat : ActualReesCoordinateRestrictionCompatibility f I)
    {ι : Type u} [Fintype ι] (U : ι → X.affineOpens)
    (hpair : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1))
    (htriple : ∀ j k l, IsAffineOpen (((U j).1 ⊓ (U k).1) ⊓ (U l).1))
    (a : ⨁ n : ℕ, actualClosedCechCocycles
      (((actualSpecIdealSheaf I) ^ n).comap f).subschemeι (fun j => (U j).1))
    (n : ℕ) (j k : ι) :
    (actualAffineOpenReesSectionsEquiv f I ((U j).1 ⊓ (U k).1) (hpair j k)
      (((actualReesCechCycleEquivFromNaturality f I hnat U hpair htriple).symm a).1 j k)).1.coeff n =
        (a n).1 j k := by
  let e := actualReesCechCycleEquivFromNaturality f I hnat U hpair htriple
  have h := congrArg (fun b => b j k)
    (actualReesCechCycleEquivFromNaturality_coeff f I hnat U hpair htriple (e.symm a) n)
  rw [e.apply_symm_apply] at h
  erw [actualReesCechOneEquiv_coeff] at h
  exact h.symm

theorem actualReesCechCycleEquivFromNaturality_symm_of
    (f : X ⟶ Spec (.of R)) (I : Ideal R)
    (hnat : ActualReesCoordinateRestrictionCompatibility f I)
    {ι : Type u} [Fintype ι] (U : ι → X.affineOpens)
    (hpair : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1))
    (htriple : ∀ j k l, IsAffineOpen (((U j).1 ⊓ (U k).1) ⊓ (U l).1)) (n : ℕ)
    (a : actualClosedCechCocycles
      (((actualSpecIdealSheaf I) ^ n).comap f).subschemeι (fun j => (U j).1)) (j k : ι) :
    (actualAffineOpenReesSectionsEquiv f I ((U j).1 ⊓ (U k).1) (hpair j k)
      (((actualReesCechCycleEquivFromNaturality f I hnat U hpair htriple).symm
        (DirectSum.of _ n a)).1 j k)).1 = Polynomial.monomial n (a.1 j k) := by
  classical
  ext d
  rw [actualReesCechCycleEquivFromNaturality_symm_coeff]
  by_cases h : d = n
  · subst d
    simp [DirectSum.of_eq_same]
  · rw [DirectSum.of_eq_of_ne _ _ _ h]
    simp [Polynomial.coeff_monomial, Ne.symm h]
    rfl

theorem actual_rees_cech_cycle_homogeneous_scalars
    (f : X ⟶ Spec (.of R)) [QuasiCompact f] (I : Ideal R)
    (hnat : ActualReesCoordinateRestrictionCompatibility f I)
    {ι : Type u} [Fintype ι] (U : ι → X.affineOpens)
    (hpair : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1))
    (htriple : ∀ j k l, IsAffineOpen (((U j).1 ⊓ (U k).1) ⊓ (U l).1))
    (m n : ℕ) (r : ↥(I ^ m))
    (a : actualClosedCechCocycles
      (((actualSpecIdealSheaf I) ^ n).comap f).subschemeι (fun j => (U j).1)) :
    letI := actualReesCechCycleScalarModule f I U
    actualReesCechCycleEquivFromNaturality f I hnat U hpair htriple
      (actualReesPowerMonomial I m r •
        (actualReesCechCycleEquivFromNaturality f I hnat U hpair htriple).symm
          (DirectSum.of _ n a)) =
      DirectSum.of _ (m + n)
        (actualRelativeCechGradedCycle f (actualSpecIdealSheaf I) U hpair m n
          ((Scheme.ΓSpecIso (.of R)).inv r.1) (by
            rw [actual_spec_ideal_sheaf_top, ← Ideal.map_pow]
            exact Ideal.mem_map_of_mem _ r.2) a) := by
  letI := actualReesCechCycleScalarModule f I U
  let e := actualReesCechCycleEquivFromNaturality f I hnat U hpair htriple
  apply e.symm.injective
  rw [e.symm_apply_apply]
  apply Subtype.ext
  funext j k
  apply (actualAffineOpenReesSectionsEquiv f I _ (hpair j k)).injective
  apply Subtype.ext
  rw [actualReesCechCycleScalarModule_apply, map_mul, Subalgebra.coe_mul,
    actualReesCechCycleEquivFromNaturality_symm_of,
    actualReesCechCycleEquivFromNaturality_symm_of]
  have hb := actual_affine_open_rees_sections_base_scalars f I
    ((U j).1 ⊓ (U k).1) (hpair j k) (actualReesPowerMonomial I m r)
  erw [hb]
  change (Polynomial.monomial m r.1).map (actualAffineOpenCoefficientMap f _) *
    Polynomial.monomial n (a.1 j k) =
      Polynomial.monomial (m + n)
        (actualSectionRestriction X le_top
          (f.appTop ((Scheme.ΓSpecIso (.of R)).inv r.1)) * a.1 j k)
  rw [Polynomial.map_monomial, Polynomial.monomial_mul_monomial,
    actual_affine_open_coefficient_scalar]

#print axioms actual_rees_cech_cycle_homogeneous_scalars
end
end Negativity

