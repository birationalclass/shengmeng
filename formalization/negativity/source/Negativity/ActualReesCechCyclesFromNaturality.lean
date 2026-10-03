module
public import Negativity.ActualReesCechDifferentialsFromNaturality

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
open scoped DirectSum
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 100000
noncomputable section
variable {R : Type u} [CommRing R] {X : Scheme.{u}}

theorem actual_rees_cech_sum_differential_iff_from_naturality
    (f : X ⟶ Spec (.of R)) (I : Ideal R)
    (hnat : ActualReesCoordinateRestrictionCompatibility f I)
    {ι : Type u} [Fintype ι] (U : ι → X.affineOpens)
    (hpair : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1))
    (htriple : ∀ j k l, IsAffineOpen (((U j).1 ⊓ (U k).1) ⊓ (U l).1))
    (a : actualCechOne (actualRelativeReesScheme f I)
      (fun j => (actualReesCechCover f I U j).1)) :
    actualCechBoundary (actualRelativeReesScheme f I)
        (fun j => (actualReesCechCover f I U j).1) a = 0 ↔
      DirectSum.map (fun n => actualClosedCechKernelDifferential
        (((actualSpecIdealSheaf I) ^ n).comap f).subschemeι (fun j => (U j).1))
          (actualReesCechOneEquiv f I U hpair a) = 0 := by
  rw [actual_rees_cech_cycle_iff_from_naturality f I hnat U hpair htriple]
  constructor
  · intro ha
    ext n
    exact ha n
  · intro ha n
    exact congrArg (fun x => x n) ha

/-- Actual Rees-image cocycles equal finite sums of the actual ideal-power
cocycles. The local restriction premise is discharged by the actual chart
naturality theorem in the geometric wrapper. -/
def actualReesCechCycleEquivFromNaturality
    (f : X ⟶ Spec (.of R)) (I : Ideal R)
    (hnat : ActualReesCoordinateRestrictionCompatibility f I)
    {ι : Type u} [Fintype ι] (U : ι → X.affineOpens)
    (hpair : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1))
    (htriple : ∀ j k l, IsAffineOpen (((U j).1 ⊓ (U k).1) ⊓ (U l).1)) :
    actualCechCocycles (actualRelativeReesScheme f I)
        (fun j => (actualReesCechCover f I U j).1) ≃+
      ⨁ n : ℕ, actualClosedCechCocycles
        (((actualSpecIdealSheaf I) ^ n).comap f).subschemeι (fun j => (U j).1) := by
  let e := actualReesCechOneEquiv f I U hpair
  let c := actualGradedClosedCechCycleEquiv
    (fun n => (((actualSpecIdealSheaf I) ^ n).comap f).subschemeι) (fun j => (U j).1)
  let h := actual_rees_cech_sum_differential_iff_from_naturality f I hnat U hpair htriple
  exact {
    toFun := fun a => c.symm ⟨e a.1, (h a.1).mp a.2⟩
    invFun := fun a => ⟨e.symm (c a).1, (h _).mpr (by rw [e.apply_symm_apply]; exact (c a).2)⟩
    left_inv := by
      intro a
      apply Subtype.ext
      change e.symm (c (c.symm ⟨e a.1, _⟩)).1 = a.1
      rw [c.apply_symm_apply]
      exact e.symm_apply_apply a.1
    right_inv := by
      intro a
      apply c.injective
      apply Subtype.ext
      change (c (c.symm ⟨e (e.symm (c a).1), _⟩)).1 = (c a).1
      exact (congrArg Subtype.val (c.apply_symm_apply ⟨e (e.symm (c a).1), _⟩)).trans
        (e.apply_symm_apply (c a).1)
    map_add' := by
      intro a b
      change c.symm ⟨e (a.1 + b.1), _⟩ = c.symm ⟨e a.1, _⟩ + c.symm ⟨e b.1, _⟩
      exact (congrArg c.symm (show ⟨e (a.1 + b.1), _⟩ = ⟨e a.1, _⟩ + ⟨e b.1, _⟩ from
        Subtype.ext (e.map_add a.1 b.1))).trans (c.symm.map_add _ _) }

theorem actualGradedClosedCechCycleEquiv_coe
    {T : Scheme.{u}} {κ : Type v} {Z : κ → Scheme.{u}}
    (i : ∀ n, Z n ⟶ T) {ι : Type u} (V : ι → T.Opens)
    (a : ⨁ n, actualClosedCechCocycles (i n) V) (n : κ) :
    ((actualGradedClosedCechCycleEquiv i V a).1 n).1 = (a n).1 := rfl

theorem actualReesCechCycleEquivFromNaturality_coeff
    (f : X ⟶ Spec (.of R)) (I : Ideal R)
    (hnat : ActualReesCoordinateRestrictionCompatibility f I)
    {ι : Type u} [Fintype ι] (U : ι → X.affineOpens)
    (hpair : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1))
    (htriple : ∀ j k l, IsAffineOpen (((U j).1 ⊓ (U k).1) ⊓ (U l).1))
    (a : actualCechCocycles (actualRelativeReesScheme f I)
      (fun j => (actualReesCechCover f I U j).1)) (n : ℕ) :
    (actualReesCechCycleEquivFromNaturality f I hnat U hpair htriple a n).1 =
      (actualReesCechOneEquiv f I U hpair a.1 n).1 := by
  let c := actualGradedClosedCechCycleEquiv
    (fun n => (((actualSpecIdealSheaf I) ^ n).comap f).subschemeι) (fun j => (U j).1)
  have h := congrArg (fun b => (b.1 n).1)
    (c.apply_symm_apply ⟨actualReesCechOneEquiv f I U hpair a.1,
      (actual_rees_cech_sum_differential_iff_from_naturality f I hnat U hpair htriple a.1).mp a.2⟩)
  have hc := actualGradedClosedCechCycleEquiv_coe
    (fun n => (((actualSpecIdealSheaf I) ^ n).comap f).subschemeι) (fun j => (U j).1)
    (c.symm ⟨actualReesCechOneEquiv f I U hpair a.1,
      (actual_rees_cech_sum_differential_iff_from_naturality f I hnat U hpair htriple a.1).mp a.2⟩) n
  exact hc.symm.trans h

theorem actualReesCechCycleEquivFromNaturality_boundary
    (f : X ⟶ Spec (.of R)) (I : Ideal R)
    (hnat : ActualReesCoordinateRestrictionCompatibility f I)
    {ι : Type u} [Fintype ι] (U : ι → X.affineOpens)
    (hpair : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1))
    (htriple : ∀ j k l, IsAffineOpen (((U j).1 ⊓ (U k).1) ⊓ (U l).1))
    (b : actualCechZero (actualRelativeReesScheme f I)
      (fun j => (actualReesCechCover f I U j).1)) :
    actualReesCechCycleEquivFromNaturality f I hnat U hpair htriple
      (actualCechCoboundary (actualRelativeReesScheme f I)
        (fun j => (actualReesCechCover f I U j).1) b) =
      DirectSum.map (fun n => actualClosedCechBoundary
        (((actualSpecIdealSheaf I) ^ n).comap f).subschemeι (fun j => (U j).1))
          (actualReesCechZeroEquiv f I U b) := by
  ext n : 1
  apply Subtype.ext
  rw [actualReesCechCycleEquivFromNaturality_coeff]
  exact actual_rees_cech_difference_coeff_from_naturality f I hnat U hpair b n

#print axioms actualReesCechCycleEquivFromNaturality
#print axioms actualReesCechCycleEquivFromNaturality_boundary
end
end Negativity


