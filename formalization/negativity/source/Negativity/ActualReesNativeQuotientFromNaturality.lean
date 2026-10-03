module
public import Negativity.ActualReesCechCyclesFromNaturality
public import Negativity.ActualNativeUnitCechCycles

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
open scoped DirectSum
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
noncomputable section
variable {R : Type u} [CommRing R] {X : Scheme.{u}}

def actualReesNativeCechCycleEquivFromNaturality
    (f : X ⟶ Spec (.of R)) (I : Ideal R)
    (hnat : ActualReesCoordinateRestrictionCompatibility f I)
    {ι : Type u} [Fintype ι] (U : ι → X.affineOpens)
    (hpair : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1))
    (htriple : ∀ j k l, IsAffineOpen (((U j).1 ⊓ (U k).1) ⊓ (U l).1)) :
    ((Scheme.Modules.baseCechComplex (actualRelativeReesToBase f I)
      (SheafOfModules.unit (actualRelativeReesScheme f I).ringCatSheaf)
      (fun j => (actualReesCechCover f I U j).1)).sc' 0 1 2).g.hom.ker ≃+
      ⨁ n : ℕ, actualClosedCechCocycles
        (((actualSpecIdealSheaf I) ^ n).comap f).subschemeι (fun j => (U j).1) :=
  (actualNativeUnitCechCycleEquiv (actualRelativeReesToBase f I)
    (fun j => (actualReesCechCover f I U j).1)).trans
      (actualReesCechCycleEquivFromNaturality f I hnat U hpair htriple)

theorem actualReesNativeCechCycleEquivFromNaturality_boundary
    (f : X ⟶ Spec (.of R)) (I : Ideal R)
    (hnat : ActualReesCoordinateRestrictionCompatibility f I)
    {ι : Type u} [Fintype ι] (U : ι → X.affineOpens)
    (hpair : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1))
    (htriple : ∀ j k l, IsAffineOpen (((U j).1 ⊓ (U k).1) ⊓ (U l).1))
    (b : (Scheme.Modules.baseCechComplex (actualRelativeReesToBase f I)
      (SheafOfModules.unit (actualRelativeReesScheme f I).ringCatSheaf)
      (fun j => (actualReesCechCover f I U j).1)).X 0) :
    actualReesNativeCechCycleEquivFromNaturality f I hnat U hpair htriple
      (((Scheme.Modules.baseCechComplex (actualRelativeReesToBase f I)
        (SheafOfModules.unit (actualRelativeReesScheme f I).ringCatSheaf)
        (fun j => (actualReesCechCover f I U j).1)).sc' 0 1 2).moduleCatToCycles b) =
      DirectSum.map (fun n => actualClosedCechBoundary
        (((actualSpecIdealSheaf I) ^ n).comap f).subschemeι (fun j => (U j).1))
          (actualReesCechZeroEquiv f I U
            (actualNativeUnitCechZeroEquiv (actualRelativeReesToBase f I)
              (fun j => (actualReesCechCover f I U j).1) b)) := by
  change actualReesCechCycleEquivFromNaturality f I hnat U hpair htriple
    (actualNativeUnitCechCycleEquiv (actualRelativeReesToBase f I)
      (fun j => (actualReesCechCover f I U j).1) _) = _
  rw [actualNativeUnitCechCycleEquiv_boundary,
    actualReesCechCycleEquivFromNaturality_boundary]

def actualReesNativeCechQuotientFromNaturality
    (f : X ⟶ Spec (.of R)) (I : Ideal R)
    (hnat : ActualReesCoordinateRestrictionCompatibility f I)
    {ι : Type u} [Fintype ι] (U : ι → X.affineOpens)
    (hpair : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1))
    (htriple : ∀ j k l, IsAffineOpen (((U j).1 ⊓ (U k).1) ⊓ (U l).1)) :
    ((Scheme.Modules.baseCechComplex (actualRelativeReesToBase f I)
      (SheafOfModules.unit (actualRelativeReesScheme f I).ringCatSheaf)
      (fun j => (actualReesCechCover f I U j).1)).sc' 0 1 2).g.hom.ker →+
      ⨁ n : ℕ, actualClosedCechHOne
        (((actualSpecIdealSheaf I) ^ n).comap f).subschemeι (fun j => (U j).1) :=
  (actualDirectSumQuotientMap (fun n => actualClosedCechBoundary
    (((actualSpecIdealSheaf I) ^ n).comap f).subschemeι (fun j => (U j).1))).comp
      (actualReesNativeCechCycleEquivFromNaturality f I hnat U hpair htriple).toAddMonoidHom

theorem actual_rees_native_cech_quotient_from_naturality_surjective
    (f : X ⟶ Spec (.of R)) (I : Ideal R)
    (hnat : ActualReesCoordinateRestrictionCompatibility f I)
    {ι : Type u} [Fintype ι] (U : ι → X.affineOpens)
    (hpair : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1))
    (htriple : ∀ j k l, IsAffineOpen (((U j).1 ⊓ (U k).1) ⊓ (U l).1)) :
    Function.Surjective (actualReesNativeCechQuotientFromNaturality f I hnat U hpair htriple) :=
  (actual_direct_sum_quotient_map_surjective _).comp
    (actualReesNativeCechCycleEquivFromNaturality f I hnat U hpair htriple).surjective

theorem actual_rees_native_cech_quotient_from_naturality_ker
    (f : X ⟶ Spec (.of R)) (I : Ideal R)
    (hnat : ActualReesCoordinateRestrictionCompatibility f I)
    {ι : Type u} [Fintype ι] (U : ι → X.affineOpens)
    (hpair : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1))
    (htriple : ∀ j k l, IsAffineOpen (((U j).1 ⊓ (U k).1) ⊓ (U l).1)) :
    (actualReesNativeCechQuotientFromNaturality f I hnat U hpair htriple).ker =
      ((Scheme.Modules.baseCechComplex (actualRelativeReesToBase f I)
        (SheafOfModules.unit (actualRelativeReesScheme f I).ringCatSheaf)
        (fun j => (actualReesCechCover f I U j).1)).sc' 0 1 2).moduleCatToCycles.range.toAddSubgroup := by
  let E := actualReesNativeCechCycleEquivFromNaturality f I hnat U hpair htriple
  let B := fun n => actualClosedCechBoundary
    (((actualSpecIdealSheaf I) ^ n).comap f).subschemeι (fun j => (U j).1)
  let K := (Scheme.Modules.baseCechComplex (actualRelativeReesToBase f I)
    (SheafOfModules.unit (actualRelativeReesScheme f I).ringCatSheaf)
    (fun j => (actualReesCechCover f I U j).1)).sc' 0 1 2
  let Z := (actualNativeUnitCechZeroEquiv (actualRelativeReesToBase f I)
    (fun j => (actualReesCechCover f I U j).1)).trans (actualReesCechZeroEquiv f I U)
  ext x
  change actualDirectSumQuotientMap B (E x) = 0 ↔ x ∈ K.moduleCatToCycles.range
  change E x ∈ (actualDirectSumQuotientMap B).ker ↔ _
  rw [actual_direct_sum_quotient_map_ker]
  constructor
  · rintro ⟨b, hb⟩
    let z := Z.symm b
    refine ⟨z, E.injective ?_⟩
    have h := actualReesNativeCechCycleEquivFromNaturality_boundary f I hnat U hpair htriple z
    change E (K.moduleCatToCycles z) = DirectSum.map B (Z z) at h
    rw [Z.apply_symm_apply] at h
    exact h.trans hb
  · rintro ⟨z, rfl⟩
    refine ⟨Z z, ?_⟩
    exact (actualReesNativeCechCycleEquivFromNaturality_boundary f I hnat U hpair htriple z).symm

#print axioms actual_rees_native_cech_quotient_from_naturality_ker
end
end Negativity

