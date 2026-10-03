module
public import Negativity.ActualReesIdealSectionCoordinates
public import Negativity.FinitePiDirectSumReuse
public import Negativity.ActualReesCechCover

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
open scoped DirectSum
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {R : Type u} [CommRing R] {X : Scheme.{u}}

@[simp]
theorem finitePiDirectSumLinearEquiv_symm_apply
    {κ ι : Type*} [Fintype ι] (M : κ → ι → Type*)
    [∀ n j, AddCommGroup (M n j)]
    (x : ∀ j, ⨁ n : κ, M n j) (n : κ) (j : ι) :
    (finitePiDirectSumLinearEquiv ℤ κ ι M).symm x n j = x j n := by
  have h := congrArg (fun y => y j n)
    ((finitePiDirectSumLinearEquiv ℤ κ ι M).apply_symm_apply x)
  simpa only [finitePiDirectSumLinearEquiv_apply] using h

/-- All genuine Rees-image zero cochains are finitely supported homogeneous
zero cochains of the actual ideal powers on the genuine source cover. -/
def actualReesCechZeroEquiv (f : X ⟶ Spec (.of R)) (I : Ideal R)
    {ι : Type u} [Fintype ι] (U : ι → X.affineOpens) :
    actualCechZero (actualRelativeReesScheme f I)
        (fun j => (actualReesCechCover f I U j).1) ≃+
      ⨁ n : ℕ, (actualCechPullbackZero
        (((actualSpecIdealSheaf I) ^ n).comap f).subschemeι (fun j => (U j).1)).ker :=
  (AddEquiv.piCongrRight (fun j => actualAffineReesPowerSectionsEquiv f I (U j))).trans
    (((finitePiDirectSumLinearEquiv ℤ ℕ ι
      (fun n j => ((((actualSpecIdealSheaf I) ^ n).comap f).subschemeι.app
        (U j).1).hom.toAddMonoidHom.ker)).symm.toAddEquiv).trans
      (DirectSum.congrAddEquiv (fun n => actualKernelZeroFamilyEquiv
        (((actualSpecIdealSheaf I) ^ n).comap f).subschemeι (fun j => (U j).1))))

/-- Finite products over pairs of affine charts commute with genuine
homogeneous power sections. The result is the actual pullback-kernel complex. -/
def actualReesCechOneEquiv (f : X ⟶ Spec (.of R)) (I : Ideal R)
    {ι : Type u} [Fintype ι] (U : ι → X.affineOpens)
    (hU : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1)) :
    actualCechOne (actualRelativeReesScheme f I)
        (fun j => (actualReesCechCover f I U j).1) ≃+
      ⨁ n : ℕ, (actualCechPullbackOne
        (((actualSpecIdealSheaf I) ^ n).comap f).subschemeι (fun j => (U j).1)).ker := by
  let M (n : ℕ) (j k : ι) :=
    ((((actualSpecIdealSheaf I) ^ n).comap f).subschemeι.app
      ((U j).1 ⊓ (U k).1)).hom.toAddMonoidHom.ker
  let e : actualCechOne (actualRelativeReesScheme f I)
      (fun j => (actualReesCechCover f I U j).1) ≃+
        ∀ j k, ⨁ n : ℕ, M n j k :=
    AddEquiv.piCongrRight (fun j => AddEquiv.piCongrRight (fun k =>
      actualAffineReesPowerSectionsEquiv f I ⟨(U j).1 ⊓ (U k).1, hU j k⟩))
  exact e.trans ((AddEquiv.piCongrRight (fun j =>
    (finitePiDirectSumLinearEquiv ℤ ℕ ι (fun n k => M n j k)).symm.toAddEquiv)).trans
    (((finitePiDirectSumLinearEquiv ℤ ℕ ι (fun n j => ∀ k, M n j k)).symm.toAddEquiv).trans
      (DirectSum.congrAddEquiv (fun n => actualKernelOneFamilyEquiv
        (((actualSpecIdealSheaf I) ^ n).comap f).subschemeι (fun j => (U j).1)))))

@[simp]
theorem actualReesCechZeroEquiv_coeff (f : X ⟶ Spec (.of R)) (I : Ideal R)
    {ι : Type u} [Fintype ι] (U : ι → X.affineOpens)
    (p : actualCechZero (actualRelativeReesScheme f I)
      (fun j => (actualReesCechCover f I U j).1)) (n : ℕ) (j : ι) :
    (actualReesCechZeroEquiv f I U p n).1 j =
      (actualAffineOpenReesSectionsEquiv f I (U j).1 (U j).2 (p j)).1.coeff n := by
  change ((finitePiDirectSumLinearEquiv ℤ ℕ ι _).symm
    (fun j => actualAffineReesPowerSectionsEquiv f I (U j) (p j)) n j).1 = _
  rw [finitePiDirectSumLinearEquiv_symm_apply]
  exact actualAffineReesPowerSectionsEquiv_coeff f I (U j) (p j) n

@[simp]
theorem actualReesCechOneEquiv_coeff (f : X ⟶ Spec (.of R)) (I : Ideal R)
    {ι : Type u} [Fintype ι] (U : ι → X.affineOpens)
    (hU : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1))
    (p : actualCechOne (actualRelativeReesScheme f I)
      (fun j => (actualReesCechCover f I U j).1)) (n : ℕ) (j k : ι) :
    (actualReesCechOneEquiv f I U hU p n).1 j k =
      (actualAffineOpenReesSectionsEquiv f I ((U j).1 ⊓ (U k).1)
        (hU j k) (p j k)).1.coeff n := by
  change (((finitePiDirectSumLinearEquiv ℤ ℕ ι _).symm
    (fun j => (finitePiDirectSumLinearEquiv ℤ ℕ ι _).symm
      (fun k => actualAffineReesPowerSectionsEquiv f I
        ⟨(U j).1 ⊓ (U k).1, hU j k⟩ (p j k))) n j) k).1 = _
  rw [finitePiDirectSumLinearEquiv_symm_apply,
    finitePiDirectSumLinearEquiv_symm_apply]
  exact actualAffineReesPowerSectionsEquiv_coeff f I
    ⟨(U j).1 ⊓ (U k).1, hU j k⟩ (p j k) n

@[simp]
theorem actualReesCechZeroEquiv_symm_coeff (f : X ⟶ Spec (.of R)) (I : Ideal R)
    {ι : Type u} [Fintype ι] (U : ι → X.affineOpens)
    (a : ⨁ n : ℕ, (actualCechPullbackZero
      (((actualSpecIdealSheaf I) ^ n).comap f).subschemeι (fun j => (U j).1)).ker)
    (n : ℕ) (j : ι) :
    (actualAffineOpenReesSectionsEquiv f I (U j).1 (U j).2
      ((actualReesCechZeroEquiv f I U).symm a j)).1.coeff n = (a n).1 j := by
  have h := actualReesCechZeroEquiv_coeff f I U
    ((actualReesCechZeroEquiv f I U).symm a) n j
  rw [(actualReesCechZeroEquiv f I U).apply_symm_apply] at h
  exact h.symm

theorem actualReesCechZeroEquiv_symm_of (f : X ⟶ Spec (.of R)) (I : Ideal R)
    {ι : Type u} [Fintype ι] (U : ι → X.affineOpens) (n : ℕ)
    (a : (actualCechPullbackZero
      (((actualSpecIdealSheaf I) ^ n).comap f).subschemeι (fun j => (U j).1)).ker)
    (j : ι) :
    (actualAffineOpenReesSectionsEquiv f I (U j).1 (U j).2
      ((actualReesCechZeroEquiv f I U).symm (DirectSum.of _ n a) j)).1 =
        Polynomial.monomial n (a.1 j) := by
  classical
  ext d
  rw [actualReesCechZeroEquiv_symm_coeff]
  by_cases h : d = n
  · subst d
    simp [DirectSum.of_eq_same]
  · rw [DirectSum.of_eq_of_ne _ _ _ h]
    simp [ZeroMemClass.coe_zero, Polynomial.coeff_monomial, Ne.symm h]
    rfl

@[simp]
theorem actualReesCechOneEquiv_symm_coeff (f : X ⟶ Spec (.of R)) (I : Ideal R)
    {ι : Type u} [Fintype ι] (U : ι → X.affineOpens)
    (hU : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1))
    (a : ⨁ n : ℕ, (actualCechPullbackOne
      (((actualSpecIdealSheaf I) ^ n).comap f).subschemeι (fun j => (U j).1)).ker)
    (n : ℕ) (j k : ι) :
    (actualAffineOpenReesSectionsEquiv f I ((U j).1 ⊓ (U k).1) (hU j k)
      ((actualReesCechOneEquiv f I U hU).symm a j k)).1.coeff n = (a n).1 j k := by
  have h := actualReesCechOneEquiv_coeff f I U hU
    ((actualReesCechOneEquiv f I U hU).symm a) n j k
  rw [(actualReesCechOneEquiv f I U hU).apply_symm_apply] at h
  exact h.symm

/-- A homogeneous actual kernel cochain gives an actual monomial section
on each Rees chart, with its actual coefficient unchanged. -/
theorem actualReesCechOneEquiv_symm_of (f : X ⟶ Spec (.of R)) (I : Ideal R)
    {ι : Type u} [Fintype ι] (U : ι → X.affineOpens)
    (hU : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1)) (n : ℕ)
    (a : (actualCechPullbackOne
      (((actualSpecIdealSheaf I) ^ n).comap f).subschemeι (fun j => (U j).1)).ker)
    (j k : ι) :
    (actualAffineOpenReesSectionsEquiv f I ((U j).1 ⊓ (U k).1) (hU j k)
      ((actualReesCechOneEquiv f I U hU).symm (DirectSum.of _ n a) j k)).1 =
        Polynomial.monomial n (a.1 j k) := by
  classical
  ext d
  rw [actualReesCechOneEquiv_symm_coeff]
  by_cases h : d = n
  · subst d
    simp [DirectSum.of_eq_same, Polynomial.coeff_monomial]
  · rw [DirectSum.of_eq_of_ne _ _ _ h]
    simp [ZeroMemClass.coe_zero, Polynomial.coeff_monomial, Ne.symm h]
    rfl

#print axioms actualReesCechZeroEquiv
#print axioms actualReesCechOneEquiv
#print axioms actualReesCechOneEquiv_coeff
#print axioms actualReesCechOneEquiv_symm_of
end
end Negativity
