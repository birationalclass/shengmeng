module
public import Negativity.ReesDirectSumBaseChange
public import Negativity.ActualAffineOpenReesCoordinates
public import Negativity.ActualSpecIdealPullback
public import Negativity.ActualNativeCechKernelComparison

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
open scoped DirectSum
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- The power-ideal coefficients and actual thickening section kernels agree
on every genuine affine open. No kernel-identification premise is supplied. -/
def actualSpecPowerSectionKernelEquiv (f : X ⟶ Spec (.of R)) (I : Ideal R)
    (U : X.affineOpens) (n : ℕ) :
    ↥((I.map (actualAffineOpenCoefficientMap f U.1)) ^ n) ≃+
      ((((actualSpecIdealSheaf I) ^ n).comap f).subschemeι.app U.1).hom.toAddMonoidHom.ker where
  toFun a := ⟨a.1, by
    change a.1 ∈ RingHom.ker
      ((((actualSpecIdealSheaf I) ^ n).comap f).subschemeι.app U.1).hom
    rw [IdealSheafData.ker_subschemeι_app]
    rw [actual_spec_ideal_power_pullback_coordinates]
    exact a.2⟩
  invFun a := ⟨a.1, by
    change a.1 ∈
      (I.map ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ U.1 le_top).hom) ^ n
    rw [← actual_spec_ideal_power_pullback_coordinates f I U n,
      ← IdealSheafData.ker_subschemeι_app]
    exact a.2⟩
  left_inv a := rfl
  right_inv a := rfl
  map_add' a b := rfl

@[simp]
theorem actualSpecPowerSectionKernelEquiv_coe (f : X ⟶ Spec (.of R))
    (I : Ideal R) (U : X.affineOpens) (n : ℕ)
    (a : ↥((I.map (actualAffineOpenCoefficientMap f U.1)) ^ n)) :
    (actualSpecPowerSectionKernelEquiv f I U n a : Γ(X, U.1)) = a.1 := rfl

/-- Local Rees polynomials are exactly finitely supported actual sections of
the ideal-power thickenings; the degree is the actual polynomial coefficient. -/
def actualLocalReesPowerSectionsEquiv (f : X ⟶ Spec (.of R)) (I : Ideal R)
    (U : X.affineOpens) :
    reesAlgebra (I.map (actualAffineOpenCoefficientMap f U.1)) ≃+
      ⨁ n : ℕ,
        ((((actualSpecIdealSheaf I) ^ n).comap f).subschemeι.app U.1).hom.toAddMonoidHom.ker :=
  (actualReesDirectSumAlgEquiv _).symm.toAddEquiv.trans
    (DirectSum.congrAddEquiv (actualSpecPowerSectionKernelEquiv f I U))

@[simp]
theorem actualLocalReesPowerSectionsEquiv_coeff (f : X ⟶ Spec (.of R))
    (I : Ideal R) (U : X.affineOpens)
    (p : reesAlgebra (I.map (actualAffineOpenCoefficientMap f U.1))) (n : ℕ) :
    (actualLocalReesPowerSectionsEquiv f I U p n : Γ(X,U.1)) = p.1.coeff n := by
  change (((actualReesDirectSumAlgEquiv
    (I.map (actualAffineOpenCoefficientMap f U.1))).symm p) n).1 = p.1.coeff n
  let a := (actualReesDirectSumAlgEquiv
    (I.map (actualAffineOpenCoefficientMap f U.1))).symm p
  have h := actualDirectSumToRees_coeff
    (I.map (actualAffineOpenCoefficientMap f U.1)) a n
  change (actualReesDirectSumAlgEquiv _ a).1.coeff n = (a n).1 at h
  simpa only [a, AlgEquiv.apply_symm_apply] using h.symm

@[simp]
theorem actualLocalReesPowerSectionsEquiv_monomial (f : X ⟶ Spec (.of R))
    (I : Ideal R) (U : X.affineOpens) (n : ℕ)
    (a : ↥((I.map (actualAffineOpenCoefficientMap f U.1)) ^ n)) :
    actualLocalReesPowerSectionsEquiv f I U
        (actualReesPowerMonomial (I.map (actualAffineOpenCoefficientMap f U.1)) n a) =
      DirectSum.of (fun n : ℕ =>
        ((((actualSpecIdealSheaf I) ^ n).comap f).subschemeι.app U.1).hom.toAddMonoidHom.ker)
        n (actualSpecPowerSectionKernelEquiv f I U n a) := by
  classical
  change DirectSum.congrAddEquiv (actualSpecPowerSectionKernelEquiv f I U)
    ((actualReesDirectSumAlgEquiv _).symm (actualReesPowerMonomial _ n a)) = _
  rw [actualReesDirectSumAlgEquiv_symm_monomial]
  simp only [DirectSum.lof_eq_of]
  change DirectSum.map (fun n => (actualSpecPowerSectionKernelEquiv f I U n).toAddMonoidHom)
    (DirectSum.of _ n a) = _
  rw [DirectSum.map_of]
  rfl

/-- Genuine Rees-image chart sections decompose into the actual power-ideal
kernel sections, via the proved closed-image coordinate ring isomorphism. -/
def actualAffineReesPowerSectionsEquiv (f : X ⟶ Spec (.of R)) (I : Ideal R)
    (U : X.affineOpens) :
    Γ(actualRelativeReesScheme f I, actualRelativeReesToSource f I ⁻¹ᵁ U.1) ≃+
      ⨁ n : ℕ,
        ((((actualSpecIdealSheaf I) ^ n).comap f).subschemeι.app U.1).hom.toAddMonoidHom.ker :=
  (actualAffineOpenReesSectionsEquiv f I U.1 U.2).toAddEquiv.trans
    (actualLocalReesPowerSectionsEquiv f I U)

@[simp]
theorem actualAffineReesPowerSectionsEquiv_coeff (f : X ⟶ Spec (.of R))
    (I : Ideal R) (U : X.affineOpens)
    (p : Γ(actualRelativeReesScheme f I, actualRelativeReesToSource f I ⁻¹ᵁ U.1))
    (n : ℕ) :
    (actualAffineReesPowerSectionsEquiv f I U p n : Γ(X,U.1)) =
      (actualAffineOpenReesSectionsEquiv f I U.1 U.2 p).1.coeff n :=
  actualLocalReesPowerSectionsEquiv_coeff f I U _ n

#print axioms actualSpecPowerSectionKernelEquiv
#print axioms actualAffineReesPowerSectionsEquiv
end
end Negativity
