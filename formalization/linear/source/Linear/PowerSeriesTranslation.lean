module
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.Data.Fintype.Sum
public import Linear.PowerSeriesDerivative
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
open scoped MvPowerSeries.WithPiTopology
variable {K σ τ : Type*} [CommRing K] [Fintype σ] [Fintype τ]

def translationImages (h : τ → MvPowerSeries σ K) :
    σ ⊕ τ → MvPowerSeries (σ ⊕ τ) K :=
  Sum.elim (fun i => MvPowerSeries.X (Sum.inl i))
    (fun j => MvPowerSeries.X (Sum.inr j) + MvPowerSeries.rename Sum.inl (h j))

theorem translationImages_hasSubst (h : τ → MvPowerSeries σ K)
    (hh : ∀ j, (h j).constantCoeff = 0) :
    MvPowerSeries.HasSubst (translationImages h) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro i
  cases i with
  | inl i => simp [translationImages]
  | inr j => simp [translationImages, hh j]

theorem translation_fixes_parameters (h : τ → MvPowerSeries σ K)
    (hh : ∀ j, (h j).constantCoeff = 0) (f : MvPowerSeries σ K) :
    MvPowerSeries.substAlgHom (translationImages_hasSubst h hh)
      (MvPowerSeries.rename Sum.inl f) = MvPowerSeries.rename Sum.inl f := by
  rw [MvPowerSeries.substAlgHom_apply, MvPowerSeries.rename_eq_subst,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.X_comp Sum.inl)
      (translationImages_hasSubst h hh)]
  congr 1
  funext i
  exact MvPowerSeries.subst_X (translationImages_hasSubst h hh) (Sum.inl i)

theorem translation_inverse (h : τ → MvPowerSeries σ K)
    (hh : ∀ j, (h j).constantCoeff = 0) (f : MvPowerSeries (σ ⊕ τ) K) :
    MvPowerSeries.substAlgHom (translationImages_hasSubst (fun j => -h j)
      (by intro j; simp [hh j]))
      (MvPowerSeries.substAlgHom (translationImages_hasSubst h hh) f) = f := by
  rw [MvPowerSeries.substAlgHom_apply, MvPowerSeries.substAlgHom_apply,
    MvPowerSeries.subst_comp_subst_apply (translationImages_hasSubst h hh)
      (translationImages_hasSubst (fun j => -h j) (by intro j; simp [hh j]))]
  have hx : (fun i => MvPowerSeries.subst (translationImages (fun j => -h j))
      (translationImages h i)) = MvPowerSeries.X := by
    funext i
    cases i with
    | inl i =>
      change MvPowerSeries.subst (translationImages (fun j => -h j))
        (MvPowerSeries.X (Sum.inl i)) = _
      exact MvPowerSeries.subst_X
        (translationImages_hasSubst (fun j => -h j) (by intro j; simp [hh j])) _
    | inr j =>
      change MvPowerSeries.subst (translationImages (fun j => -h j))
        (MvPowerSeries.X (Sum.inr j) + MvPowerSeries.rename Sum.inl (h j)) = _
      rw [
        MvPowerSeries.subst_add (translationImages_hasSubst (fun j => -h j)
          (by intro j; simp [hh j])), MvPowerSeries.subst_X
          (translationImages_hasSubst (fun j => -h j) (by intro j; simp [hh j]))]
      have hp := translation_fixes_parameters (fun j => -h j)
        (by intro j; simp [hh j]) (h j)
      rw [MvPowerSeries.substAlgHom_apply] at hp
      rw [hp]
      simp [translationImages]
  rw [hx, MvPowerSeries.subst_self]
  rfl

def powerSeriesTranslationEquiv (h : τ → MvPowerSeries σ K)
    (hh : ∀ j, (h j).constantCoeff = 0) :
    MvPowerSeries (σ ⊕ τ) K ≃ₐ[K] MvPowerSeries (σ ⊕ τ) K where
  __ := MvPowerSeries.substAlgHom (translationImages_hasSubst h hh)
  invFun := MvPowerSeries.substAlgHom (translationImages_hasSubst (fun j => -h j)
    (by intro j; simp [hh j]))
  left_inv := translation_inverse h hh
  right_inv := by
    intro f
    simpa using translation_inverse (fun j => -h j) (by intro j; simp [hh j]) f

theorem powerSeriesTranslationEquiv_parameter (h : τ → MvPowerSeries σ K)
    (hh : ∀ j, (h j).constantCoeff = 0) (f : MvPowerSeries σ K) :
    powerSeriesTranslationEquiv h hh (MvPowerSeries.rename Sum.inl f) =
      MvPowerSeries.rename Sum.inl f := translation_fixes_parameters h hh f

theorem powerSeriesTranslationEquiv_normal (h : τ → MvPowerSeries σ K)
    (hh : ∀ j, (h j).constantCoeff = 0) (j : τ) :
    powerSeriesTranslationEquiv h hh (MvPowerSeries.X (Sum.inr j)) =
      MvPowerSeries.X (Sum.inr j) + MvPowerSeries.rename Sum.inl (h j) := by
  exact MvPowerSeries.substAlgHom_X (translationImages_hasSubst h hh) _

theorem powerSeriesTranslationEquiv_pderiv_normal (h : τ → MvPowerSeries σ K)
    (hh : ∀ j, (h j).constantCoeff = 0) (j : τ)
    (f : MvPowerSeries (σ ⊕ τ) K) :
    MvPowerSeries.pderiv (Sum.inr j) (powerSeriesTranslationEquiv h hh f) =
      powerSeriesTranslationEquiv h hh (MvPowerSeries.pderiv (Sum.inr j) f) := by
  classical
  let : UniformSpace K := ⊥
  have he : Continuous (powerSeriesTranslationEquiv h hh) := by
    change Continuous (MvPowerSeries.substAlgHom (R := K) (translationImages_hasSubst h hh))
    rw [MvPowerSeries.coe_substAlgHom]
    exact MvPowerSeries.continuous_subst (translationImages_hasSubst h hh)
  apply powerSeries_pderiv_commutes_of_variables (powerSeriesTranslationEquiv h hh).toAlgHom he
  intro k
  change MvPowerSeries.pderiv (Sum.inr j) (powerSeriesTranslationEquiv h hh (MvPowerSeries.X k)) =
    powerSeriesTranslationEquiv h hh (MvPowerSeries.pderiv (Sum.inr j) (MvPowerSeries.X k))
  cases k with
  | inl k =>
    have hk := powerSeriesTranslationEquiv_parameter h hh (MvPowerSeries.X k)
    simp only [MvPowerSeries.rename_X] at hk
    simp [hk, MvPowerSeries.pderiv_X_of_ne]
  | inr k =>
    rw [powerSeriesTranslationEquiv_normal]
    have hp := powerSeries_pderiv_rename_off_image (K := K)
      (Sum.inl : σ → σ ⊕ τ) (Sum.inr j) (by simp) (h k)
    rw [map_add, hp, add_zero]
    by_cases hk : k = j
    · subst k; simp
    · have hne : Sum.inr k ≠ (Sum.inr j : σ ⊕ τ) := by simpa using hk
      simp [MvPowerSeries.pderiv_X_of_ne hne]

theorem powerSeriesTranslationEquiv_jacobian [DecidableEq τ] (h : τ → MvPowerSeries σ K)
    (hh : ∀ j, (h j).constantCoeff = 0)
    (H : τ → MvPowerSeries (σ ⊕ τ) K) :
    Matrix.det (fun i j => MvPowerSeries.pderiv (Sum.inr j)
        (powerSeriesTranslationEquiv h hh (H i))) =
      powerSeriesTranslationEquiv h hh
        (Matrix.det (fun i j => MvPowerSeries.pderiv (Sum.inr j) (H i))) := by
  classical
  rw [AlgEquiv.map_det]
  congr 1
  funext i j
  exact powerSeriesTranslationEquiv_pderiv_normal h hh j (H i)
end LinearStudy
