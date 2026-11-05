module
public import Linear.PowerSeriesFlatten
public import Linear.PowerSeriesFlattenDerivative
public import Linear.PowerSeriesTranslation
public import Mathlib.Logic.Equiv.Fin.Basic
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy

def totalVariableSplit (r c : ℕ) : Fin (r + c) ≃ Fin r ⊕ Fin c :=
  (finCongr (Nat.add_comm r c)).trans
    ((finSumFinEquiv : Fin c ⊕ Fin r ≃ Fin (c + r)).symm.trans (Equiv.sumComm _ _))

theorem totalVariableSplit_normal (r c : ℕ) (i : Fin c) :
    totalVariableSplit r c (normalVariableIndex r c i) = Sum.inr i := by
  have hi : finCongr (Nat.add_comm r c) (normalVariableIndex r c i) = i.castAdd r := by
    ext; rfl
  simp [totalVariableSplit, hi]

theorem totalVariableSplit_parameter (r c : ℕ) (i : Fin r) :
    totalVariableSplit r c (i.addNat c) = Sum.inl i := by
  have hi : finCongr (Nat.add_comm r c) (i.addNat c) = i.natAdd c := by
    ext; simp [Fin.addNat, Fin.natAdd]; omega
  simp [totalVariableSplit, hi]

def powerSeriesCoordinateChart (K : Type*) [CommRing K] (r c : ℕ) :
    MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K) ≃+*
      MvPowerSeries (Fin r ⊕ Fin c) K :=
  (nestedPowerSeriesEquiv K r c).trans
    (MvPowerSeries.renameEquiv K (totalVariableSplit r c)).toRingEquiv

theorem powerSeriesCoordinateChart_X (K : Type*) [CommRing K] (r c : ℕ) (i : Fin c) :
    powerSeriesCoordinateChart K r c (MvPowerSeries.X i) = MvPowerSeries.X (Sum.inr i) := by
  simp [powerSeriesCoordinateChart, nestedPowerSeriesEquiv_X, totalVariableSplit_normal]

theorem powerSeriesCoordinateChart_C (K : Type*) [CommRing K] (r c : ℕ)
    (f : MvPowerSeries (Fin r) K) :
    powerSeriesCoordinateChart K r c (MvPowerSeries.C f) = MvPowerSeries.rename Sum.inl f := by
  change MvPowerSeries.rename (totalVariableSplit r c)
    (nestedPowerSeriesEquiv K r c (MvPowerSeries.C f)) = _
  rw [nestedPowerSeriesEquiv_C, MvPowerSeries.rename_rename]
  have hi : (totalVariableSplit r c) ∘ (fun i : Fin r => i.addNat c) = Sum.inl := by
    funext i
    exact totalVariableSplit_parameter r c i
  simp only [hi]

theorem powerSeriesCoordinateChart_pderiv (K : Type*) [CommRing K] (r c : ℕ)
    (j : Fin c) (f : MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K)) :
    powerSeriesCoordinateChart K r c (MvPowerSeries.pderiv j f) =
      MvPowerSeries.pderiv (Sum.inr j) (powerSeriesCoordinateChart K r c f) := by
  change MvPowerSeries.rename (totalVariableSplit r c)
    (nestedPowerSeriesEquiv K r c (MvPowerSeries.pderiv j f)) =
      MvPowerSeries.pderiv (Sum.inr j)
        (MvPowerSeries.rename (totalVariableSplit r c) (nestedPowerSeriesEquiv K r c f))
  rw [nestedPowerSeriesEquiv_pderiv]
  simpa only [totalVariableSplit_normal] using
    (powerSeries_pderiv_rename_equiv (totalVariableSplit r c)
      (normalVariableIndex r c j) (nestedPowerSeriesEquiv K r c f)).symm

def nestedPowerSeriesTranslationRingEquiv (K : Type*) [CommRing K] (r c : ℕ)
    (h : Fin c → MvPowerSeries (Fin r) K) (hh : ∀ j, (h j).constantCoeff = 0) :
    MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K) ≃+*
      MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K) :=
  (powerSeriesCoordinateChart K r c).trans
    ((powerSeriesTranslationEquiv h hh).toRingEquiv.trans (powerSeriesCoordinateChart K r c).symm)

theorem nestedPowerSeriesTranslationRingEquiv_C (K : Type*) [CommRing K] (r c : ℕ)
    (h : Fin c → MvPowerSeries (Fin r) K) (hh : ∀ j, (h j).constantCoeff = 0)
    (b : MvPowerSeries (Fin r) K) :
    nestedPowerSeriesTranslationRingEquiv K r c h hh (MvPowerSeries.C b) = MvPowerSeries.C b := by
  apply (powerSeriesCoordinateChart K r c).injective
  change powerSeriesCoordinateChart K r c
    ((powerSeriesCoordinateChart K r c).symm
      (powerSeriesTranslationEquiv h hh
        (powerSeriesCoordinateChart K r c (MvPowerSeries.C b)))) = _
  rw [RingEquiv.apply_symm_apply, powerSeriesCoordinateChart_C,
    powerSeriesTranslationEquiv_parameter]

def nestedPowerSeriesTranslation (K : Type*) [CommRing K] (r c : ℕ)
    (h : Fin c → MvPowerSeries (Fin r) K) (hh : ∀ j, (h j).constantCoeff = 0) :
    MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K) ≃ₐ[MvPowerSeries (Fin r) K]
      MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K) where
  __ := nestedPowerSeriesTranslationRingEquiv K r c h hh
  commutes' := nestedPowerSeriesTranslationRingEquiv_C K r c h hh

theorem nestedPowerSeriesTranslation_X (K : Type*) [CommRing K] (r c : ℕ)
    (h : Fin c → MvPowerSeries (Fin r) K) (hh : ∀ j, (h j).constantCoeff = 0) (j : Fin c) :
    nestedPowerSeriesTranslation K r c h hh (MvPowerSeries.X j) =
      MvPowerSeries.X j + MvPowerSeries.C (h j) := by
  apply (powerSeriesCoordinateChart K r c).injective
  change powerSeriesCoordinateChart K r c
    ((powerSeriesCoordinateChart K r c).symm
      (powerSeriesTranslationEquiv h hh
        (powerSeriesCoordinateChart K r c (MvPowerSeries.X j)))) = _
  rw [RingEquiv.apply_symm_apply, powerSeriesCoordinateChart_X,
    powerSeriesTranslationEquiv_normal, map_add, powerSeriesCoordinateChart_X,
    powerSeriesCoordinateChart_C]

theorem coordinateChart_nestedPowerSeriesTranslation (K : Type*) [CommRing K] (r c : ℕ)
    (h : Fin c → MvPowerSeries (Fin r) K) (hh : ∀ j, (h j).constantCoeff = 0)
    (f : MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K)) :
    powerSeriesCoordinateChart K r c (nestedPowerSeriesTranslation K r c h hh f) =
      powerSeriesTranslationEquiv h hh (powerSeriesCoordinateChart K r c f) := by
  change powerSeriesCoordinateChart K r c
    ((powerSeriesCoordinateChart K r c).symm
      (powerSeriesTranslationEquiv h hh (powerSeriesCoordinateChart K r c f))) = _
  rw [RingEquiv.apply_symm_apply]

theorem nestedPowerSeriesTranslation_pderiv (K : Type*) [CommRing K] (r c : ℕ)
    (h : Fin c → MvPowerSeries (Fin r) K) (hh : ∀ j, (h j).constantCoeff = 0)
    (j : Fin c) (f : MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K)) :
    nestedPowerSeriesTranslation K r c h hh (MvPowerSeries.pderiv j f) =
      MvPowerSeries.pderiv j (nestedPowerSeriesTranslation K r c h hh f) := by
  apply (powerSeriesCoordinateChart K r c).injective
  rw [coordinateChart_nestedPowerSeriesTranslation, powerSeriesCoordinateChart_pderiv,
    powerSeriesCoordinateChart_pderiv, coordinateChart_nestedPowerSeriesTranslation]
  exact (powerSeriesTranslationEquiv_pderiv_normal h hh j _).symm

theorem nestedPowerSeriesTranslation_jacobian (K : Type*) [CommRing K] (r c : ℕ)
    (h : Fin c → MvPowerSeries (Fin r) K) (hh : ∀ j, (h j).constantCoeff = 0)
    (H : Fin c → MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K)) :
    nestedPowerSeriesTranslation K r c h hh
      (Matrix.det (fun i j => MvPowerSeries.pderiv j (H i))) =
      Matrix.det (fun i j => MvPowerSeries.pderiv j
        (nestedPowerSeriesTranslation K r c h hh (H i))) := by
  rw [AlgEquiv.map_det]
  congr 1
  funext i j
  exact nestedPowerSeriesTranslation_pderiv K r c h hh j (H i)
end LinearStudy
