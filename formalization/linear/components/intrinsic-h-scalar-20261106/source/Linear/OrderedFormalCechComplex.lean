/- Copyright (c) 2026 Chris Birkbeck. Released under Apache2.0.
Generic extraction of the already reviewed original ordered Cech alternating-sum proof. -/
module
public import Linear.ModuleOrderedBaseCech
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
universe u v w
variable {X : Scheme.{u}} {D : Type w} [Category.{v} D] [Preadditive D]
variable {ι : Type u} [LinearOrder ι]
/-- Ordered formal intersections with ANY actual contravariant coefficient functor. -/
def orderedFormalCechObject (F : (FormalCoproduct.{u} X.Opens)ᵒᵖ ⥤ D)
    (U : ι → X.Opens) (n : ℕ) : D := F.obj (op (orderedCechFormalObject U n))
/-- The actual original ordered face induces a coefficient coface. -/
def orderedFormalCechCoface (F : (FormalCoproduct.{u} X.Opens)ᵒᵖ ⥤ D)
    (U : ι → X.Opens) (n : ℕ) (k : Fin (n+2)) :
    orderedFormalCechObject F U n ⟶ orderedFormalCechObject F U (n+1) :=
  F.map (orderedCechFace U n k).op
theorem orderedFormalCechCoface_comp (F : (FormalCoproduct.{u} X.Opens)ᵒᵖ ⥤ D)
    (U : ι → X.Opens) (n : ℕ) {i j : Fin (n+2)} (hij : i ≤ j) :
    orderedFormalCechCoface F U n i ≫ orderedFormalCechCoface F U (n+1) j.succ =
      orderedFormalCechCoface F U n j ≫ orderedFormalCechCoface F U (n+1) i.castSucc := by
  dsimp only [orderedFormalCechCoface]
  rw [← F.map_comp,← F.map_comp,← op_comp,← op_comp,orderedCechFace_comp U n hij]
theorem orderedFormalCechCoface_comp' (F : (FormalCoproduct.{u} X.Opens)ᵒᵖ ⥤ D)
    (U : ι → X.Opens) (n : ℕ) {i : Fin (n+3)} {j : Fin (n+2)} (hij : i ≤ j.castSucc) :
    orderedFormalCechCoface F U n (i.castLT (lt_of_le_of_lt hij j.is_lt)) ≫
      orderedFormalCechCoface F U (n+1) j.succ =
    orderedFormalCechCoface F U n j ≫ orderedFormalCechCoface F U (n+1) i := by
  have hle : i.castLT (lt_of_le_of_lt hij j.is_lt) ≤ j := by
    rw [Fin.le_iff_val_le_val] at hij ⊢
    exact hij
  simpa using orderedFormalCechCoface_comp F U n hle
/-- The SAME original integer signs on the ordered coefficient cochain differential. -/
def orderedFormalCechDifferential (F : (FormalCoproduct.{u} X.Opens)ᵒᵖ ⥤ D)
    (U : ι → X.Opens) (n : ℕ) :
    orderedFormalCechObject F U n ⟶ orderedFormalCechObject F U (n+1) :=
  ∑ k : Fin (n+2), (-1 : ℤ) ^ (k : ℕ) • orderedFormalCechCoface F U n k
theorem orderedFormalCechDifferential_comp (F : (FormalCoproduct.{u} X.Opens)ᵒᵖ ⥤ D)
    (U : ι → X.Opens) (n : ℕ) :
    orderedFormalCechDifferential F U n ≫ orderedFormalCechDifferential F U (n+1) = 0 := by
  dsimp [orderedFormalCechDifferential]
  simp only [comp_sum, sum_comp, ← Finset.sum_product']
  let P := Fin (n + 3) × Fin (n + 2)
  let T : Finset P := {ij : P | (ij.1 : ℕ) ≤ (ij.2 : ℕ)}
  rw [Finset.univ_product_univ, ← Finset.sum_add_sum_compl T,
    ← eq_neg_iff_add_eq_zero, ← Finset.sum_neg_distrib]
  let φ : ∀ ij : P, ij ∈ T → P := fun ij hij =>
    (ij.2.succ, Fin.castLT ij.1
      (lt_of_le_of_lt (Finset.mem_filter.mp hij).right (Fin.is_lt ij.2)))
  apply Finset.sum_bij φ
  · intro ij hij
    simp_rw [T, φ, Finset.compl_filter, Finset.mem_filter_univ,
      Fin.val_succ, Fin.val_castLT] at hij ⊢
    omega
  · rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    rw [Prod.mk_inj]
    exact ⟨by simpa [φ, Fin.castSucc_castLT] using!
        congr_arg Fin.castSucc (congr_arg Prod.snd h),
      by simpa [φ] using! congr_arg Prod.fst h⟩
  · rintro ⟨i', j'⟩ hij'
    simp_rw [T, Finset.compl_filter, Finset.mem_filter_univ,
      not_le] at hij'
    refine ⟨(Fin.castSucc j', i'.pred (by
      rintro rfl
      simp only [Fin.val_zero, not_lt_zero] at hij')), ?_, ?_⟩
    · simpa [T] using! Nat.le_sub_one_of_lt hij'
    · simp only [φ, Fin.succ_pred, Fin.castLT_castSucc]
  · rintro ⟨i, j⟩ hij
    dsimp
    simp only [zsmul_comp, comp_zsmul, smul_smul, ← neg_smul]
    congr 1
    · simp only [φ, Fin.val_succ, Fin.val_castLT, pow_add, pow_one,
        mul_neg, neg_mul, neg_neg, mul_one]
      apply mul_comm
    · rw [orderedFormalCechCoface_comp' F U n]
      simpa [T] using! hij


/-- The actual ordered coefficient cochain complex in any preadditive target. -/
def orderedFormalCechComplex (F : (FormalCoproduct.{u} X.Opens)ᵒᵖ ⥤ D)
    (U : ι → X.Opens) : CochainComplex D ℕ :=
  CochainComplex.of (orderedFormalCechObject F U) (orderedFormalCechDifferential F U)
    (orderedFormalCechDifferential_comp F U)
@[simp] theorem orderedFormalCechComplex_X (F : (FormalCoproduct.{u} X.Opens)ᵒᵖ ⥤ D)
    (U : ι → X.Opens) (n : ℕ) : (orderedFormalCechComplex F U).X n =
    orderedFormalCechObject F U n := rfl
@[simp] theorem orderedFormalCechComplex_d (F : (FormalCoproduct.{u} X.Opens)ᵒᵖ ⥤ D)
    (U : ι → X.Opens) (n : ℕ) : (orderedFormalCechComplex F U).d n (n+1) =
    orderedFormalCechDifferential F U n := by simp [orderedFormalCechComplex]
end LinearStudy
