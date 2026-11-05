module
public import Linear.ChainExactOfAllHomExact
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
universe u v
/-- An actual degree-zero isomorphism with the SAME relations gives an actual
opcycle-zero isomorphism.Relation compatibility is required explicitly. -/
theorem chain_opcycles_zero_isIso_of_same_relations {A : Type u} [Category.{v} A] [Abelian A]
    {K L : ChainComplex A ℕ} (f : K ⟶ L) [IsIso (f.f 0)]
    (h : ∀ (M : A) (a : L.X 0 ⟶ M),
      K.d 1 0 ≫ f.f 0 ≫ a = 0 → L.d 1 0 ≫ a = 0) :
    IsIso (HomologicalComplex.opcyclesMap f 0) := by
  let b := inv (f.f 0) ≫ K.pOpcycles 0
  have hb : L.d 1 0 ≫ b = 0 := by
    apply h _ b
    dsimp [b]
    simp only [IsIso.hom_inv_id_assoc,K.d_pOpcycles]
  let g := L.descOpcycles b 1 (by simp) hb
  refine ⟨⟨g,?_,?_⟩⟩
  · apply (cancel_epi (K.pOpcycles 0)).mp
    simp only [Category.assoc,HomologicalComplex.p_opcyclesMap_assoc]
    dsimp [g]
    rw [HomologicalComplex.p_descOpcycles]
    simp [b]
  · apply (cancel_epi (L.pOpcycles 0)).mp
    dsimp [g]
    rw [← Category.assoc,HomologicalComplex.p_descOpcycles]
    simp only [b,Category.assoc,HomologicalComplex.p_opcyclesMap,IsIso.inv_hom_id_assoc,
      Category.comp_id]
/-- SAME degree-zero relations imply actual degree-zero quasi-isomorphism. -/
theorem chain_quasiIsoAt_zero_of_same_relations {A : Type u} [Category.{v} A] [Abelian A]
    {K L : ChainComplex A ℕ} (f : K ⟶ L) [IsIso (f.f 0)]
    (h : ∀ (M : A) (a : L.X 0 ⟶ M),
      K.d 1 0 ≫ f.f 0 ≫ a = 0 → L.d 1 0 ≫ a = 0) : QuasiIsoAt f 0 := by
  letI := chain_opcycles_zero_isIso_of_same_relations f h
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact IsIso.of_isIso_fac_right (HomologicalComplex.homologyι_naturality f 0)
end LinearStudy
