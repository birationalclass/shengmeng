module
public import Linear.AcyclicChainOpcycleSequence
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Homology.ShortComplex.Ab
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {A : Type u} [Category.{v} A] [Abelian A]
/-- Actual native Hom complex,without projectivity or coefficient injectivity. -/
def chainActualHomCochain (K : ChainComplex A ℕ) (F : A) : CochainComplex AddCommGrpCat.{v} ℕ :=
  ((preadditiveYoneda.obj F).mapHomologicalComplex (.up ℕ)).obj K.op
/-- Positive exactness of SAME actual Hom complex extends every opcycle map.
No source projectivity,term acyclicity or preselected extension is a premise. -/
theorem chainActualHomExact_opcycle_extension (K : ChainComplex A ℕ) (F : A)
    (p : ℕ) (hH : (chainActualHomCochain K F).ExactAt (p+1))
    (a : K.opcycles (p+1) ⟶ F) :
    ∃ b : K.X p ⟶ F, K.fromOpcycles (p+1) p ≫ b = a := by
  let H := chainActualHomCochain K F
  let z : H.X (p+1) := K.pOpcycles (p+1) ≫ a
  have hz : H.d (p+1) (p+2) z = 0 := by
    change K.d (p+2) (p+1) ≫ (K.pOpcycles (p+1) ≫ a) = 0
    rw [← Category.assoc,K.d_pOpcycles,zero_comp]
  have hex : (H.sc' p (p+1) (p+2)).Exact :=
    (HomologicalComplex.exactAt_iff' H p (p+1) (p+2) (by simp) (by simp)).mp hH
  obtain ⟨b,hb⟩ := (ShortComplex.ab_exact_iff _).mp hex z hz
  refine ⟨b,?_⟩
  apply (cancel_epi (K.pOpcycles (p+1))).1
  rw [← Category.assoc,K.p_fromOpcycles]
  exact hb
end LinearStudy
