module
public import Linear.ChainActualHomCycles
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {A : Type u} [Category.{v} A] [Abelian A]
/-- Native coefficient action on SAME actual Hom cochain complex. -/
def chainActualHomCochainCoefficientMap (K : ChainComplex A ℕ) {F G : A} (a : F ⟶ G) :
    chainActualHomCochain K F ⟶ chainActualHomCochain K G :=
  (NatTrans.mapHomologicalComplex (preadditiveYoneda.map a) (.up ℕ)).app K.op
/-- Native kernel/cycles comparison commutes with actual coefficients. -/
theorem chainActualHomCyclesNativeIso_inv_coefficient_naturality
    (K : ChainComplex A ℕ) {F G : A} (a : F ⟶ G) (n : ℕ) :
    (preadditiveYoneda.map a).app (K.op.cycles n) ≫ (chainActualHomCyclesNativeIso K G n).inv =
      (chainActualHomCyclesNativeIso K F n).inv ≫
        HomologicalComplex.cyclesMap (chainActualHomCochainCoefficientMap K a) n := by
  apply (cancel_mono ((chainActualHomCochain K G).iCycles n)).1
  rw [Category.assoc,chainActualHomCyclesNativeIso_inv_iCycles,
    Category.assoc,HomologicalComplex.cyclesMap_i,← Category.assoc,
    chainActualHomCyclesNativeIso_inv_iCycles]
  exact ((preadditiveYoneda.map a).naturality (K.op.iCycles n)).symm
/-- The SAME actual Hom-cycles/original-opcycles inverse preserves
coefficient maps;native opposite/cycle comparison is retained. -/
theorem chainActualHomCyclesOpcyclesIso_inv_coefficient_naturality
    (K : ChainComplex A ℕ) {F G : A} (a : F ⟶ G) (n : ℕ) :
    (preadditiveYoneda.map a).app (op (K.opcycles n)) ≫
      (chainActualHomCyclesOpcyclesIso K G n).inv =
      (chainActualHomCyclesOpcyclesIso K F n).inv ≫
        HomologicalComplex.cyclesMap (chainActualHomCochainCoefficientMap K a) n := by
  dsimp only [chainActualHomCyclesOpcyclesIso,Iso.trans_inv,Functor.mapIso_inv]
  rw [← Category.assoc,← (preadditiveYoneda.map a).naturality (K.cyclesOpIso n).inv,
    Category.assoc,chainActualHomCyclesNativeIso_inv_coefficient_naturality]
  simp only [Category.assoc]
/-- Forward SAME actual Hom-cycles/opcycles comparison naturality. -/
theorem chainActualHomCyclesOpcyclesIso_coefficient_naturality
    (K : ChainComplex A ℕ) {F G : A} (a : F ⟶ G) (n : ℕ) :
    HomologicalComplex.cyclesMap (chainActualHomCochainCoefficientMap K a) n ≫
      (chainActualHomCyclesOpcyclesIso K G n).hom =
      (chainActualHomCyclesOpcyclesIso K F n).hom ≫
        (preadditiveYoneda.map a).app (op (K.opcycles n)) := by
  apply (cancel_mono (chainActualHomCyclesOpcyclesIso K G n).inv).1
  rw [Category.assoc,Iso.hom_inv_id,Category.comp_id,Category.assoc,
    chainActualHomCyclesOpcyclesIso_inv_coefficient_naturality,← Category.assoc,
    Iso.hom_inv_id,Category.id_comp]
end LinearStudy
