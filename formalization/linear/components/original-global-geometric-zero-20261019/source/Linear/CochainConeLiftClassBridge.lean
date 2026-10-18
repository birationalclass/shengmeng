module
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
open CochainComplex.HomComplex
universe u v
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Native cone lift formula. The premises are ACTUAL cochain lifting equations,
not the desired equality of extension classes. This lemma does not yet identify
an original Koszul augmentation or its ordered top functional. -/
theorem cochainConeLiftClassBridge
    (S : ShortComplex (CochainComplex A ℤ)) (K : CochainComplex A ℤ)
    (a : Cocycle S.X₁ K 0) (b : Cochain S.X₂ K 0) (c : Cocycle S.X₃ K 1)
    (hb : (Cochain.ofHom S.f).comp b (zero_add 0) = a.val)
    (hc : δ 0 1 b = (Cochain.ofHom S.g).comp c.val (zero_add 1)) :
    CohomologyClass.mk ((CochainComplex.mappingCone.fst S.f).postcomp (Cocycle.homOf a)) =
      CohomologyClass.mk (c.precomp (CochainComplex.mappingCone.descShortComplex S)) := by
  let x := (CochainComplex.mappingCone.fst S.f).postcomp (Cocycle.homOf a)
  let y := c.precomp (CochainComplex.mappingCone.descShortComplex S)
  let beta := CochainComplex.mappingCone.descCochain S.f
    (0 : Cochain S.X₁ K (-1)) b (by omega)
  have hd : δ 0 1 beta = (y-x).val := by
    dsimp only [beta]
    rw [CochainComplex.mappingCone.δ_descCochain S.f _ b _ 1 rfl]
    simp only [δ_zero,zero_add,hb,hc,Int.negOnePow_one,Units.neg_smul,one_smul,
      Cochain.comp_neg]
    change _ = (Cochain.ofHom (CochainComplex.mappingCone.descShortComplex S)).comp c.val
      (zero_add 1) - (CochainComplex.mappingCone.fst S.f).val.comp
        (Cochain.ofHom (Cocycle.homOf a)) (add_zero 1)
    rw [Cocycle.cochain_ofHom_homOf_eq_coe]
    rw [CochainComplex.mappingCone.descShortComplex,
      CochainComplex.mappingCone.ofHom_desc]
    simp only [CochainComplex.mappingCone.descCochain,Cochain.comp_zero,zero_add]
    erw [Cochain.comp_assoc_of_second_is_zero_cochain]
    abel
  have hz : CohomologyClass.mk (y-x) = 0 :=
    (CohomologyClass.mk_eq_zero_iff _).mpr
      ((mem_coboundaries_iff (y-x) 0 rfl).mpr ⟨beta,hd⟩)
  rw [CohomologyClass.mk_sub] at hz
  exact (sub_eq_zero.mp hz).symm

end LinearStudy
