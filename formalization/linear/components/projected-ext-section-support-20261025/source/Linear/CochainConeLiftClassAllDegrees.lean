module
public import Linear.CochainConeLiftClassBridge
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

/-- Compose ACTUAL cocycles in arbitrary degrees through the native cochain
composition. Closedness follows from the native Hom-complex differential. -/
def actualHomCocycleComp {F G K : CochainComplex A ℤ} {n m p : ℤ}
    (a : Cocycle F G n) (b : Cocycle G K m) (h : n+m=p) : Cocycle F K p :=
  Cocycle.mk (a.val.comp b.val h) (p+1) rfl (by
    rw [δ_comp _ _ h (n+1) (m+1) (p+1) rfl rfl rfl]
    simp only [Cocycle.δ_eq_zero,Cochain.comp_zero,Cochain.zero_comp,smul_zero,add_zero])

/-- In EVERY integer degree,ACTUAL lift equations identify the SAME cone
cohomology class,with the exact native (-1)^q factor. Actual injective lifts
are constructed separately;the arbitrary-r ORIGINAL epsilon still needs iteration. -/
theorem cochainConeLiftClass_allDegrees
    (S : ShortComplex (CochainComplex A ℤ)) (K : CochainComplex A ℤ) (q : ℤ)
    (a : Cocycle S.X₁ K q) (b : Cochain S.X₂ K q) (c : Cocycle S.X₃ K (q+1))
    (hb : (Cochain.ofHom S.f).comp b (zero_add q) = a.val)
    (hc : δ q (q+1) b = (Cochain.ofHom S.g).comp c.val (zero_add (q+1))) :
    CohomologyClass.mk (c.precomp (CochainComplex.mappingCone.descShortComplex S)) =
      CohomologyClass.mk (q.negOnePow •
        actualHomCocycleComp (CochainComplex.mappingCone.fst S.f) a (by omega)) := by
  let x := actualHomCocycleComp (CochainComplex.mappingCone.fst S.f) a
    (show 1+q=q+1 by omega)
  let y := c.precomp (CochainComplex.mappingCone.descShortComplex S)
  let beta := CochainComplex.mappingCone.descCochain S.f
    (0 : Cochain S.X₁ K (q-1)) b (by omega)
  have hd : δ q (q+1) beta = (y-q.negOnePow • x).val := by
    dsimp only [beta]
    rw [CochainComplex.mappingCone.δ_descCochain S.f _ b _ (q+1) rfl]
    simp only [δ_zero,zero_add,hb,hc,Int.negOnePow_succ,Units.neg_smul,
      Cochain.comp_neg,Cochain.comp_units_smul]
    change _ = (Cochain.ofHom (CochainComplex.mappingCone.descShortComplex S)).comp c.val
      (zero_add (q+1)) - q.negOnePow •
        ((CochainComplex.mappingCone.fst S.f).val.comp a.val (show 1+q=q+1 by omega))
    rw [CochainComplex.mappingCone.descShortComplex,CochainComplex.mappingCone.ofHom_desc]
    simp only [CochainComplex.mappingCone.descCochain,Cochain.comp_zero,zero_add]
    erw [Cochain.comp_assoc_of_second_is_zero_cochain]
    abel
  have hz : CohomologyClass.mk (y-q.negOnePow • x) = 0 :=
    (CohomologyClass.mk_eq_zero_iff _).mpr
      ((mem_coboundaries_iff (y-q.negOnePow • x) q rfl).mpr ⟨beta,hd⟩)
  rw [CohomologyClass.mk_sub] at hz
  exact sub_eq_zero.mp hz

end LinearStudy
