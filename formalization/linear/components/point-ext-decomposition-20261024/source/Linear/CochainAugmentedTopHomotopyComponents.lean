module
public import Linear.CochainSingleSupportComponents
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
open CochainComplex.HomComplex
universe u v
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- ACTUAL source homotopy components give the original lifting recursion
in every intermediate degree,with the exact Hom-complex sign. -/
theorem cochainAugmentedTopHomotopy_middle
    {K L : CochainComplex A ℤ} {E N : A} (q j : ℤ)
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E)
    (c : Cocycle ((CochainComplex.singleFunctor A 0).obj E) L q)
    (a : K.X (-q) ⟶ N) (phi : (CochainComplex.singleFunctor A 0).obj N ⟶ L)
    (t : Cochain K L (q-1))
    (ht : δ (q-1) q t = (c.precomp alpha).val -
      (Cochain.toSingleMk a (show -q+q=0 by omega)).comp (Cochain.ofHom phi) (add_zero q))
    (hj0 : j ≠ 0) (hjq : j ≠ -q) :
    t.v j (j+q-1) (by omega) ≫ L.d (j+q-1) (j+q) +
      q.negOnePow • K.d j (j+1) ≫ t.v (j+1) (j+q) (by omega) = 0 := by
  have hv := congrArg (fun z : Cochain K L q => z.v j (j+q) rfl) ht
  rw [δ_v (q-1) q (by omega) t j (j+q) rfl (j+q-1) (j+1) rfl rfl] at hv
  rw [Cochain.sub_v,cochainSingleAugmentation_precomp_v_zero q j (j+q) rfl alpha c hj0,
    cochainTopFunctional_postcomp_v_zero q j (j+q) rfl a phi hjq,sub_self] at hv
  exact hv

/-- The top component starts from the SAME actual top functional. The
negative resolution term is zero;the native (-1)^q sign is retained. -/
theorem cochainAugmentedTopHomotopy_top
    {K L : CochainComplex A ℤ} {E N : A} (q : ℤ) (hq : 0 < q)
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E)
    (c : Cocycle ((CochainComplex.singleFunctor A 0).obj E) L q)
    (a : K.X (-q) ⟶ N) (phi : (CochainComplex.singleFunctor A 0).obj N ⟶ L)
    (t : Cochain K L (q-1))
    (ht : δ (q-1) q t = (c.precomp alpha).val -
      (Cochain.toSingleMk a (show -q+q=0 by omega)).comp (Cochain.ofHom phi) (add_zero q))
    (hL : IsZero (L.X (-1))) :
    q.negOnePow • K.d (-q) (-q+1) ≫ t.v (-q+1) 0 (by omega) =
      -(a ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N).inv ≫ phi.f 0) := by
  have hv := congrArg (fun z : Cochain K L q => z.v (-q) 0 (by omega)) ht
  rw [δ_v (q-1) q (by omega) t (-q) 0 (by omega) (-1) (-q+1) rfl rfl,
    hL.eq_of_tgt (t.v (-q) (-1) (by omega)) 0,zero_comp,zero_add,Cochain.sub_v,
    cochainSingleAugmentation_precomp_v_zero q (-q) 0 (by omega) alpha c (by omega),
    zero_sub,Cochain.comp_zero_cochain_v,Cochain.toSingleMk_v,Cochain.ofHom_v] at hv
  simpa only [Preadditive.neg_comp,Category.assoc] using hv

/-- The bottom component ends at the SAME actual augmentation and cocycle,
when the source has zero next differential. -/
theorem cochainAugmentedTopHomotopy_bottom
    {K L : CochainComplex A ℤ} {E N : A} (q : ℤ) (hq : 0 < q)
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E)
    (c : Cocycle ((CochainComplex.singleFunctor A 0).obj E) L q)
    (a : K.X (-q) ⟶ N) (phi : (CochainComplex.singleFunctor A 0).obj N ⟶ L)
    (t : Cochain K L (q-1))
    (ht : δ (q-1) q t = (c.precomp alpha).val -
      (Cochain.toSingleMk a (show -q+q=0 by omega)).comp (Cochain.ofHom phi) (add_zero q))
    (hK : K.d 0 1 = 0) :
    t.v 0 (q-1) (zero_add (q-1)) ≫ L.d (q-1) q =
      alpha.f 0 ≫ c.val.v 0 q (zero_add q) := by
  have hv := congrArg (fun z : Cochain K L q => z.v 0 q (zero_add q)) ht
  rw [δ_v (q-1) q (by omega) t 0 q (zero_add q) (q-1) 1 rfl rfl,hK,
    zero_comp,smul_zero,add_zero,Cochain.sub_v,
    cochainTopFunctional_postcomp_v_zero q 0 q (zero_add q) a phi (by omega),sub_zero] at hv
  change _ = ((Cochain.ofHom alpha).comp c.val (zero_add q)).v 0 q (zero_add q) at hv
  rw [Cochain.zero_cochain_comp_v,Cochain.ofHom_v] at hv
  exact hv

end LinearStudy
