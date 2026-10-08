module
public import Linear.ProjectiveFiberRepresentativeRelation
public import Linear.ProjectiveAffineFiberPointEquiv
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy

/-- The actual normalized-point equivalence, with its point action exposed
so that evaluation relations can be transported rather than merely counted. -/
theorem projectiveAffineFiber_whole_point_equiv_action {n : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n) (y : Fin n → ℂ)
    (hy : normalizedProjectivePoint y ∈ V.zeroSet)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (hchart : ∀ (v : CoordinateVector n) (hv : v ≠ 0),
      f.onPoints (Projectivization.mk ℂ v hv) = normalizedProjectivePoint y → v 0 ≠ 0) :
    ∃ e : MvPolynomial.zeroLocus ℂ (projectiveAffineFiberIdeal f V y) ≃
        (f.onPoints ⁻¹' {normalizedProjectivePoint y}),
      ∀ a, (e a).val=normalizedProjectivePoint a.val := by
  let j : MvPolynomial.zeroLocus ℂ (projectiveAffineFiberIdeal f V y) →
      (f.onPoints ⁻¹' {normalizedProjectivePoint y}) := fun a =>
    ⟨normalizedProjectivePoint a.val,(projectiveAffineFiberIdeal_point f V y a.val a.property).2.2⟩
  have hinj : Function.Injective j := by
    intro a b hab
    exact Subtype.ext (normalizedProjectivePoint_injective (congrArg Subtype.val hab))
  have hsurj : Function.Surjective j := by
    intro z
    let v := z.val.rep
    have hv : v ≠ 0 := Projectivization.rep_nonzero z.val
    have hfz : f.onPoints (Projectivization.mk ℂ v hv)=normalizedProjectivePoint y := by
      rw [Projectivization.mk_rep]
      exact z.property
    have hv0 := hchart v hv hfz
    let a := fun i : Fin n => v i.succ/v 0
    have hnorm := normalizedProjectivePoint_coordinate_ratios v hv hv0
    have hfa : f.onPoints (normalizedProjectivePoint a)=normalizedProjectivePoint y := by
      rw [hnorm]
      exact hfz
    have ha : normalizedProjectivePoint a ∈ V.zeroSet := by
      rw [←hV]
      change f.onPoints (normalizedProjectivePoint a) ∈ V.zeroSet
      rwa [hfa]
    refine ⟨⟨a,projectiveAffineFiberIdeal_mem_of_point f V y a ha hfa⟩,?_⟩
    apply Subtype.ext
    exact hnorm.trans (Projectivization.mk_rep z.val)
  exact ⟨Equiv.ofBijective j ⟨hinj,hsurj⟩,fun _ => rfl⟩

/-- The manuscript relation on the ACTUAL whole PROJECTIVE point fiber,
for every chosen nonzero coordinate representative. Its indexing set is
not replaced silently by an unspecified affine subset. -/
theorem projective_whole_point_fiber_arbitrary_representative_relation {n r : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n) (y : Fin n → ℂ)
    (hy : normalizedProjectivePoint y ∈ V.zeroSet)
    (hV : f.onPoints ⁻¹' V.zeroSet=V.zeroSet)
    (hchart : ∀ (v : CoordinateVector n) (hv : v ≠ 0),
      f.onPoints (Projectivization.mk ℂ v hv)=normalizedProjectivePoint y → v 0 ≠ 0)
    (hrel : ProjectiveWholeFiberHomogeneousRelationConclusion f V y r) :
    let S := f.onPoints ⁻¹' {normalizedProjectivePoint y}
    ∃ hS : S.Finite,
      letI : Fintype S := hS.fintype
      ∀ (v : S → CoordinateVector n) (hv : ∀ x, v x ≠ 0),
        (∀ x, Projectivization.mk ℂ (v x) (hv x)=x.val) →
        ∃ weights : S → ℂ, (∀ x,weights x ≠ 0) ∧
          ∀ P : CoordinateRing n, P.IsHomogeneous (r*(f.degree-1)-1) →
            ∑ x : S, weights x*MvPolynomial.eval (v x) P=0 := by
  classical
  intro S
  obtain ⟨e,he⟩ := projectiveAffineFiber_whole_point_equiv_action f V y hy hV hchart
  obtain ⟨hA,hArep⟩ := projective_whole_fiber_arbitrary_representative_relation f V y hrel
  let A := MvPolynomial.zeroLocus ℂ (projectiveAffineFiberIdeal f V y)
  letI : Fintype A := hA.fintype
  letI : Fintype S := Fintype.ofEquiv A e
  have hS : S.Finite := Set.toFinite S
  refine ⟨hS,?_⟩
  letI : Fintype S := hS.fintype
  intro v hv hrep
  obtain ⟨lam,hlam,hpoly⟩ := hArep (fun a => v (e a)) (fun a => hv (e a))
    (fun a => (hrep (e a)).trans (he a))
  refine ⟨fun x => lam (e.symm x),fun x => hlam _,?_⟩
  intro P hP
  have hh := hpoly P hP
  rw [← e.sum_comp (fun x => lam (e.symm x)*MvPolynomial.eval (v x) P)]
  simpa only [Equiv.symm_apply_apply] using hh

end LinearStudy
