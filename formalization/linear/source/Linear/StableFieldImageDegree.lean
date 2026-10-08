module
public import Linear.FieldEndomorphismDegree
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace LinearStudy

theorem stableField_image_le
    {k F : Type*} [Field k] [Field F] [Algebra k F]
    (E : IntermediateField k F) (φ : F →ₐ[k] F) (σ : E →ₐ[k] E)
    (hc : ∀ a : E, φ (a : F) = (σ a : F)) : E.map φ ≤ E := by
  rintro z ⟨a, ha, rfl⟩
  exact (hc ⟨a, ha⟩).symm ▸ (σ ⟨a, ha⟩).property

/-- The coefficient image field in the actual ambient field has exactly
the degree of the actual restricted endomorphism, with its inclusion constructed. -/
theorem stableField_image_finrank_and_finite
    {k F : Type*} [Field k] [Field F] [Algebra k F]
    (E : IntermediateField k F) (φ : F →ₐ[k] F) (σ : E →ₐ[k] E)
    (hc : ∀ a : E, φ (a : F) = (σ a : F))
    [Module.Finite σ.fieldRange E] :
    letI : Algebra (E.map φ) E :=
      (IntermediateField.inclusion (stableField_image_le E φ σ hc)).toRingHom.toAlgebra
    Module.finrank (E.map φ) E = Module.finrank σ.fieldRange E ∧
      Module.Finite (E.map φ) E := by
  let R := E.map φ
  let S := σ.fieldRange
  let ν := IntermediateField.inclusion (stableField_image_le E φ σ hc)
  letI : Algebra R E := ν.toRingHom.toAlgebra
  let u : S →ₐ[k] R := (E.val.comp S.val).codRestrict R.toSubalgebra (by
    rintro ⟨z, a, rfl⟩
    exact ⟨(a : F), a.property, hc a⟩)
  have hu : Function.Bijective u := by
    refine ⟨u.injective, ?_⟩
    rintro ⟨z, a, ha, rfl⟩
    refine ⟨⟨σ ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    exact (hc ⟨a, ha⟩).symm
  let i := AlgEquiv.ofBijective u hu
  have hcompat : (algebraMap R E).comp i.toRingEquiv.toRingHom = algebraMap S E := by
    ext z
    rfl
  have hr : Module.finrank S E = Module.finrank R E :=
    Algebra.finrank_eq_of_equiv_equiv i.toRingEquiv (RingEquiv.refl E) hcompat
  have hfinS : (algebraMap S E).Finite := RingHom.finite_algebraMap.mpr inferInstance
  have hfinI : i.symm.toRingHom.Finite := RingHom.Finite.of_surjective _ i.symm.surjective
  have hfin := hfinS.comp hfinI
  have he : (algebraMap S E).comp i.symm.toRingHom = algebraMap R E := by
    rw [← hcompat]
    apply RingHom.ext
    intro z
    change ν (i (i.symm z)) = ν z
    rw [i.apply_symm_apply]
  rw [he] at hfin
  exact ⟨hr.symm, RingHom.finite_algebraMap.mp hfin⟩

end LinearStudy
