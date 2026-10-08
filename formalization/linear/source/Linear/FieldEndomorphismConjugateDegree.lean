module
public import Linear.FieldEndomorphismDegree
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy

/-- Actual image-field degree is preserved by a commuting field isomorphism. -/
theorem fieldEndomorphism_finrank_conjugate
    {k L M : Type*} [Field k] [Field L] [Field M] [Algebra k L] [Algebra k M]
    (e : L ≃ₐ[k] M) (φ : L →ₐ[k] L) (ψ : M →ₐ[k] M)
    (hc : ∀ x, e (φ x) = ψ (e x)) :
    Module.finrank φ.fieldRange L = Module.finrank ψ.fieldRange M := by
  let S := φ.fieldRange
  let R := ψ.fieldRange
  have hR : S.map e.toAlgHom = R := by
    ext z
    constructor
    · rintro ⟨a, ⟨b, rfl⟩, rfl⟩
      exact ⟨e b, (hc b).symm⟩
    · rintro ⟨a, rfl⟩
      refine ⟨φ (e.symm a), ⟨e.symm a, rfl⟩, ?_⟩
      change e (φ (e.symm a)) = ψ a
      rw [hc, e.apply_symm_apply]
  let i := (S.equivMap e.toAlgHom).trans (IntermediateField.equivOfEq hR)
  exact Algebra.finrank_eq_of_equiv_equiv i.toRingEquiv e.toRingEquiv (by
    apply RingHom.ext
    intro z
    rfl)

end LinearStudy
