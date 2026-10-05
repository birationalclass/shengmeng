import PerfectPairing

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace JordanSize
variable {K V Z : Type*} [Field K]
 [AddCommGroup V] [Module K V] [AddCommGroup Z] [Module K Z]

/-- The actual normalized image vectors, not an assumed injective map. -/
def transportChain (T : Module.End K V) (R : Module.End K Z)
    (L : V →ₗ[K] Z) (c a : K) (hc : c ≠ 0)
    (h : ∀ x, R (L x) = c • L (T x))
    {r : ℕ} (C : JordanChain T a (r+1))
    (hend : L (C.vectors 0) ≠ 0) : JordanChain R (c*a) (r+1) := by
  let v : Fin (r+1) → Z := fun i => (c⁻¹)^i.val • L (C.vectors i)
  have hrel : ∀ i : Fin (r+1), (R-(c*a) • 1) (v i) =
      if h : i.val=0 then 0 else v ⟨i.val-1, by omega⟩ := by
    intro i
    have he : (R-(c*a) • 1) (L (C.vectors i)) =
        c • L ((T-a • 1) (C.vectors i)) := by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
        h, map_sub, map_smul, smul_sub, smul_smul]
    change (R-(c*a) • 1) ((c⁻¹)^i.val • L (C.vectors i)) = _
    rw [map_smul, he, C.relation]
    split_ifs with hi
    · simp
    · change (c⁻¹)^i.val • (c • L (C.vectors ⟨i.val-1, by omega⟩)) =
        (c⁻¹)^(i.val-1) • L (C.vectors ⟨i.val-1, by omega⟩)
      rw [smul_smul]
      congr 1
      rw [show i.val=(i.val-1)+1 by omega, pow_succ]
      field_simp
      simp
  exact ⟨v, chainRelations_independent R (c*a) v
    (by simpa [v] using hend) hrel, hrel⟩

end JordanSize
