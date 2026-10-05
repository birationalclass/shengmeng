import JordanChains

noncomputable section
namespace JordanSize
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

abbrev SemilinearSymmetry (σ : K ≃+* K) := by
  letI := RingHomInvPair.of_ringEquiv σ
  letI := RingHomInvPair.of_ringEquiv_symm σ
  exact (V ≃ₛₗ[(σ : K →+* K)] V)

/-- A conjugation (or any semilinear symmetry) carries the entire chain. -/
def conjugateChain (σ : K ≃+* K) (J : SemilinearSymmetry (V:=V) σ)
    (T : Module.End K V) (a : K) (r : ℕ)
    (h : ∀ x, J (T x) = T (J x)) (C : JordanChain T a r) :
    JordanChain T (σ a) r := by
  letI := RingHomInvPair.of_ringEquiv σ
  letI := RingHomInvPair.of_ringEquiv_symm σ
  refine {vectors := fun i => J (C.vectors i), independent := ?_, relation := ?_}
  · exact C.independent.map_of_surjective_injective σ J.toAddEquiv.toAddMonoidHom
      σ.surjective (fun x hx => J.injective (by simpa using hx))
      (fun c x => J.map_smulₛₗ c x)
  · intro i
    have he : (T-(σ a) • 1) (J (C.vectors i)) =
        J ((T-a • 1) (C.vectors i)) := by
      simp [LinearMap.sub_apply, ← h, map_sub, J.map_smulₛₗ]
    rw [he, C.relation]
    split_ifs <;> simp

end JordanSize
