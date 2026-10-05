import JordanFactors
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

noncomputable section
universe u
namespace JordanSize
variable {K : Type*} [Field K] [IsAlgClosed K]

/-- Evaluation as the ordinary bilinear map `(L,x) ↦ L x`. -/
def evalBilinear {V Z : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup Z] [Module K Z] : (V →ₗ[K] Z) →ₗ[K] V →ₗ[K] Z where
  toFun L := L
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Every equivariant multilinear map intertwines the unipotent parts.
No associativity assumption on the given multilinear map is used. -/
theorem unipotent_multilinear (n : ℕ) {M : Fin n → Type u} {Z : Type u}
    [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    [∀ i, FiniteDimensional K (M i)]
    [AddCommGroup Z] [Module K Z] [FiniteDimensional K Z]
    (B : MultilinearMap K M Z) (T : ∀ i, Module.End K (M i))
    (R : Module.End K Z) (FT : ∀ i, Factors (T i)) (FR : Factors R)
    (hB : ∀ x, R (B x) = B (fun i => T i (x i))) (x : ∀ i, M i) :
    FR.u (B x) = B (fun i => (FT i).u (x i)) := by
  induction n generalizing Z with
  | zero =>
    have hx : (fun i => T i (x i)) = x := by funext i; exact Fin.elim0 i
    have hu : (fun i => (FT i).u (x i)) = x := by funext i; exact Fin.elim0 i
    rw [hu]
    apply FR.fixed
    simpa only [hx] using hB x
  | succ n ih =>
    let eT : M (Fin.last n) ≃ₗ[K] M (Fin.last n) :=
      LinearEquiv.ofBijective (T (Fin.last n))
        ((Module.End.isUnit_iff _).mp (FT (Fin.last n)).T_unit)
    let eR : Z ≃ₗ[K] Z :=
      LinearEquiv.ofBijective R ((Module.End.isUnit_iff _).mp FR.T_unit)
    let e : (M (Fin.last n) →ₗ[K] Z) ≃ₗ[K] (M (Fin.last n) →ₗ[K] Z) :=
      LinearEquiv.arrowCongr eT eR
    let A : Module.End K (M (Fin.last n) →ₗ[K] Z) := e.toLinearMap
    have hA : IsUnit A := (Module.End.isUnit_iff A).mpr e.bijective
    let FA : Factors A := jordanFactors A hA
    have hcur : ∀ y, A (B.curryRight y) =
        B.curryRight (fun i => T i.castSucc (y i)) := by
      intro y
      ext z
      change R (B (Fin.snoc y (eT.symm z))) =
        B (Fin.snoc (fun i => T i.castSucc (y i)) z)
      rw [hB]
      congr 1
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [eT] using eT.apply_symm_apply z
      · simp
    have heval : ∀ (L : M (Fin.last n) →ₗ[K] Z) z,
        R (evalBilinear L z) = evalBilinear (A L) (T (Fin.last n) z) := by
      intro L z
      change R (L z) = R (L (eT.symm (eT z)))
      rw [eT.symm_apply_apply]
    have h := unipotent_bilinear evalBilinear A (T (Fin.last n)) R
      FA (FT (Fin.last n)) FR heval (B.curryRight (Fin.init x)) (x (Fin.last n))
    change FR.u (B (Fin.snoc (Fin.init x) (x (Fin.last n)))) =
      (FA.u (B.curryRight (Fin.init x))) ((FT (Fin.last n)).u (x (Fin.last n))) at h
    rw [ih B.curryRight (fun i => T i.castSucc) A (fun i => FT i.castSucc) FA
      hcur (Fin.init x)] at h
    have hx' : Fin.snoc (fun i => (FT i.castSucc).u (Fin.init x i))
        ((FT (Fin.last n)).u (x (Fin.last n))) =
        (fun i => (FT i).u (x i)) := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [Fin.init]
    simpa only [MultilinearMap.curryRight_apply, Fin.snoc_init_self, hx'] using h

end JordanSize
#print axioms JordanSize.unipotent_multilinear
