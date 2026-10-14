module
public import Linear.FinitePiDualEquiv
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace LinearStudy
variable {R I J : Type*} [CommRing R]
variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (P : I → Type*) (Q : J → Type*)
variable [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)]
variable [∀ j, AddCommGroup (Q j)] [∀ j, Module R (Q j)]

/-- The ACTUAL dual of an original tuple map in its canonical component
coordinates. The coordinate equivalences are constructed universal maps. -/
def finitePiDualComponentMap (T : (∀ i, P i) →ₗ[R] (∀ j, Q j)) :
    (∀ j, Module.Dual R (Q j)) →ₗ[R] (∀ i, Module.Dual R (P i)) :=
  (finitePiDualEquiv P).symm.toLinearMap.comp
    (T.dualMap.comp (finitePiDualEquiv Q).toLinearMap)

/-- The original dual component is the sum of original entry pairings
on each actual coordinate inclusion. -/
theorem finitePiDualComponentMap_apply (T : (∀ i, P i) →ₗ[R] (∀ j, Q j))
    (φ : ∀ j, Module.Dual R (Q j)) (i : I) (x : P i) :
    finitePiDualComponentMap P Q T φ i x = ∑ j, φ j (T (Pi.single i x) j) := by
  change ((finitePiDualEquiv P).symm
    (T.dualMap (finitePiDualEquiv Q φ))) i x = _
  have he := congrArg (fun ψ : Module.Dual R (∀ i, P i) => ψ (Pi.single i x))
    ((finitePiDualEquiv P).apply_symm_apply (T.dualMap (finitePiDualEquiv Q φ)))
  calc
    ((finitePiDualEquiv P).symm (T.dualMap (finitePiDualEquiv Q φ))) i x =
        T.dualMap (finitePiDualEquiv Q φ) (Pi.single i x) := by
      simpa only [finitePiDualEquiv_single] using he
    _ = ∑ j, φ j (T (Pi.single i x) j) := by
      change finitePiDualEquiv Q φ (T (Pi.single i x)) = _
      exact finitePiDualEquiv_apply Q φ (T (Pi.single i x))

/-- The coordinate matrix consists precisely of the transposes of the
original entries proj_j T single_i. No matrix comparison is an input. -/
theorem finitePiDualComponentMap_entries (T : (∀ i, P i) →ₗ[R] (∀ j, Q j))
    (φ : ∀ j, Module.Dual R (Q j)) (i : I) :
    finitePiDualComponentMap P Q T φ i =
      ∑ j, ((LinearMap.proj j).comp (T.comp (LinearMap.single R P i))).dualMap (φ j) := by
  apply LinearMap.ext
  intro x
  rw [finitePiDualComponentMap_apply]
  simp only [LinearMap.sum_apply,LinearMap.dualMap_apply,LinearMap.comp_apply,
    LinearMap.proj_apply,LinearMap.single_apply]

/-- The constructed finite component transpose commutes with the
original assembled dual map. -/
theorem finitePiDualComponentMap_square (T : (∀ i, P i) →ₗ[R] (∀ j, Q j)) :
    (finitePiDualEquiv P).toLinearMap.comp (finitePiDualComponentMap P Q T) =
      T.dualMap.comp (finitePiDualEquiv Q).toLinearMap := by
  apply LinearMap.ext
  intro φ
  exact (finitePiDualEquiv P).apply_symm_apply (T.dualMap (finitePiDualEquiv Q φ))

end LinearStudy
