module
public import Linear.GenericFreeAway
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.TensorProduct.Tower
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace LinearStudy

/-- On a nonempty principal open where an actual module is free, every
field-valued fiber has the original module's generic rank. The residue
map need not be injective. -/
theorem module_tensor_finrank_eq_of_free_away
    {R M K : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Field K] [Algebra R K]
    (r : R) (hr : r ≠ 0)
    [Module.Free (Localization.Away r) (LocalizedModule.Away r M)]
    (hrK : algebraMap R K r ≠ 0) :
    Module.finrank K (K ⊗[R] M) = Module.finrank R M := by
  let Rr := Localization.Away r
  let Mr := LocalizedModule.Away r M
  let ψ : Rr →+* K := IsLocalization.Away.lift r
    (isUnit_iff_ne_zero.mpr hrK)
  letI : Algebra Rr K := ψ.toAlgebra
  letI : IsScalarTower R Rr K := IsScalarTower.of_algebraMap_eq' (by
    exact (IsLocalization.Away.lift_comp (S := Rr) r (isUnit_iff_ne_zero.mpr hrK)).symm)
  letI : IsDomain Rr := Localization.Away.isDomain hr
  let e : K ⊗[Rr] Mr ≃ₗ[K] K ⊗[R] M :=
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K)
      (LocalizedModule.equivTensorProduct (Submonoid.powers r) M)).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R Rr K K M)
  have hp : Submonoid.powers r ≤ nonZeroDivisors R :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hr
  have hd : Module.finrank Rr Mr = Module.finrank R M :=
    (IsLocalization.finrank_eq Rr (Submonoid.powers r) hp).trans
      (IsLocalizedModule.finrank_eq (Submonoid.powers r)
        (LocalizedModule.mkLinearMap (Submonoid.powers r) M) hp)
  exact e.finrank_eq.symm.trans (Module.finrank_baseChange.trans hd)

end LinearStudy
