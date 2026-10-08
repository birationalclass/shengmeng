module
public import Linear.FreeAwayFiberRank
public import Mathlib.RingTheory.Localization.Module
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace LinearStudy

/-- Localizing an algebra over a target element does not change a
field-valued fiber where that element is nonzero. All actions come from
the original algebra map and its actual induced localization map. -/
theorem localizedAlgebra_fiber_equiv
    {R A K : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Field K] [Algebra R K] (b : R) (hbK : algebraMap R K b ≠ 0) :
    let Rb := Localization.Away b
    let Ab := Localization.Away (algebraMap R A b)
    let ψ := Localization.awayMapₐ (Algebra.ofId R A) b
    let τ : Rb →+* K := IsLocalization.Away.lift b (isUnit_iff_ne_zero.mpr hbK)
    letI : Algebra Rb Ab := ψ.toRingHom.toAlgebra
    letI : SMul Rb Ab := ψ.toRingHom.toAlgebra.toSMul
    letI : Module Rb Ab := Algebra.toModule
    letI : Algebra Rb K := τ.toAlgebra
    Nonempty ((K ⊗[Rb] Ab) ≃ₗ[K] K ⊗[R] A) := by
  dsimp only
  let Rb := Localization.Away b
  let Ab := Localization.Away (algebraMap R A b)
  let ψ := Localization.awayMapₐ (Algebra.ofId R A) b
  let τ : Rb →+* K := IsLocalization.Away.lift b (isUnit_iff_ne_zero.mpr hbK)
  letI : Algebra Rb Ab := ψ.toRingHom.toAlgebra
  letI : SMul Rb Ab := ψ.toRingHom.toAlgebra.toSMul
  letI : Module Rb Ab := Algebra.toModule
  letI : Algebra Rb K := τ.toAlgebra
  letI : IsScalarTower R Rb Ab := IsScalarTower.of_algHom ψ
  letI : IsScalarTower R Rb K := IsScalarTower.of_algebraMap_eq' (by
    exact (IsLocalization.Away.lift_comp (S := Rb) b (isUnit_iff_ne_zero.mpr hbK)).symm)
  let l : A →ₗ[R] Ab := (Algebra.linearMap A Ab).restrictScalars R
  letI : IsLocalizedModule (Submonoid.powers b) l :=
    IsLocalizedModule.restrictScalars_powers b (Algebra.linearMap A Ab)
  let e : Rb ⊗[R] A ≃ₗ[Rb] Ab :=
    (IsLocalizedModule.isBaseChange (Submonoid.powers b) Rb l).equiv
  exact ⟨(TensorProduct.AlgebraTensorModule.congr (.refl K K) e.symm).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R Rb K K A)⟩

/-- The same localization retains the actual original generic rank. -/
theorem localizedAlgebra_finrank_eq
    {R A : Type*} [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]
    (b : R) (hb : b ≠ 0) :
    let Rb := Localization.Away b
    let Ab := Localization.Away (algebraMap R A b)
    let ψ := Localization.awayMapₐ (Algebra.ofId R A) b
    letI : Algebra Rb Ab := ψ.toRingHom.toAlgebra
    letI : SMul Rb Ab := ψ.toRingHom.toAlgebra.toSMul
    letI : Module Rb Ab := Algebra.toModule
    Module.finrank Rb Ab = Module.finrank R A := by
  dsimp only
  let Rb := Localization.Away b
  let Ab := Localization.Away (algebraMap R A b)
  let ψ := Localization.awayMapₐ (Algebra.ofId R A) b
  letI : Algebra Rb Ab := ψ.toRingHom.toAlgebra
  letI : SMul Rb Ab := ψ.toRingHom.toAlgebra.toSMul
  letI : Module Rb Ab := Algebra.toModule
  letI : IsScalarTower R Rb Ab := IsScalarTower.of_algHom ψ
  let l : A →ₗ[R] Ab := (Algebra.linearMap A Ab).restrictScalars R
  letI : IsLocalizedModule (Submonoid.powers b) l :=
    IsLocalizedModule.restrictScalars_powers b (Algebra.linearMap A Ab)
  have hp : Submonoid.powers b ≤ nonZeroDivisors R :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hb
  exact (IsLocalization.finrank_eq Rb (Submonoid.powers b) hp).trans
    (IsLocalizedModule.finrank_eq (Submonoid.powers b) l hp)

end LinearStudy
