module
public import Linear.NativeProjectiveChart
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
namespace LinearStudy
variable {K S : Type*} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]

/-- The actual local generator map of the positive projective twist
on the native degree-zero chart D_+(a). Its target is the ACTUAL away
localization, and its source the ACTUAL homogeneous chart ring. -/
def nativeHomogeneousAwayTwistMap (a : S) (m : ℕ) :
    HomogeneousLocalization.Away 𝓑 a →ₗ[HomogeneousLocalization.Away 𝓑 a]
      Localization.Away a :=
  (algebraMap S (Localization.Away a) a)^m •
    Algebra.linearMap (HomogeneousLocalization.Away 𝓑 a) (Localization.Away a)

theorem nativeHomogeneousAwayTwistMap_apply (a : S) (m : ℕ)
    (z : HomogeneousLocalization.Away 𝓑 a) :
    nativeHomogeneousAwayTwistMap 𝓑 a m z =
      (algebraMap S (Localization.Away a) a)^m*z.val := rfl

/-- The actual positive-twist chart map is injective. This proof uses
the native homogeneous-fraction embedding and the actual inverted element. -/
theorem nativeHomogeneousAwayTwistMap_injective (a : S) (m : ℕ) :
    Function.Injective (nativeHomogeneousAwayTwistMap 𝓑 a m) := by
  have ha : IsUnit (algebraMap S (Localization.Away a) a) :=
    IsLocalization.map_units (M := Submonoid.powers a)
      (Localization.Away a) ⟨a,⟨1,by simp⟩⟩
  intro x y hxy
  apply HomogeneousLocalization.val_injective (Submonoid.powers a)
  exact (ha.pow m).mul_left_cancel hxy

/-- The ACTUAL degree-m chart module, realized as a rank-one image in
the full native localization. Identifying it with a global O(m) sheaf
requires the separate restriction/gluing construction. -/
def nativeHomogeneousAwayTwistModule (a : S) (m : ℕ) :
    Submodule (HomogeneousLocalization.Away 𝓑 a) (Localization.Away a) :=
  LinearMap.range (nativeHomogeneousAwayTwistMap 𝓑 a m)

def nativeHomogeneousAwayTwistEquiv (a : S) (m : ℕ) :
    HomogeneousLocalization.Away 𝓑 a ≃ₗ[HomogeneousLocalization.Away 𝓑 a]
      nativeHomogeneousAwayTwistModule 𝓑 a m :=
  LinearEquiv.ofInjective (nativeHomogeneousAwayTwistMap 𝓑 a m)
    (nativeHomogeneousAwayTwistMap_injective 𝓑 a m)

end LinearStudy
