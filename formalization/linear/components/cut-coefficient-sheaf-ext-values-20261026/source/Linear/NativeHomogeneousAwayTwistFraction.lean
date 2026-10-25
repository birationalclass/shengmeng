module
public import Linear.NativeHomogeneousAwayTwist
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
variable {K S : Type*} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]

/-- For a genuine degree-one chart coordinate, the degree-m chart map
sends h/a^(n+m) to h/a^n. Thus the chart module consists of actual
degree-m fractions in the native away localization. -/
theorem nativeHomogeneousAwayTwistMap_fraction (a : S) (ha : a ∈ 𝓑 1)
    (m n : ℕ) (h : S) (hh : h ∈ 𝓑 (n+m)) :
    nativeHomogeneousAwayTwistMap 𝓑 a m
      (HomogeneousLocalization.Away.mk 𝓑 ha (n+m) h
        (by simpa only [smul_eq_mul,mul_one] using hh)) =
      IsLocalization.mk' (M := Submonoid.powers a) (Localization.Away a) h
        ⟨a^n,⟨n,rfl⟩⟩ := by
  let L := Localization.Away a
  let u : L := algebraMap S L a
  let z := HomogeneousLocalization.Away.mk 𝓑 ha (n+m) h
    (by simpa only [smul_eq_mul,mul_one] using hh)
  let w : L := IsLocalization.mk' (M := Submonoid.powers a) L h ⟨a^n,⟨n,rfl⟩⟩
  have hu : IsUnit u := IsLocalization.map_units
    (M := Submonoid.powers a) L ⟨a,⟨1,by simp⟩⟩
  have hz : u^(n+m)*z.val = algebraMap S L h := by
    dsimp only [z,u]
    rw [HomogeneousLocalization.Away.val_mk,Localization.mk_eq_mk',← map_pow]
    exact IsLocalization.mk'_spec' L _ _
  have hw : u^n*w = algebraMap S L h := by
    dsimp only [w,u]
    rw [← map_pow]
    exact IsLocalization.mk'_spec' L _ _
  apply (hu.pow (n+m)).mul_left_cancel
  change u^(n+m)*(u^m*z.val) = u^(n+m)*w
  calc
    u^(n+m)*(u^m*z.val) = u^m*(u^(n+m)*z.val) := by ring
    _ = u^m*algebraMap S L h := by rw [hz]
    _ = (u^m*u^n)*w := by rw [mul_assoc,hw]
    _ = u^(n+m)*w := by rw [← pow_add,Nat.add_comm m n]

/-- Membership of an actual homogeneous numerator of degree n+m in
the native degree-m chart module; no abstract fraction-space model is supplied. -/
theorem nativeHomogeneousAwayTwist_fraction_mem (a : S) (ha : a ∈ 𝓑 1)
    (m n : ℕ) (h : S) (hh : h ∈ 𝓑 (n+m)) :
    IsLocalization.mk' (M := Submonoid.powers a) (Localization.Away a) h ⟨a^n,⟨n,rfl⟩⟩ ∈
      nativeHomogeneousAwayTwistModule 𝓑 a m := by
  exact ⟨HomogeneousLocalization.Away.mk 𝓑 ha (n+m) h
      (by simpa only [smul_eq_mul,mul_one] using hh),
    nativeHomogeneousAwayTwistMap_fraction 𝓑 a ha m n h hh⟩

end LinearStudy
