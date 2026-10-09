module
public import Linear.FiniteDomainDualNonzero
public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
namespace LinearStudy
open CategoryTheory
universe u
variable {R S : Type u} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
variable [Algebra R S] [FaithfulSMul R S] [Module.Finite R S]
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- The constructed embedding of the actual native dual into the actual
upper fraction field IS its module localization. Surjectivity after
localization is proved from an actual nonzero functional, not assumed. -/
theorem coextensionFractionEmbedding_isLocalizedModule :
    IsLocalizedModule (nonZeroDivisors S) (coextensionFractionEmbedding (R := R) (S := S)) := by
  let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
  let E := coextensionFractionEmbedding (R := R) (S := S)
  obtain ⟨ell,hell⟩ := coextensionDual_exists_nonzero_at_one (R := R) (S := S)
  have he : Function.Injective E := coextensionFractionEmbedding_injective (R := R) (S := S)
  have hellne : ell ≠ 0 := by
    intro h
    apply hell
    rw [h]
    rfl
  have hE : E ell ≠ 0 := by
    intro h
    exact hellne (he (h.trans (map_zero E).symm))
  refine ⟨IsLocalizedModule.map_units (Algebra.linearMap S (FractionRing S)),?_,?_⟩
  · intro z
    obtain ⟨a,b,hb,hab⟩ := IsFractionRing.div_surjective S (z/(E ell))
    have hbF : algebraMap S (FractionRing S) b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective S (FractionRing S))).mpr
        (nonZeroDivisors.ne_zero hb)
    have hmul := (div_eq_div_iff hbF hE).mp hab
    refine ⟨(a • ell,⟨b,hb⟩),?_⟩
    rw [map_smul]
    simpa only [Submonoid.smul_def,Algebra.smul_def] using
      (mul_comm (algebraMap S (FractionRing S) b) z).trans hmul.symm
  · intro x y hxy
    exact ⟨1,congrArg (fun x : D => (1 : nonZeroDivisors S) • x) (he hxy)⟩

end LinearStudy
