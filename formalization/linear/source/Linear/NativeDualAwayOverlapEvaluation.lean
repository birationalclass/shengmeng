module
public import Linear.OriginalAwayOverlapFraction
public import Linear.FiniteNativeDualRefinementEvaluation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
namespace LinearStudy
open CategoryTheory
universe u
variable {R S : Type u} [CommRing R] [CommRing S]
variable [Algebra R S] [Module.Finite R S]
attribute [local instance] LocalizedModule.moduleOfIsLocalization

/-- The actual native finite-dual comparison commutes with restriction to
the actual overlap D(a*b). Both module restrictions are constructed, and
the target restriction is mathlib's original away-to-away ring map. -/
theorem finiteNativeDual_awayOverlap_evaluation
    (a b : R)
    (ha : Function.Injective (algebraMap R (Localization.Away a)))
    (hab : Function.Injective (algebraMap R (Localization.Away (a*b))))
    (ell : LocalizedModule (Submonoid.powers a)
      ((ModuleCat.restrictScalars (algebraMap R S)).obj
        ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))))
    (x : LocalizedModule (Submonoid.powers a) S) :
    finiteNativeCoextensionLocalizationEquiv (Q := Localization.Away (a*b))
      (Submonoid.powers (a*b)) hab
      (originalLocalizedModuleAwayOverlap a b ell)
      (originalLocalizedModuleAwayOverlap a b x) =
      (IsLocalization.Away.awayToAwayRight a b :
        Localization.Away a →+* Localization.Away (a*b))
        (finiteNativeCoextensionLocalizationEquiv (Q := Localization.Away a)
          (Submonoid.powers a) ha ell x) := by
  induction ell using LocalizedModule.induction_on with
  | _ ell s =>
    induction x using LocalizedModule.induction_on with
    | _ x t =>
      obtain ⟨n,hn⟩ := s.property
      obtain ⟨k,hk⟩ := t.property
      have hs : s = (⟨a^n,⟨n,rfl⟩⟩ : Submonoid.powers a) := Subtype.ext hn.symm
      have ht : t = (⟨a^k,⟨k,rfl⟩⟩ : Submonoid.powers a) := Subtype.ext hk.symm
      subst s t
      rw [originalLocalizedModuleAwayOverlap_mk,originalLocalizedModuleAwayOverlap_mk,
        finiteNativeCoextensionLocalizationEquiv_apply_fraction,
        finiteNativeCoextensionLocalizationEquiv_apply_fraction]
      have hd : (⟨a^n,⟨n,rfl⟩⟩ : Submonoid.powers a) * ⟨a^k,⟨k,rfl⟩⟩ =
          ⟨a^(n+k),⟨n+k,rfl⟩⟩ := by
        apply Subtype.ext
        simp only [Submonoid.coe_mul,pow_add]
      have hd' : (⟨(a*b)^n,⟨n,rfl⟩⟩ : Submonoid.powers (a*b)) * ⟨(a*b)^k,⟨k,rfl⟩⟩ =
          ⟨(a*b)^(n+k),⟨n+k,rfl⟩⟩ := by
        apply Subtype.ext
        simp only [Submonoid.coe_mul,pow_add]
      rw [hd,hd',originalAwayOverlap_mk]
      congr 1
      rw [(nativeCoextensionOriginalDualEquiv (R := R) (S := S)).map_smul,
        LinearMap.smul_apply,LinearMap.map_smul]
      simp only [smul_eq_mul,pow_add,mul_assoc]

end LinearStudy
