module
public import Linear.ModuleBaseSourceUpperAction
public import Linear.ModuleBaseSourceFractionAction
public import Linear.NativeCoextensionLocalizationSourceAction
public import Linear.NativeNormalizationFullChartComparison
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open CategoryTheory
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Retain the SAME original S action on the R-restricted native dual. -/
@[instance_reducible] def actualRestrictedNativeDualSourceModule :
    Module S (actualRestrictedNativeDual (R := R) (S := S)) :=
  ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)).isModule

attribute [local instance] actualRestrictedNativeDualSourceModule

/-- The restricted base scalar is the original scalar obtained via R->S. -/
theorem actualRestrictedNativeDualBaseSourceTower :
    IsScalarTower R S (actualRestrictedNativeDual (R := R) (S := S)) :=
  IsScalarTower.of_compHom R S _

attribute [local instance] actualRestrictedNativeDualBaseSourceTower
variable [Module.Finite R S]
attribute [local instance] LocalizedModule.moduleOfIsLocalization

/-- After the ACTUAL base-to-source localization comparison, source
numerator multiplication remains precomposition on original values. -/
theorem nativeDualSourceChangedUpperAction_eval
    (a : R) (hinj : Function.Injective (algebraMap R (Localization.Away a)))
    (s : S)
    (ell : LocalizedModule (Submonoid.powers a)
      (actualRestrictedNativeDual (R := R) (S := S)))
    (x : LocalizedModule (Submonoid.powers a) S) :
    finiteNativeCoextensionLocalizationEquiv (Q := Localization.Away a)
      (Submonoid.powers a) hinj
      ((moduleBaseSourceLocalizationEquiv (S := S) a).symm
        (s • moduleBaseSourceLocalizationEquiv (S := S) a ell)) x =
    finiteNativeCoextensionLocalizationEquiv (Q := Localization.Away a)
      (Submonoid.powers a) hinj ell (x * LocalizedModule.mk s 1) := by
  have h := moduleBaseSourceLocalizationEquiv_upper_action
    (M := actualRestrictedNativeDual (R := R) (S := S)) a s ell
  rw [← h, LinearEquiv.symm_apply_apply]
  exact nativeDualLocalizedUpperMultiplication_eval_all
    (Q := Localization.Away a) (Submonoid.powers a) hinj s ell x


/-- ACTUAL source localization fractions act on the original localized
native dual by precomposition. Denominators are the original images. -/
theorem nativeDualSourceChangedFractionAction_eval
    (a : R) (hinj : Function.Injective (algebraMap R (Localization.Away a)))
    (s : S) (p : Submonoid.powers a) :
    let P' := Submonoid.powers (algebraMap R S a)
    let p' : P' := ⟨algebraMap R S p, by
      obtain ⟨n,hn⟩ := p.property
      exact ⟨n,by simpa only [map_pow] using congrArg (algebraMap R S) hn⟩⟩
    letI : Module (Localization.Away (algebraMap R S a))
      (LocalizedModule P' (actualRestrictedNativeDual (R := R) (S := S))) :=
      nativeLocalizedModuleScalar P'
    ∀ ell : LocalizedModule (Submonoid.powers a)
      (actualRestrictedNativeDual (R := R) (S := S)),
    ∀ x : LocalizedModule (Submonoid.powers a) S,
      finiteNativeCoextensionLocalizationEquiv (Q := Localization.Away a)
        (Submonoid.powers a) hinj
        ((moduleBaseSourceLocalizationEquiv (S := S) a).symm
          ((Localization.mk s p' : Localization.Away (algebraMap R S a)) •
            moduleBaseSourceLocalizationEquiv (S := S) a ell)) x =
      finiteNativeCoextensionLocalizationEquiv (Q := Localization.Away a)
        (Submonoid.powers a) hinj ell (x * LocalizedModule.mk s p) := by
  dsimp only
  let P' := Submonoid.powers (algebraMap R S a)
  letI : Module (Localization.Away a)
    (LocalizedModule (Submonoid.powers a) (actualRestrictedNativeDual (R := R) (S := S))) :=
    nativeLocalizedModuleScalar (Submonoid.powers a)
  letI : Module (Localization.Away (algebraMap R S a))
    (LocalizedModule P' (actualRestrictedNativeDual (R := R) (S := S))) :=
    nativeLocalizedModuleScalar P'
  intro ell x
  have hg := moduleBaseSourceLocalizationEquiv_source_fraction_action
    (M := actualRestrictedNativeDual (R := R) (S := S)) a s p ell
  rw [← hg, LinearEquiv.symm_apply_apply]
  have hv := nativeDualLocalizedSourceFraction_eval (Q := Localization.Away a)
    (Submonoid.powers a) hinj s p ell x
  rw [localizedModule_abstract_smul_eq_native (Submonoid.powers a)] at hv
  have hm : nativeDualUpperMultiplication (R := R) s =
      DistribSMul.toLinearMap R (actualRestrictedNativeDual (R := R) (S := S)) s := by
    apply LinearMap.ext
    intro d
    rfl
  simpa only [← Localization.mk_eq_mk', nativeDualLocalizedUpperMultiplication,
    hm] using hv


/-- EVERY actual localized source scalar acts by precomposition after
the ORIGINAL universal base/source comparison. This covers all fractions,
and the original ring comparison identifies their denominator images. -/
theorem nativeDualSourceChangedAction_eval_all
    (a : R) (hinj : Function.Injective (algebraMap R (Localization.Away a))) :
    letI := nativeLocalizedUpperAlgebra (S := S) (Submonoid.powers a)
    let P' := Submonoid.powers (algebraMap R S a)
    letI : Module (Localization.Away (algebraMap R S a))
      (LocalizedModule P' (actualRestrictedNativeDual (R := R) (S := S))) :=
      nativeLocalizedModuleScalar P'
    ∀ b : Localization.Away (algebraMap R S a),
    ∀ ell : LocalizedModule (Submonoid.powers a)
      (actualRestrictedNativeDual (R := R) (S := S)),
    ∀ x : LocalizedModule (Submonoid.powers a) S,
      finiteNativeCoextensionLocalizationEquiv (Q := Localization.Away a)
        (Submonoid.powers a) hinj
        ((moduleBaseSourceLocalizationEquiv (S := S) a).symm
          (b • moduleBaseSourceLocalizationEquiv (S := S) a ell)) x =
      finiteNativeCoextensionLocalizationEquiv (Q := Localization.Away a)
        (Submonoid.powers a) hinj ell
        (x * (nativeNormalizationFullChartEquiv (S := S) a).symm b) := by
  dsimp only
  letI := nativeLocalizedUpperAlgebra (S := S) (Submonoid.powers a)
  let P' := Submonoid.powers (algebraMap R S a)
  letI : Module (Localization.Away (algebraMap R S a))
    (LocalizedModule P' (actualRestrictedNativeDual (R := R) (S := S))) :=
    nativeLocalizedModuleScalar P'
  intro b ell x
  obtain ⟨⟨s,q⟩,hq⟩ := IsLocalization.mk'_surjective P' b
  obtain ⟨n,hn⟩ := q.property
  let p : Submonoid.powers a := ⟨a^n,⟨n,rfl⟩⟩
  let p' : P' := ⟨algebraMap R S p, by
    obtain ⟨j,hj⟩ := p.property
    exact ⟨j,by simpa only [map_pow] using congrArg (algebraMap R S) hj⟩⟩
  have hpq : p' = q := by
    apply Subtype.ext
    change algebraMap R S (a^n) = (q : S)
    rw [map_pow]
    exact hn
  have hb : b = (Localization.mk s p' : Localization.Away (algebraMap R S a)) := by
    rw [Localization.mk_eq_mk', hpq]
    exact hq.symm
  have hv : (nativeNormalizationFullChartEquiv (S := S) a).symm
      (Localization.mk s p') = (LocalizedModule.mk s p : LocalizedModule (Submonoid.powers a) S) := by
    apply (nativeNormalizationFullChartEquiv (S := S) a).injective
    rw [AlgEquiv.apply_symm_apply, nativeNormalizationFullChartEquiv_mk]
    exact Localization.mk_eq_mk'_apply s p'
  rw [hb, hv]
  exact nativeDualSourceChangedFractionAction_eval a hinj s p ell x

end LinearStudy
