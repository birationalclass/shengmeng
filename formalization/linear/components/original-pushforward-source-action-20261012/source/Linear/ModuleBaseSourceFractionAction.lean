module
public import Linear.ModuleBaseSourceUpperAction
public import Linear.NativeLocalizationScalarComparison
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
universe u
variable {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- The ORIGINAL comparison changes a base denominator into its original
source image. It intertwines all such source-fraction actions. -/
theorem moduleBaseSourceLocalizationEquiv_source_fraction_action
    (a : R) (s : S) (p : Submonoid.powers a) :
    let P' := Submonoid.powers (algebraMap R S a)
    let p' : P' := ⟨algebraMap R S p, by
      obtain ⟨n,hn⟩ := p.property
      exact ⟨n,by simpa only [map_pow] using congrArg (algebraMap R S) hn⟩⟩
    letI : Module (Localization (Submonoid.powers a)) (LocalizedModule (Submonoid.powers a) M) :=
      nativeLocalizedModuleScalar (Submonoid.powers a)
    letI : Module (Localization (Submonoid.powers (algebraMap R S a))) (LocalizedModule P' M) :=
      nativeLocalizedModuleScalar P'
    ∀ x : LocalizedModule (Submonoid.powers a) M,
      moduleBaseSourceLocalizationEquiv (S := S) a
        ((Localization.mk (1 : R) p : Localization (Submonoid.powers a)) •
          IsLocalizedModule.map (Submonoid.powers a)
            (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
            (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
            (DistribSMul.toLinearMap R M s) x) =
      (Localization.mk s p' : Localization (Submonoid.powers (algebraMap R S a))) •
        moduleBaseSourceLocalizationEquiv (S := S) a x := by
  dsimp only
  let P' := Submonoid.powers (algebraMap R S a)
  letI : Module (Localization (Submonoid.powers a)) (LocalizedModule (Submonoid.powers a) M) :=
    nativeLocalizedModuleScalar (Submonoid.powers a)
  letI : Module (Localization (Submonoid.powers (algebraMap R S a))) (LocalizedModule P' M) :=
    nativeLocalizedModuleScalar P'
  intro x
  induction x using LocalizedModule.induction_on with
  | _ m q =>
    rw [IsLocalizedModule.map_LocalizedModules, LocalizedModule.mk_smul_mk,
      one_smul, moduleBaseSourceLocalizationEquiv_mk,
      moduleBaseSourceLocalizationEquiv_mk, LocalizedModule.mk_smul_mk]
    apply congrArg (LocalizedModule.mk (s • m))
    apply Subtype.ext
    exact (algebraMap R S).map_mul (p : R) (q : R)

end LinearStudy
