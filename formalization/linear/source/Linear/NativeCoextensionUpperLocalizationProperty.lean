module
public import Linear.NativeCoextensionSemilinearLocalization
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
namespace LinearStudy
open CategoryTheory
universe u
variable {R S Q : Type u} [CommRing R] [CommRing S] [CommRing Q]
variable [Algebra R S] [Algebra R Q] [Module.Finite R S]
variable (P : Submonoid R) [IsLocalization P Q]
attribute [local instance] LocalizedModule.moduleOfIsLocalization

omit [Module.Finite R S] in
/-- Original and localized base scalars have the same actual image in
the localized original upper ring. -/
theorem nativeLocalizedAlgebra_base_map_commutes :
    let S' := LocalizedModule P S
    letI : Module Q S' := LocalizedModule.moduleOfIsLocalization
    letI : Algebra Q S' := LocalizedModule.algebraOfIsLocalization (S := P) Q
    ∀ a : R, LocalizedModule.numeratorRingHom (S := P) (A := S) (algebraMap R S a) =
      algebraMap Q S' (algebraMap R Q a) := by
  let S' := LocalizedModule P S
  letI : Module Q S' := LocalizedModule.moduleOfIsLocalization
  letI : Algebra Q S' := LocalizedModule.algebraOfIsLocalization (S := P) Q
  dsimp only
  intro a
  change LocalizedModule.mk (algebraMap R S a) 1 = _
  simpa only [IsLocalization.mk'_one] using
    (LocalizedModule.algebraMap_mk' (S := P) (A := S) Q a 1).symm

/-- The original semilinear comparison is an actual upper-ring linear map
to the localized native coextension with its original restriction of scalars. -/
def finiteNativeCoextensionUpperLocalizationMap
    (hinj : Function.Injective (algebraMap R Q)) :
    let S' := LocalizedModule P S
    letI : Module Q S' := LocalizedModule.moduleOfIsLocalization
    letI : Algebra Q S' := LocalizedModule.algebraOfIsLocalization (S := P) Q
    ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)) →ₗ[S]
      ((ModuleCat.restrictScalars (LocalizedModule.numeratorRingHom (S := P) (A := S))).obj
        ((ModuleCat.coextendScalars (algebraMap Q S')).obj (ModuleCat.of Q Q))) := by
  let S' := LocalizedModule P S
  letI : Module Q S' := LocalizedModule.moduleOfIsLocalization
  letI : Algebra Q S' := LocalizedModule.algebraOfIsLocalization (S := P) Q
  exact (ModuleCat.semilinearMapAddEquiv
    (LocalizedModule.numeratorRingHom (S := P) (A := S))
    ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))
    ((ModuleCat.coextendScalars (algebraMap Q S')).obj (ModuleCat.of Q Q))
    (finiteNativeCoextensionSemilinearLocalizationMap P hinj)).hom

/-- The ACTUAL native comparison is the localization of the original
upper-ring dual at the image of the original base multiplicative set. -/
theorem finiteNativeCoextensionUpperLocalizationMap_isLocalizedModule
    (hinj : Function.Injective (algebraMap R Q)) :
    let S' := LocalizedModule P S
    letI : Module Q S' := LocalizedModule.moduleOfIsLocalization
    letI : Algebra Q S' := LocalizedModule.algebraOfIsLocalization (S := P) Q
    IsLocalizedModule (Algebra.algebraMapSubmonoid S P)
      (finiteNativeCoextensionUpperLocalizationMap P hinj) := by
  let S' := LocalizedModule P S
  letI : Module Q S' := LocalizedModule.moduleOfIsLocalization
  letI : Algebra Q S' := LocalizedModule.algebraOfIsLocalization (S := P) Q
  let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
  letI : Module R D := Module.compHom D (algebraMap R S)
  letI : IsScalarTower R S D := IsScalarTower.of_compHom R S D
  let X := (ModuleCat.restrictScalars (algebraMap R S)).obj D
  let N := (ModuleCat.coextendScalars (algebraMap Q S')).obj (ModuleCat.of Q Q)
  let Y := (ModuleCat.restrictScalars (LocalizedModule.numeratorRingHom (S := P) (A := S))).obj N
  letI : Module Q Y := Module.compHom Y (algebraMap Q S')
  letI : IsScalarTower Q S' Y := IsScalarTower.of_compHom Q S' Y
  let NR := (ModuleCat.restrictScalars (algebraMap Q S')).obj N
  let e := finiteNativeCoextensionLocalizedTargetEquiv (S := S) P hinj
  dsimp only
  constructor
  · intro b
    obtain ⟨_, a, ha, rfl⟩ := b
    rw [Module.End.isUnit_iff]
    change Function.Bijective (fun y : Y =>
      (LocalizedModule.numeratorRingHom (S := P) (A := S) (algebraMap R S a)) • (y : N))
    rw [nativeLocalizedAlgebra_base_map_commutes (Q := Q) P]
    exact ((IsLocalization.map_units Q ⟨a, ha⟩).map (algebraMap Q S')).smul_bijective
  · intro y
    obtain ⟨w, hw⟩ := e.surjective (y : NR)
    induction w using LocalizedModule.induction_on with
    | h ell s =>
      refine ⟨⟨(ell : D), ⟨algebraMap R S s, Algebra.mem_algebraMapSubmonoid_of_mem s⟩⟩, ?_⟩
      with_unfolding_all change
        (LocalizedModule.numeratorRingHom (S := P) (A := S) (algebraMap R S s)) • (y : N) =
          (e (LocalizedModule.mk ell 1) : N)
      rw [nativeLocalizedAlgebra_base_map_commutes (Q := Q) P]
      change (algebraMap R Q s) • (y : NR) = e (LocalizedModule.mk ell 1)
      rw [← hw, ← e.map_smul]
      rw [IsScalarTower.algebraMap_smul, LocalizedModule.smul'_mk]
      with_unfolding_all exact (congrArg (fun z => (e z : N))
        (LocalizedModule.mk_cancel (M := X) s ell))
  · intro x1 x2 h
    change e (LocalizedModule.mk (x1 : X) 1) = e (LocalizedModule.mk (x2 : X) 1) at h
    obtain ⟨c, hc⟩ := (LocalizedModule.mk_eq (M := X) (S := P)).mp (e.injective h)
    simp only [one_smul] at hc
    refine ⟨⟨algebraMap R S c, Algebra.mem_algebraMapSubmonoid_of_mem c⟩, ?_⟩
    change (c : R) • (x1 : X) = (c : R) • (x2 : X)
    exact hc

end LinearStudy
