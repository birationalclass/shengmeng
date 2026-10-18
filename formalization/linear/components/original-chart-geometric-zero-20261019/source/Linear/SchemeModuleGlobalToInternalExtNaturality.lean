module
public import Linear.SchemeModuleGlobalToInternalExtCocycle
public import Linear.SchemeModuleInjectiveInternalHomNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u
variable {X : Scheme.{u}} {N N' : X.Modules} (I : InjectiveResolution N)
  (J : InjectiveResolution N') (P : X.Modules)

/-- SAME injective cocycle maps naturally to ACTUAL derived SHEAF Ext,
using native comparison isos for the SAME actual resolution morphism. -/
theorem schemeModuleInjectiveCocycleToInternalExt_naturality {c : N ⟶ N'}
    (phi : InjectiveResolution.Hom I J c) (q : ℕ) (f : injectiveCocycleGroup I P q) :
    schemeModuleInjectiveCocycleToInternalExt J P q
        (injectiveCocycleTransport I J P q phi.hom f) =
      schemeModuleInjectiveCocycleToInternalExt I P q f ≫
        (schemeModuleInternalExtFunctor P q).map c := by
  have h := InjectiveResolution.isoRightDerivedObj_inv_naturality c I J phi.hom
    (by simpa using phi.ι_f_zero_comp_hom_f_zero)
    (schemeModuleInternalHomCoefficientFunctor X P) q
  change (schemeModuleInternalExtInjectiveResolutionIso P N q I).inv ≫
      (schemeModuleInternalExtFunctor P q).map c =
    HomologicalComplex.homologyMap
      (((schemeModuleInternalHomCoefficientFunctor X P).mapHomologicalComplex
        (ComplexShape.up ℕ)).map phi.hom) q ≫
      (schemeModuleInternalExtInjectiveResolutionIso P N' q J).inv at h
  change (schemeModuleInjectiveInternalHomClassMap J P q _) ≫ _ =
    (schemeModuleInjectiveInternalHomClassMap I P q f ≫ _) ≫ _
  rw [schemeModuleInjectiveInternalHomClassMap_naturality]
  simp only [Category.assoc]
  rw [← h]

/-- ACTUAL positive global-to-local map is coefficient-natural on SAME
native global Ext classes. Prove on the native surjective cocycle presentation. -/
theorem schemeModuleGlobalToInternalExtViaResolution_naturality {c : N ⟶ N'}
    (phi : InjectiveResolution.Hom I J c) (n : ℕ) (e : Ext.{u} P N (n+1)) :
    schemeModuleGlobalToInternalExtViaResolution J P n
        (e.comp (Ext.mk₀ c) (add_zero _)) =
      schemeModuleGlobalToInternalExtViaResolution I P n e ≫
        (schemeModuleInternalExtFunctor P (n+1)).map c := by
  obtain ⟨f,rfl⟩ := injectiveCocycleExtMap_surjective I P (n+1) e
  rw [← injectiveCocycleExtMap_transport I J P (n+1) phi f]
  rw [schemeModuleGlobalToInternalExtViaResolution_cocycle,
    schemeModuleGlobalToInternalExtViaResolution_cocycle]
  exact schemeModuleInjectiveCocycleToInternalExt_naturality I J P phi (n+1) f

/-- The constructed map is INDEPENDENT of the chosen actual injective
resolution. Native descent constructs the needed comparison map. No
resolution-independence or desired Ext map is assumed. -/
theorem schemeModuleGlobalToInternalExtViaResolution_independent
    {N : X.Modules} (I J : InjectiveResolution N) (P : X.Modules) (n : ℕ) :
    schemeModuleGlobalToInternalExtViaResolution I P n =
      schemeModuleGlobalToInternalExtViaResolution J P n := by
  let phi : InjectiveResolution.Hom I J (𝟙 N) :=
    { hom := InjectiveResolution.desc (𝟙 N) J I
      ι_f_zero_comp_hom_f_zero := by
        simpa using InjectiveResolution.desc_commutes_zero (𝟙 N) J I }
  apply AddMonoidHom.ext
  intro e
  have h := schemeModuleGlobalToInternalExtViaResolution_naturality I J P phi n e
  have hi : (schemeModuleInternalExtFunctor P (n+1)).map (𝟙 N) =
      𝟙 (schemeModuleInternalExt P N (n+1)) :=
    (schemeModuleInternalExtFunctor P (n+1)).map_id N
  erw [Ext.comp_mk₀_id,hi,Category.comp_id] at h
  exact h.symm

end LinearStudy
