module
public import Linear.TildeNativeModuleExtMappedChain
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u

/-- Construct the actual MODULE morphism from an actual affine SHEAF
morphism using ONLY native Hom full faithfulness,not an Ext bijection. -/
def tildeActualFunctionalPreimage (R : CommRingCat.{u}) {M N : ModuleCat.{u} R}
    (a : (tilde.functor R).obj M ⟶ (tilde.functor R).obj N) : M ⟶ N :=
  (tilde.functor R).preimage a

/-- The constructed module functional sheafifies to the SAME actual map. -/
theorem tildeActualFunctionalPreimage_map (R : CommRingCat.{u}) {M N : ModuleCat.{u} R}
    (a : (tilde.functor R).obj M ⟶ (tilde.functor R).obj N) :
    (tilde.functor R).map (tildeActualFunctionalPreimage R a) = a :=
  (tilde.functor R).map_preimage a

/-- Derive the actual module cocycle from the original actual sheaf
cocycle,using faithfulness on Hom and the SAME differential. -/
theorem tildeActualFunctionalPreimage_isCocycle (R : CommRingCat.{u})
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (r : ℕ) (N : ModuleCat.{u} R)
    (a : (tilde.functor R).obj (C.X r) ⟶ (tilde.functor R).obj N)
    (ha : (tilde.functor R).map (C.d (r+1) r) ≫ a = 0) :
    C.d (r+1) r ≫ tildeActualFunctionalPreimage R a = 0 := by
  apply (tilde.functor R).map_injective
  rw [Functor.map_comp,tildeActualFunctionalPreimage_map,Functor.map_zero]
  exact ha

/-- The ACTUAL native MODULE Ext representative constructed from the
SAME actual affine sheaf cocycle and actual module projective resolution. -/
def tildeActualCocycleModuleExt (R : CommRingCat.{u}) {E N : ModuleCat.{u} R}
    (P : ProjectiveResolution E) (r : ℕ)
    (a : (tilde.functor R).obj (P.complex.X r) ⟶ (tilde.functor R).obj N)
    (ha : (tilde.functor R).map (P.complex.d (r+1) r) ≫ a = 0) : Ext.{u} E N r :=
  P.extMk (tildeActualFunctionalPreimage R a) (r+1) rfl
    (tildeActualFunctionalPreimage_isCocycle R P.complex r N a ha)

/-- Explicit STATEMENT of forward native tilde action on the constructed
MODULE Ext class. This makes no assertion of Ext-bijectivity. -/
def tildeActualCocycleModuleExtLaw (R : CommRingCat.{u}) {E N : ModuleCat.{u} R}
    (P : ProjectiveResolution E) (r : ℕ)
    (a : (tilde.functor R).obj (P.complex.X r) ⟶ (tilde.functor R).obj N)
    (ha : (tilde.functor R).map (P.complex.d (r+1) r) ≫ a = 0) : Prop :=
  letI := HasDerivedCategory.standard (ModuleCat.{u} R)
  letI := HasExt.standard (Spec R).Modules
  letI := HasDerivedCategory.standard (Spec R).Modules
  letI := tilde_functor_preservesHomology R
  letI := Functor.preservesFiniteLimits_of_preservesHomology (tilde.functor R)
  letI := Functor.preservesFiniteColimits_of_preservesHomology (tilde.functor R)
  letI := mappedOriginalChainAugmentation_quasiIso (tilde.functor R) P.complex P.π
  (tildeActualCocycleModuleExt R P r a ha).mapExactFunctor (tilde.functor R) =
    originalChainTopExtClass (((tilde.functor R).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex) r
      (mappedOriginalChainAugmentation (tilde.functor R) P.complex P.π) a
      (by change (tilde.functor R).map (P.complex.d (r+1) r) ≫ a = 0;exact ha)

/-- PROVE that the actual constructed MODULE class maps to the SAME
actual sheaf roof. Only Hom fullness/faithfulness and the proved forward
Ext action are used;no unproved Ext inverse or projectivity of sheaves. -/
theorem tildeActualCocycleModuleExtLaw_proof (R : CommRingCat.{u}) {E N : ModuleCat.{u} R}
    (P : ProjectiveResolution E) (r : ℕ)
    (a : (tilde.functor R).obj (P.complex.X r) ⟶ (tilde.functor R).obj N)
    (ha : (tilde.functor R).map (P.complex.d (r+1) r) ≫ a = 0) :
    tildeActualCocycleModuleExtLaw R P r a ha := by
  letI := HasDerivedCategory.standard (ModuleCat.{u} R)
  letI := HasExt.standard (Spec R).Modules
  letI := HasDerivedCategory.standard (Spec R).Modules
  letI := tilde_functor_preservesHomology R
  letI := Functor.preservesFiniteLimits_of_preservesHomology (tilde.functor R)
  letI := Functor.preservesFiniteColimits_of_preservesHomology (tilde.functor R)
  dsimp only [tildeActualCocycleModuleExtLaw]
  have h := tildeNativeModuleExtMappedChainLaw_proof R P r (tildeActualFunctionalPreimage R a)
    (tildeActualFunctionalPreimage_isCocycle R P.complex r N a ha)
  dsimp only [tildeNativeModuleExtMappedChainLaw] at h
  simpa only [tildeActualCocycleModuleExt,tildeActualFunctionalPreimage_map] using h

end LinearStudy
