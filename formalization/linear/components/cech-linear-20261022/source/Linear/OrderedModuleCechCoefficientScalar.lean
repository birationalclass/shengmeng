module
public import Linear.OrderedModuleCechCoefficientFactors
public import Linear.FormalCechScalarIdentity
public import Linear.OriginalGlobalModuleScalarRingHom
public import Linear.HomologicalComplexScalarHomology
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
universe u
/-- ORIGINAL coefficient multiplication by the actual pulled-back base
section equals the ORIGINAL base-linear presheaf scalar identity map. -/
theorem baseModulePresheafFunctor_map_originalScalar
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules) (r : Γ(S,⊤)) :
    (baseModulePresheafFunctor π).map (originalGlobalModuleScalar (π.appTop r) M) =
      r • 𝟙 (baseModulePresheaf π M) := by
  ext U x
  rfl
/-- ORIGINAL ordered Cech coefficient multiplication is the native
base-linear scalar identity complex map,with all original signs retained. -/
theorem orderedBaseCechComplexFunctor_map_originalScalar
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules) (r : Γ(S,⊤))
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    (orderedBaseCechComplexFunctor π U).map (originalGlobalModuleScalar (π.appTop r) M) =
      r • 𝟙 (orderedBaseCechComplex π M U) := by
  let P := baseModulePresheaf π M
  let E := FormalCoproduct.evalOp.{u} X.Opens (ModuleCat.{u} Γ(S,⊤))
  let T := orderedFormalCechCoefficientFunctor (D:=ModuleCat.{u} Γ(S,⊤)) U
  let a : P ⟶ P := (baseModulePresheafFunctor π).map (originalGlobalModuleScalar (π.appTop r) M)
  calc
    _ = T.map (E.map a) := orderedBaseCechComplexFunctor_map_eq_formal π U _
    _ = T.map (E.map (r • 𝟙 P)) :=
      congrArg (fun g : P ⟶ P => T.map (E.map g))
        (baseModulePresheafFunctor_map_originalScalar π M r)
    _ = T.map (r • 𝟙 (E.obj P)) :=
      congrArg (fun g : E.obj P ⟶ E.obj P => T.map g)
        (formalProductEvaluation_map_smul_id P r)
    _ = _ := orderedFormalCechCoefficientFunctor_map_smul_id U (E.obj P) r
/-- The SAME scalar coefficient map induces native scalar multiplication
on ORIGINAL module-valued ordered Cech homology,in EVERY degree. -/
theorem orderedBaseCech_homologyMap_originalScalar
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules) (r : Γ(S,⊤))
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((orderedBaseCechComplexFunctor π U).map (originalGlobalModuleScalar (π.appTop r) M)) n =
      r • 𝟙 ((orderedBaseCechComplex π M U).homology n) := by
  calc
    _ = HomologicalComplex.homologyMap (r • 𝟙 (orderedBaseCechComplex π M U)) n :=
      congrArg (fun g : orderedBaseCechComplex π M U ⟶ orderedBaseCechComplex π M U =>
        HomologicalComplex.homologyMap g n)
        (orderedBaseCechComplexFunctor_map_originalScalar π M r U)
    _ = _ := actualHomologicalComplex_homologyMap_smul_id (orderedBaseCechComplex π M U) r n
end LinearStudy
