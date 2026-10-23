module
public import Linear.OrderedModuleCechActualAbelianFactorization
public import Linear.OrderedFreeSheafHomCoefficientNaturality
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
/-- The SAME original module-valued/abelian Cech comparison is natural
in ORIGINAL module coefficient maps,including all original faces/signs.
No desired cohomology naturality or scalar compatibility is an input. -/
theorem orderedModuleCechActualAbelianComplexIso_coefficient_naturality
    {X S : Scheme.{u}} (π : X ⟶ S) {M N : X.Modules} (f : M ⟶ N)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    ((forget₂ (ModuleCat.{u} Γ(S,⊤)) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).map
        ((orderedBaseCechComplexFunctor π U).map f) ≫
      (orderedModuleCechActualAbelianComplexIso π N U).hom =
    (orderedModuleCechActualAbelianComplexIso π M U).hom ≫
      orderedTopAbelianCechCoefficientMap X U ((schemeModuleToActualAbelianSheaf X).map f) := by
  let H := forget₂ (ModuleCat.{u} Γ(S,⊤)) AddCommGrpCat.{u}
  let HC := H.mapHomologicalComplex (.up ℕ)
  let E := FormalCoproduct.evalOp.{u} X.Opens (ModuleCat.{u} Γ(S,⊤))
  let F := E.obj (baseModulePresheaf π M)
  let G := E.obj (baseModulePresheaf π N)
  let T := orderedFormalCechCoefficientFunctor (D:=ModuleCat.{u} Γ(S,⊤)) U
  let B := orderedFormalCechCoefficientFunctor (D:=AddCommGrpCat.{u}) U
  let a := E.map ((baseModulePresheafFunctor π).map f)
  let eM := HC.mapIso (Iso.refl (orderedBaseCechComplex π M U))
  let eN := HC.mapIso (Iso.refl (orderedBaseCechComplex π N U))
  have h₁ : CommSq (HC.map ((orderedBaseCechComplexFunctor π U).map f)) eM.hom eN.hom
      (HC.map (T.map a)) := by
    constructor
    change HC.map ((orderedBaseCechComplexFunctor π U).map f) ≫
      (HC.mapIso (Iso.refl (orderedBaseCechComplex π N U))).hom =
      (HC.mapIso (Iso.refl (orderedBaseCechComplex π M U))).hom ≫ HC.map (T.map a)
    simp only [Functor.mapIso_refl,Iso.refl_hom,Category.comp_id,Category.id_comp]
    exact congrArg HC.map (orderedBaseCechComplexFunctor_map_eq_formal π U f)
  have h₂ : CommSq (HC.map (T.map a))
      (orderedFormalCechWhiskeringIso U F H).hom
      (orderedFormalCechWhiskeringIso U G H).hom
      (B.map (Functor.whiskerRight a H)) :=
    ⟨orderedFormalCechWhiskeringIso_coefficient_naturality U a H⟩
  have h₃ : CommSq (B.map (Functor.whiskerRight a H))
      (B.mapIso (orderedBaseModuleActualAbelianCoefficientIso π M)).hom
      (B.mapIso (orderedBaseModuleActualAbelianCoefficientIso π N)).hom
      (orderedTopAbelianCechCoefficientMap X U ((schemeModuleToActualAbelianSheaf X).map f)) := by
    constructor
    change B.map _ ≫ B.map _ = B.map _ ≫ B.map _
    simpa only [Functor.map_comp] using congrArg B.map
      (orderedBaseModuleActualAbelianCoefficientIso_coefficient_naturality π f)
  rw [orderedModuleCechActualAbelianComplexIso_factorization,
    orderedModuleCechActualAbelianComplexIso_factorization]
  change HC.map ((orderedBaseCechComplexFunctor π U).map f) ≫
      (eN.hom ≫ ((orderedFormalCechWhiskeringIso U G H).hom ≫
        (B.mapIso (orderedBaseModuleActualAbelianCoefficientIso π N)).hom)) =
    (eM.hom ≫ ((orderedFormalCechWhiskeringIso U F H).hom ≫
      (B.mapIso (orderedBaseModuleActualAbelianCoefficientIso π M)).hom)) ≫
        orderedTopAbelianCechCoefficientMap X U ((schemeModuleToActualAbelianSheaf X).map f)
  exact (h₁.vert_comp (h₂.vert_comp h₃)).w
end LinearStudy
