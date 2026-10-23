module
public import Linear.NativeTwistRegradingCoefficientSquares
public import Linear.OrderedCechModuleScalarNaturality
public import Linear.SchemeModuleFiniteSupportCohomology
public import Linear.NativeProjectiveTwistRegrading
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {K R M N : Type u} [Field K] [CommRing R] [Algebra K R]
variable [AddCommGroup M] [Module R M] [Module K M]
variable [AddCommGroup N] [Module R N] [Module K N]
variable (A : ℕ → Submodule K R) [GradedAlgebra A]
variable (D : ℤ → Submodule K M) (E : ℤ → Submodule K N)
variable (hD : ∀ n : ℕ,∀ j : ℤ,∀ z : R,z ∈ A n → ∀ x : M,x ∈ D j → z • x ∈ D ((n:ℤ)+j))
variable (hE : ∀ n : ℕ,∀ j : ℤ,∀ z : R,z ∈ A n → ∀ x : N,x ∈ E j → z • x ∈ E ((n:ℤ)+j))
variable (f : M →ₗ[R] N) (hf : ∀ j : ℤ,∀ x : M,x ∈ D j → f x ∈ E j)
attribute [local instance] nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule
open AlgebraicGeometry.Scheme.Modules CategoryTheory.Limits
variable {ι : Type u} [LinearOrder ι] (U : ι → (Proj A).Opens)
/-- The SAME actual ordered-Cech regrading hom respects the ORIGINAL
coefficient morphism in EVERY integer twist,by functoriality of actual maps. -/
theorem nativeOrderedCechRegradingIso_coefficient_hom (k : ℤ) :
    orderedTopAbelianCechCoefficientMap (Proj A) U ((schemeModuleToActualAbelianSheaf (Proj A)).map
      (nativeProjectiveDegreeZeroSheafMap A (integerGradingShift D k) (integerGradingShift E k)
        (integerGradingShift_smul_homogeneous A D hD k)
        (integerGradingShift_smul_homogeneous A E hE k) f (fun j x hx => hf (j+k) x hx) 0)) ≫
      (orderedTopAbelianCechCoefficientIso U ((schemeModuleToActualAbelianSheaf (Proj A)).mapIso
        (nativeProjectiveTwistRegradingIso A E hE k))).hom =
    (orderedTopAbelianCechCoefficientIso U ((schemeModuleToActualAbelianSheaf (Proj A)).mapIso
        (nativeProjectiveTwistRegradingIso A D hD k))).hom ≫
      orderedTopAbelianCechCoefficientMap (Proj A) U ((schemeModuleToActualAbelianSheaf (Proj A)).map
        (nativeProjectiveDegreeZeroSheafMap A D E hD hE f hf k)) := by
  rw [orderedTopAbelianCechCoefficientIso_hom_eq_map,orderedTopAbelianCechCoefficientIso_hom_eq_map]
  let C := schemeModuleToActualAbelianSheaf (Proj A) ⋙
    sheafToPresheaf (_root_.Opens.grothendieckTopology (Proj A)) AddCommGrpCat.{u} ⋙
    FormalCoproduct.evalOp.{u} (Proj A).Opens AddCommGrpCat.{u} ⋙ orderedFormalCechCoefficientFunctor U
  change C.map _ ≫ C.map _ = C.map _ ≫ C.map _
  simpa only [Functor.map_comp] using
    congrArg C.map (nativeProjectiveTwistRegradingIso_coefficient_hom A D E hD hE f hf k)
/-- The SAME ordered-Cech inverse regrading respects the ORIGINAL map.
The proof maps the proved original O-linear sheaf square,without transfer
of coefficient actions or assumptions about the final Cech comparison. -/
theorem nativeOrderedCechRegradingIso_coefficient_inv (k : ℤ) :
    orderedTopAbelianCechCoefficientMap (Proj A) U ((schemeModuleToActualAbelianSheaf (Proj A)).map
      (nativeProjectiveDegreeZeroSheafMap A D E hD hE f hf k)) ≫
      (orderedTopAbelianCechCoefficientIso U ((schemeModuleToActualAbelianSheaf (Proj A)).mapIso
        (nativeProjectiveTwistRegradingIso A E hE k))).inv =
    (orderedTopAbelianCechCoefficientIso U ((schemeModuleToActualAbelianSheaf (Proj A)).mapIso
        (nativeProjectiveTwistRegradingIso A D hD k))).inv ≫
      orderedTopAbelianCechCoefficientMap (Proj A) U ((schemeModuleToActualAbelianSheaf (Proj A)).map
        (nativeProjectiveDegreeZeroSheafMap A (integerGradingShift D k) (integerGradingShift E k)
          (integerGradingShift_smul_homogeneous A D hD k)
          (integerGradingShift_smul_homogeneous A E hE k) f (fun j x hx => hf (j+k) x hx) 0)) := by
  rw [orderedTopAbelianCechCoefficientIso_inv_eq_map,orderedTopAbelianCechCoefficientIso_inv_eq_map]
  let C := schemeModuleToActualAbelianSheaf (Proj A) ⋙
    sheafToPresheaf (_root_.Opens.grothendieckTopology (Proj A)) AddCommGrpCat.{u} ⋙
    FormalCoproduct.evalOp.{u} (Proj A).Opens AddCommGrpCat.{u} ⋙ orderedFormalCechCoefficientFunctor U
  change C.map _ ≫ C.map _ = C.map _ ≫ C.map _
  simpa only [Functor.map_comp] using
    congrArg C.map (nativeProjectiveTwistRegradingIso_coefficient_inv A D E hD hE f hf k)
end LinearStudy
