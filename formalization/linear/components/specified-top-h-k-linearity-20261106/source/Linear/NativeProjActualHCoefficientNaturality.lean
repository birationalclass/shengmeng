module
public import Linear.NativeProjActualHComparison
public import Linear.NoetherianOrderedCechHCoefficientNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
universe u
variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]
variable (B : ℕ → Submodule K A) [GradedAlgebra B]
attribute [local irreducible] noetherianFiniteOrderedAffineCover_actualHigherHIso
  topFiniteOrderedCech_actualHigherHIso_of_localAcyclic orderedFreeSheafActualHomComplexIso
  acyclicResolutionActualCochainExtIso
/-- The SAME finite-type native-Proj Cech/native-H comparison is natural
in ORIGINAL module coefficient maps. Noetherianity and BOTH local
acyclicity conditions are derived from the original affine cover. -/
theorem finiteTypeNativeProj_orderedActualHigherHIso_coefficient_naturality
    [IsNoetherianRing A] [Algebra.FiniteType K A]
    {ι : Type u} [LinearOrder ι] [Finite ι] (a : ι → A) (ha : ∀ i,a i ∈ B 1)
    (hcover : (⨆ i,Proj.basicOpen B (a i)) = ⊤)
    {M N : (Proj B).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) (q : ℕ) :
    HomologicalComplex.homologyMap
        (orderedTopAbelianCechCoefficientMap (Proj B) (fun i => Proj.basicOpen B (a i))
          ((schemeModuleToActualAbelianSheaf (Proj B)).map f)) (q+1) ≫
      (finiteTypeNativeProj_orderedActualHigherHIso B a ha hcover N q).hom =
    (finiteTypeNativeProj_orderedActualHigherHIso B a ha hcover M q).hom ≫
      (CategoryTheory.Sheaf.functorH.{u} (_root_.Opens.grothendieckTopology (Proj B)) (q+1)).map
        ((schemeModuleToActualAbelianSheaf (Proj B)).map f) := by
  letI := finiteTypeNativeProj_isLocallyNoetherian_of_cover B a ha hcover
  exact noetherianFiniteOrderedAffineCover_actualHigherHIso_coefficient_naturality (Proj B)
    (fun i => Proj.basicOpen B (a i)) (by rw [hcover])
    (fun p t => nativeProjective_cechIntersection_isAffine B a ha p t.1) f q
end LinearStudy
