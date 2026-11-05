module
public import Linear.NoetherianOrderedAffineCoverActualHComparison
public import Linear.FiniteTypeNativeProjActualCohomology
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
universe u
variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]
variable (B : ℕ → Submodule K A) [GradedAlgebra B]
/-- Finite-type native Proj ordered Cech computes SAME actual positive H.
Source Noetherianity,affine intersections and local H acyclicity are DERIVED.
Only original degree-one cover and genuine QC coefficient are explicit. -/
def finiteTypeNativeProj_orderedActualHigherHIso
    [IsNoetherianRing A] [Algebra.FiniteType K A]
    {ι : Type u} [LinearOrder ι] [Finite ι] (a : ι → A) (ha : ∀ i,a i ∈ B 1)
    (hcover : (⨆ i,Proj.basicOpen B (a i)) = ⊤)
    (M : (Proj B).Modules) [M.IsQuasicoherent] (q : ℕ) :
    (orderedTopAbelianCechComplex (Proj B) (fun i => Proj.basicOpen B (a i))
      ((schemeModuleToActualAbelianSheaf (Proj B)).obj M)).homology (q+1) ≅
        AddCommGrpCat.of (schemeModuleActualCohomology (Proj B) M (q+1)) := by
  letI := finiteTypeNativeProj_isLocallyNoetherian_of_cover B a ha hcover
  exact noetherianFiniteOrderedAffineCover_actualHigherHIso (Proj B)
    (fun i => Proj.basicOpen B (a i)) (by rw [hcover])
    (fun p t => nativeProjective_cechIntersection_isAffine B a ha p t.1) M q
/-- Original module-valued native Proj ordered Cech HOMOLOGY computes actual
positive H after forgetting base scalars. No comparison or desired vanishing
certificate;all affine-intersection and Noetherian properties are derived. -/
def finiteTypeNativeProj_moduleCechActualHigherHIso
    [IsNoetherianRing A] [Algebra.FiniteType K A]
    {ι : Type u} [LinearOrder ι] [Finite ι] (a : ι → A) (ha : ∀ i,a i ∈ B 1)
    (hcover : (⨆ i,Proj.basicOpen B (a i)) = ⊤)
    {Y : Scheme.{u}} (pi : Proj B ⟶ Y) (M : (Proj B).Modules) [M.IsQuasicoherent] (q : ℕ) :
    (forget₂ (ModuleCat.{u} Γ(Y,⊤)) AddCommGrpCat.{u}).obj
      ((orderedBaseCechComplex pi M (fun i => Proj.basicOpen B (a i))).homology (q+1)) ≅
        AddCommGrpCat.of (schemeModuleActualCohomology (Proj B) M (q+1)) := by
  letI := finiteTypeNativeProj_isLocallyNoetherian_of_cover B a ha hcover
  exact noetherianFiniteOrderedAffineCover_moduleCechActualHigherHIso pi
    (fun i => Proj.basicOpen B (a i)) (by rw [hcover])
    (fun p t => nativeProjective_cechIntersection_isAffine B a ha p t.1) M q
end LinearStudy
