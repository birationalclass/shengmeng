module
public import Linear.FiniteTypeHomogeneousChartNoetherian
public import Linear.NativeProjectiveCechAffineIntersections
public import Linear.NoetherianOrderedAffineCoverNativeH
public import Linear.OrderedModuleCechActualAbelian
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]
variable (B : ℕ → Submodule K A) [GradedAlgebra B]
/-- A native finite-type graded Proj with an ACTUAL degree-one cover is locally
Noetherian,DERIVED from its original affine chart rings. -/
theorem finiteTypeNativeProj_isLocallyNoetherian_of_cover
    [IsNoetherianRing A] [Algebra.FiniteType K A]
    {ι : Type u} (a : ι → A) (ha : ∀ i,a i ∈ B 1)
    (hcover : (⨆ i,Proj.basicOpen B (a i)) = ⊤) : IsLocallyNoetherian (Proj B) := by
  let C : ι → (Proj B).affineOpens := fun i =>
    ⟨Proj.basicOpen B (a i),Proj.isAffineOpen_basicOpen B (a i) (ha i) one_pos⟩
  apply isLocallyNoetherian_of_affine_cover (S := C) hcover
  intro i
  letI : IsNoetherianRing (HomogeneousLocalization.Away B (a i)) :=
    finiteTypeHomogeneousChart_isNoetherian B (a i) 1 (ha i)
  exact isNoetherianRing_of_ringEquiv (HomogeneousLocalization.Away B (a i))
    (Proj.basicOpenIsoAway B (a i) (ha i) one_pos).commRingCatIsoToRingEquiv
/-- For the SAME native finite-type source Proj,original ordered module-Cech
positive exactness implies actual native H vanishing.No source Noetherianity,
affine-intersection or local-H certificate is added.Original Cech exactness is
still explicit and is NOT asserted by this theorem. -/
theorem finiteTypeNativeProj_actualHigherH_vanish_of_orderedCechExact
    [IsNoetherianRing A] [Algebra.FiniteType K A]
    {ι : Type u} [LinearOrder ι] [Finite ι] (a : ι → A) (ha : ∀ i,a i ∈ B 1)
    (hcover : (⨆ i,Proj.basicOpen B (a i)) = ⊤)
    {Y : Scheme.{u}} (π : Proj B ⟶ Y) (M : (Proj B).Modules) [M.IsQuasicoherent]
    (hC : ∀ p,(Scheme.Modules.orderedBaseCechComplex π M
      (fun i => Proj.basicOpen B (a i))).ExactAt (p+1)) (n : ℕ) :
    Subsingleton (schemeModuleActualCohomology (Proj B) M (n+1)) := by
  letI := finiteTypeNativeProj_isLocallyNoetherian_of_cover B a ha hcover
  exact noetherianFiniteOrderedAffineCover_actualHigherH_vanish_of_moduleCechExact π
    (fun i => Proj.basicOpen B (a i)) (by rw [hcover])
    (fun p t => nativeProjective_cechIntersection_isAffine B a ha p t.1) M hC n
end LinearStudy
