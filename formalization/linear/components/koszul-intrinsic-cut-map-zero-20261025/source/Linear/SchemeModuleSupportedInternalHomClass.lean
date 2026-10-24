module
public import Linear.SchemeModuleSupportedUnitHomLifting
public import Linear.SchemeModuleInjectiveInternalHomCycleSurjective
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
/-- For an ACTUAL closed discrete direct image source, every global internal-Hom cohomology class comes from a cocycle in the SAME coefficient resolution. -/
theorem schemeModuleInjectiveInternalHomClassMap_closedDiscrete_surjective
    {D X : Scheme.{u}} [DiscreteTopology D] (f : D ⟶ X) (hf : IsClosedMap f)
    (L : D.Modules) {N : X.Modules} (I : InjectiveResolution N) (q : ℕ) :
    Function.Surjective
      (schemeModuleInjectiveInternalHomClassMap I ((Scheme.Modules.pushforward f).obj L) q) := by
  let P := (Scheme.Modules.pushforward f).obj L
  let K := schemeModuleInjectiveInternalHomComplex I P
  intro s
  obtain ⟨z,hz⟩ := schemeModule_unitHom_lift_of_closedDiscreteSubHom f hf L
    (I.cocomplex.X q) (K.cycles q) (K.homology q) (K.iCycles q) (K.homologyπ q) s
  obtain ⟨c,hc⟩ := schemeModuleInjectiveInternalHomCycleMap_surjective I P q z
  refine ⟨c, ?_⟩
  change schemeModuleInjectiveInternalHomCycleMap I P q c ≫ K.homologyπ q = s
  rw [hc,hz]
/-- A class is zero precisely when the SAME original injective cocycle has an ACTUAL global primitive. Closed-discrete support derives the needed lifting; no global projectivity or quasi-coherence of injectives is assumed. -/
theorem schemeModuleInjectiveInternalHomClassMap_closedDiscrete_zero_iff
    {D X : Scheme.{u}} [DiscreteTopology D] (f : D ⟶ X) (hf : IsClosedMap f)
    (L : D.Modules) {N : X.Modules} (I : InjectiveResolution N) (n : ℕ)
    (c : injectiveCocycleGroup I ((Scheme.Modules.pushforward f).obj L) (n+1)) :
    schemeModuleInjectiveInternalHomClassMap I ((Scheme.Modules.pushforward f).obj L) (n+1) c = 0 ↔
      ∃ g : (Scheme.Modules.pushforward f).obj L ⟶ I.cocomplex.X n,
        g ≫ I.cocomplex.d n (n+1) = c.val := by
  let P := (Scheme.Modules.pushforward f).obj L
  let K := schemeModuleInjectiveInternalHomComplex I P
  constructor
  · intro hz
    let z := schemeModuleInjectiveInternalHomCycleMap I P (n+1) c
    have hz' : z ≫ K.homologyπ (n+1) = 0 := hz
    let S : ShortComplex X.Modules :=
      ShortComplex.mk (K.toCycles n (n+1)) (K.homologyπ (n+1))
        (K.toCycles_comp_homologyπ n (n+1))
    have hs : S.Exact := S.exact_of_g_is_cokernel (K.homologyIsCokernel n (n+1) (by simp))
    letI : Epi S.toCycles := hs.epi_toCycles
    obtain ⟨t,ht⟩ := schemeModule_unitHom_lift_of_closedDiscreteSubHom f hf L
      (I.cocomplex.X n) S.X₁ S.cycles (𝟙 _) S.toCycles (S.liftCycles z hz')
    have htz : t ≫ K.toCycles n (n+1) = z := by
      calc
        t ≫ K.toCycles n (n+1) = t ≫ S.toCycles ≫ S.iCycles := by rw [S.toCycles_i]
        _ = S.liftCycles z hz' ≫ S.iCycles := by rw [← Category.assoc,ht]
        _ = z := S.liftCycles_i _ _
    refine ⟨schemeModuleHomUnitAddEquiv P (I.cocomplex.X n) t, ?_⟩
    apply (schemeModuleHomUnitAddEquiv P (I.cocomplex.X (n+1))).symm.injective
    rw [schemeModuleHomUnitAddEquiv_symm_postcompose]
    rw [AddEquiv.symm_apply_apply]
    change t ≫ K.d n (n+1) = _
    rw [← K.toCycles_i n (n+1), ← Category.assoc,htz]
    exact schemeModuleInjectiveInternalHomCycleMap_i I P (n+1) c
  · rintro ⟨g,hg⟩
    exact schemeModuleInjectiveInternalHomClassMap_boundary_zero I P n c g hg
end LinearStudy
