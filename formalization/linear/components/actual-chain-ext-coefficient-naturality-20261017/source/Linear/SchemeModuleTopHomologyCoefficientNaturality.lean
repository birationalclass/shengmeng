module
public import Linear.SchemeModuleTopHomCoefficientNaturality
public import Mathlib.CategoryTheory.CommSq
public import Linear.SchemeModuleChainTopOpcycleIso
public import Linear.SchemeModuleChainTopHomology
public import Linear.SchemeModuleHomCokernelCoefficientNaturality
public import Linear.SchemeModuleSourceHomCoefficientComplex
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- Native top cohomology/cokernel comparison for SAME Hom complex commutes with coefficients.
Its square comes from native HomologyMapData on actual universal cokernels. -/
theorem schemeModuleChainTopHomologyCokernelIso_coefficientNaturality
    (K : ChainComplex X.Modules ℕ) (p : ℕ) (hAbove : IsZero (K.X (p+2)))
    {N M : X.Modules} (c : N ⟶ M) :
    HomologicalComplex.homologyMap (schemeModuleSourceHomCoefficientComplexMap K c) (p+1) ≫
        (schemeModuleChainTopHomologyCokernelIso K M p hAbove).hom =
      (schemeModuleChainTopHomologyCokernelIso K N p hAbove).hom ≫
        schemeModuleChainDifferentialHomCokernelCoefficientMap K p c := by
  let SN : ShortComplex X.Modules := ShortComplex.mk
    (schemeModuleHomPrecompose (N := N) (K.d (p+1) p))
    (schemeModuleHomPrecompose (N := N) (K.d (p+2) (p+1))) (by
      rw [← schemeModuleHomPrecompose_comp,K.d_comp_d]
      exact schemeModuleHomPrecompose_zero _ _ N)
  let SM : ShortComplex X.Modules := ShortComplex.mk
    (schemeModuleHomPrecompose (N := M) (K.d (p+1) p))
    (schemeModuleHomPrecompose (N := M) (K.d (p+2) (p+1))) (by
      rw [← schemeModuleHomPrecompose_comp,K.d_comp_d]
      exact schemeModuleHomPrecompose_zero _ _ M)
  let phi : SN ⟶ SM :=
    { τ₁ := schemeModuleHomPostcompose (P := K.X p) c
      τ₂ := schemeModuleHomPostcompose (P := K.X (p+1)) c
      τ₃ := schemeModuleHomPostcompose (P := K.X (p+2)) c
      comm₁₂ := (schemeModuleInternalHomSourceNatTrans (K.d (p+1) p)).naturality c
      comm₂₃ := (schemeModuleInternalHomSourceNatTrans (K.d (p+2) (p+1))).naturality c }
  have hgN : SN.g = 0 := by
    change schemeModuleHomPrecompose (N := N) (K.d (p+2) (p+1)) = 0
    rw [hAbove.eq_of_src (K.d (p+2) (p+1)) 0]
    exact schemeModuleHomPrecompose_zero _ _ N
  have hgM : SM.g = 0 := by
    change schemeModuleHomPrecompose (N := M) (K.d (p+2) (p+1)) = 0
    rw [hAbove.eq_of_src (K.d (p+2) (p+1)) 0]
    exact schemeModuleHomPrecompose_zero _ _ M
  let cN : CokernelCofork SN.f := CokernelCofork.ofπ (cokernel.π SN.f) (cokernel.condition SN.f)
  let cM : CokernelCofork SM.f := CokernelCofork.ofπ (cokernel.π SM.f) (cokernel.condition SM.f)
  have hcomm : phi.τ₂ ≫ cM.π = cN.π ≫
      schemeModuleChainDifferentialHomCokernelCoefficientMap K p c := by
    exact (schemeModuleChainDifferentialHomCokernelCoefficientMap_projection K p c).symm
  let gamma := ShortComplex.HomologyMapData.ofIsColimitCokernelCofork phi
    hgN cN (cokernelIsCokernel SN.f) hgM cM (cokernelIsCokernel SM.f)
    (schemeModuleChainDifferentialHomCokernelCoefficientMap K p c)
    hcomm
  have hck : ShortComplex.homologyMap phi ≫
      (ShortComplex.HomologyData.ofHasCokernel SM hgM).left.homologyIso.hom =
    (ShortComplex.HomologyData.ofHasCokernel SN hgN).left.homologyIso.hom ≫
      schemeModuleChainDifferentialHomCokernelCoefficientMap K p c :=
    gamma.left.homologyMap_comm
  have hsc := schemeModuleSourceHomHomologyIsoSc_coefficientNaturality K p c
  have hs : CommSq
      (HomologicalComplex.homologyMap (schemeModuleSourceHomCoefficientComplexMap K c) (p+1))
      ((schemeModuleInternalHomCochainComplex N K).homologyIsoSc' p (p+1) (p+2) (by simp) (by simp)).hom
      ((schemeModuleInternalHomCochainComplex M K).homologyIsoSc' p (p+1) (p+2) (by simp) (by simp)).hom
      (ShortComplex.homologyMap phi) := ⟨hsc⟩
  have ht : CommSq (ShortComplex.homologyMap phi)
      (ShortComplex.HomologyData.ofHasCokernel SN hgN).left.homologyIso.hom
      (ShortComplex.HomologyData.ofHasCokernel SM hgM).left.homologyIso.hom
      (schemeModuleChainDifferentialHomCokernelCoefficientMap K p c) := ⟨hck⟩
  dsimp only [schemeModuleChainTopHomologyCokernelIso,Iso.trans_hom]
  exact (hs.vert_comp ht).w

end LinearStudy
