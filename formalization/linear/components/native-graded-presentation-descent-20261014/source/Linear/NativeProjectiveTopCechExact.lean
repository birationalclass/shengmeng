module
public import Linear.NativeProjectiveMatrixHomology
public import Linear.NativeProjectiveOrderedCechExact
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace MvPolynomial
open LinearStudy AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable {K : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- An ACTUAL short exact sequence of quasicoherent sheaves on the original
coordinate Proj gives a cokernel sequence on top ordered Cech homology.
The needed next-degree vanishing follows from the finite coordinate cover;
it is not supplied as an extra vanishing hypothesis. -/
def coordinateNativeTopCech_shortExact_gIsCokernel
    {T : ShortComplex (Proj (homogeneousSubmodule σ K)).Modules}
    (hT : T.ShortExact)
    [T.X₁.IsQuasicoherent] [T.X₂.IsQuasicoherent] [T.X₃.IsQuasicoherent]
    (n : ℕ) (hc : Fintype.card σ = n+2) :
    IsColimit (CokernelCofork.ofπ
      (T.map (coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n)).g
      (T.map (coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n)).zero) := by
  let F := Scheme.Modules.orderedBaseCechComplexFunctor
    (homogeneousProjπ (R := K) (σ := σ)) (coordinateOpenCover (R := K) (σ := σ))
  let C := T.map F
  have hC : C.ShortExact := nativeProjectiveOrderedCech_shortExact
    (homogeneousSubmodule σ K) (fun i : ULift σ => X i.down)
    (fun i => isHomogeneous_X K i.down) (homogeneousProjπ (R := K) (σ := σ)) hT
  have hz : C.X₁.ExactAt (n+2) := by
    apply Scheme.Modules.orderedBaseCechComplex_exactAt_of_card_le
    simpa using (le_of_eq hc)
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at hz
  have hEpi : Epi (HomologicalComplex.homologyMap C.g (n+1)) :=
    (hC.homology_exact₃ (n+1) (n+2) (by simp [ComplexShape.up_Rel])).epi_f_iff.mpr
      (hz.eq_of_tgt _ _)
  letI : Epi (T.map (coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n)).g := hEpi
  have hex : (T.map (coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n)).Exact :=
    hC.homology_exact₂ (n+1)
  exact hex.gIsCokernel

/-- Actual top-Cech cokernel comparison for a genuine short exact
quasicoherent sheaf sequence, constructed using its proved colimit data. -/
def coordinateNativeTopCech_shortExact_cokernelIso
    {T : ShortComplex (Proj (homogeneousSubmodule σ K)).Modules}
    (hT : T.ShortExact)
    [T.X₁.IsQuasicoherent] [T.X₂.IsQuasicoherent] [T.X₃.IsQuasicoherent]
    (n : ℕ) (hc : Fintype.card σ = n+2) :
    cokernel (T.map (coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n)).f ≅
    (coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).obj T.X₃ :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (coordinateNativeTopCech_shortExact_gIsCokernel hT n hc)

theorem coordinateNativeTopCech_shortExact_cokernelIso_quotient
    {T : ShortComplex (Proj (homogeneousSubmodule σ K)).Modules}
    (hT : T.ShortExact)
    [T.X₁.IsQuasicoherent] [T.X₂.IsQuasicoherent] [T.X₃.IsQuasicoherent]
    (n : ℕ) (hc : Fintype.card σ = n+2) :
    cokernel.π (T.map (coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n)).f ≫
      (coordinateNativeTopCech_shortExact_cokernelIso hT n hc).hom =
    (coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).map T.g := by
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit _) (coordinateNativeTopCech_shortExact_gIsCokernel hT n hc)
      WalkingParallelPair.one

end MvPolynomial
