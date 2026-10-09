module
public import Linear.LocalExactReflection
public import Linear.ExtendScalarsActualTensor
public import Linear.Vendor.KoszulComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory
universe u
variable {R : Type u} [CommRing R]

/-- Exactness of an actual module chain complex is reflected from the
actual tensor-localized chain complexes at maximal ideals. -/
theorem moduleChainComplex_exactAt_of_local
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (j : ℕ)
    (hlocal : ∀ (P : Ideal R) [P.IsMaximal],
      (((ModuleCat.extendScalars (algebraMap R (Localization.AtPrime P))).mapHomologicalComplex _).obj K).ExactAt j) :
    K.ExactAt j := by
  rw [HomologicalComplex.exactAt_iff,ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  apply linearMaps_exact_of_baseChange_exact_maximal (K.sc j).f.hom (K.sc j).g.hom
  · exact ModuleCat.hom_ext_iff.mp (K.sc j).zero
  · intro P hP
    have h := hlocal P
    rw [HomologicalComplex.exactAt_iff,ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h
    let S := Localization.AtPrime P
    exact (Function.Exact.iff_of_ladder_addEquiv
      (extendScalarsActualTensorAddEquiv (S := S) (K.sc j).X₁)
      (extendScalarsActualTensorAddEquiv (S := S) (K.sc j).X₂)
      (extendScalarsActualTensorAddEquiv (S := S) (K.sc j).X₃)
      (f₁₂ := (((ModuleCat.extendScalars (algebraMap R S)).map (K.sc j).f).hom.toAddMonoidHom))
      (f₂₃ := (((ModuleCat.extendScalars (algebraMap R S)).map (K.sc j).g).hom.toAddMonoidHom))
      (g₁₂ := ((K.sc j).f.hom.baseChange S).toAddMonoidHom)
      (g₂₃ := ((K.sc j).g.hom.baseChange S).toAddMonoidHom)
      (AddMonoidHom.ext fun x => congrFun
        (extendScalarsActualTensor_naturality (S := S) (K.sc j).f) x)
      (AddMonoidHom.ext fun x => congrFun
        (extendScalarsActualTensor_naturality (S := S) (K.sc j).g) x)).mpr h

end LinearStudy
