module
public import Linear.OriginalChainDegreeOneConeMap
public import Linear.CochainConeLiftDerivedBridge
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
open CochainComplex.HomComplex
universe u v
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The actual cone projection pulls back to the SAME ordered top functional
of the original chain complex. This is a cocycle equality,not an assumed class. -/
theorem originalChainDegreeOneConeMap_topCocycle
    (C : ChainComplex A ℕ) (h : C.d 2 1 = 0) :
    (CochainComplex.mappingCone.fst
      ((CochainComplex.singleFunctor A 0).map (C.d 1 0))).precomp
        (originalChainDegreeOneConeMap C h) =
      Cocycle.toSingleMk (originalChainAsCochainXIso C (-1) 1 (by norm_num)).hom
        (by norm_num) (-2) (by norm_num) (by
          rw [originalChainAsCochain_d C (-2) (-1) 2 1 (by norm_num) (by norm_num)]
          simp [Category.assoc,h]) := by
  apply Subtype.ext
  exact CochainComplex.mappingCone.lift_fst _ _ _ _

/-- The native triangle pulls back to MINUS the original ordered top cocycle.
The sign is derived from the native cone definition and the actual comparison. -/
theorem originalChainDegreeOneConeMap_triangleTop
    (C : ChainComplex A ℕ) (h : C.d 2 1 = 0) :
    originalChainDegreeOneConeMap C h ≫
      (CochainComplex.mappingCone.triangle
        ((CochainComplex.singleFunctor A 0).map (C.d 1 0))).mor₃ =
      -Cocycle.equivHomShift.symm
        (Cocycle.toSingleMk (originalChainAsCochainXIso C (-1) 1 (by norm_num)).hom
          (by norm_num) (-2) (by norm_num) (by
            rw [originalChainAsCochain_d C (-2) (-1) 2 1 (by norm_num) (by norm_num)]
            simp [Category.assoc,h])) := by
  rw [cochainConeTriangle_mor3_neg_fst,map_neg,Preadditive.comp_neg,
    ← Cocycle.equivHomShift_symm_precomp,originalChainDegreeOneConeMap_topCocycle]

end LinearStudy
