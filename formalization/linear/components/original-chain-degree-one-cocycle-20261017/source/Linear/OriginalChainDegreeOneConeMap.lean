module
public import Linear.ChainResolutionAsCochain
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
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

/-- Construct a map from the SAME original chain complex to the cone of its
ACTUAL first differential. The top differential vanishing is explicit here;
original bounded Koszul applications still must derive it. -/
def originalChainDegreeOneConeMap (C : ChainComplex A ℕ)
    (h : C.d 2 1 = 0) :
    originalChainAsCochain C ⟶ CochainComplex.mappingCone
      ((CochainComplex.singleFunctor A 0).map (C.d 1 0)) := by
  let a : Cocycle (originalChainAsCochain C)
      ((CochainComplex.singleFunctor A 0).obj (C.X 1)) 1 :=
    Cocycle.toSingleMk (originalChainAsCochainXIso C (-1) 1 (by norm_num)).hom
      (by norm_num) (-2) (by norm_num) (by
        rw [originalChainAsCochain_d C (-2) (-1) 2 1 (by norm_num) (by norm_num)]
        simp [Category.assoc,h])
  let b : Cochain (originalChainAsCochain C)
      ((CochainComplex.singleFunctor A 0).obj (C.X 0)) 0 :=
    Cochain.toSingleMk (originalChainAsCochainXIso C 0 0 (by norm_num)).hom (by norm_num)
  refine CochainComplex.mappingCone.lift _ a b ?_
  change δ 0 1 (Cochain.toSingleMk
    (originalChainAsCochainXIso C 0 0 (by norm_num)).hom (by norm_num)) +
      (Cochain.toSingleMk
        (originalChainAsCochainXIso C (-1) 1 (by norm_num)).hom (by norm_num)).comp
          (Cochain.ofHom ((CochainComplex.singleFunctor A 0).map (C.d 1 0)))
          (add_zero 1) = 0
  rw [Cochain.δ_toSingleMk _ _ 1 (-1) (by norm_num),
    ← Cochain.toSingleMk_postcomp]
  rw [originalChainAsCochain_d C (-1) 0 1 0 (by norm_num) (by norm_num)]
  simp [Category.assoc]

end LinearStudy
