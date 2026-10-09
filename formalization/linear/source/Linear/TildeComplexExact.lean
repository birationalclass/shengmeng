module
public import Linear.TildePreservesMono
public import Linear.KoszulExactResolution
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u

/-- The original exterior Koszul mapped to actual native affine modules. -/
def tildeFunctionKoszulComplex (R : CommRingCat.{u}) {r : ℕ} (H : Fin r → R) :
    ChainComplex (Spec R).Modules ℕ :=
  ((tilde.functor R).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (koszulComplex (Fintype.linearCombination R H))

def tildeFunctionKoszulQuotientComplex (R : CommRingCat.{u}) {r : ℕ} (H : Fin r → R) :
    ChainComplex (Spec R).Modules ℕ :=
  ((tilde.functor R).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    ((ChainComplex.single₀ (ModuleCat R)).obj
      (ModuleCat.of R (R ⧸ Ideal.span (Set.range H))))

/-- The actual mapped quotient augmentation, with both complexes explicit. -/
def tildeFunctionKoszulAugmentation (R : CommRingCat.{u}) {r : ℕ} (H : Fin r → R) :
    tildeFunctionKoszulComplex R H ⟶ tildeFunctionKoszulQuotientComplex R H :=
  ((tilde.functor R).mapHomologicalComplex (ComplexShape.down ℕ)).map
    (functionKoszulAugmentationMap H)

/-- Exactness of the actual associated-sheaf complex on native Spec R,
proved from the constructed affine module complex and tilde exactness. -/
theorem tilde_chainComplex_exactAt (R : CommRingCat.{u})
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (j : ℕ) (h : K.ExactAt j) :
    (((tilde.functor R).mapHomologicalComplex (ComplexShape.down ℕ)).obj K).ExactAt j := by
  letI := tilde_functor_preservesHomology R
  change ((K.sc j).map (tilde.functor R)).Exact
  exact h.map (tilde.functor R)

/-- The same actual exterior Koszul gives a genuine native affine sheaf
complex that is exact in every positive degree. Twisting and projective
gluing are not asserted here. -/
theorem tilde_functionKoszul_exactAt (R : CommRingCat.{u}) {r : ℕ}
    (H : Fin r → R)
    (he : ∀ j : ℕ,0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j)
    (j : ℕ) (hj : 0 < j) :
    (((tilde.functor R).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (koszulComplex (Fintype.linearCombination R H))).ExactAt j :=
  tilde_chainComplex_exactAt R _ j (he j hj)

/-- The genuine affine sheaf complex carries the mapped natural quotient
augmentation, which is a quasi-isomorphism. No duality assumption is used. -/
theorem tilde_functionKoszul_augmentation_quasiIso (R : CommRingCat.{u}) {r : ℕ}
    (H : Fin r → R)
    (he : ∀ j : ℕ,0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j) :
    QuasiIso (((tilde.functor R).mapHomologicalComplex (ComplexShape.down ℕ)).map
      (functionKoszulAugmentationMap H)) := by
  letI := tilde_functor_preservesHomology R
  letI := functionKoszulAugmentation_quasiIso_of_exact H he
  infer_instance

end LinearStudy
