module
public import Linear.LocalComplexExactReflection
public import Linear.KoszulFunctionResolution
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory
universe u
variable {R : Type u} [CommRing R] {r : ℕ}

/-- Actual global affine Koszul exactness reflected from the corresponding
actual localized exterior-power complexes, using a constructed base-change
isomorphism. It does not assume a global regular sequence or global CM. -/
theorem functionKoszul_exactAt_of_local
    (H : Fin r → R) (j : ℕ)
    (hlocal : ∀ (P : Ideal R) [P.IsMaximal],
      (koszulComplex (Fintype.linearCombination (Localization.AtPrime P)
        (fun i => algebraMap R (Localization.AtPrime P) (H i)))).ExactAt j) :
    (koszulComplex (Fintype.linearCombination R H)).ExactAt j := by
  apply moduleChainComplex_exactAt_of_local
  intro P hP
  let S := Localization.AtPrime P
  let H' : Fin r → S := fun i => algebraMap R S (H i)
  have hl : (List.ofFn H).map (algebraMap R S)=List.ofFn H' := by
    simp [H',List.map_ofFn,Function.comp_def]
  let e := koszulComplex.ofListBaseChangeIso (algebraMap R S) (List.ofFn H) (List.ofFn H') hl
  have e' : ((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (koszulComplex (Fintype.linearCombination R H)) ≅
      koszulComplex (Fintype.linearCombination S H') := by
    simpa only [koszul_ofFn] using e
  exact HomologicalComplex.ExactAt.of_iso (hlocal P) e'.symm

end LinearStudy
