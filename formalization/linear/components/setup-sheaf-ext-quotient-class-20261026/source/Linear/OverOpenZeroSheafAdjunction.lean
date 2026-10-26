module
public import Linear.OverOpenZeroPresheafAdjunction
public import Linear.OverOpenZeroSheafFunctor
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory
universe u
variable {C : Type u} [Preorder C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u}) (U : C)
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Compose the PROVED presheaf adjunction with native sheafification. -/
def overOpenZeroPresheafSheafificationAdjunction :
    (overOpenZeroPresheafFunctor R.obj U ⋙ PresheafOfModules.sheafification (𝟙 R.obj)) ⊣
      (SheafOfModules.forget R ⋙ PresheafOfModules.pushforward₀ (Over.forget U) R.obj) :=
  (overOpenZeroPresheafAdjunction R.obj U).comp
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj))

/-- Actual SHEAF Hom equivalence using only proved presheaf comparison,
native sheafification and native fully faithful forgetful functor. -/
def overOpenZeroSheafHomEquiv (N : SheafOfModules.{u} (R.over U)) (M : SheafOfModules.{u} R) :
    ((overOpenZeroSheafFunctor R U).obj N ⟶ M) ≃
      (N ⟶ (SheafOfModules.overFunctor R U).obj M) :=
  ((overOpenZeroPresheafSheafificationAdjunction R U).homEquiv N.val M).trans
    ((SheafOfModules.fullyFaithfulForget (R.over U)).homEquiv
      (X := N) (Y := (SheafOfModules.overFunctor R U).obj M)).symm

/-- ACTUAL SHEAF extension-by-zero is left adjoint to ACTUAL native
restriction. The desired adjunction is proved,not supplied. -/
def overOpenZeroSheafAdjunction :
    overOpenZeroSheafFunctor R U ⊣ SheafOfModules.overFunctor R U :=
  Adjunction.mkOfHomEquiv {
    homEquiv := overOpenZeroSheafHomEquiv R U
    homEquiv_naturality_left_symm := by
      intro N' N M c a
      change ((overOpenZeroPresheafSheafificationAdjunction R U).homEquiv N'.val M).symm
          ((SheafOfModules.forget (R.over U)).map (c ≫ a)) =
        (overOpenZeroPresheafFunctor R.obj U ⋙ PresheafOfModules.sheafification (𝟙 R.obj)).map
          ((SheafOfModules.forget (R.over U)).map c) ≫
            ((overOpenZeroPresheafSheafificationAdjunction R U).homEquiv N.val M).symm
              ((SheafOfModules.forget (R.over U)).map a)
      rw [Functor.map_comp]
      exact (overOpenZeroPresheafSheafificationAdjunction R U).homEquiv_naturality_left_symm _ _
    homEquiv_naturality_right := by
      intro N M M' a c
      apply (SheafOfModules.forget (R.over U)).map_injective
      change (overOpenZeroPresheafSheafificationAdjunction R U).homEquiv N.val M' (a ≫ c) =
        (overOpenZeroPresheafSheafificationAdjunction R U).homEquiv N.val M a ≫
          (SheafOfModules.forget R ⋙ PresheafOfModules.pushforward₀ (Over.forget U) R.obj).map c
      exact (overOpenZeroPresheafSheafificationAdjunction R U).homEquiv_naturality_right a c }

end LinearStudy
