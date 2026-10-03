module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem actual_affine_ideal_pushforward {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (J : X.IdealSheafData) :
    (J.map f).ideal ⟨⊤, isAffineOpen_top Y⟩ =
      (J.ideal ⟨⊤, isAffineOpen_top X⟩).comap f.appTop.hom := by
  have : IsAffineHom f := isAffineHom_of_isAffine f
  exact IdealSheafData.ideal_map_of_isAffineHom J f ⟨⊤, isAffineOpen_top Y⟩

/-- Final theorem: actual scheme-theoretic pullback of an ideal sheaf
between affine schemes is extension of the actual coordinate-ring ideal.
This is derived from the actual pullback/pushforward Galois connection,
not from a supplied ring-to-scheme compatibility assertion. -/
theorem actual_affine_ideal_pullback {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (I : Y.IdealSheafData) :
    (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ =
      (I.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom := by
  let K := I.ideal ⟨⊤, isAffineOpen_top Y⟩
  let L := (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩
  have h (J : Ideal Γ(X, ⊤)) : L ≤ J ↔ K.map f.appTop.hom ≤ J := by
    have hleft : L ≤ J ↔ I.comap f ≤ IdealSheafData.ofIdealTop J := by
      constructor
      · intro hj
        apply IdealSheafData.le_of_isAffine
        simpa using hj
      · intro hj
        simpa using hj ⟨⊤, isAffineOpen_top X⟩
    rw [hleft, ← IdealSheafData.le_map_iff_comap_le, Ideal.map_le_iff_le_comap]
    constructor
    · intro hj
      have hh := hj ⟨⊤, isAffineOpen_top Y⟩
      rw [actual_affine_ideal_pushforward] at hh
      simpa using hh
    · intro hj
      apply IdealSheafData.le_of_isAffine
      rw [actual_affine_ideal_pushforward]
      simpa using hj
  exact ((h (K.map f.appTop.hom)).mpr le_rfl).antisymm ((h L).mp le_rfl)

end
end Negativity
