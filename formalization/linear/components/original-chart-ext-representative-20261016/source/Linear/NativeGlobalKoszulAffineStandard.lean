module
public import Linear.NativeGlobalKoszulSpecSectionComplex
import all Mathlib.AlgebraicGeometry.Modules.Tilde
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]

/-- ACTUAL entire affine SHEAF-complex comparison for the SAME ORIGINAL
global Koszul,ALL integer twists. Its target is the native standard exterior
Koszul on ORIGINAL H_i/a^q,sheafified by the actual native tilde functor.
Source quasicoherence and ALL differential/scalar compatibility are PROVED. -/
def nativeProjectiveKoszulStandardAffineIso [IsNoetherianRing S]
    {J : Type} (b : J → S) (hb : ∀ i, b i ∈ 𝓑 1)
    (hgen : Algebra.adjoin K (Set.range b) = ⊤)
    {r q : ℕ} (H : Fin r → S) (hH : ∀ i, H i ∈ 𝓑 q) (k : ℤ)
    (a : S) (ha : a ∈ 𝓑 1) :
    let R := CommRingCat.of (HomogeneousLocalization.Away 𝓑 a)
    letI : (tilde.functor R).Additive :=
      AlgebraicGeometry.instAdditiveModuleCatCarrierModulesSpecFunctor (R := R)
    let j := Proj.awayι 𝓑 a ha one_pos
    nativeProjectiveKoszulOnAffine 𝓑 R j H hH k ≅
      ((tilde.functor R).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (koszulComplex (Fintype.linearCombination (HomogeneousLocalization.Away 𝓑 a)
          (fun i => HomogeneousLocalization.Away.mk 𝓑 ha q (H i)
            (by simpa using hH i)))) := by
  let R := CommRingCat.of (HomogeneousLocalization.Away 𝓑 a)
  letI : (tilde.functor R).Additive :=
      AlgebraicGeometry.instAdditiveModuleCatCarrierModulesSpecFunctor (R := R)
  let j := Proj.awayι 𝓑 a ha one_pos
  let T := (tilde.functor R).mapHomologicalComplex (ComplexShape.down ℕ)
  exact (nativeProjectiveKoszulAffineCounitIso 𝓑 b hb hgen R j H hH k).symm ≪≫
    T.mapIso (nativeProjectiveKoszulSpecSectionComplexIso 𝓑 H hH k a ha) ≪≫
    T.mapIso (homogeneousKoszulCoordinateComplexIso
      (fun i => HomogeneousLocalization.Away.mk 𝓑 ha q (H i)
        (by simpa using hH i))).symm

end LinearStudy
