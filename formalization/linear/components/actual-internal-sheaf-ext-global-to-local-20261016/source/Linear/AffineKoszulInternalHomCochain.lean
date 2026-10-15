module
public import Linear.SchemeModuleInternalHomComplex
public import Linear.AffineKoszulHomCoefficientRestriction
public import Mathlib.CategoryTheory.Abelian.Ext
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u

/-- ACTUAL internal-Hom cochain complex of the SAME associated original
Koszul chain complex into the ORIGINAL tilde N. Source exactness is not
needed to construct this complex;derived SHEAF Ext comparison is separate. -/
def affineKoszulInternalHomCochainComplex (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (r : ℕ) (H : Fin r → R) :
    CochainComplex (Spec R).Modules ℕ :=
  schemeModuleInternalHomCochainComplex (tilde N)
    (((tilde.functor R).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (koszulComplex (Fintype.linearCombination R H)))

theorem affineKoszulInternalHomCochainComplex_X (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (r j : ℕ) (H : Fin r → R) :
    (affineKoszulInternalHomCochainComplex R N r H).X j =
      schemeModuleHomModuleSheaf
        (tilde (ModuleCat.of R (⋀[R]^j (Fin r → R)))) (tilde N) := rfl

/-- All original differentials retain their original precomposition value. -/
theorem affineKoszulInternalHomCochainComplex_d (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (r : ℕ) (H : Fin r → R) (i j : ℕ) :
    (affineKoszulInternalHomCochainComplex R N r H).d i j =
      schemeModuleHomPrecompose ((tilde.functor R).map
        ((koszulComplex (Fintype.linearCombination R H)).d j i)) := rfl

/-- Reuse the NATIVE library linear-Yoneda Hom cochain complex of the
SAME original Koszul chain complex;no replacement cochain model. -/
def affineKoszulNativeHomCochainComplex (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (r : ℕ) (H : Fin r → R) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  (koszulComplex (Fintype.linearCombination R H)).linearYonedaObj R N

/-- The actual native categorical Hom term is the SAME original linear-map
module,by the existing ModuleCat.homLinearEquiv;no coefficient condition. -/
def affineKoszulNativeHomCochainTermIso (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (r j : ℕ) (H : Fin r → R) :
    (affineKoszulNativeHomCochainComplex R N r H).X j ≅
      ModuleCat.of R ((⋀[R]^j (Fin r → R)) →ₗ[R] N) :=
  ModuleCat.homLinearEquiv.toModuleIso

/-- Original native Hom differentials and original linear precomposition
are the SAME map under the SAME existing categorical/linear Hom iso. -/
theorem affineKoszulNativeHomCochainTermIso_d (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (r : ℕ) (H : Fin r → R) (i j : ℕ) :
    (affineKoszulNativeHomCochainComplex R N r H).d i j ≫
        (affineKoszulNativeHomCochainTermIso R N r j H).hom =
      (affineKoszulNativeHomCochainTermIso R N r i H).hom ≫
        ModuleCat.ofHom (LinearMap.lcomp R N
          ((koszulComplex (Fintype.linearCombination R H)).d j i).hom) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro x
  rfl

/-- Consecutive ACTUAL internal-Hom differentials use the ORIGINAL
explicit Koszul differential,not only an unspecified chain morphism. -/
theorem affineKoszulInternalHomCochainComplex_d_next (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (r : ℕ) (H : Fin r → R) (j : ℕ) :
    (affineKoszulInternalHomCochainComplex R N r H).d j (j+1) =
      schemeModuleHomPrecompose ((tilde.functor R).map
        (ModuleCat.ofHom (koszulComplex.d (Fintype.linearCombination R H) j))) := by
  rw [affineKoszulInternalHomCochainComplex_d,koszulComplex.d_eq_d]

end LinearStudy
