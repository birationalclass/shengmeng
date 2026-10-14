module
public import Linear.SchemeModuleFiniteSupportCohomology
public import Linear.AffineKoszulGeometricAllCohomologySupport
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u v
attribute [local irreducible] affineKoszulInternalHomCohomologyClosedCutUnitIso
variable (k : Type v) [Field k] (R : CommRingCat.{u}) [Algebra k R]
  (N : ModuleCat.{u} R) (r : ℕ) (H : Fin r → R)

/-- ACTUAL positive SHEAF cohomology of EVERY actual internal-Hom
cohomology object vanishes on the SAME ambient Spec R. Derive its SAME
original finite-cut support from the proved ACTUAL geometric unit and
the original field-finite quotient. N is ANY original coefficient module;
source exactness is explicit here and derived by the original-cut wrapper. -/
theorem affineKoszulInternalHom_actualHigherSheafCohomology_vanish
    (he : ∀ j : ℕ,0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j)
    (hfin : Module.Finite k (R ⧸ Ideal.span (Set.range H))) (j p : ℕ) :
    Subsingleton (schemeModuleActualCohomology (Spec R)
      ((affineKoszulInternalHomCochainComplex R N r H).homology j) (p+1)) := by
  let I := Ideal.span (Set.range H)
  let C := CommRingCat.of (R ⧸ I)
  letI : Module.Finite k C := hfin
  letI : IsArtinianScheme (Spec C) := finiteFieldAlgebra_spec_isArtinian k C
  let i : Spec C ⟶ Spec R := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let M := (affineKoszulInternalHomCochainComplex R N r H).homology j
  exact schemeModule_actualHigherCohomology_vanish_of_artinianSupportIso i M
    ((Scheme.Modules.pullback i).obj M)
    (affineKoszulInternalHomCohomologyClosedCutUnitIso R N r H he j) p

/-- A clearly specified OUTPUT proposition on SAME ORIGINAL actual
internal-Hom cohomology objects and native DERIVED SHEAF H. It is proved
from original source exactness/quotient finiteness,never assumed. -/
def affineKoszulActualHigherSheafCohomologyConclusions : Prop :=
  ∀ (N : ModuleCat.{u} R) (j p : ℕ),
    Subsingleton (schemeModuleActualCohomology (Spec R)
      ((affineKoszulInternalHomCochainComplex R N r H).homology j) (p+1))

/-- Produce the actual all-coefficients/all-degrees higher-SHEAF vanishing
OUTPUT from proved actual finite-cut support,no desired certificate. -/
theorem affineKoszulActualHigherSheafCohomologyConclusions_of_exact_fieldFinite
    (he : ∀ j : ℕ,0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j)
    (hfin : Module.Finite k (R ⧸ Ideal.span (Set.range H))) :
    affineKoszulActualHigherSheafCohomologyConclusions R r H :=
  fun N j p => affineKoszulInternalHom_actualHigherSheafCohomology_vanish k R N r H he hfin j p

end LinearStudy
