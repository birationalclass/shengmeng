module
public import Linear.AffineQuasicoherentHomActualOpenEvaluation
public import Linear.FinitePresentationHomCodomainLocalization
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {R : CommRingCat.{u}} (M N : (Spec R).Modules)
variable [M.IsQuasicoherent] [N.IsQuasicoherent]

/-- The actual internal Hom of the original quasicoherent module sheaves
on Spec R is quasicoherent when the SAME global source is finitely
presented. Derived from actual open-section evaluation and restriction
and library finite-presentation localization, including the zero open. -/
theorem affineFinitePresentationInternalHom_isQuasicoherent
    [Module.FinitePresentation R ((moduleSpecΓFunctor (R := R)).obj M)] :
    (schemeModuleHomModuleSheaf M N).IsQuasicoherent := by
  let H := schemeModuleHomModuleSheaf M N
  apply (isQuasicoherent_iff_isIso_fromTildeΓ H).mpr
  apply (isIso_fromTildeΓ_iff_isLocalizing H).mpr
  have hN : IsLocalizing (modulesSpecToSheaf.obj N) :=
    (isIso_fromTildeΓ_iff_isLocalizing N).mp inferInstance
  intro r
  let U : (Spec R).Opens := PrimeSpectrum.basicOpen r
  let S := Submonoid.powers r
  let g := ((modulesSpecToSheaf.obj N).obj.map U.leTop.op).hom
  let f := ((modulesSpecToSheaf.obj H).obj.map U.leTop.op).hom
  letI : IsLocalizedModule S g := hN r
  let E0 := affineQuasicoherentHomActualOpenSectionsLinearEquiv N M ⊤
  let EU := affineQuasicoherentHomActualOpenSectionsLinearEquiv N M U
  let L := LinearMap.compRight (M := (moduleSpecΓFunctor (R := R)).obj M) R g
  have hcomp : EU.toLinearMap.comp f = L.comp E0.toLinearMap := by
    ext h x
    exact affineQuasicoherentHomActualOpenSectionsLinearEquiv_restrict M N U.leTop h x
  change IsLocalizedModule S f
  apply (IsLocalizedModule.comp_iff_of_bijective_left S EU.toLinearMap EU.bijective).mp
  rw [hcomp]
  letI : IsLocalizedModule S L := finitePresentationHom_codomain_isLocalizedModule S g
  exact IsLocalizedModule.of_linearEquiv_right S L E0
end LinearStudy
