module
public import Linear.AffineQuasicoherentHomOpenSections
public import Linear.SchemeModuleHomOpenEvaluation
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
variable {R : CommRingCat.{u}} (N : (Spec R).Modules)

/-- Actual global sections of the restriction pushforward are the same
R-module as the original sections on U; no affine/principal condition on
U and no quasicoherence premise on N is needed. -/
def affineOpenPushforwardSectionsLinearEquiv (U : (Spec R).Opens) :
    (moduleSpecΓFunctor (R := R)).obj
      ((Scheme.Modules.pushforward U.ι).obj (N.restrict U.ι)) ≃ₗ[R] Γ(N,U) := by
  let i : op (U.ι ''ᵁ ⊤) ⟶ op U := (eqToHom U.ι_image_top.symm).op
  let E := Iso.addCommGroupIsoToAddEquiv
    ((N.restrictAppIso U.ι ⊤) ≪≫
      N.presheaf.mapIso (eqToIso U.ι_image_top.symm).op)
  refine { __ := E, map_smul' := ?_ }
  intro c x
  let y : Γ(N,U.ι ''ᵁ ⊤) := (N.restrictAppIso U.ι ⊤).hom x
  change N.presheaf.map i
      ((U.ι.appIso ⊤).inv (U.ι.app ⊤ ((Scheme.ΓSpecIso R).inv c)) • y) =
    ((Spec R).presheaf.map U.leTop.op ((Scheme.ΓSpecIso R).inv c)) •
      N.presheaf.map i y
  let j : op ⊤ ⟶ op (U.ι ''ᵁ ⊤) := (homOfLE le_top).op
  let r : Γ(Spec R,U.ι ''ᵁ ⊤) :=
    (Spec R).presheaf.map j ((Scheme.ΓSpecIso R).inv c)
  have hc : (U.ι.appIso ⊤).inv (U.ι.app ⊤ ((Scheme.ΓSpecIso R).inv c)) = r := by
    have hb := U.ι.app_appIso_inv ⊤
    change U.ι.app ⊤ ≫ (U.ι.appIso ⊤).inv = (Spec R).presheaf.map j at hb
    exact congr($(hb) ((Scheme.ΓSpecIso R).inv c))
  rw [hc]
  have hm := N.val.map_smul i r y
  change N.presheaf.map i (r • y) =
    ((Spec R).presheaf.map i r) • N.presheaf.map i y at hm
  rw [hm]
  congr 1

variable (M : (Spec R).Modules) [M.IsQuasicoherent]
/-- On any actual open U, the genuine internal Hom sections correspond
to maps from the SAME global source into the SAME original sections of
the target on U. This is the codomain-localization interface. -/
def affineQuasicoherentHomActualOpenSectionsLinearEquiv (U : (Spec R).Opens) :
    Γ(schemeModuleHomModuleSheaf M N,U) ≃ₗ[R]
      ((moduleSpecΓFunctor (R := R)).obj M →ₗ[R] Γ(N,U)) :=
  (affineQuasicoherentHomOpenSectionsLinearEquiv M N U).trans
    (LinearEquiv.arrowCongr (LinearEquiv.refl R _) (affineOpenPushforwardSectionsLinearEquiv N U))
end LinearStudy
