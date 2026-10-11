module
public import Linear.TildePushforward
public import Linear.ExtendScalarsActualTensor
public import Linear.NativeAffineInternalHomLinear
public import Linear.OriginalTildeScalar
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The actual associated module of the same affine algebra is its actual
structure-sheaf pushforward. No finiteness or replacement model is assumed. -/
def actualAffineAlgebraStructurePushforwardIso :
    tilde (ModuleCat.of A B) ≅
      (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
        (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf) := by
  let φ : CommRingCat.of A ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap A B)
  let e : ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of B B)) ≅
      ModuleCat.of A B := (restrictedAlgebraModuleEquiv (R := A) (S := B)).toModuleIso
  exact (tilde.functor (CommRingCat.of A)).mapIso e.symm ≪≫
    tildePushforwardIso φ (ModuleCat.of B B) ≪≫
    (Scheme.Modules.pushforward (Spec.map φ)).mapIso tildeSelf

/-- Actual affine algebra duals correspond linearly to sections of the SAME
internal Hom of the actual structure-sheaf pushforward. The comparison is the
specified fully faithful tilde map and actual pushforward/unit isomorphisms. -/
def actualAffineAlgebraDualInternalHomSectionsLinearEquiv :
    let P := (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
      (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf)
    let Q : (Spec (CommRingCat.of A)).Modules := SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf
    letI := originalAffineHomBaseModule (CommRingCat.of A) P Q
    (B →ₗ[A] A) ≃ₗ[A] Γ(schemeModuleHomModuleSheaf P Q,⊤) := by
  let P := (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
    (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf)
  let Q : (Spec (CommRingCat.of A)).Modules := SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf
  letI := originalAffineHomBaseModule (CommRingCat.of A) P Q
  let F := tilde.functor (CommRingCat.of A)
  let e : tilde (ModuleCat.of A B) ≅ P := actualAffineAlgebraStructurePushforwardIso
  let t : tilde (ModuleCat.of A A) ≅ Q := tildeSelf
  let E : (B →ₗ[A] A) ≃ Γ(schemeModuleHomModuleSheaf P Q,⊤) :=
    (ModuleCat.homEquiv (M := ModuleCat.of A B) (N := ModuleCat.of A A)).symm.trans
      ((tilde.fullyFaithfulFunctor (R := CommRingCat.of A)).homEquiv.trans
        ((Iso.homCongr e t).trans (schemeModuleHomTopSectionsEquiv P Q).symm))
  refine { __ := E, map_add' := ?_, map_smul' := ?_ }
  · intro f g
    apply (schemeModuleHomTopSectionsEquiv P Q).injective
    change e.inv ≫ F.map (ModuleCat.ofHom (f+g)) ≫ t.hom = _
    rw [schemeModuleHomTopSectionsEquiv_add]
    change e.inv ≫ F.map (ModuleCat.ofHom (f+g)) ≫ t.hom =
      (e.inv ≫ F.map (ModuleCat.ofHom f) ≫ t.hom) +
        (e.inv ≫ F.map (ModuleCat.ofHom g) ≫ t.hom)
    change e.inv ≫ F.map (ModuleCat.ofHom f + ModuleCat.ofHom g) ≫ t.hom = _
    have hf := tilde.map_add (R := CommRingCat.of A) (ModuleCat.ofHom f) (ModuleCat.ofHom g)
    refine (congrArg (fun h => e.inv ≫ h ≫ t.hom) hf).trans ?_
    apply SheafOfModules.hom_ext
    ext U x
    exact (t.hom.app U.unop).hom.map_add _ _
  · intro r f
    apply (schemeModuleHomTopSectionsEquiv P Q).injective
    change schemeModuleHomTopSectionsEquiv P Q (E (r • f)) =
      schemeModuleHomTopSectionsEquiv P Q
        (((Scheme.ΓSpecIso (CommRingCat.of A)).inv r) • E f)
    rw [schemeModuleHomTopSectionsEquiv_smul]
    change e.inv ≫ F.map (ModuleCat.ofHom (r • f)) ≫ t.hom =
      (e.inv ≫ F.map (ModuleCat.ofHom f) ≫ t.hom) ≫
        originalGlobalModuleScalar ((Scheme.ΓSpecIso (CommRingCat.of A)).inv r) Q
    have h : ModuleCat.ofHom (r • f) = ModuleCat.ofHom f ≫
        ModuleCat.ofHom (r • (LinearMap.id : A →ₗ[A] A)) := by
      apply ModuleCat.hom_ext
      ext x
      rfl
    rw [h,F.map_comp,← originalTildeScalar_unit (R := CommRingCat.of A) r]
    with_unfolding_all simp only [Category.assoc,Iso.hom_inv_id_assoc]
    rfl

end LinearStudy
