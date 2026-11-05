module
public import Linear.ModuleShortComplexTopQuotientNaturality
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace CategoryTheory.ShortComplex
universe u v
variable {B : Type u} [CommRing B] {S T : ShortComplex (ModuleCat.{v} B)}

/-- Actual componentwise scalar multiplication of a short-complex map. -/
def moduleCatScaleMap (q : B) (φ : S ⟶ T) : S ⟶ T where
  τ₁ := q • φ.τ₁
  τ₂ := q • φ.τ₂
  τ₃ := q • φ.τ₃
  comm₁₂ := by rw [Linear.smul_comp, Linear.comp_smul, φ.comm₁₂]
  comm₂₃ := by rw [Linear.smul_comp, Linear.comp_smul, φ.comm₂₃]

theorem moduleCatBoundaryQuotientMap_scale (q : B) (φ : S ⟶ T) :
    moduleCatBoundaryQuotientMap (moduleCatScaleMap q φ) =
      q • moduleCatBoundaryQuotientMap φ := by
  apply LinearMap.ext
  intro s
  induction s using Submodule.Quotient.induction_on with
  | _ s =>
    change T.f.hom.range.mkQ (q • φ.τ₂.hom s) =
      q • T.f.hom.range.mkQ (φ.τ₂.hom s)
    exact T.f.hom.range.mkQ.map_smul q _

/-- The ACTUAL abstract homology map preserves a scalar when both
outgoing differentials vanish. This follows from actual quotient naturality. -/
theorem moduleCatTopHomologyMap_scale (q : B) (φ : S ⟶ T)
    (hs : S.g=0) (ht : T.g=0) :
    homologyMap (moduleCatScaleMap q φ) = q • homologyMap φ := by
  apply (cancel_mono (T.asIsoHomologyι ht ≪≫ T.moduleCatOpcyclesIso).hom).mp
  rw [moduleCatTopHomologyQuotient_naturality (moduleCatScaleMap q φ) hs ht,
    moduleCatBoundaryQuotientMap_scale]
  change (S.asIsoHomologyι hs ≪≫ S.moduleCatOpcyclesIso).hom ≫
      (q • ModuleCat.ofHom (moduleCatBoundaryQuotientMap φ)) = _
  rw [Linear.comp_smul, ← moduleCatTopHomologyQuotient_naturality φ hs ht, Linear.smul_comp]

end CategoryTheory.ShortComplex

namespace HomologicalComplex
open CategoryTheory
universe u v
variable {B : Type u} [CommRing B] {ι : Type} {c : ComplexShape ι}
    {A D : HomologicalComplex (ModuleCat.{v} B) c}

theorem moduleCatShortComplexFunctor_scale (q : B) (φ : A ⟶ D) (j : ι) :
    (shortComplexFunctor (ModuleCat.{v} B) c j).map (q • φ) =
    ShortComplex.moduleCatScaleMap q ((shortComplexFunctor (ModuleCat.{v} B) c j).map φ) := by
  apply ShortComplex.Hom.ext
  all_goals simp [shortComplexFunctor, shortComplexFunctor', ShortComplex.moduleCatScaleMap,
    smul_f_apply] <;> rfl

/-- Top homology preserves actual coefficient scalar multiplication,
with outgoing-zero hypotheses exposed and later checked on the original complex. -/
theorem moduleCatTopHomologyMap_scale (q : B) (φ : A ⟶ D) (j : ι)
    (ha : (A.sc j).g=0) (hd : (D.sc j).g=0) :
    homologyMap (q • φ) j = q • homologyMap φ j := by
  change ShortComplex.homologyMap ((shortComplexFunctor (ModuleCat.{v} B) c j).map (q • φ)) = _
  rw [moduleCatShortComplexFunctor_scale]
  exact ShortComplex.moduleCatTopHomologyMap_scale q _ ha hd

end HomologicalComplex
