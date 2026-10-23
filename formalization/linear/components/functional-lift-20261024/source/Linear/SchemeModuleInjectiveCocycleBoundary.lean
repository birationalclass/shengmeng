module
public import Linear.SchemeModuleInjectiveInternalHomBoundaryClass
public import Linear.SchemeModuleInjectiveCocycleEvaluation
public import Mathlib.CategoryTheory.CommSq
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u
variable {X : Scheme.{u}}

set_option maxHeartbeats 50000
/-- The ACTUAL derived internal Ext source boundary sends SAME actual
curried lifts to SAME terminal cocycle,with no desired square premise. -/
theorem schemeModuleInjectiveCocycleToInternalExt_boundary
    (S : ShortComplex X.Modules) (hS : S.ShortExact) {N : X.Modules}
    (I : InjectiveResolution N) (q : ℕ)
    (a : injectiveCocycleGroup I S.X₁ q) (b : S.X₂ ⟶ I.cocomplex.X q)
    (c : injectiveCocycleGroup I S.X₃ (q+1))
    (hb : S.f ≫ b = a.val) (hbc : b ≫ I.cocomplex.d q (q+1) = S.g ≫ c.val) :
    schemeModuleInjectiveCocycleToInternalExt I S.X₁ q a ≫
      schemeModuleInternalExtSourceBoundaryViaResolution S hS N I q =
      schemeModuleInjectiveCocycleToInternalExt I S.X₃ (q+1) c := by
  let aIso := schemeModuleInternalExtInjectiveResolutionIso S.X₁ N q I
  let cIso := schemeModuleInternalExtInjectiveResolutionIso S.X₃ N (q+1) I
  have hs : CommSq (schemeModuleInternalExtSourceBoundaryViaResolution S hS N I q)
      aIso.hom cIso.hom
      ((schemeModuleHomSourceShortComplex_shortExact S hS I.cocomplex).δ q (q+1) rfl) :=
    ⟨schemeModuleInternalExtSourceBoundary_resolution_square S hS N I q⟩
  have hi := (CommSq.vert_inv (g := aIso) (h := cIso) hs).w
  rw [schemeModuleInjectiveCocycleToInternalExt_apply,schemeModuleInjectiveCocycleToInternalExt_apply]
  erw [Category.assoc,← hi,← Category.assoc,
    schemeModuleInjectiveInternalHomClassMap_boundary S hS I q a b c hb hbc]

end LinearStudy
