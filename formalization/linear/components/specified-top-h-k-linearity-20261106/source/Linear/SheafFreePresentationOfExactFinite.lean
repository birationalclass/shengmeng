module
public import Linear.SheafFreePresentationOfExact
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory Limits
universe u v₁ u₁
variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{u}}
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The constructed exact free-source presentation is finite when its
actual source index types are finite. -/
theorem sheafFreePresentationOfExact_isFinite {ι σ : Type u} [Finite ι] [Finite σ]
    (c : ShortComplex (SheafOfModules.{u} R)) (hc : c.Exact) [Epi c.g]
    (e₁ : SheafOfModules.free ι ≅ c.X₁) (e₂ : SheafOfModules.free σ ≅ c.X₂) :
    (sheafFreePresentationOfExact c hc e₁ e₂).IsFinite := by
  constructor <;> constructor
  · change Finite σ
    infer_instance
  · change Finite ι
    infer_instance

end LinearStudy
