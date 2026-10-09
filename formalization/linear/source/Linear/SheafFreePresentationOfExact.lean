module
public import Linear.NativeProjectiveOverCokernel
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
namespace LinearStudy
open CategoryTheory Limits
universe u v₁ u₁
variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{u}}
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- An actual exact epimorphic sheaf complex, together with constructed
free source identifications, yields mathlib's actual presentation. -/
def sheafFreePresentationOfExact {ι σ : Type u}
    (c : ShortComplex (SheafOfModules.{u} R)) (hc : c.Exact) [Epi c.g]
    (e₁ : SheafOfModules.free ι ≅ c.X₁) (e₂ : SheafOfModules.free σ ≅ c.X₂) :
    c.X₃.Presentation := by
  let a := e₁.hom ≫ c.f ≫ e₂.inv
  let b := e₂.hom ≫ c.g
  have hab : a ≫ b = 0 := by
    simp only [a, b, Category.assoc, Iso.inv_hom_id_assoc, c.zero, comp_zero]
  let c' := ShortComplex.mk a b hab
  let e : c' ≅ c := ShortComplex.isoMk e₁ e₂ (Iso.refl _) (by
    simp [c', a, Category.assoc]) (by simp [c', b])
  have hc' : c'.Exact := (ShortComplex.exact_iff_of_iso e).mpr hc
  haveI : Epi c'.g := by
    change Epi (e₂.hom ≫ c.g)
    infer_instance
  exact SheafOfModules.presentationOfIsCokernelFree a b hab hc'.gIsCokernel

end LinearStudy
