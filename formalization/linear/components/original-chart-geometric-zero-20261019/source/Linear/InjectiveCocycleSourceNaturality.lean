module
public import Linear.InjectiveCocycleExtPresentation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian
universe u v w
variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]
variable {N : A} (I : InjectiveResolution N)

/-- Precompose the SAME actual cocycle,with no change of resolution. -/
def injectiveCocyclePrecompose {P Q : A} (g : P ⟶ Q) (q : ℕ) :
    injectiveCocycleGroup I Q q →+ injectiveCocycleGroup I P q where
  toFun f := ⟨g ≫ f.val,by
    change (g ≫ f.val) ≫ I.cocomplex.d q (q+1) = 0
    rw [Category.assoc,f.property,Limits.comp_zero]⟩
  map_zero' := by apply Subtype.ext; exact Limits.comp_zero
  map_add' f h := by
    apply Subtype.ext
    change g ≫ (f.val+h.val) = g ≫ f.val + g ≫ h.val
    rw [Preadditive.comp_add]

/-- Native source Ext action agrees with this SAME cocycle precomposition. -/
theorem injectiveCocycleExtMap_precompose {P Q : A} (g : P ⟶ Q) (q : ℕ)
    (f : injectiveCocycleGroup I Q q) :
    (Ext.mk₀ g).comp (injectiveCocycleExtMap I Q q f) (zero_add q) =
      injectiveCocycleExtMap I P q (injectiveCocyclePrecompose I g q f) :=
  I.mk₀_comp_extMk f.val (q+1) rfl f.property g

end LinearStudy
