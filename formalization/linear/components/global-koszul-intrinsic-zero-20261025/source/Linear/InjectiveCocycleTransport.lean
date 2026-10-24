module
public import Linear.InjectiveCocycleExtPresentation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u v w
variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]
variable {N N' : A} (I : InjectiveResolution N) (J : InjectiveResolution N') (P : A) (q : ℕ)

/-- Transport SAME actual cocycle along an actual resolution cochain map. -/
def injectiveCocycleTransport (phi : I.cocomplex ⟶ J.cocomplex) :
    injectiveCocycleGroup I P q →+ injectiveCocycleGroup J P q where
  toFun f := ⟨f.val ≫ phi.f q,by
    change (f.val ≫ phi.f q) ≫ J.cocomplex.d q (q+1) = 0
    have hf : f.val ≫ I.cocomplex.d q (q+1) = 0 := f.property
    rw [Category.assoc,phi.comm,← Category.assoc,hf,zero_comp]⟩
  map_zero' := by apply Subtype.ext; exact zero_comp
  map_add' f g := by
    apply Subtype.ext
    change (f.val+g.val) ≫ phi.f q = f.val ≫ phi.f q + g.val ≫ phi.f q
    rw [Preadditive.add_comp]

/-- The native global Ext class is transported by SAME coefficient map;
this is a PROVED representative formula,not a desired map compatibility input. -/
theorem injectiveCocycleExtMap_transport {c : N ⟶ N'}
    (phi : InjectiveResolution.Hom I J c) (f : injectiveCocycleGroup I P q) :
    injectiveCocycleExtMap J P q (injectiveCocycleTransport I J P q phi.hom f) =
      (injectiveCocycleExtMap I P q f).comp (Ext.mk₀ c) (add_zero _) :=
  (I.extMk_comp_mk₀ f.val (q+1) rfl f.property phi).symm

end LinearStudy
