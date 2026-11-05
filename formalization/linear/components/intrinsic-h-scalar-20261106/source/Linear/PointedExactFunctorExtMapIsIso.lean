module
public import Linear.PointedExactFunctorExtMap
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian CategoryTheory.ComposableArrows
universe u v u' v' w
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] [EnoughInjectives C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {O : C} {P : D} (e : P ⟶ F.obj O)
/-- Native dimension shifting extends a degree-zero pointed comparison to every degree,
provided actual injectives are acyclic for the fixed target source. -/
theorem pointedExactFunctorExtMap_bijective
    (hzero : ∀ M : C, Function.Bijective (pointedExactFunctorExtMap F e M 0))
    (hinj : ∀ (I : C) [Injective I] (n : ℕ), Subsingleton (Ext.{w} P (F.obj I) (n+1)))
    (M : C) (n : ℕ) : Function.Bijective (pointedExactFunctorExtMap F e M n) := by
  induction n generalizing M with
  | zero => exact hzero M
  | succ n ih =>
    let S := ShortComplex.cokernelSequence (Injective.ι M)
    letI : Mono S.f := (inferInstance : Mono (Injective.ι M))
    letI : Injective S.X₂ := (inferInstance : Injective (Injective.under M))
    have hS : S.ShortExact := ⟨ShortComplex.cokernelSequence_exact (Injective.ι M)⟩
    let hT := hS.map_of_exact F
    let a₁ := AddCommGrpCat.ofHom ((Ext.mk₀ S.g).postcomp O (add_zero n))
    let b₁ := AddCommGrpCat.ofHom (hS.extClass.postcomp O (show n+1=n+1 from rfl))
    let a₂ := AddCommGrpCat.ofHom ((Ext.mk₀ (F.map S.g)).postcomp P (add_zero n))
    let b₂ := AddCommGrpCat.ofHom (hT.extClass.postcomp P (show n+1=n+1 from rfl))
    let R₁ := mk₂ a₁ b₁
    let R₂ := mk₂ a₂ b₂
    let v₀ := AddCommGrpCat.ofHom (pointedExactFunctorExtMap F e S.X₂ n)
    let v₁ := AddCommGrpCat.ofHom (pointedExactFunctorExtMap F e S.X₃ n)
    let v₂ := AddCommGrpCat.ofHom (pointedExactFunctorExtMap F e S.X₁ (n+1))
    have w₀ : a₁ ≫ v₁ = v₀ ≫ a₂ := by
      ext x
      exact pointedExactFunctorExtMap_postcompose F e S.g n x
    have w₁ : b₁ ≫ v₂ = v₁ ≫ b₂ := by
      ext x
      exact pointedExactFunctorExtMap_boundary F e hS n x
    let phi : R₁ ⟶ R₂ := homMk₂ v₀ v₁ v₂ w₀ w₁
    have hR₁ : R₁.Exact :=
      (Ext.covariant_sequence_exact₃' O hS n (n+1) rfl).exact_toComposableArrows
    have hR₂ : R₂.Exact :=
      (Ext.covariant_sequence_exact₃' P hT n (n+1) rfl).exact_toComposableArrows
    have hb₁ : Epi b₁ := (AddCommGrpCat.epi_iff_surjective _).mpr (by
      intro x
      exact Ext.covariant_sequence_exact₁ O hS x (Ext.eq_zero_of_injective _) rfl)
    have hb₂ : Epi b₂ := (AddCommGrpCat.epi_iff_surjective _).mpr (by
      letI : Subsingleton (Ext.{w} P (S.map F).X₂ (n+1)) := hinj S.X₂ n
      intro x
      exact Ext.covariant_sequence_exact₁ P hT x (Subsingleton.elim _ _) rfl)
    have hv₀ : IsIso v₀ := (ConcreteCategory.isIso_iff_bijective _).mpr (ih S.X₂)
    have hv₁ : IsIso v₁ := (ConcreteCategory.isIso_iff_bijective _).mpr (ih S.X₃)
    have hv₂ : IsIso v₂ := Abelian.isIso_of_epi_of_isIso phi hR₁ hR₂ hb₁ hb₂
      (by letI := hv₀; exact (inferInstance : Epi v₀)) hv₁
    letI := hv₂
    exact ConcreteCategory.bijective_of_isIso v₂
end LinearStudy
