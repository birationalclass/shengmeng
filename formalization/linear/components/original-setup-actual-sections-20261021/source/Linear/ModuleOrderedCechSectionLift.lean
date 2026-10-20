module
public import Linear.ModuleOrderedCechAugmentation
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import all Linear.ModuleOrderedBaseCechFunctor
import all Mathlib.CategoryTheory.Limits.HasLimits
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry.Scheme.Modules
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u
variable {X Y : Scheme.{u}} (π : X ⟶ Y)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

/-- Restriction of global sections commutes with actual module-sheaf maps. -/
theorem orderedBaseCechAugmentation_naturality
    {M N : X.Modules} (f : M ⟶ N) :
    orderedBaseCechAugmentation π M U ≫
        ((orderedBaseCechComplexFunctor π U).map f).f 0 =
      ((baseModulePresheafFunctor π).map f).app (op ⊤) ≫
        orderedBaseCechAugmentation π N U := by
  apply Pi.hom_ext
  intro i
  change orderedBaseCechAugmentation π M U ≫
      CategoryTheory.Limits.Pi.map (fun j : OrderedCechIndex ι 0 =>
        ((baseModulePresheafFunctor π).map f).app
          (op (∏ᶜ fun k : Fin 1 => U (j.1 k)))) ≫
        Pi.π (fun j : OrderedCechIndex ι 0 => baseCechFactor π N U 0 j.1) i = _
  erw [Pi.map_π, orderedBaseCechAugmentation_comp_π_assoc,
    Category.assoc, orderedBaseCechAugmentation_comp_π]
  exact ((baseModulePresheafFunctor π).map f).naturality (homOfLE le_top).op

/-- On a cover whose actual Cech image of a short complex is short exact,
vanishing of the kernel's first actual ordered-Cech cohomology gives a lift
of every global section. The lift is obtained by correcting local lifts
with a kernel coboundary and gluing. No global section surjectivity or
derived-cohomology comparison is assumed. -/
theorem orderedCechShortExact_sections_surjective
    (T : ShortComplex X.Modules)
    (hcover : (⊤ : X.Opens) ≤ iSup U)
    (hC : (T.map (orderedBaseCechComplexFunctor π U)).ShortExact)
    (hK : (orderedBaseCechComplex π T.X₁ U).ExactAt 1) :
    Function.Surjective (T.g.app ⊤) := by
  let C := T.map (orderedBaseCechComplexFunctor π U)
  have hdegree := (HomologicalComplex.shortExact_iff_degreewise_shortExact C).mp hC
  let f := C.f
  let g := C.g
  intro z
  obtain ⟨a,ha⟩ := (hdegree 0).moduleCat_surjective_g
    (orderedBaseCechAugmentation π T.X₃ U z)
  change C.X₂.X 0 at a
  change g.f 0 a = orderedBaseCechAugmentation π T.X₃ U z at ha
  have hza : C.X₃.d 0 1 (g.f 0 a) = 0 := by
    rw [ha]
    exact ConcreteCategory.congr_hom (orderedBaseCechAugmentation_comp_d π T.X₃ U) z
  have hga : g.f 1 (C.X₂.d 0 1 a) = 0 := by
    erw [← ConcreteCategory.comp_apply, ← g.comm]
    exact hza
  obtain ⟨b,hb⟩ := (ShortComplex.moduleCat_exact_iff _).mp (hdegree 1).exact
    (C.X₂.d 0 1 a) hga
  change C.X₁.X 1 at b
  change f.f 1 b = C.X₂.d 0 1 a at hb
  have hdb : C.X₁.d 1 2 b = 0 := by
    apply (hdegree 2).moduleCat_injective_f
    rw [map_zero]
    calc
      f.f 2 (C.X₁.d 1 2 b) = C.X₂.d 1 2 (f.f 1 b) :=
        (ConcreteCategory.congr_hom (f.comm 1 2) b).symm
      _ = 0 := by rw [hb]; exact ConcreteCategory.congr_hom (C.X₂.d_comp_d 0 1 2) a
  have hK' : (C.X₁.sc' 0 1 2).Exact :=
    (HomologicalComplex.exactAt_iff' C.X₁ 0 1 2 (by simp) (by simp)).mp hK
  obtain ⟨t,ht⟩ := (ShortComplex.moduleCat_exact_iff _).mp hK' b hdb
  change C.X₁.X 0 at t
  change C.X₁.d 0 1 t = b at ht
  have hcycle : C.X₂.d 0 1 (a - f.f 0 t) = 0 := by
    rw [map_sub]
    have hn := (ConcreteCategory.congr_hom (f.comm 0 1) t).symm
    change f.f 1 (C.X₁.d 0 1 t) = C.X₂.d 0 1 (f.f 0 t) at hn
    rw [← hn, ht, hb, sub_self]
  obtain ⟨s,hs⟩ := orderedBaseCechAugmentation_surjective_cycles π T.X₂ U hcover
    (a - f.f 0 t) hcycle
  refine ⟨s, orderedBaseCechAugmentation_injective π T.X₃ U hcover ?_⟩
  calc
    orderedBaseCechAugmentation π T.X₃ U (T.g.app ⊤ s) =
        g.f 0 (orderedBaseCechAugmentation π T.X₂ U s) :=
      (ConcreteCategory.congr_hom (orderedBaseCechAugmentation_naturality π U T.g) s).symm
    _ = g.f 0 a - g.f 0 (f.f 0 t) := by rw [hs, map_sub]
    _ = orderedBaseCechAugmentation π T.X₃ U z := by
      rw [ha, show g.f 0 (f.f 0 t) = 0 from
        ConcreteCategory.congr_hom (HomologicalComplex.congr_hom C.zero 0) t, sub_zero]
end AlgebraicGeometry.Scheme.Modules
