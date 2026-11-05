module
public import Linear.TildeBasicOpenMono
public import Mathlib.CategoryTheory.Abelian.Exact
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {R : CommRingCat.{u}} {M N : ModuleCat.{u} R}

theorem tilde_open_map_injective (f : M ⟶ N) (hf : Function.Injective f.hom)
    (U : (Spec R).Opens) :
    Function.Injective ((modulesSpecToSheaf.map (tilde.map f)).1.app (.op U)).hom := by
  intro x y hxy
  apply TopCat.Presheaf.IsSheaf.section_ext (modulesSpecToSheaf.obj (tilde M)).2
  intro p hpU
  obtain ⟨_,⟨_,⟨a,rfl⟩,rfl⟩,hpa,haU⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hpU U.2
  refine ⟨PrimeSpectrum.basicOpen a,haU,hpa,?_⟩
  apply tilde_basicOpen_map_injective f hf a
  have hn := (modulesSpecToSheaf.map (tilde.map f)).1.naturality (homOfLE haU).op
  exact (congrArg (fun g => g.hom x) hn).symm.trans
    ((congrArg (fun z => (modulesSpecToSheaf.obj (tilde N)).1.map (homOfLE haU).op z) hxy).trans
      (congrArg (fun g => g.hom y) hn))

/-- The actual native affine associated-sheaf construction preserves
monomorphisms, proved from localization and the basic-open cover. -/
theorem tilde_map_mono (f : M ⟶ N) [Mono f] : Mono (tilde.map f) := by
  apply (modulesSpecToSheaf (R := R)).mono_of_mono_map
  apply (TopCat.Sheaf.forget (ModuleCat R) (Spec R)).mono_of_mono_map
  apply +allowSynthFailures NatTrans.mono_of_mono_app
  intro U
  apply (ModuleCat.mono_iff_injective _).mpr
  exact tilde_open_map_injective f ((ModuleCat.mono_iff_injective f).mp inferInstance) U.unop

/-- Actual affine associated sheaves preserve homology, using the proved
mono preservation and existing adjunction/cokernel preservation. -/
theorem tilde_functor_preservesHomology (R : CommRingCat.{u}) :
    (tilde.functor R).PreservesHomology := by
  letI : (tilde.functor R).PreservesMonomorphisms := ⟨fun f _ => tilde_map_mono f⟩
  exact Functor.preservesHomology_of_preservesMonos_and_cokernels (tilde.functor R)

end LinearStudy
