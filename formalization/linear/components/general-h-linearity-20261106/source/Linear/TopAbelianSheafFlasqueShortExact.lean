module
public import Linear.TopAbelianSheafInjectiveFlasque
public import Linear.TopAbelianSheafIntegerSections
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
variable {X : TopCat.{u}} {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
/-- The actual cokernel after embedding a flasque sheaf into an injective is again flasque. -/
theorem topAbelianSheaf_flasque_quotient_of_injective (hS : S.ShortExact)
    (hF : TopCat.Sheaf.IsFlasque S.X₁) (hI : Injective S.X₂) :
    TopCat.Sheaf.IsFlasque S.X₃ := by
  letI := hF
  letI := hI
  letI := topAbelianSheaf_injective_isFlasque X S.X₂
  exact TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ hS

/-- A flasque first term lifts every actual morphism from the native constant integer SHEAF. -/
theorem topAbelianSheaf_shortExact_integerHom_lift_of_flasque (hS : S.ShortExact)
    (hF : TopCat.Sheaf.IsFlasque S.X₁)
    (a : (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ S.X₃) :
    ∃ b, b ≫ S.g = a := by
  letI := hF
  have he := TopCat.Sheaf.IsFlasque.epi_of_shortExact (U := ⊤) hS
  obtain ⟨s,hs⟩ := (AddCommGrpCat.epi_iff_surjective _).mp he
    (topAbelianSheafIntegerHomSectionsAddEquiv X S.X₃ a)
  let b := (topAbelianSheafIntegerHomSectionsAddEquiv X S.X₂).symm s
  refine ⟨b, (topAbelianSheafIntegerHomSectionsAddEquiv X S.X₃).injective ?_⟩
  exact (topAbelianSheafIntegerHomSectionsAddEquiv_postcompose X S.g b).trans
    ((congrArg (S.g.hom.app (op ⊤))
      ((topAbelianSheafIntegerHomSectionsAddEquiv X S.X₂).apply_symm_apply s)).trans hs)
end LinearStudy
