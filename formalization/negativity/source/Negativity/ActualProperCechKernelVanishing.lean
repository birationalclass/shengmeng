module
public import Negativity.ActualReesHOneFinite
public import Negativity.ActualRelativeCechKernelGeneratorVanishing
public import Negativity.ActualProperCechCover
public import Negativity.AffineBaseCechVanishing

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Properness over an affine locally Noetherian base supplies an actual
finite affine Cech cover and a uniform vanishing bound for the genuine
ideal-power H¹ kernels. The cover, Rees-module finiteness and shift are
proved internally, rather than supplied as geometric hypotheses. -/
theorem actual_proper_affine_cech_kernel_vanishing
    {X Y : Scheme.{u}} [IsAffine Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (J : Y.IdealSheafData) :
    ∃ (ι : Type u) (_ : Fintype ι) (U : ι → X.affineOpens),
      iSup (fun j => (U j).1) = ⊤ ∧
        ∃ c : ℕ, ActualRelativeCechKernelVanishing f J U c := by
  classical
  letI : IsNoetherianRing Γ(Y, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
  letI : IsNoetherianRing Γ(Spec (.of Γ(Y, ⊤)), ⊤) :=
    IsLocallyNoetherian.component_noetherian
      ⟨⊤, isAffineOpen_top (Spec (.of Γ(Y, ⊤)))⟩
  let g := f ≫ Y.toSpecΓ
  letI : IsProper g := inferInstance
  obtain ⟨ι, hι, U, hcover, hpair, htriple⟩ :=
    exists_actual_proper_affine_cech_cover f
  letI : Fintype ι := hι
  letI : LinearOrder ι := LinearOrder.lift'
    (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  have hfinite := actual_relative_cech_hone_finite_of_proper_spec
    g (J.ideal ⟨⊤, isAffineOpen_top Y⟩) U hcover hpair htriple
  obtain ⟨c, hc⟩ := actual_relative_cech_kernel_vanishing_of_hone_finite
    g (actualSpecIdealSheaf (J.ideal ⟨⊤, isAffineOpen_top Y⟩)) U hpair hfinite
  exact ⟨ι, hι, U, hcover, c,
    actual_affine_base_cech_kernel_vanishing f J U c hc⟩

#print axioms actual_proper_affine_cech_kernel_vanishing
end
end Negativity
