module
public import Negativity.ActualReesHOneFiniteFromNative
public import Negativity.ActualReesProperCechFinite

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
open scoped DirectSum
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Properness proves finite generation of the genuine summed actual
ideal-power Čech H¹ module. Geometry, scalar action and native comparison
are all constructed, and the proper finiteness theorem is reused. -/
theorem actual_relative_cech_hone_finite_of_proper_spec
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f] (I : Ideal R)
    {ι : Type u} [Fintype ι] [LinearOrder ι] (U : ι → X.affineOpens)
    (hcover : iSup (fun j => (U j).1) = ⊤)
    (hpair : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1))
    (htriple : ∀ j k l, IsAffineOpen (((U j).1 ⊓ (U k).1) ⊓ (U l).1)) :
    letI := actualRelativeCechHOnePolynomialReesModule f (actualSpecIdealSheaf I) U hpair
    Module.Finite (reesAlgebra ((actualSpecIdealSheaf I).ideal ⟨⊤, isAffineOpen_top _⟩))
      (⨁ n : ℕ, actualClosedCechHOne
        (((actualSpecIdealSheaf I) ^ n).comap f).subschemeι (fun j => (U j).1)) := by
  letI : Module.Finite Γ(Spec (.of (reesAlgebra I)), ⊤)
      ((Scheme.Modules.baseCechComplex (actualRelativeReesToBase f I)
        (SheafOfModules.unit (actualRelativeReesScheme f I).ringCatSheaf)
        (fun j => (actualReesCechCover f I U j).1)).homology 1) :=
    actual_rees_structure_cech_homology_finite f I U hcover 1
  exact actual_relative_cech_hone_finite_of_native_rees f I U hpair htriple

#print axioms actual_relative_cech_hone_finite_of_proper_spec
end
end Negativity
