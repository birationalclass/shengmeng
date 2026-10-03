module
public import Negativity.ActualReesCechCover
public import Negativity.ActualReesFinitenessHypotheses
public import Negativity.ActualReesStructureSheafCoherence
public import Negativity.External.Aintlib.ForMathlib.SchemeModuleProperLowDegreeCechFinite
public import Negativity.External.Aintlib.ForMathlib.SchemeModuleOrderedBaseCechHomotopyEquiv

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Final theorem: the actual relative Rees image has finite native
structure-sheaf Cech cohomology on the actual induced finite affine
cover. Properness, coherence and all Rees geometry are constructed;
the proper cohomology theorem is reused from the audited AINTLIB code. -/
theorem actual_rees_structure_cech_homology_finite
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f] (I : Ideal R)
    {ι : Type u} [Fintype ι] [LinearOrder ι] (U : ι → X.affineOpens)
    (hU : iSup (fun j => (U j).1) = ⊤) (n : ℕ) :
    Module.Finite Γ(Spec (.of (reesAlgebra I)), ⊤)
      ((Scheme.Modules.baseCechComplex (actualRelativeReesToBase f I)
        (Scheme.Modules.unitObj (actualRelativeReesScheme f I))
        (fun j => (actualReesCechCover f I U j).1)).homology n) := by
  let W := actualRelativeReesScheme f I
  let π := actualRelativeReesToBase f I
  let V : ι → W.Opens := fun j => (actualReesCechCover f I U j).1
  let M : W.Modules := Scheme.Modules.unitObj W
  letI : IsProper π := actual_relative_rees_scheme_proper f I
  letI : IsNoetherian W := actual_relative_rees_scheme_noetherian f I
  letI : W.IsSeparated := actual_relative_rees_scheme_separated f I
  letI : LocallyOfFinitePresentation π :=
    actual_relative_rees_scheme_locally_of_finite_presentation f I
  obtain ⟨hfin, hqc⟩ := actual_structure_sheaf_finite_type_and_quasicoherent W
  letI : M.IsFiniteType := hfin
  letI : M.IsQuasicoherent := hqc
  letI : Module.Finite Γ(Spec (.of (reesAlgebra I)), ⊤)
      ((Scheme.Modules.orderedBaseCechComplex π M V).homology n) :=
    Scheme.Modules.orderedBaseCechHomologyFinite_of_isProper V
      (actual_rees_cech_cover_covers f I U hU)
      (fun j => (actualReesCechCover f I U j).2) M n
  exact Scheme.Modules.baseCechComplex_homology_module_finite_of_orderedBaseCechComplex
    π M V n

#print axioms actual_rees_structure_cech_homology_finite
end
end Negativity
