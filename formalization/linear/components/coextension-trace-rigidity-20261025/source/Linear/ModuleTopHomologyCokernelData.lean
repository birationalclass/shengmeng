module
public import Mathlib.Algebra.Homology.HomologySequence
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace CategoryTheory.ShortComplex.ShortExact
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C : Type*} [Category* C] [Abelian C] {ι : Type*} {c : ComplexShape ι}
    {S : ShortComplex (HomologicalComplex C c)}

/-- Cokernel data for actual homology of a short exact sequence whose
next kernel homology vanishes. The native coordinate application proves
this vanishing from its finite cover. IsColimit is data,not a proposition. -/
def homology_gIsCokernel_of_next_exact (hS : S.ShortExact) (i j : ι)
    (hij : c.Rel i j) (hz : S.X₁.ExactAt j) :
    IsColimit (CokernelCofork.ofπ (S.map (HomologicalComplex.homologyFunctor C c i)).g
      (S.map (HomologicalComplex.homologyFunctor C c i)).zero) := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at hz
  haveI : Epi (HomologicalComplex.homologyMap S.g i) :=
    (hS.homology_exact₃ i j hij).epi_f_iff.mpr (hz.eq_of_tgt _ _)
  exact (hS.homology_exact₂ i).gIsCokernel

end CategoryTheory.ShortComplex.ShortExact
