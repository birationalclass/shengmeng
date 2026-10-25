module
public import Linear.SchemeModuleChainSourceAcyclic
public import Linear.TildeComplexExact
public import Linear.SchemeModuleFiniteFreeFrameInternalExt
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
/-- An ACTUAL original finite basis gives the actual finite-free sheaf
frame,using mathlib's actual tilde-Finsupp comparison. -/
def tildeOriginalBasisFreeFrame (R : CommRingCat.{u})
    {M : Type u} [AddCommGroup M] [Module R M] {ι : Type u} (b : Module.Basis ι R M) :
    tilde (ModuleCat.of R M) ≅ SheafOfModules.free (R:=(Spec R).ringCatSheaf) ι :=
  (tilde.functor R).mapIso b.repr.toModuleIso ≪≫ tildeFinsupp ι
/-- ALL SAME actual affine Koszul terms have vanishing positive derived
SHEAF Ext for arbitrary coefficients. The finite free frames are derived
from ORIGINAL exterior coordinate bases,no acyclicity input. -/
theorem tildeFunctionKoszul_sourceInternalExtAcyclic (R : CommRingCat.{u})
    {r : ℕ} (H : Fin r → R) (N : (Spec R).Modules) :
    schemeModuleChainSourceExtAcyclic (tildeFunctionKoszulComplex R H) N := by
  intro p j
  let b := ((Pi.basisFun R (Fin r)).exteriorPower p).reindex
    (Equiv.ulift.symm : Set.powersetCard (Fin r) p ≃ ULift.{u} (Set.powersetCard (Fin r) p))
  change IsZero (schemeModuleInternalExt
    (tilde (ModuleCat.of R (⋀[R]^p (Fin r → R)))) N (j+1))
  exact schemeModuleFiniteFreeFrameInternalExt_succ N _ (tildeOriginalBasisFreeFrame R b) j
/-- The SAME actual affine Koszul complex vanishes above original rank,
using its original coordinate generators and actual tilde functor. -/
theorem tildeFunctionKoszul_isZero_above_rank (R : CommRingCat.{u})
    {r : ℕ} (H : Fin r → R) (p : ℕ) (hp : r < p) :
    IsZero ((tildeFunctionKoszulComplex R H).X p) := by
  let hz := koszulComplex.isZero_X_of_card_generators_lt
    (Fintype.linearCombination R H) (Pi.basisFun R (Fin r))
    (Pi.basisFun R (Fin r)).span_eq p (by simpa using hp)
  exact (tilde.functor R).map_isZero hz
end LinearStudy
