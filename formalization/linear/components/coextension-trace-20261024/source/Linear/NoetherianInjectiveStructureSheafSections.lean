module
public import Linear.NoetherianInjectiveCompatibleFractions
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import all Mathlib.AlgebraicGeometry.StructureSheaf
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite
universe u
/-- On a Noetherian affine spectrum, every section of an injective module's actual
associated sheaf over ANY open comes from one element of the original module. -/
theorem noetherian_injective_structureSheaf_toOpen_surjective
    {R I : Type u} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup I] [Module R I] [Module.Injective R I]
    (U : Opens (PrimeSpectrum.Top R)) :
    Function.Surjective (StructureSheaf.toOpenₗ R I U) := by
  letI : NoetherianSpace (PrimeSpectrum.Top R) :=
    (inferInstance : NoetherianSpace (PrimeSpectrum R))
  intro s
  obtain ⟨ι,hi,a,b,ibU,iU,hab,H⟩ :=
    StructureSheaf.exists_le_iSup_basicOpen_and_smul_eq_smul_and_eq_const U
      (NoetherianSpace.isCompact (U : Set (PrimeSpectrum.Top R))) s
  letI : Fintype ι := hi
  obtain ⟨n,x,hx⟩ := noetherian_injective_compatible_family_lift b a hab
  refine ⟨x,?_⟩
  refine (structureSheafInType R I).eq_of_locally_eq' (fun i => PrimeSpectrum.basicOpen (b i))
    _ (fun i => (ibU i).hom) iU _ _ ?_
  intro i
  rw [StructureSheaf.toOpenₗ_eq_const, StructureSheaf.res_const]
  refine Eq.trans ?_ (H i).symm
  apply Subtype.ext
  funext p
  change LocalizedModule.mk x (1 : p.val.asIdeal.primeCompl) =
    LocalizedModule.mk (a i) ⟨b i,p.property⟩
  apply LocalizedModule.mk_eq.mpr
  refine ⟨⟨b i ^ n,p.val.asIdeal.primeCompl.pow_mem p.property n⟩,?_⟩
  simpa [Submonoid.smul_def, smul_smul, pow_succ, mul_comm] using hx i
  all_goals simp
end LinearStudy