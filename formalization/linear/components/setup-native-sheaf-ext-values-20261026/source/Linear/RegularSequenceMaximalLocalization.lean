module
public import Linear.HomogeneousLocalization
public import Linear.RegularGeneratorsFree
public import Mathlib.RingTheory.LocalProperties.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open RingTheory.Sequence
/-- Weak regularity of the ACTUAL ring sequence is detected at ALL actual
maximal localizations. No global CM,finiteness or freeness is an input. -/
theorem weaklyRegular_of_maximal_localizations
    {A : Type*} [CommRing A] (rs : List A)
    (hlocal : ∀ (P : Ideal A) [P.IsMaximal],
      IsWeaklyRegular (Localization.AtPrime P)
        (rs.map (algebraMap A (Localization.AtPrime P)))) :
    IsWeaklyRegular A rs := by
  refine ⟨fun i hi => ?_⟩
  let I := Ideal.ofList (rs.take i)
  rw [ideal_smul_top_self]
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem I rs[i]).mpr
  intro a ha
  apply Ideal.mem_of_localization_maximal
  intro P hP
  let L := Localization.AtPrime P
  let f : A →+* L := algebraMap A L
  have hl := (hlocal P).regular_mod_prev i (by simpa using hi)
  change IsSMulRegular (L ⧸ (Ideal.ofList ((rs.map f).take i) •
    (⊤ : Submodule L L))) ((rs.map f)[i]'(by simpa using hi)) at hl
  rw [← List.map_take,← Ideal.map_ofList,ideal_smul_top_self] at hl
  simp only [List.getElem_map] at hl
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem (I.map f) (f rs[i])).mp hl
  change f rs[i] * f a ∈ I.map f
  rw [← map_mul]
  exact Ideal.mem_map_of_mem f ha
/-- Derive finite freeness from ACTUAL source-point regularity and the
base local maximal parameters,using the existing regular-generators theorem.
This is a local algebra criterion only;original geometric local-ring
identifications and regularity inputs are NOT asserted or weakened. -/
theorem finite_free_of_maximal_local_regular_parameters
    {R S : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing S] [Algebra R S] [Module.Finite R S]
    (rs : List R) (hgen : Ideal.ofList rs=IsLocalRing.maximalIdeal R)
    (hlocal : ∀ (P : Ideal S) [P.IsMaximal],
      IsWeaklyRegular (Localization.AtPrime P)
        ((rs.map (algebraMap R S)).map (algebraMap S (Localization.AtPrime P)))) :
    Module.Free R S :=
  free_of_regular_maximal_algebraMap rs
    (weaklyRegular_of_maximal_localizations _ hlocal) hgen
end LinearStudy
