module
public import Negativity.ActualReesCechCycleSemilinearFromNaturality
public import Negativity.ActualReesNativeQuotientFromNaturality
public import Negativity.ActualReesCechNaturality
public import Negativity.ActualNativeUnitCechLinearComparison
public import Negativity.ModuleCatHomologySemilinearReuse

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
open scoped DirectSum
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 100000
noncomputable section
variable {R : Type u} [CommRing R] {X : Scheme.{u}}

theorem actualReesNativeUnitCycle_smul
    (f : X ⟶ Spec (.of R)) (I : Ideal R)
    {ι : Type u} (U : ι → X.affineOpens) (r : Γ(Spec (.of (reesAlgebra I)),⊤))
    (a : ((Scheme.Modules.baseCechComplex (actualRelativeReesToBase f I)
      (SheafOfModules.unit (actualRelativeReesScheme f I).ringCatSheaf)
      (fun j => (actualReesCechCover f I U j).1)).sc' 0 1 2).g.hom.ker) :
    letI := actualReesCechCycleScalarModule f I U
    actualNativeUnitCechCycleEquiv (actualRelativeReesToBase f I)
        (fun j => (actualReesCechCover f I U j).1) (r • a) =
      (Scheme.ΓSpecIso (.of (reesAlgebra I))).hom r •
        actualNativeUnitCechCycleEquiv (actualRelativeReesToBase f I)
          (fun j => (actualReesCechCover f I U j).1) a := by
  letI := actualReesCechCycleScalarModule f I U
  apply Subtype.ext
  change actualNativeUnitCechOneEquiv (actualRelativeReesToBase f I)
    (fun j => (actualReesCechCover f I U j).1) (r • a.1) = _
  rw [actualNativeUnitCechOneEquiv_smul]
  funext j k
  rw [actualReesCechCycleScalarModule_apply]
  change actualSectionRestriction _ le_top ((actualRelativeReesToBase f I).appTop r) * _ =
    actualSectionRestriction _ le_top ((actualRelativeReesToBase f I).appTop
      ((Scheme.ΓSpecIso (.of (reesAlgebra I))).inv
        ((Scheme.ΓSpecIso (.of (reesAlgebra I))).hom r))) * _
  rw [(Scheme.ΓSpecIso (.of (reesAlgebra I))).hom_inv_id_apply]
  rfl

/-- The map from actual native W cocycles to actual ideal-power H¹ is
semilinear for the genuine base-ring coordinate isomorphism. -/
def actualReesNativeCechQuotientSemilinear
    (f : X ⟶ Spec (.of R)) [QuasiCompact f] (I : Ideal R)
    {ι : Type u} [Fintype ι] (U : ι → X.affineOpens)
    (hpair : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1))
    (htriple : ∀ j k l, IsAffineOpen (((U j).1 ⊓ (U k).1) ⊓ (U l).1)) :
    letI := actualRelativeCechHOnePolynomialReesModule f (actualSpecIdealSheaf I) U hpair
    ((Scheme.Modules.baseCechComplex (actualRelativeReesToBase f I)
      (SheafOfModules.unit (actualRelativeReesScheme f I).ringCatSheaf)
      (fun j => (actualReesCechCover f I U j).1)).sc' 0 1 2).g.hom.ker →ₛₗ[
      (actualReesCechScalarEquiv I).toRingHom]
        ⨁ n : ℕ, actualClosedCechHOne
          (((actualSpecIdealSheaf I) ^ n).comap f).subschemeι (fun j => (U j).1) := by
  let hnat := actual_rees_coordinate_restriction_compatibility f I
  letI := actualReesCechCycleScalarModule f I U
  letI := actualRelativeCechOneModule f (fun j => (U j).1)
  letI := actualRelativeCechCyclePolynomialReesModule f (actualSpecIdealSheaf I) U hpair
  letI := actualRelativeCechHOnePolynomialReesModule f (actualSpecIdealSheaf I) U hpair
  let E := actualReesCechCycleSemilinearFromNaturality f I hnat U hpair htriple
  let q := actualRelativeCechHOnePolynomialQuotientMap f (actualSpecIdealSheaf I) U hpair
  let N := actualNativeUnitCechCycleEquiv (actualRelativeReesToBase f I)
    (fun j => (actualReesCechCover f I U j).1)
  refine { actualReesNativeCechQuotientFromNaturality f I hnat U hpair htriple with
    map_smul' := ?_ }
  intro r a
  change q (E (N (r • a))) = actualReesCechScalarEquiv I r • q (E (N a))
  rw [actualReesNativeUnitCycle_smul]
  have hE := E.map_smulₛₗ ((Scheme.ΓSpecIso (.of (reesAlgebra I))).hom r) (N a)
  have hq := q.map_smul
    (actualSpecReesScalarEquiv I ((Scheme.ΓSpecIso (.of (reesAlgebra I))).hom r)) (E (N a))
  exact (congrArg q hE).trans hq

theorem actual_rees_native_cech_quotient_semilinear_surjective
    (f : X ⟶ Spec (.of R)) [QuasiCompact f] (I : Ideal R)
    {ι : Type u} [Fintype ι] (U : ι → X.affineOpens)
    (hpair : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1))
    (htriple : ∀ j k l, IsAffineOpen (((U j).1 ⊓ (U k).1) ⊓ (U l).1)) :
    letI := actualRelativeCechHOnePolynomialReesModule f (actualSpecIdealSheaf I) U hpair
    Function.Surjective (actualReesNativeCechQuotientSemilinear f I U hpair htriple) :=
  actual_rees_native_cech_quotient_from_naturality_surjective f I
    (actual_rees_coordinate_restriction_compatibility f I) U hpair htriple

theorem actual_rees_native_cech_quotient_semilinear_ker
    (f : X ⟶ Spec (.of R)) [QuasiCompact f] (I : Ideal R)
    {ι : Type u} [Fintype ι] (U : ι → X.affineOpens)
    (hpair : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1))
    (htriple : ∀ j k l, IsAffineOpen (((U j).1 ⊓ (U k).1) ⊓ (U l).1)) :
    letI := actualRelativeCechHOnePolynomialReesModule f (actualSpecIdealSheaf I) U hpair
    (actualReesNativeCechQuotientSemilinear f I U hpair htriple).ker =
      ((Scheme.Modules.baseCechComplex (actualRelativeReesToBase f I)
        (SheafOfModules.unit (actualRelativeReesScheme f I).ringCatSheaf)
        (fun j => (actualReesCechCover f I U j).1)).sc' 0 1 2).moduleCatToCycles.range := by
  letI := actualRelativeCechHOnePolynomialReesModule f (actualSpecIdealSheaf I) U hpair
  ext a
  exact SetLike.ext_iff.mp (actual_rees_native_cech_quotient_from_naturality_ker f I
    (actual_rees_coordinate_restriction_compatibility f I) U hpair htriple) a

/-- The actual native H¹ comparison, including every scalar in the genuine
base Rees ring and the actual ideal-power quotient on the source cover. -/
def actualReesNativeHOneSemilinearComparison
    (f : X ⟶ Spec (.of R)) [QuasiCompact f] (I : Ideal R)
    {ι : Type u} [Fintype ι] (U : ι → X.affineOpens)
    (hpair : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1))
    (htriple : ∀ j k l, IsAffineOpen (((U j).1 ⊓ (U k).1) ⊓ (U l).1)) :
    letI := actualRelativeCechHOnePolynomialReesModule f (actualSpecIdealSheaf I) U hpair
    (Scheme.Modules.baseCechComplex (actualRelativeReesToBase f I)
      (SheafOfModules.unit (actualRelativeReesScheme f I).ringCatSheaf)
      (fun j => (actualReesCechCover f I U j).1)).homology 1 →ₛₗ[
      (actualReesCechScalarEquiv I).toRingHom]
        ⨁ n : ℕ, actualClosedCechHOne
          (((actualSpecIdealSheaf I) ^ n).comap f).subschemeι (fun j => (U j).1) := by
  letI := actualRelativeCechHOnePolynomialReesModule f (actualSpecIdealSheaf I) U hpair
  let K := (Scheme.Modules.baseCechComplex (actualRelativeReesToBase f I)
    (SheafOfModules.unit (actualRelativeReesScheme f I).ringCatSheaf)
    (fun j => (actualReesCechCover f I U j).1)).sc' 0 1 2
  exact (actualModuleCatHomologySemilinearQuotientMap K
    (actualReesCechScalarEquiv I).toRingHom
    (actualReesNativeCechQuotientSemilinear f I U hpair htriple)
    (actual_rees_native_cech_quotient_semilinear_ker f I U hpair htriple).ge).comp
      (actualNativeUnitCechHOneExplicitIso (actualRelativeReesToBase f I)
        (fun j => (actualReesCechCover f I U j).1)).hom.hom

theorem actual_rees_native_hone_semilinear_comparison_bijective
    (f : X ⟶ Spec (.of R)) [QuasiCompact f] (I : Ideal R)
    {ι : Type u} [Fintype ι] (U : ι → X.affineOpens)
    (hpair : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1))
    (htriple : ∀ j k l, IsAffineOpen (((U j).1 ⊓ (U k).1) ⊓ (U l).1)) :
    letI := actualRelativeCechHOnePolynomialReesModule f (actualSpecIdealSheaf I) U hpair
    Function.Bijective (actualReesNativeHOneSemilinearComparison f I U hpair htriple) := by
  letI := actualRelativeCechHOnePolynomialReesModule f (actualSpecIdealSheaf I) U hpair
  let K := (Scheme.Modules.baseCechComplex (actualRelativeReesToBase f I)
    (SheafOfModules.unit (actualRelativeReesScheme f I).ringCatSheaf)
    (fun j => (actualReesCechCover f I U j).1)).sc' 0 1 2
  exact (actual_module_cat_homology_semilinear_quotient_map_bijective K
    (actualReesCechScalarEquiv I).toRingHom
    (actualReesNativeCechQuotientSemilinear f I U hpair htriple)
    (actual_rees_native_cech_quotient_semilinear_surjective f I U hpair htriple)
    (actual_rees_native_cech_quotient_semilinear_ker f I U hpair htriple)).comp
      (actualNativeUnitCechHOneExplicitIso (actualRelativeReesToBase f I)
        (fun j => (actualReesCechCover f I U j).1)).toLinearEquiv.bijective

/-- Native proper-cohomology finiteness transfers to the actual summed
ideal-power H¹ module through proved, fully scalar-compatible geometric coordinates. -/
theorem actual_relative_cech_hone_finite_of_native_rees
    (f : X ⟶ Spec (.of R)) [QuasiCompact f] (I : Ideal R)
    {ι : Type u} [Fintype ι] (U : ι → X.affineOpens)
    (hpair : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1))
    (htriple : ∀ j k l, IsAffineOpen (((U j).1 ⊓ (U k).1) ⊓ (U l).1))
    [Module.Finite Γ(Spec (.of (reesAlgebra I)), ⊤)
      ((Scheme.Modules.baseCechComplex (actualRelativeReesToBase f I)
        (SheafOfModules.unit (actualRelativeReesScheme f I).ringCatSheaf)
        (fun j => (actualReesCechCover f I U j).1)).homology 1)] :
    letI := actualRelativeCechHOnePolynomialReesModule f (actualSpecIdealSheaf I) U hpair
    Module.Finite (reesAlgebra ((actualSpecIdealSheaf I).ideal ⟨⊤, isAffineOpen_top _⟩))
      (⨁ n : ℕ, actualClosedCechHOne
        (((actualSpecIdealSheaf I) ^ n).comap f).subschemeι (fun j => (U j).1)) := by
  letI := actualRelativeCechHOnePolynomialReesModule f (actualSpecIdealSheaf I) U hpair
  let K := (Scheme.Modules.baseCechComplex (actualRelativeReesToBase f I)
    (SheafOfModules.unit (actualRelativeReesScheme f I).ringCatSheaf)
    (fun j => (actualReesCechCover f I U j).1)).sc' 0 1 2
  let h := actualNativeUnitCechHOneExplicitIso (actualRelativeReesToBase f I)
    (fun j => (actualReesCechCover f I U j).1)
  letI : Module.Finite Γ(Spec (.of (reesAlgebra I)), ⊤) K.homology :=
    Module.Finite.of_surjective h.hom.hom h.toLinearEquiv.surjective
  let σ := (actualReesCechScalarEquiv I).toRingHom
  letI : RingHomSurjective σ := ⟨(actualReesCechScalarEquiv I).surjective⟩
  exact actual_module_cat_homology_finite_of_semilinear_quotient K σ
    (actualReesNativeCechQuotientSemilinear f I U hpair htriple)
    (actual_rees_native_cech_quotient_semilinear_surjective f I U hpair htriple)
    (actual_rees_native_cech_quotient_semilinear_ker f I U hpair htriple)

#print axioms actual_relative_cech_hone_finite_of_native_rees
#print axioms actual_rees_native_hone_semilinear_comparison_bijective
end
end Negativity

