module
public import Linear.TildeKoszulSourceInternalExtAcyclic
public import Linear.TildeKoszulCoforkActualModuleExt
public import Linear.AffineKoszulActualModuleExtInternalHomTop
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
/-- The ACTUAL original affine quotient-cofork gives the categorical
cokernel iso. No desired cokernel iso is a hypothesis. -/
def tildeKoszulActualCutCokernelIso (R : CommRingCat.{u}) {r : ℕ} (H : Fin r → R) :
    cokernel ((tildeFunctionKoszulComplex R H).d 1 0) ≅
      (tildeKoszulOriginalCutCokernelCofork R H).pt :=
  (colimit.isColimit (parallelPair ((tildeFunctionKoszulComplex R H).d 1 0) 0)).coconePointUniqueUpToIso
    (tildeKoszulOriginalCutCokernelCoforkIsColimit R H)
/-- The categorical quotient projection is the SAME original cut map. -/
theorem tildeKoszulActualCutCokernelIso_projection (R : CommRingCat.{u}) {r : ℕ}
    (H : Fin r → R) :
    cokernel.π ((tildeFunctionKoszulComplex R H).d 1 0) ≫
        (tildeKoszulActualCutCokernelIso R H).hom=
      (tildeKoszulOriginalCutCokernelCofork R H).π :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit (parallelPair ((tildeFunctionKoszulComplex R H).d 1 0) 0))
      (tildeKoszulOriginalCutCokernelCoforkIsColimit R H) .one
/-- SAME ACTUAL whole quotient augmentation;do not replace its roof. -/
theorem tildeKoszulActualCutCokernelAugmentation_eq_cofork
    (R : CommRingCat.{u}) {r : ℕ} (H : Fin r → R) :
    originalChainCokernelTargetAugmentation (tildeFunctionKoszulComplex R H)
      (tildeKoszulOriginalCutCokernelCofork R H).pt (tildeKoszulActualCutCokernelIso R H)=
        originalChainCoforkAugmentation (tildeFunctionKoszulComplex R H)
          (tildeKoszulOriginalCutCokernelCofork R H) := by
  apply HomologicalComplex.to_single_hom_ext
  rw [originalChainCokernelTargetAugmentation_f_zero]
  simpa only [originalChainCoforkAugmentation,ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
    using tildeKoszulActualCutCokernelIso_projection R H
/-- Actual source Koszul exactness DERIVES quasiisomorphism of SAME
actual categorical/original cut quotient augmentation. -/
theorem tildeKoszulActualCutCokernelAugmentation_quasiIso
    (R : CommRingCat.{u}) {r : ℕ} (H : Fin r → R)
    (he : ∀ j : ℕ,0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j) :
    QuasiIso (originalChainCokernelTargetAugmentation (tildeFunctionKoszulComplex R H)
      (tildeKoszulOriginalCutCokernelCofork R H).pt (tildeKoszulActualCutCokernelIso R H)) := by
  rw [tildeKoszulActualCutCokernelAugmentation_eq_cofork]
  exact tildeKoszulCoforkAugmentation_quasiIso_of_exact R H he
/-- ACTUAL derived SHEAF Ext of original affine quotient-cut structure
sheaf is top cohomology of SAME original Koszul internal-Hom complex.
Source Ext acyclicity and above-rank zero are DERIVED,not new inputs. -/
def affineKoszulActualSheafExtTopHomologyIso (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (p : ℕ) (H : Fin (p+1) → R)
    (he : ∀ j : ℕ,0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j) :
    schemeModuleInternalExt (tildeKoszulOriginalCutCokernelCofork R H).pt (tilde N) (p+1) ≅
      (affineKoszulInternalHomCochainComplex R N (p+1) H).homology (p+1) :=
  schemeModuleAcyclicCokernelRankCanonicalExtIso (tildeFunctionKoszulComplex R H)
    (tildeKoszulOriginalCutCokernelCofork R H).pt (tildeKoszulActualCutCokernelIso R H)
    (tildeKoszulActualCutCokernelAugmentation_quasiIso R H he) (tilde N) (p+1) (by omega)
    (tildeFunctionKoszul_sourceInternalExtAcyclic R H (tilde N))
    (tildeFunctionKoszul_isZero_above_rank R H ((p+1)+1) (by omega))
/-- Construct ACTUAL derived SHEAF Ext/associated MODULE Ext object iso
for SAME original affine quotient and coefficient,through SAME actual
Koszul internal-Hom complex. Original class/trace calibration still needs
its actual representative square;this object iso alone does not prove it. -/
def affineKoszulActualSheafExtTopModuleExtIso (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (p : ℕ) (H : Fin (p+1) → R)
    (he : ∀ j : ℕ,0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j) :
    schemeModuleInternalExt (tildeKoszulOriginalCutCokernelCofork R H).pt (tilde N) (p+1) ≅
      tilde (ModuleCat.of R
        (CategoryTheory.Abelian.Ext.{u} (ModuleCat.of R (R ⧸ Ideal.span (Set.range H))) N (p+1))) :=
  affineKoszulActualSheafExtTopHomologyIso R N p H he ≪≫
    (affineKoszulActualModuleExtInternalHomTopIso R N p H he).symm
end LinearStudy
