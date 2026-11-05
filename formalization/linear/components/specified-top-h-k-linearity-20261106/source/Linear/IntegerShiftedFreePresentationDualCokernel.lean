module
public import Linear.IntegerShiftedFreePresentationHomKernelCoordinates
public import Linear.VectorDualCokernelKernel
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
variable {K S I J M : Type} [Field K] [CommRing S] [Algebra K S]
variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable [AddCommGroup M] [Module K M] [Module S M]
variable (c : (I → S) →ₗ[S] (J → S))
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (z : I → ℤ) (w : J → ℤ)
variable (hh : ∀ t : ℤ, ∀ x : I → S, x ∈ integerShiftedFreePiece 𝓑 z t →
  c x ∈ integerShiftedFreePiece 𝓑 w t)
variable (ℳ : ℤ → Submodule K M) [DirectSum.Decomposition ℳ]
variable (b : (J → S) →ₗ[S] M)
variable (bhh : ∀ t : ℤ, ∀ x : J → S, x ∈ integerShiftedFreePiece 𝓑 w t → b x ∈ ℳ t)
variable (hb : Function.Surjective b) (hrel : LinearMap.range c = LinearMap.ker b)

/-- Original homogeneous presentation Hom embeds into its ACTUAL original
coefficient tuple module,with image exactly the original relation kernel. -/
def integerShiftedFreePresentationHomCoefficientMap (d : ℤ) :
    integerGradedHomPiece 𝓑 ℳ d →ₗ[K] integerShiftedFreeDualCoordinatePiece 𝓑 w d :=
  (LinearMap.ker (integerShiftedFreeDualDegreeRelationMatrix c 𝓑 z w hh d)).subtype.comp
    (integerShiftedFreePresentationHomPolynomialKernelEquiv c 𝓑 z w hh ℳ b bhh hb hrel d).toLinearMap

theorem integerShiftedFreePresentationHomCoefficientMap_apply (d : ℤ)
    (φ : integerGradedHomPiece 𝓑 ℳ d) (j : J) :
    (integerShiftedFreePresentationHomCoefficientMap c 𝓑 z w hh ℳ b bhh hb hrel d φ).1 j =
      φ.1 (b (Pi.single j (1:S))) := by
  exact integerShiftedFreePresentationHomPolynomialKernelEquiv_apply c 𝓑 z w hh ℳ b bhh hb hrel d φ j

/-- The ACTUAL cokernel of the actual transpose multiplication dual
is the K-dual of ORIGINAL homogeneous Hom_S(M,S)_d. Both intermediate
kernel comparisons are constructed from original presentation data;
no matrix,Hom kernel or cokernel-duality identity is an input. -/
def integerShiftedFreePresentationDualCokernelHomIso (d : ℤ) :
    cokernel (ModuleCat.ofHom (integerShiftedFreeDualDegreeRelationMatrix c 𝓑 z w hh d).dualMap) ≅
      ModuleCat.of K (Module.Dual K (integerGradedHomPiece 𝓑 ℳ d)) :=
  (vectorDualCokernelKernelIso (integerShiftedFreeDualDegreeRelationMatrix c 𝓑 z w hh d)).trans
    (integerShiftedFreePresentationHomPolynomialKernelEquiv c 𝓑 z w hh ℳ b bhh hb hrel d).dualMap.toModuleIso

/-- The comparison respects the ORIGINAL cokernel quotient and ORIGINAL
coefficient evaluation phi(b(e_j)),which is the necessary quotient square
for the later actual Cech-duality connection. -/
theorem integerShiftedFreePresentationDualCokernelHomIso_quotient (d : ℤ) :
    cokernel.π (ModuleCat.ofHom (integerShiftedFreeDualDegreeRelationMatrix c 𝓑 z w hh d).dualMap) ≫
      (integerShiftedFreePresentationDualCokernelHomIso c 𝓑 z w hh ℳ b bhh hb hrel d).hom =
    ModuleCat.ofHom (integerShiftedFreePresentationHomCoefficientMap c 𝓑 z w hh ℳ b bhh hb hrel d).dualMap := by
  unfold integerShiftedFreePresentationDualCokernelHomIso
  rw [Iso.trans_hom,← Category.assoc,vectorDualCokernelKernelIso_quotient]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro ψ
  rfl

end LinearStudy
