module
public import Linear.ActualPresentationDualKernel
public import Linear.IntegerGradedSurjectionPreimage
public import Linear.NativeProjectiveRingIntegerPieces
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace LinearStudy
variable {K S R E M : Type*} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup R] [Module S R]
variable [AddCommGroup E] [Module S E] [Module K E]
variable [AddCommGroup M] [Module S M] [Module K M]
variable (𝓑 : ℕ → Submodule K S)

/-- The ACTUAL degree-d homogeneous S-linear maps into the original
integer-graded ring: a degree-t argument is sent into original degree t+d.
This is a K-submodule of the original S-linear Hom module. -/
def integerGradedHomPiece (𝒟 : ℤ → Submodule K M) (d : ℤ) :
    Submodule K (Module.Dual S M) where
  carrier := {φ | ∀ t : ℤ, ∀ x : M, x ∈ 𝒟 t →
    φ x ∈ nativeProjectiveRingIntegerPiece 𝓑 (t+d)}
  zero_mem' := by
    intro t x hx
    exact (nativeProjectiveRingIntegerPiece 𝓑 (t+d)).zero_mem
  add_mem' := by
    intro φ ψ hφ hψ t x hx
    exact (nativeProjectiveRingIntegerPiece 𝓑 (t+d)).add_mem (hφ t x hx) (hψ t x hx)
  smul_mem' := by
    intro a φ hφ t x hx
    exact (nativeProjectiveRingIntegerPiece 𝓑 (t+d)).smul_mem a (hφ t x hx)

variable (ℰ : ℤ → Submodule K E) (ℳ : ℤ → Submodule K M)
variable [DirectSum.Decomposition ℰ] [DirectSum.Decomposition ℳ]
variable (b : E →ₗ[S] M)
variable (hh : ∀ t : ℤ, ∀ x : E, x ∈ ℰ t → b x ∈ ℳ t)
variable (hb : Function.Surjective b)

include hh hb in
/-- Homogeneity descends and ascends along the actual original homogeneous
surjection. Homogeneous preimages are PROVED using original projections;
no degreewise-surjectivity premise is added. -/
theorem integerGradedHomPiece_comp_iff (d : ℤ) (φ : Module.Dual S M) :
    φ.comp b ∈ integerGradedHomPiece 𝓑 ℰ d ↔
      φ ∈ integerGradedHomPiece 𝓑 ℳ d := by
  constructor
  · intro hφ t x hx
    obtain ⟨y,hy,he⟩ := integerDegreeZeroSurjection_homogeneous_preimages ℰ ℳ b hh hb t x hx
    rw [← he]
    exact hφ t y hy
  · intro hφ t x hx
    exact hφ t (b x) (hh t x hx)

variable (c : R →ₗ[S] E)
variable (h : LinearMap.range c = LinearMap.ker b)

/-- The degree-d part of the ACTUAL original dual relation kernel;
it is cut out by the actual original grading on E and original c*. -/
def actualPresentationGradedDualKernelPiece (d : ℤ) :
    Submodule K (LinearMap.ker c.dualMap) :=
  (integerGradedHomPiece 𝓑 ℰ d).comap
    ((LinearMap.ker c.dualMap).subtype.restrictScalars K)

include hh in
/-- Under the actual original presentation-dual equivalence, the preimage
of the actual degree-d relation kernel is exactly original Hom degree d. -/
theorem actualPresentationGradedDualKernel_comap (d : ℤ) :
    (actualPresentationGradedDualKernelPiece 𝓑 ℰ c d).comap
      ((actualPresentationDualKernelEquiv c b hb h).restrictScalars K).toLinearMap =
    integerGradedHomPiece 𝓑 ℳ d := by
  ext φ
  change (actualPresentationDualKernelEquiv c b hb h φ).1 ∈ integerGradedHomPiece 𝓑 ℰ d ↔
    φ ∈ integerGradedHomPiece 𝓑 ℳ d
  have he : (actualPresentationDualKernelEquiv c b hb h φ).1 = φ.comp b := by
    ext x
    exact actualPresentationDualKernelEquiv_apply c b hb h φ x
  rw [he]
  exact integerGradedHomPiece_comp_iff 𝓑 ℰ ℳ b hh hb d φ

/-- Original degree-d homogeneous Hom is canonically the degree-d part
of the ACTUAL original relation kernel, using only the original graded
presentation. No homology, derived duality or arbitrary kernel comparison
is supplied as a premise. -/
def actualPresentationGradedDualKernelEquiv (d : ℤ) :
    integerGradedHomPiece 𝓑 ℳ d ≃ₗ[K]
      actualPresentationGradedDualKernelPiece 𝓑 ℰ c d :=
  (LinearEquiv.ofEq _ _ (actualPresentationGradedDualKernel_comap 𝓑 ℰ ℳ b hh hb c h d).symm).trans
    (((actualPresentationDualKernelEquiv c b hb h).restrictScalars K).ofSubmodule'
      (actualPresentationGradedDualKernelPiece 𝓑 ℰ c d))

/-- The homogeneous comparison still acts by the original quotient b
on every original argument, rather than choosing new Hom coordinates. -/
theorem actualPresentationGradedDualKernelEquiv_apply (d : ℤ)
    (φ : integerGradedHomPiece 𝓑 ℳ d) (x : E) :
    (actualPresentationGradedDualKernelEquiv 𝓑 ℰ ℳ b hh hb c h d φ).1.1 x = φ.1 (b x) := by
  rfl

end LinearStudy
