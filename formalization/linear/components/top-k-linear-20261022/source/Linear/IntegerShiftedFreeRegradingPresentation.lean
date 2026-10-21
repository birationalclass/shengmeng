module
public import Linear.IntegerGradingShift
public import Linear.IntegerShiftedFreeGeneralRelationPi
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace LinearStudy
variable {K S I J M : Type} [Field K] [CommRing S] [Algebra K S]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]

/-- Regrade the ORIGINAL free weights w->w-k. The actual original
coefficient pieces are equal degree by degree,including negative pieces. -/
theorem integerShiftedFreePiece_regrade (w : I → ℤ) (k d : ℤ) :
    integerShiftedFreePiece B (fun i => w i-k) d =
      integerShiftedFreePiece B w (d+k) := by
  unfold integerShiftedFreePiece
  congr 1
  funext i
  congr 1
  dsimp only
  omega

/-- ORIGINAL degree-zero c remains homogeneous for the actual regraded
free families;the underlying original c is not changed. -/
theorem integerShiftedFreeRelation_regrade (z : I → ℤ) (w : J → ℤ)
    (c : (I → S) →ₗ[S] (J → S))
    (hc : ∀ d : ℤ, ∀ x : I → S, x ∈ integerShiftedFreePiece B z d →
      c x ∈ integerShiftedFreePiece B w d) (k : ℤ) :
    ∀ d : ℤ, ∀ x : I → S, x ∈ integerShiftedFreePiece B (fun i => z i-k) d →
      c x ∈ integerShiftedFreePiece B (fun j => w j-k) d := by
  intro d x hx
  rw [integerShiftedFreePiece_regrade] at hx ⊢
  exact hc (d+k) x hx

variable [AddCommGroup M] [Module K M] [Module S M]

/-- ORIGINAL beta remains homogeneous into the actual original shifted
M grading. No graded-surjectivity or new presentation map is supplied. -/
theorem integerShiftedFreeQuotient_regrade (w : J → ℤ) (D : ℤ → Submodule K M)
    (β : (J → S) →ₗ[S] M)
    (hβ : ∀ d : ℤ, ∀ x : J → S, x ∈ integerShiftedFreePiece B w d → β x ∈ D d)
    (k : ℤ) :
    ∀ d : ℤ, ∀ x : J → S, x ∈ integerShiftedFreePiece B (fun j => w j-k) d →
      β x ∈ integerGradingShift D k d := by
  intro d x hx
  rw [integerShiftedFreePiece_regrade] at hx
  exact hβ (d+k) x hx

/-- ORIGINAL homogeneous Hom on D[k] is ORIGINAL Hom on D at degree
 d-k. This is equality of actual submodules of ORIGINAL S-linear maps. -/
theorem integerGradedHomPiece_regrade (D : ℤ → Submodule K M) (k d : ℤ) :
    integerGradedHomPiece B (integerGradingShift D k) d =
      integerGradedHomPiece B D (d-k) := by
  apply Submodule.ext
  intro φ
  constructor
  · intro h t x hx
    have hx' : x ∈ integerGradingShift D k (t-k) := by
      simpa only [integerGradingShift,sub_add_cancel] using hx
    have hv := h (t-k) x hx'
    have hd : (t-k)+d=t+(d-k) := by omega
    simpa only [hd] using hv
  · intro h t x hx
    have hv := h (t+k) x hx
    have hd : (t+k)+(d-k)=t+d := by omega
    simpa only [hd] using hv

/-- Genuine original homogeneous-Hom degree transport,not an abstract
comparison or a new canonical/duality hypothesis. -/
def integerGradedHomRegradingEquiv (D : ℤ → Submodule K M) (k d : ℤ) :
    integerGradedHomPiece B (integerGradingShift D k) d ≃ₗ[K]
      integerGradedHomPiece B D (d-k) :=
  LinearEquiv.ofEq _ _ (integerGradedHomPiece_regrade B D k d)

/-- ORIGINAL S-linear phi and every original phi(x) are unchanged. -/
theorem integerGradedHomRegradingEquiv_apply (D : ℤ → Submodule K M) (k d : ℤ)
    (φ : integerGradedHomPiece B (integerGradingShift D k) d) :
    (integerGradedHomRegradingEquiv B D k d φ).1=φ.1 := rfl

end LinearStudy
