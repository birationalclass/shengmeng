module
public import Linear.SchemeModuleChainSourceAcyclic
public import Linear.SchemeModuleInternalExtSourceBoundaryNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- SAME actual source dimension shift is independent of coefficient resolution. -/
theorem schemeModuleChainOpcycleExtShiftIso_independent (K : ChainComplex X.Modules ℕ)
    (p : ℕ) (hK : K.ExactAt (p+1)) (N : X.Modules) (I J : InjectiveResolution N)
    (q : ℕ) (hA : ∀ j,IsZero (schemeModuleInternalExt (K.X p) N (j+1))) :
    schemeModuleChainOpcycleExtShiftIso K p hK N I q hA =
      schemeModuleChainOpcycleExtShiftIso K p hK N J q hA := by
  apply Iso.ext
  rw [schemeModuleChainOpcycleExtShiftIso_hom,schemeModuleChainOpcycleExtShiftIso_hom]
  exact schemeModuleInternalExtSourceBoundaryViaResolution_independent _ _ N I J (q+1)

/-- SAME actual final Hom quotient comparison is independent of resolution. -/
theorem schemeModuleChainOpcycleHomCokernelIso_independent (K : ChainComplex X.Modules ℕ)
    (p : ℕ) (hK : K.ExactAt (p+1)) (N : X.Modules) (I J : InjectiveResolution N)
    (hA : IsZero (schemeModuleInternalExt (K.X p) N 1)) :
    schemeModuleChainOpcycleHomCokernelIso K p hK N I hA =
      schemeModuleChainOpcycleHomCokernelIso K p hK N J hA :=
by
  dsimp only [schemeModuleChainOpcycleHomCokernelIso]
  exact schemeModuleHomSourceBoundaryCokernelIso_independent
    (schemeModuleChainOpcycleSequence K p) (schemeModuleChainOpcycleSequence_shortExact K p hK) N I J hA

/-- Independence survives ALL actual successive source-boundary shifts. -/
theorem schemeModuleChainOpcycleIteratedExtIso_independent (K : ChainComplex X.Modules ℕ)
    (hK : ∀ p,K.ExactAt (p+1)) (N : X.Modules) (I J : InjectiveResolution N)
    (hA : ∀ p j,IsZero (schemeModuleInternalExt (K.X p) N (j+1))) (p q : ℕ) :
    schemeModuleChainOpcycleIteratedExtIso K hK N I hA p q =
      schemeModuleChainOpcycleIteratedExtIso K hK N J hA p q := by
  induction q generalizing p with
  | zero => rfl
  | succ q ih =>
    let a : schemeModuleInternalExt (K.opcycles ((p+1)+q)) N 1 ≅
        schemeModuleInternalExt (K.opcycles (p+(q+1))) N 1 :=
      eqToIso (congrArg (fun z => schemeModuleInternalExt (K.opcycles z) N 1)
        (by omega : (p+1)+q = p+(q+1)))
    change (schemeModuleChainOpcycleExtShiftIso K p (hK p) N I q (hA p)).symm ≪≫
        schemeModuleChainOpcycleIteratedExtIso K hK N I hA (p+1) q ≪≫ a =
      (schemeModuleChainOpcycleExtShiftIso K p (hK p) N J q (hA p)).symm ≪≫
        schemeModuleChainOpcycleIteratedExtIso K hK N J hA (p+1) q ≪≫ a
    rw [schemeModuleChainOpcycleExtShiftIso_independent K p (hK p) N I J q (hA p),ih (p+1)]

/-- SAME actual high-Ext/opcycle-cokernel comparison is independent of resolution. -/
theorem schemeModuleChainOpcycleExtCokernelIso_independent (K : ChainComplex X.Modules ℕ)
    (hK : ∀ p,K.ExactAt (p+1)) (N : X.Modules) (I J : InjectiveResolution N)
    (hA : ∀ p j,IsZero (schemeModuleInternalExt (K.X p) N (j+1))) (p q : ℕ) :
    schemeModuleChainOpcycleExtCokernelIso K hK N I hA p q =
      schemeModuleChainOpcycleExtCokernelIso K hK N J hA p q := by
  unfold schemeModuleChainOpcycleExtCokernelIso
  rw [schemeModuleChainOpcycleIteratedExtIso_independent K hK N I J hA p q,
    schemeModuleChainOpcycleHomCokernelIso_independent K (p+q) (hK (p+q)) N I J (hA (p+q) 0)]

/-- The WHOLE actual top SHEAF Ext/cohomology comparison is independent of resolution. -/
theorem schemeModuleAcyclicChainTopInternalExtIso_independent (K : ChainComplex X.Modules ℕ)
    (hK : ∀ p,K.ExactAt (p+1)) (N : X.Modules) (I J : InjectiveResolution N)
    (q : ℕ) (hA : ∀ p j,IsZero (schemeModuleInternalExt (K.X p) N (j+1)))
    (hAbove : IsZero (K.X (q+2))) :
    schemeModuleAcyclicChainTopInternalExtIso K hK N I q hA hAbove =
      schemeModuleAcyclicChainTopInternalExtIso K hK N J q hA hAbove := by
  unfold schemeModuleAcyclicChainTopInternalExtIso
  rw [schemeModuleChainOpcycleIteratedExtIso_independent K hK N I J hA 0 q,
    schemeModuleChainOpcycleHomCokernelIso_independent K q (hK q) N I J (hA q 0)]

/-- Retain SAME actual target iso and augmentation while changing coefficient resolution. -/
theorem schemeModuleAcyclicCokernelTopInternalExtIso_independent (K : ChainComplex X.Modules ℕ)
    (E : X.Modules) (e : cokernel (K.d 1 0) ≅ E)
    (he : QuasiIso (originalChainCokernelTargetAugmentation K E e))
    (N : X.Modules) (I J : InjectiveResolution N) (q : ℕ)
    (hA : ∀ p j,IsZero (schemeModuleInternalExt (K.X p) N (j+1)))
    (hAbove : IsZero (K.X (q+2))) :
    schemeModuleAcyclicCokernelTopInternalExtIso K E e he N I q hA hAbove =
      schemeModuleAcyclicCokernelTopInternalExtIso K E e he N J q hA hAbove := by
  unfold schemeModuleAcyclicCokernelTopInternalExtIso
  rw [schemeModuleAcyclicChainTopInternalExtIso_independent K _ N I J q hA hAbove]

/-- The exact positive-rank comparison is independent of coefficient resolution. -/
theorem schemeModuleAcyclicCokernelRankInternalExtIso_independent (K : ChainComplex X.Modules ℕ)
    (E : X.Modules) (e : cokernel (K.d 1 0) ≅ E)
    (he : QuasiIso (originalChainCokernelTargetAugmentation K E e))
    (N : X.Modules) (I J : InjectiveResolution N) (r : ℕ) (hr : 0<r)
    (hA : ∀ p j,IsZero (schemeModuleInternalExt (K.X p) N (j+1)))
    (hAbove : IsZero (K.X (r+1))) :
    schemeModuleAcyclicCokernelRankInternalExtIso K E e he N I r hr hA hAbove =
      schemeModuleAcyclicCokernelRankInternalExtIso K E e he N J r hr hA hAbove := by
  dsimp only [schemeModuleAcyclicCokernelRankInternalExtIso]
  rw [schemeModuleAcyclicCokernelTopInternalExtIso_independent K E e he N I J (r-1) hA]

/-- Native chosen-resolution construction equals the computation through ANY resolution. -/
theorem schemeModuleAcyclicCokernelRankCanonicalExtIso_eq_viaResolution
    (K : ChainComplex X.Modules ℕ) (E : X.Modules) (e : cokernel (K.d 1 0) ≅ E)
    (he : QuasiIso (originalChainCokernelTargetAugmentation K E e))
    (N : X.Modules) (I : InjectiveResolution N) (r : ℕ) (hr : 0<r)
    (hA : schemeModuleChainSourceExtAcyclic K N) (hAbove : IsZero (K.X (r+1))) :
    schemeModuleAcyclicCokernelRankCanonicalExtIso K E e he N r hr hA hAbove =
      schemeModuleAcyclicCokernelRankInternalExtIso K E e he N I r hr hA hAbove :=
  schemeModuleAcyclicCokernelRankInternalExtIso_independent K E e he N (injectiveResolution N) I r hr hA hAbove

end LinearStudy
