module
public import Linear.NativeProjectiveLaurentInitial
public import Linear.ProjectiveLaurentCechWeights
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u
variable {K : Type u} [Field K] {σ : Type} [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The ACTUAL native integer-twist Cech term is factorwise isomorphic
to its global homogeneous Laurent-weight presentation. -/
def coordinateNativeLaurentOrderedCechObjectIso (k : ℤ) (n : ℕ) :
    Scheme.Modules.orderedBaseCechObject (homogeneousProjπ (R := K) (σ := σ))
      (coordinateNativeIntegerTwist (K := K) (σ := σ) k)
      (coordinateOpenCover (R := K) (σ := σ)) n ≅
        coordinateHomogeneousLaurentOrderedCechObject (R := K) (σ := σ) k n :=
  Pi.mapIso fun a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
    (coordinateNativeIntegerTwistCechFactorLaurentEquiv (K := K) a.1 k).toModuleIso

/-- All geometric cofaces commute with the degreewise actual-native
Laurent comparison, including the changing-anchor first face. -/
theorem coordinateNativeLaurentOrderedCechCoface_naturality
    (k : ℤ) (n : ℕ) (j : Fin (n + 2)) :
    (coordinateNativeLaurentOrderedCechObjectIso (K := K) (σ := σ) k n).hom ≫
      coordinateHomogeneousLaurentOrderedCechCoface (R := K) (σ := σ) k n j =
    Scheme.Modules.orderedBaseCechCoface (homogeneousProjπ (R := K) (σ := σ))
      (coordinateNativeIntegerTwist (K := K) (σ := σ) k)
      (coordinateOpenCover (R := K) (σ := σ)) n j ≫
        (coordinateNativeLaurentOrderedCechObjectIso (K := K) (σ := σ) k (n+1)).hom := by
  unfold coordinateNativeLaurentOrderedCechObjectIso
  unfold coordinateHomogeneousLaurentOrderedCechCoface
  apply Pi.hom_ext
  intro a
  erw [Category.assoc, Pi.lift_comp_π, Pi.mapIso_hom_π_assoc]
  conv_rhs =>
    erw [Category.assoc, Pi.mapIso_hom_π,
      ← Category.assoc, Scheme.Modules.orderedBaseCechCoface_comp_π]
  let p : Scheme.Modules.orderedBaseCechObject (homogeneousProjπ (R := K) (σ := σ))
      (coordinateNativeIntegerTwist (K := K) (σ := σ) k)
      (coordinateOpenCover (R := K) (σ := σ)) n ⟶
        Scheme.Modules.baseCechFactor (homogeneousProjπ (R := K) (σ := σ))
          (coordinateNativeIntegerTwist (K := K) (σ := σ) k)
          (coordinateOpenCover (R := K) (σ := σ)) n (a.delete j).1 :=
    Pi.π _ (a.delete j)
  change p ≫ (coordinateNativeIntegerTwistCechFactorLaurentEquiv (K := K)
      (a.delete j).1 k).toModuleIso.hom ≫
      ModuleCat.ofHom (coordinateHomogeneousLaurentDeleteLinearMap (R := K) a j k) =
    (p ≫ (Scheme.Modules.baseModulePresheaf (homogeneousProjπ (R := K) (σ := σ))
        (coordinateNativeIntegerTwist (K := K) (σ := σ) k)).map
          (coordinateOpenCechDelete (R := K) a j).op) ≫
      (coordinateNativeIntegerTwistCechFactorLaurentEquiv (K := K) a.1 k).toModuleIso.hom
  rw [Category.assoc]
  apply congrArg (fun f => p ≫ f)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  exact (coordinateNativeIntegerTwistCechFactorLaurentEquiv_delete a j k s).symm

/-- The full alternating differential of the ACTUAL native integer
twist is the alternating deletion differential on Laurent weights. -/
theorem coordinateNativeLaurentOrderedCechDifferential_naturality (k : ℤ) (n : ℕ) :
    (coordinateNativeLaurentOrderedCechObjectIso (K := K) (σ := σ) k n).hom ≫
      coordinateHomogeneousLaurentOrderedCechDifferential (R := K) (σ := σ) k n =
    Scheme.Modules.orderedBaseCechDifferential (homogeneousProjπ (R := K) (σ := σ))
      (coordinateNativeIntegerTwist (K := K) (σ := σ) k)
      (coordinateOpenCover (R := K) (σ := σ)) n ≫
        (coordinateNativeLaurentOrderedCechObjectIso (K := K) (σ := σ) k (n+1)).hom := by
  rw [coordinateHomogeneousLaurentOrderedCechDifferential,
    Scheme.Modules.orderedBaseCechDifferential, Preadditive.comp_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp,
    coordinateNativeLaurentOrderedCechCoface_naturality]

/-- Consecutive Laurent-weight differentials compose to zero, as a
consequence of their proved comparison with the actual geometric complex. -/
theorem coordinateNativeLaurentOrderedCechDifferential_comp (k : ℤ) (n : ℕ) :
    coordinateHomogeneousLaurentOrderedCechDifferential (R := K) (σ := σ) k n ≫
      coordinateHomogeneousLaurentOrderedCechDifferential (R := K) (σ := σ) k (n+1) = 0 := by
  apply (cancel_epi (coordinateNativeLaurentOrderedCechObjectIso (K := K) (σ := σ) k n).hom).1
  rw [Limits.comp_zero, ← Category.assoc,
    coordinateNativeLaurentOrderedCechDifferential_naturality, Category.assoc,
    coordinateNativeLaurentOrderedCechDifferential_naturality, ← Category.assoc,
    Scheme.Modules.orderedBaseCechDifferential_comp, Limits.zero_comp]

/-- The Laurent-weight complex of the actual original Proj scheme;
no choice of an anchor coordinate is required in its global definition. -/
def coordinateNativeLaurentOrderedCechComplex (k : ℤ) :
    CochainComplex (ModuleCat.{u} Γ(Spec (CommRingCat.of K),
      (⊤ : (Spec (CommRingCat.of K)).Opens))) ℕ :=
  CochainComplex.of (coordinateHomogeneousLaurentOrderedCechObject (R := K) (σ := σ) k)
    (coordinateHomogeneousLaurentOrderedCechDifferential (R := K) (σ := σ) k)
    (coordinateNativeLaurentOrderedCechDifferential_comp (K := K) (σ := σ) k)

@[simp] theorem coordinateNativeLaurentOrderedCechComplex_X (k : ℤ) (n : ℕ) :
    (coordinateNativeLaurentOrderedCechComplex (K := K) (σ := σ) k).X n =
      coordinateHomogeneousLaurentOrderedCechObject (R := K) (σ := σ) k n := rfl

@[simp] theorem coordinateNativeLaurentOrderedCechComplex_d (k : ℤ) (n : ℕ) :
    (coordinateNativeLaurentOrderedCechComplex (K := K) (σ := σ) k).d n (n+1) =
      coordinateHomogeneousLaurentOrderedCechDifferential (R := K) (σ := σ) k n := by
  simp [coordinateNativeLaurentOrderedCechComplex]

/-- The ACTUAL native integer-twist Cech complex is isomorphic to
its explicit homogeneous Laurent-weight complex, including all differentials. -/
def coordinateNativeLaurentOrderedCechComplexIso (k : ℤ) :
    Scheme.Modules.orderedBaseCechComplex (homogeneousProjπ (R := K) (σ := σ))
      (coordinateNativeIntegerTwist (K := K) (σ := σ) k)
      (coordinateOpenCover (R := K) (σ := σ)) ≅
        coordinateNativeLaurentOrderedCechComplex (K := K) (σ := σ) k :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => coordinateNativeLaurentOrderedCechObjectIso (K := K) (σ := σ) k n) (by
      intro n m hnm
      simp only [ComplexShape.up_Rel] at hnm
      subst m
      rw [Scheme.Modules.orderedBaseCechComplex_d, coordinateNativeLaurentOrderedCechComplex_d]
      exact coordinateNativeLaurentOrderedCechDifferential_naturality k n)
end MvPolynomial
