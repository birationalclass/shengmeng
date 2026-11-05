/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate. Ticket T-A2d (step 4).
-/
module
public import Linear.ProjectiveLaurentWeight
public import Linear.ProjectiveCoordinateOpens
public import Linear.ProjStructureSectionSquare
public import Linear.ModuleOrderedBaseCech
public import Linear.ModuleBaseCechFactors
@[expose] public section
set_option backward.privateInPublic true
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra
/-- The standard coordinate cover, lifted to the universe of the projective scheme. -/
abbrev coordinateOpenCover (i : ULift.{u} σ) :
    (Proj (homogeneousSubmodule σ R)).Opens :=
  coordinateOpen (R := R) i.down

/-- Every member of the universe-lifted standard coordinate cover is affine. -/
theorem coordinateOpenCover_isAffineOpen (i : ULift.{u} σ) :
    IsAffineOpen (coordinateOpenCover (R := R) i) :=
  coordinateOpen_isAffineOpen i.down

/-- The universe-lifted standard coordinate opens cover projective space. -/
theorem iSup_coordinateOpenCover_eq_top :
    ⨆ i : ULift.{u} σ, coordinateOpenCover (R := R) i = ⊤ := by
  apply top_unique
  rw [← iSup_coordinateOpen_eq_top (R := R)]
  exact iSup_le fun i => le_iSup (coordinateOpenCover (R := R)) (ULift.up i)

/-- The intersection of the standard coordinate charts indexed by a Cech tuple. -/
abbrev coordinateOpenCechIntersection {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) :
    (Proj (homogeneousSubmodule σ R)).Opens :=
  ∏ᶜ fun k : Fin (n + 1) => coordinateOpenCover (R := R) (a k)

/-- A standard Cech intersection is contained in each chart occurring in its tuple. -/
theorem coordinateOpenCechIntersection_le {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ)
    (k : Fin (n + 1)) :
    coordinateOpenCechIntersection (R := R) a ≤ coordinateOpenCover (R := R) (a k) :=
  leOfHom (Pi.π (fun l : Fin (n + 1) => coordinateOpenCover (R := R) (a l)) k)

private theorem coordinateProductPolynomial_eq_prod {n : ℕ}
    (a : Fin (n + 1) → σ) :
    coordinateProductPolynomial (R := R) a = ∏ k, X (a k) := by
  classical
  rw [coordinateProductPolynomial, coordinateTailPolynomial, Fin.prod_univ_succ]

/-- The coordinate product of a full Cech tuple is the deleted tuple product times the removed
coordinate. -/
theorem coordinateProductPolynomial_eq_delete_mul [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 2)) :
    coordinateProductPolynomial (R := R) (fun l => (a.1 l).down) =
      coordinateProductPolynomial (R := R) (fun l => ((a.delete k).1 l).down) *
        X (a.1 k).down := by
  classical
  rw [coordinateProductPolynomial_eq_prod, coordinateProductPolynomial_eq_prod,
    Fin.prod_univ_succAbove, mul_comm]
  rfl

/-- Deleting a noninitial Cech coordinate removes exactly that factor from the affine-chart tail
product. -/
theorem coordinateTailPolynomial_eq_delete_succ_mul [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 1)) :
    coordinateTailPolynomial (R := R) (fun l => (a.1 l).down) =
      coordinateTailPolynomial (R := R)
          (fun l => ((a.delete k.succ).1 l).down) *
        X (a.1 k.succ).down := by
  have h := coordinateProductPolynomial_eq_delete_mul (R := R) a k.succ
  rw [coordinateProductPolynomial, coordinateProductPolynomial] at h
  change X (a.1 0).down *
      coordinateTailPolynomial (R := R) (fun l => (a.1 l).down) =
    (X (a.1 0).down *
      coordinateTailPolynomial (R := R)
        (fun l => ((a.delete k.succ).1 l).down)) *
      X (a.1 k.succ).down at h
  rw [mul_assoc] at h
  exact X_mul_cancel_left_iff.mp h

/-- For a noninitial deletion, localization first at the deleted tail and then at the removed
coordinate is localization directly at the full tail. -/
theorem coordinateTailAwayMap_comp_delete_succ [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 1))
    (q : HomogeneousLocalization.Away
      (homogeneousSubmodule σ R) (X (a.1 0).down)) :
    HomogeneousLocalization.awayMap
        (homogeneousSubmodule σ R)
        (X_mem_homogeneousSubmodule_one R (a.1 k.succ).down)
        (coordinateProductPolynomial_eq_delete_mul (R := R) a k.succ)
        (HomogeneousLocalization.awayMap
          (homogeneousSubmodule σ R)
          (coordinateTailPolynomial_mem (R := R)
            (fun l => ((a.delete k.succ).1 l).down))
          (rfl : coordinateProductPolynomial (R := R)
              (fun l => ((a.delete k.succ).1 l).down) =
            X (a.1 0).down *
              coordinateTailPolynomial (R := R)
                (fun l => ((a.delete k.succ).1 l).down))
          q) =
      HomogeneousLocalization.awayMap
        (homogeneousSubmodule σ R)
        (coordinateTailPolynomial_mem (R := R) (fun l => (a.1 l).down))
        (rfl : coordinateProductPolynomial (R := R) (fun l => (a.1 l).down) =
          X (a.1 0).down *
            coordinateTailPolynomial (R := R) (fun l => (a.1 l).down))
        q := by
  have hy' : coordinateProductPolynomial (R := R) (fun l => (a.1 l).down) =
      X (a.1 0).down *
        (coordinateTailPolynomial (R := R)
          (fun l => ((a.delete k.succ).1 l).down) * X (a.1 k.succ).down) := by
    rw [coordinateProductPolynomial, coordinateTailPolynomial_eq_delete_succ_mul]
  have h := congrArg
    (fun f : HomogeneousLocalization.Away
        (homogeneousSubmodule σ R) (X (a.1 0).down) →+*
        HomogeneousLocalization.Away (homogeneousSubmodule σ R)
          (coordinateProductPolynomial (R := R) (fun l => (a.1 l).down)) => f q)
    (HomogeneousLocalization.awayMap_comp
      (homogeneousSubmodule σ R)
      (X_mem_homogeneousSubmodule_one R (a.1 0).down)
      (coordinateTailPolynomial_mem (R := R)
        (fun l => ((a.delete k.succ).1 l).down))
      (X_mem_homogeneousSubmodule_one R (a.1 k.succ).down)
      (rfl : coordinateProductPolynomial (R := R)
          (fun l => ((a.delete k.succ).1 l).down) =
        X (a.1 0).down *
          coordinateTailPolynomial (R := R)
            (fun l => ((a.delete k.succ).1 l).down))
      (coordinateProductPolynomial_eq_delete_mul (R := R) a k.succ)
      hy')
  rw [RingHom.comp_apply] at h
  exact h

private theorem basicOpen_prod {ι : Type*} [Fintype ι]
    (f : ι → MvPolynomial σ R) :
    Proj.basicOpen (homogeneousSubmodule σ R) (∏ i, f i) =
      ⨅ i, Proj.basicOpen (homogeneousSubmodule σ R) (f i) := by
  classical
  ext x
  rw [TopologicalSpace.Opens.coe_iInf]
  simp only [Set.mem_iInter]
  let y : ProjectiveSpectrum (homogeneousSubmodule σ R) := x
  change (∏ i, f i) ∉ y.asHomogeneousIdeal.toIdeal ↔
    ∀ i, f i ∉ y.asHomogeneousIdeal.toIdeal
  have hprod : (∏ i, f i) ∈ y.asHomogeneousIdeal.toIdeal ↔
      ∃ i, f i ∈ y.asHomogeneousIdeal.toIdeal := by
    simpa using (Ideal.IsPrime.prod_mem_iff
      (s := Finset.univ) (x := f) (p := y.asHomogeneousIdeal.toIdeal))
  rw [not_congr hprod]
  simp

/-- A standard Cech intersection is the single basic open at its tuple coordinate product. -/
theorem coordinateOpenCechIntersection_eq_basicOpen {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) :
    coordinateOpenCechIntersection (R := R) a =
      Proj.basicOpen (homogeneousSubmodule σ R)
        (coordinateProductPolynomial (R := R) (fun k => (a k).down)) := by
  rw [show coordinateOpenCechIntersection (R := R) a =
      ⨅ k : Fin (n + 1), coordinateOpenCover (R := R) (a k) from
    (IsLimit.conePointUniqueUpToIso (limit.isLimit _)
      (Preorder.isLimitIInf _)).to_eq]
  rw [coordinateProductPolynomial_eq_prod]
  exact (basicOpen_prod (R := R) (fun k : Fin (n + 1) => X (a k).down)).symm

/-- The actual coordinate intersection is affine, derived from its homogeneous positive-degree product; no separatedness input is required. -/
theorem coordinateOpenCechIntersection_isAffineOpen {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) :
    IsAffineOpen (coordinateOpenCechIntersection (R := R) a) := by
  rw [coordinateOpenCechIntersection_eq_basicOpen]
  exact Proj.isAffineOpen_basicOpen (homogeneousSubmodule σ R) _
    (coordinateProductPolynomial_mem (R := R) (fun k => (a k).down)) (Nat.succ_pos n)

/-- The canonical homogeneous localization presentation of a standard Cech intersection's
structure-sheaf sections. -/
noncomputable def coordinateOpenCechIntersectionAwayIso {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) :
    CommRingCat.of
        (HomogeneousLocalization.Away (homogeneousSubmodule σ R)
          (coordinateProductPolynomial (R := R) (fun k => (a k).down))) ≅
      Γ(Proj (homogeneousSubmodule σ R), coordinateOpenCechIntersection (R := R) a) :=
  (Proj.basicOpenIsoAway (homogeneousSubmodule σ R)
      (coordinateProductPolynomial (R := R) (fun k => (a k).down))
      (coordinateProductPolynomial_mem (R := R) (fun k => (a k).down))
      (Nat.succ_pos n)).trans
    ((Proj (homogeneousSubmodule σ R)).presheaf.mapIso
      (eqToIso (coordinateOpenCechIntersection_eq_basicOpen (R := R) a)).op)

/-- Sections on a standard projective Cech intersection, in Laurent-monomial coordinates. -/
noncomputable def coordinateOpenCechIntersectionLaurentRingEquiv {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) :
    Γ(Proj (homogeneousSubmodule σ R),
        coordinateOpenCechIntersection (R := R) a) ≃+*
      AddMonoidAlgebra R
        (laurentExponentSubmonoid
          (coordinateTailExponent (fun k => (a k).down))) :=
  (coordinateOpenCechIntersectionAwayIso (R := R) a).commRingCatIsoToRingEquiv.symm |>.trans
    ((coordinateProductAwayRingEquiv (R := R) (fun k => (a k).down)).trans
      (laurentMonomialRingEquiv R
        (coordinateTailExponent (fun k => (a k).down))))

/-- Laurent-monomial coordinates with coefficients transported to the global sections of the
affine base. -/
noncomputable def coordinateOpenCechIntersectionBaseLaurentRingEquiv {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) :
    Γ(Proj (homogeneousSubmodule σ R),
        coordinateOpenCechIntersection (R := R) a) ≃+*
      AddMonoidAlgebra Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        (laurentExponentSubmonoid
          (coordinateTailExponent (fun k => (a k).down))) :=
  (coordinateOpenCechIntersectionLaurentRingEquiv (R := R) a).trans
    (AddMonoidAlgebra.mapRingEquiv _
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm)

/-- The structure morphism on a projective Cech intersection is the coefficient map into its
homogeneous localization presentation. -/
theorem coordinateOpenCechIntersection_structure_section_square {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        (homogeneousProjπ (R := R) (σ := σ)).appTop ≫
        (Proj (homogeneousSubmodule σ R)).presheaf.map (homOfLE le_top).op ≫
        (coordinateOpenCechIntersectionAwayIso (R := R) a).inv =
      CommRingCat.ofHom
        (homogeneousAwayCoeffHom
          (coordinateProductPolynomial (R := R) (fun k => (a k).down))) := by
  simp only [coordinateOpenCechIntersectionAwayIso, Iso.trans_inv,
    Functor.mapIso_inv]
  rw [← Category.assoc
    ((Proj (homogeneousSubmodule σ R)).presheaf.map (homOfLE le_top).op)]
  rw [← Functor.map_comp]
  rw [show (homOfLE le_top).op ≫
      (eqToIso (coordinateOpenCechIntersection_eq_basicOpen (R := R) a)).op.inv =
        (homOfLE le_top).op from Subsingleton.elim _ _]
  simpa [homogeneousProjπ, homogeneousAwayCoeffHom] using
    (LinearStudy.Proj_structure_section_square
      (homogeneousSubmodule σ R)
      (algebraMap R (homogeneousSubmodule σ R 0))
      (coordinateProductPolynomial (R := R) (fun k => (a k).down))
      (coordinateProductPolynomial_mem (R := R) (fun k => (a k).down))
      (Nat.succ_pos n))

/-- The base scalar map into a projective Cech intersection in homogeneous-localization
coordinates. -/
theorem coordinateOpenCechIntersection_baseScalarHom {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) :
    (homogeneousProjπ (R := R) (σ := σ)).appTop ≫
        (Proj (homogeneousSubmodule σ R)).presheaf.map (homOfLE le_top).op ≫
        (coordinateOpenCechIntersectionAwayIso (R := R) a).inv =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫
        CommRingCat.ofHom
          (homogeneousAwayCoeffHom
            (coordinateProductPolynomial (R := R) (fun k => (a k).down))) := by
  rw [← Iso.inv_comp_eq]
  exact coordinateOpenCechIntersection_structure_section_square (R := R) a

/-- A base scalar is the constant Laurent monomial in coefficient-ring coordinates. -/
@[simp]
theorem coordinateOpenCechIntersectionLaurentRingEquiv_baseScalar {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ)
    (r : Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))) :
    coordinateOpenCechIntersectionLaurentRingEquiv (R := R) a
        (((Proj (homogeneousSubmodule σ R)).presheaf.map
          (homOfLE le_top).op).hom
            ((homogeneousProjπ (R := R) (σ := σ)).appTop.hom r)) =
      AddMonoidAlgebra.single 0
        ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r) := by
  change laurentMonomialRingEquiv R _
      (coordinateProductAwayRingEquiv (R := R) _
        ((coordinateOpenCechIntersectionAwayIso (R := R) a).inv.hom
          (((Proj (homogeneousSubmodule σ R)).presheaf.map
            (homOfLE le_top).op).hom
              ((homogeneousProjπ (R := R) (σ := σ)).appTop.hom r)))) = _
  have hscalar := congrArg
    (fun q : Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens)) →+*
        HomogeneousLocalization.Away (homogeneousSubmodule σ R)
          (coordinateProductPolynomial (R := R) (fun k => (a k).down)) => q r)
    (congrArg CommRingCat.Hom.hom
      (coordinateOpenCechIntersection_baseScalarHom (R := R) a))
  change (coordinateOpenCechIntersectionAwayIso (R := R) a).inv.hom
      (((Proj (homogeneousSubmodule σ R)).presheaf.map
        (homOfLE le_top).op).hom
          ((homogeneousProjπ (R := R) (σ := σ)).appTop.hom r)) =
    algebraMap R
      (HomogeneousLocalization.Away (homogeneousSubmodule σ R)
        (coordinateProductPolynomial (R := R) (fun k => (a k).down)))
      ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r) at hscalar
  rw [hscalar, coordinateProductAwayRingEquiv_algebraMap,
    laurentMonomialRingEquiv_algebraMap_coeff]
  rfl

/-- A base scalar is the constant Laurent monomial after transporting coefficients to the affine
base's global-section ring. -/
@[simp]
theorem coordinateOpenCechIntersectionBaseLaurentRingEquiv_baseScalar {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ)
    (r : Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))) :
    coordinateOpenCechIntersectionBaseLaurentRingEquiv (R := R) a
        (((Proj (homogeneousSubmodule σ R)).presheaf.map
          (homOfLE le_top).op).hom
            ((homogeneousProjπ (R := R) (σ := σ)).appTop.hom r)) =
      algebraMap
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        (AddMonoidAlgebra
          Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          (laurentExponentSubmonoid
            (coordinateTailExponent (fun k => (a k).down)))) r := by
  change AddMonoidAlgebra.mapRingEquiv _
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm
        (coordinateOpenCechIntersectionLaurentRingEquiv (R := R) a
          (((Proj (homogeneousSubmodule σ R)).presheaf.map
            (homOfLE le_top).op).hom
              ((homogeneousProjπ (R := R) (σ := σ)).appTop.hom r))) = _
  rw [coordinateOpenCechIntersectionLaurentRingEquiv_baseScalar,
    AddMonoidAlgebra.mapRingEquiv_single]
  change AddMonoidAlgebra.single 0
      ((Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm
        ((Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv r)) =
    AddMonoidAlgebra.single 0 r
  rw [(Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm_apply_apply]

private noncomputable def coordinateOpenCechIntersectionBaseCechFactorAddEquiv {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) :
    Scheme.Modules.baseCechFactor
        (homogeneousProjπ (R := R) (σ := σ))
        (SheafOfModules.unit (Proj (homogeneousSubmodule σ R)).ringCatSheaf)
        (coordinateOpenCover (R := R) (σ := σ)) n a ≃+
      Γ(Proj (homogeneousSubmodule σ R),
        coordinateOpenCechIntersection (R := R) a) :=
  AddEquiv.refl _

private theorem coordinateOpenCechIntersectionBaseCechFactorAddEquiv_smul {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ)
    (r : Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens)))
    (x : Scheme.Modules.baseCechFactor
        (homogeneousProjπ (R := R) (σ := σ))
        (SheafOfModules.unit (Proj (homogeneousSubmodule σ R)).ringCatSheaf)
        (coordinateOpenCover (R := R) (σ := σ)) n a) :
    coordinateOpenCechIntersectionBaseCechFactorAddEquiv (R := R) a (r • x) =
      ((Proj (homogeneousSubmodule σ R)).presheaf.map
        (homOfLE (show coordinateOpenCechIntersection (R := R) a ≤ ⊤ from
          le_top)).op).hom
          ((homogeneousProjπ (R := R) (σ := σ)).appTop.hom r) *
        coordinateOpenCechIntersectionBaseCechFactorAddEquiv (R := R) a x := by
  rfl

/-- A standard projective Cech intersection factor is the free module on its allowed Laurent
monomials over the affine base's global-section ring. -/
noncomputable def coordinateOpenCechIntersectionBaseLaurentLinearEquiv {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) :
    Scheme.Modules.baseCechFactor
        (homogeneousProjπ (R := R) (σ := σ))
        (SheafOfModules.unit (Proj (homogeneousSubmodule σ R)).ringCatSheaf)
        (coordinateOpenCover (R := R) (σ := σ)) n a ≃ₗ[
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))]
      AddMonoidAlgebra
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        (laurentExponentSubmonoid
          (coordinateTailExponent (fun k => (a k).down))) :=
  { (coordinateOpenCechIntersectionBaseCechFactorAddEquiv (R := R) a).trans
      (coordinateOpenCechIntersectionBaseLaurentRingEquiv (R := R) a).toAddEquiv with
    map_smul' := by
      intro r x
      change coordinateOpenCechIntersectionBaseLaurentRingEquiv (R := R) a
          (coordinateOpenCechIntersectionBaseCechFactorAddEquiv (R := R) a (r • x)) =
        r • coordinateOpenCechIntersectionBaseLaurentRingEquiv (R := R) a
          (coordinateOpenCechIntersectionBaseCechFactorAddEquiv (R := R) a x)
      rw [coordinateOpenCechIntersectionBaseCechFactorAddEquiv_smul]
      rw [map_mul,
        coordinateOpenCechIntersectionBaseLaurentRingEquiv_baseScalar]
      rw [Algebra.smul_def] }

/-- A standard projective Cech intersection factor, reindexed by global homogeneous Laurent
weights of total degree `d` allowed on its coordinate tuple. -/
noncomputable def coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) (d : ℤ) :
    Scheme.Modules.baseCechFactor
        (homogeneousProjπ (R := R) (σ := σ))
        (SheafOfModules.unit (Proj (homogeneousSubmodule σ R)).ringCatSheaf)
        (coordinateOpenCover (R := R) (σ := σ)) n a ≃ₗ[
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))]
      AddMonoidAlgebra
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        {e : HomogeneousLaurentExponent σ d //
          e.IsAllowedOn (fun k => (a k).down)} :=
  (coordinateOpenCechIntersectionBaseLaurentLinearEquiv (R := R) a).trans
    (AddMonoidAlgebra.mapDomainLinearEquiv
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      (coordinateLaurentExponentEquiv (fun k => (a k).down) d))

/-- The homogeneous-weight factor equivalence sends a local Laurent basis vector to the same
monomial indexed by its global weight. -/
@[simp]
theorem coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv_basis_apply
    {n : ℕ} (a : Fin (n + 1) → ULift.{u} σ) (d : ℤ)
    (e : laurentExponentSubmonoid
      (coordinateTailExponent (fun k => (a k).down)))
    (r : Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))) :
    coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv (R := R) a d
        ((coordinateOpenCechIntersectionBaseLaurentLinearEquiv (R := R) a).symm
          (AddMonoidAlgebra.single e r)) =
      AddMonoidAlgebra.single
        (coordinateLaurentExponentEquiv (fun k => (a k).down) d e) r := by
  rw [coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv,
    LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    AddMonoidAlgebra.mapDomainLinearEquiv_single]


end
end MvPolynomial
