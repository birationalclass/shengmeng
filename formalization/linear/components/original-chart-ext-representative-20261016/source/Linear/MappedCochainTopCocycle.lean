module
public import Linear.CochainResolutionExactFunctorObjects
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
open CochainComplex.HomComplex
universe v u v' u'
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {B : Type u'} [Category.{v'} B] [Abelian B]
variable (F : A ⥤ B) [F.Additive]

/-- Mapping the ACTUAL shifted top cocycle by an additive functor and
its native single-complex comparison gives the cocycle of the SAME
mapped functional. Native shift conventions are retained throughout. -/
theorem mappedCochainResolutionTopCocycle
    (K : CochainComplex A ℤ) {M : A} (r : ℕ)
    (a : K.X (-(r:ℤ)) ⟶ M) (ha : K.d (-(r:ℤ)-1) (-(r:ℤ)) ≫ a = 0) :
    mappedCochainResolutionCocycle F K r
        (Cocycle.equivHomShift.symm (Cocycle.toSingleMk a (by simp) (-(r:ℤ)-1) (by omega) ha)) =
      Cocycle.equivHomShift.symm
        (Cocycle.toSingleMk (K := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
          (F.map a) (by simp) (-(r:ℤ)-1) (by omega)
          (by change F.map (K.d _ _) ≫ F.map a = 0; rw [← F.map_comp,ha,F.map_zero])) := by
  apply Cocycle.equivHomShift.injective
  ext : 1
  apply (Cochain.toSingleEquiv (show -(r:ℤ)+(r:ℤ)=0 by omega)).injective
  simp [mappedCochainResolutionCocycle,ShiftedHom.comp_mk₀,ShiftedHom.map,
    Cochain.toSingleEquiv,Cocycle.equivHomShift_apply,Cochain.rightUnshift_v,
    Cocycle.equivHomShift_symm_apply,Cochain.rightShift_v,
    Functor.mapCochainComplexSingleFunctor,Functor.map_comp,Category.assoc]
  erw [HomologicalComplex.XIsoOfEq_hom_naturality_assoc]
  simp [HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    HomologicalComplex.XIsoOfEq,eqToHom_map,← F.map_comp_assoc]

end LinearStudy