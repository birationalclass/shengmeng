module
public import Linear.OverOpenZeroPresheafAdjunction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory Opposite DirectSum
universe u
variable {C : Type u} [Preorder C] (R : Cᵒᵖ ⥤ RingCat.{u}) (U : C)

/-- The actual extension of the local unit maps into the original unit. -/
def overOpenUnitZeroPresheafToUnit :
    overOpenZeroPresheaf R U (PresheafOfModules.unit ((Over.forget U).op ⋙ R)) ⟶
      PresheafOfModules.unit R :=
  overOpenZeroHomExtend R U _ _ (𝟙 _)

/-- On every original summand this is the identity on the same coefficient ring. -/
theorem overOpenUnitZeroPresheafToUnit_lof (V : Cᵒᵖ) (i : V.unop ⟶ U)
    (x : R.obj V) :
    (overOpenUnitZeroPresheafToUnit R U).app V
      (DirectSum.lof (R.obj V) _
        (fun _ : V.unop ⟶ U => R.obj V) i x) = x := by
  classical
  exact overOpenZeroHomExtend_lof R U
    (PresheafOfModules.unit ((Over.forget U).op ⋙ R))
    (PresheafOfModules.unit R) (𝟙 _) V i x

/-- There is at most one summand,so the actual local-unit inclusion is mono. -/
theorem overOpenUnitZeroPresheafToUnit_mono :
    Mono (overOpenUnitZeroPresheafToUnit R U) := by
  classical
  apply PresheafOfModules.mono_of_injective
  intro V x y h
  apply DFinsupp.ext
  intro i
  have hc : DirectSum.component (R.obj V) (V.unop ⟶ U)
      (fun _ => R.obj V) i = ((overOpenUnitZeroPresheafToUnit R U).app V).hom := by
    apply DirectSum.linearMap_ext
    intro j
    have hj : j = i := Subsingleton.elim _ _
    subst j
    apply LinearMap.ext
    intro z
    change DirectSum.component (R.obj V) _ (fun _ => R.obj V) i
        (DirectSum.lof (R.obj V) _ (fun _ => R.obj V) i z) =
      (overOpenUnitZeroPresheafToUnit R U).app V
        (DirectSum.lof (R.obj V) _ (fun _ => R.obj V) i z)
    rw [DirectSum.component.lof_self,overOpenUnitZeroPresheafToUnit_lof]
  change DirectSum.component (R.obj V) _ (fun _ => R.obj V) i x =
    DirectSum.component (R.obj V) _ (fun _ => R.obj V) i y
  rw [hc]
  exact h
end LinearStudy
