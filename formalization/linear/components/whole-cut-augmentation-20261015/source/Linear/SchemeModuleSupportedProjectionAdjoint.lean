module
public import Linear.SchemeModuleSupportedRestrictionIso
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open CategoryTheory AlgebraicGeometry
variable {A B : Type*} [Category* A] [Category* B]

/-- The SAME actual unit followed by pushforward of a chart map carries
an original source projection to its adjoint chart projection. The chart
projection identity is explicit here;original applications derive it. -/
theorem adjunction_unitProjection_eq_adjoint {F : A ⥤ B} {G : B ⥤ A}
    (adj : F ⊣ G) {P M : A} {Q : B} (u : P ⟶ M) (e : F.obj M ⟶ Q)
    (v : F.obj P ⟶ Q) (hv : F.map u ≫ e = v) :
    u ≫ (adj.unit.app M ≫ G.map e) = (adj.homEquiv P Q) v := by
  rw [← adj.homEquiv_unit,← adj.homEquiv_naturality_left,hv]

/-- The ACTUAL supported-restriction comparison preserves the original
projection as the native adjoint of its original chart map. All generic
conditions are explicit,no arbitrary global comparison map is chosen. -/
theorem schemeModuleSupportedRestrictionIso_projection_adjoint
    {X Y : Scheme} (j : X ⟶ Y) [IsOpenImmersion j]
    (M : Y.Modules) (Q : X.Modules)
    (hu : IsIso ((Scheme.Modules.restrictAdjunction j).unit.app M))
    (e : (Scheme.Modules.restrictFunctor j).obj M ≅ Q)
    {P : Y.Modules} (u : P ⟶ M)
    (v : (Scheme.Modules.restrictFunctor j).obj P ⟶ Q)
    (hv : (Scheme.Modules.restrictFunctor j).map u ≫ e.hom = v) :
    u ≫ (schemeModuleSupportedRestrictionIso j M Q hu e).hom =
      ((Scheme.Modules.restrictAdjunction j).homEquiv P Q) v := by
  rw [schemeModuleSupportedRestrictionIso_hom]
  exact adjunction_unitProjection_eq_adjoint (Scheme.Modules.restrictAdjunction j) u e.hom v hv

end LinearStudy