module
public import Linear.SchemeModuleInternalHomBifunctor
public import Linear.SchemeModuleHomUnitSourceNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}
/-- Transport ACTUAL internal Hom through original source and coefficient isomorphisms. Reuse the genuine internal-Hom functors. -/
def schemeModuleHomTransportIso {M M' N N' : X.Modules} (s : M ≅ M') (t : N ≅ N') :
    schemeModuleHomModuleSheaf M N ≅ schemeModuleHomModuleSheaf M' N' :=
  (schemeModuleInternalHomFunctor X N).mapIso s.symm.op ≪≫
    (schemeModuleInternalHomCoefficientFunctor X M').mapIso t
/-- Its actual map is original inverse-source precomposition followed by original coefficient postcomposition. -/
theorem schemeModuleHomTransportIso_hom {M M' N N' : X.Modules}
    (s : M ≅ M') (t : N ≅ N') :
    (schemeModuleHomTransportIso s t).hom =
      schemeModuleHomPrecompose (N := N) s.inv ≫ schemeModuleHomPostcompose t.hom := rfl
/-- Transport keeps SAME original curried functional,with the specified source and coefficient frames. -/
theorem schemeModuleHomTransportIso_curry {M M' N N' : X.Modules}
    (s : M ≅ M') (t : N ≅ N') (a : M ⟶ N) :
    (schemeModuleHomUnitAddEquiv M N).symm a ≫ (schemeModuleHomTransportIso s t).hom =
      (schemeModuleHomUnitAddEquiv M' N').symm (s.inv ≫ a ≫ t.hom) := by
  rw [schemeModuleHomTransportIso_hom,← Category.assoc,
    ← schemeModuleHomUnitAddEquiv_symm_precompose,
    ← schemeModuleHomUnitAddEquiv_symm_postcompose]
  simp only [Category.assoc]
/-- An ACTUAL source differential square gives the ACTUAL internal-Hom square in the reversed direction. No desired Hom-square assumption is supplied. -/
theorem schemeModuleHomTransportIso_differential
    {A B A' B' N N' : X.Modules} (s : A ≅ A') (t : B ≅ B') (e : N ≅ N')
    (d : A ⟶ B) (d' : A' ⟶ B') (w : d ≫ t.hom = s.hom ≫ d') :
    schemeModuleHomPrecompose (N := N) d ≫ (schemeModuleHomTransportIso s e).hom =
      (schemeModuleHomTransportIso t e).hom ≫ schemeModuleHomPrecompose (N := N') d' := by
  have w' : s.inv ≫ d = d' ≫ t.inv := by
    apply (cancel_mono t.hom).1
    simp only [Category.assoc]
    rw [w]
    simp only [Iso.inv_hom_id_assoc,Iso.inv_hom_id,Category.comp_id]
  rw [schemeModuleHomTransportIso_hom,schemeModuleHomTransportIso_hom,
    ← Category.assoc,← schemeModuleHomPrecompose_comp,w',schemeModuleHomPrecompose_comp]
  have he : schemeModuleHomPrecompose (N := N) d' ≫
        schemeModuleHomPostcompose (P := A') e.hom =
      schemeModuleHomPostcompose (P := B') e.hom ≫
        schemeModuleHomPrecompose (N := N') d' :=
    ((schemeModuleInternalHomSourceNatTrans d').naturality e.hom).symm
  simpa only [Category.assoc] using
    congrArg (fun z => schemeModuleHomPrecompose (N := N) t.inv ≫ z) he
end LinearStudy
