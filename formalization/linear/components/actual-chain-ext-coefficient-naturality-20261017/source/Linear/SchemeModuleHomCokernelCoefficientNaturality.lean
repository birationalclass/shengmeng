module
public import Linear.SchemeModuleHomSourceBoundaryCokernel
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- Actual coefficient action on SAME source-Hom cokernel. -/
def schemeModuleHomSourceCokernelCoefficientMap (S : ShortComplex X.Modules)
    {N M : X.Modules} (c : N ⟶ M) :
    cokernel (schemeModuleHomPrecompose (N := N) S.f) ⟶
      cokernel (schemeModuleHomPrecompose (N := M) S.f) :=
  cokernel.map _ _ (schemeModuleHomPostcompose (P := S.X₂) c)
    (schemeModuleHomPostcompose (P := S.X₁) c)
    ((schemeModuleInternalHomSourceNatTrans S.f).naturality c).symm

/-- SAME actual cokernel projection intertwines coefficient action. -/
theorem schemeModuleHomSourceCokernelCoefficientMap_projection (S : ShortComplex X.Modules)
    {N M : X.Modules} (c : N ⟶ M) :
    cokernel.π (schemeModuleHomPrecompose (N := N) S.f) ≫
        schemeModuleHomSourceCokernelCoefficientMap S c =
      schemeModuleHomPostcompose (P := S.X₁) c ≫
        cokernel.π (schemeModuleHomPrecompose (N := M) S.f) :=
  cokernel.π_desc _ _ _

/-- Coefficient naturality of SAME ACTUAL normalized Hom-cokernel/Ext1
comparison. Native resolution lift is constructed,not supplied as an input. -/
theorem schemeModuleHomSourceBoundaryCokernelIso_coefficientNaturality
    (S : ShortComplex X.Modules) (hS : S.ShortExact) {N M : X.Modules} (c : N ⟶ M)
    (I : InjectiveResolution N) (J : InjectiveResolution M)
    (hN : IsZero (schemeModuleInternalExt S.X₂ N 1))
    (hM : IsZero (schemeModuleInternalExt S.X₂ M 1)) :
    schemeModuleHomSourceCokernelCoefficientMap S c ≫
        (schemeModuleHomSourceBoundaryCokernelIso S hS M J hM).hom =
      (schemeModuleHomSourceBoundaryCokernelIso S hS N I hN).hom ≫
        (schemeModuleInternalExtFunctor S.X₃ 1).map c := by
  let phi := InjectiveResolution.desc c J I
  have comm : I.ι.f 0 ≫ phi.f 0 = c ≫ J.ι.f 0 :=
    InjectiveResolution.desc_commutes_zero c J I
  have hδ := schemeModuleInternalExtSourceBoundaryViaResolution_naturality S hS c I J phi comm 0
  have hz : schemeModuleHomPostcompose (P := S.X₁) c ≫
        ((schemeModuleInternalExtZeroIso S.X₁).app M).inv =
      ((schemeModuleInternalExtZeroIso S.X₁).app N).inv ≫
        (schemeModuleInternalExtFunctor S.X₁ 0).map c :=
    (schemeModuleInternalExtZeroIso S.X₁).inv.naturality c
  apply (cancel_epi (cokernel.π (schemeModuleHomPrecompose (N := N) S.f))).1
  rw [← Category.assoc,schemeModuleHomSourceCokernelCoefficientMap_projection,
    Category.assoc,schemeModuleHomSourceBoundaryCokernelIso_hom]
  rw [← Category.assoc,hz,Category.assoc,← hδ,← Category.assoc,
    ← schemeModuleHomSourceBoundaryCokernelIso_hom,Category.assoc]

end LinearStudy
