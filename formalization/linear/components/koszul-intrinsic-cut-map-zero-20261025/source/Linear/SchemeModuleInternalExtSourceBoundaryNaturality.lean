module
public import Linear.SchemeModuleInternalExtSourceBoundary
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- A SAME actual coefficient complex map gives an actual morphism
between SAME original source short complexes of internal Hom. -/
def schemeModuleHomSourceShortComplexMap (S : ShortComplex X.Modules)
    {K L : CochainComplex X.Modules ℕ} (phi : K ⟶ L) :
    schemeModuleHomSourceShortComplex S K ⟶ schemeModuleHomSourceShortComplex S L where
  τ₁ := ((schemeModuleInternalHomCoefficientFunctor X S.X₃).mapHomologicalComplex
    (ComplexShape.up ℕ)).map phi
  τ₂ := ((schemeModuleInternalHomCoefficientFunctor X S.X₂).mapHomologicalComplex
    (ComplexShape.up ℕ)).map phi
  τ₃ := ((schemeModuleInternalHomCoefficientFunctor X S.X₁).mapHomologicalComplex
    (ComplexShape.up ℕ)).map phi
  comm₁₂ := (NatTrans.mapHomologicalComplex (schemeModuleInternalHomSourceNatTrans S.g)
    (ComplexShape.up ℕ)).naturality phi
  comm₂₃ := (NatTrans.mapHomologicalComplex (schemeModuleInternalHomSourceNatTrans S.f)
    (ComplexShape.up ℕ)).naturality phi

/-- Coefficient naturality of the actual derived SHEAF Ext source
connecting map,using ANY actual comparison lift between resolutions. -/
theorem schemeModuleInternalExtSourceBoundaryViaResolution_naturality
    (S : ShortComplex X.Modules) (hS : S.ShortExact) {N M : X.Modules} (c : N ⟶ M)
    (I : InjectiveResolution N) (J : InjectiveResolution M)
    (phi : I.cocomplex ⟶ J.cocomplex)
    (comm : I.ι.f 0 ≫ phi.f 0 = c ≫ J.ι.f 0) (q : ℕ) :
    schemeModuleInternalExtSourceBoundaryViaResolution S hS N I q ≫
        (schemeModuleInternalExtFunctor S.X₃ (q+1)).map c =
      (schemeModuleInternalExtFunctor S.X₁ q).map c ≫
        schemeModuleInternalExtSourceBoundaryViaResolution S hS M J q := by
  let hI := schemeModuleHomSourceShortComplex_shortExact S hS I.cocomplex
  let hJ := schemeModuleHomSourceShortComplex_shortExact S hS J.cocomplex
  have hδ := HomologicalComplex.HomologySequence.δ_naturality
    (schemeModuleHomSourceShortComplexMap S phi) hI hJ q (q+1) rfl
  have hC := schemeModuleInternalExtInjectiveResolutionIso_naturality S.X₃ c (q+1)
    I J phi comm
  have hA := schemeModuleInternalExtInjectiveResolutionIso_naturality S.X₁ c q
    I J phi comm
  have hδ' : hI.δ q (q+1) rfl ≫
      (HomologicalComplex.homologyFunctor X.Modules (ComplexShape.up ℕ) (q+1)).map
        (((schemeModuleInternalHomCoefficientFunctor X S.X₃).mapHomologicalComplex
          (ComplexShape.up ℕ)).map phi) =
      (HomologicalComplex.homologyFunctor X.Modules (ComplexShape.up ℕ) q).map
        (((schemeModuleInternalHomCoefficientFunctor X S.X₁).mapHomologicalComplex
          (ComplexShape.up ℕ)).map phi) ≫ hJ.δ q (q+1) rfl := hδ
  apply (cancel_mono (schemeModuleInternalExtInjectiveResolutionIso S.X₃ M (q+1) J).hom).1
  rw [Category.assoc,hC,← Category.assoc,
    schemeModuleInternalExtSourceBoundary_resolution_square,Category.assoc]
  erw [hδ']
  rw [← Category.assoc,← hA,Category.assoc,
    ← schemeModuleInternalExtSourceBoundary_resolution_square,← Category.assoc]

/-- The SAME source connecting morphism is independent of the chosen
actual coefficient injective resolution. -/
theorem schemeModuleInternalExtSourceBoundaryViaResolution_independent
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (N : X.Modules)
    (I J : InjectiveResolution N) (q : ℕ) :
    schemeModuleInternalExtSourceBoundaryViaResolution S hS N I q =
      schemeModuleInternalExtSourceBoundaryViaResolution S hS N J q := by
  let phi := InjectiveResolution.desc (𝟙 N) J I
  have comm : I.ι.f 0 ≫ phi.f 0 = (𝟙 N) ≫ J.ι.f 0 := by
    exact InjectiveResolution.desc_commutes_zero (𝟙 N) J I
  have h := schemeModuleInternalExtSourceBoundaryViaResolution_naturality S hS
    (𝟙 N) I J phi comm q
  have hA := (schemeModuleInternalExtFunctor S.X₁ q).map_id N
  have hC := (schemeModuleInternalExtFunctor S.X₃ (q+1)).map_id N
  rw [hA,hC] at h
  calc
    schemeModuleInternalExtSourceBoundaryViaResolution S hS N I q =
        schemeModuleInternalExtSourceBoundaryViaResolution S hS N I q ≫ 𝟙 _ :=
      (Category.comp_id _).symm
    _ = 𝟙 _ ≫ schemeModuleInternalExtSourceBoundaryViaResolution S hS N J q := h
    _ = schemeModuleInternalExtSourceBoundaryViaResolution S hS N J q := Category.id_comp _

/-- The actual canonical source boundary. Independence is PROVED above. -/
def schemeModuleInternalExtSourceBoundary
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (N : X.Modules) (q : ℕ) :
    schemeModuleInternalExt S.X₁ N q ⟶ schemeModuleInternalExt S.X₃ N (q+1) :=
  schemeModuleInternalExtSourceBoundaryViaResolution S hS N (injectiveResolution N) q

/-- Compute the SAME canonical boundary by ANY actual injective resolution. -/
theorem schemeModuleInternalExtSourceBoundary_eq_viaResolution
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (N : X.Modules)
    (I : InjectiveResolution N) (q : ℕ) :
    schemeModuleInternalExtSourceBoundary S hS N q =
      schemeModuleInternalExtSourceBoundaryViaResolution S hS N I q :=
  schemeModuleInternalExtSourceBoundaryViaResolution_independent S hS N
    (injectiveResolution N) I q

end LinearStudy
