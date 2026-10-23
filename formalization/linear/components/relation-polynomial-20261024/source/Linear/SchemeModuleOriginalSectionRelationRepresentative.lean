module
public import Linear.SchemeModuleOriginalSectionRelationDescent
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u
attribute [local instance] schemeModuleActualCohomologyAddCommGroup
/-- Full original section-relation descent with an arbitrary explicit
per-functional representation predicate. STATEMENT only. No desired
representation is assumed for a particular section relation. -/
def schemeModuleOriginalSectionRelationRepresentativeStatement
    {K : Type u} [Field K] {X : Scheme.{u}}
    (pi : X ⟶ Spec (CommRingCat.of K)) {E M : X.Modules}
    (CC : ChainComplex X.Modules ℕ) (r : ℕ)
    (alpha : CC ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
    (hAbove : IsZero (CC.X (r+1))) (phi : CC.X r ≅ M)
    (Rep : (schemeModuleActualCohomology X M r →+ K) → Prop) : Prop :=
  letI : Module K Γ(E,⊤) := schemeModuleSectionsSpecModule pi E
  ∀ lambda : Module.Dual K Γ(E,⊤),lambda ≠ 0 →
    (∀ s : Γ(CC.X 0,⊤),lambda ((alpha.f 0).app ⊤ s)=0) →
    ∃ ell : schemeModuleActualCohomology X M r →+ K,ell ≠ 0 ∧
      (∀ a : K,∀ x : schemeModuleActualCohomology X M r,
      ell (CategoryTheory.Sheaf.H.map ((schemeModuleToActualAbelianSheaf X).map
        (originalGlobalModuleScalar (pi.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a)) M)) r x)=a * ell x) ∧
      (∀ s : Γ(E,⊤),ell (schemeModuleOriginalActualSectionBoundary CC r alpha hAlpha hAbove phi s)=lambda s) ∧ Rep ell
/-- Reuse the PROVED original scalar-linear quotient descent and a
verified per-functional construction. This small generic bridge avoids
repeating native/graded objects inside the kernel proof of composition. -/
theorem schemeModuleOriginalSectionRelationRepresentativeStatement_of_exact
    {K : Type u} [Field K] {X : Scheme.{u}}
    (pi : X ⟶ Spec (CommRingCat.of K)) {E M : X.Modules}
    (CC : ChainComplex X.Modules ℕ) (r : ℕ)
    (alpha : CC ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
    (hAbove : IsZero (CC.X (r+1))) (phi : CC.X r ≅ M)
    (Rep : (schemeModuleActualCohomology X M r →+ K) → Prop)
    (hExact : schemeModuleOriginalActualSectionExactStatement CC r alpha hAlpha hAbove phi)
    (hRep : ∀ ell : schemeModuleActualCohomology X M r →+ K,
      (∀ a : K,∀ x : schemeModuleActualCohomology X M r,
      ell (CategoryTheory.Sheaf.H.map ((schemeModuleToActualAbelianSheaf X).map
        (originalGlobalModuleScalar (pi.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a)) M)) r x)=a * ell x) → ell ≠ 0 → Rep ell) :
    schemeModuleOriginalSectionRelationRepresentativeStatement pi CC r alpha hAlpha hAbove phi Rep := by
  dsimp only [schemeModuleOriginalSectionRelationRepresentativeStatement]
  letI : Module K Γ(E,⊤) := schemeModuleSectionsSpecModule pi E
  letI : Module K (schemeModuleActualCohomology X M r) := schemeModuleActualHSpecModule pi M r
  intro lambda hne hrel
  obtain ⟨ell,hell,hvalue⟩ := schemeModuleOriginalActualSectionRelation_nonzero_descent
    pi CC r alpha hAlpha hAbove phi hExact lambda hne hrel
  have hellAdd : ell.toAddMonoidHom ≠ 0 := by
    intro hz
    apply hell
    apply LinearMap.ext
    intro x
    exact congrArg (fun f : schemeModuleActualCohomology X M r →+ K => f x) hz
  have hscalar (a : K) (x : schemeModuleActualCohomology X M r) :
      ell (CategoryTheory.Sheaf.H.map ((schemeModuleToActualAbelianSheaf X).map
        (originalGlobalModuleScalar (pi.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a)) M)) r x)=a * ell x := by
    change ell (a • x)=a * ell x
    exact ell.map_smul a x
  exact ⟨ell.toAddMonoidHom,hellAdd,hscalar,hvalue,hRep ell.toAddMonoidHom hscalar hellAdd⟩
end LinearStudy
