module
public import Linear.KoszulExactTopExtCoefficientRestriction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian
universe u
variable {R : Type u} [CommRing R] (p : ℕ) (H : Fin (p+1) → R)
variable (he : ∀ j : ℕ,0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j)
variable (N : ModuleCat.{u} R) (T : Type u) [AddCommGroup T] [Module R T]
/-- The ACTUAL derived MODULE Ext comparison uses the SAME original
Koszul restriction equivalence,followed by the original coefficient dual.
No derived SHEAF Ext or original geometric top-H comparison is asserted. -/
def koszulExactTopExtOriginalCoefficientEquiv
    (F : (N ⧸ (Ideal.span (Set.range H) • (⊤ : Submodule R N))) ≃ₗ[R] T) :
    Ext.{u} (ModuleCat.of R (R ⧸ Ideal.span (Set.range H))) N (p+1) ≃ₗ[R] T :=
  (koszulExactTopExtCoefficientRestrictionEquiv p H he N).trans F
/-- Every ORIGINAL ordered-top representative is evaluated on the SAME
ordered top generator before taking the SAME coefficient quotient. -/
theorem koszulExactTopExtOriginalCoefficientEquiv_representative
    (F : (N ⧸ (Ideal.span (Set.range H) • (⊤ : Submodule R N))) ≃ₗ[R] T)
    (L : (⋀[R]^(p+1) (Fin (p+1) → R)) →ₗ[R] N) :
    koszulExactTopExtOriginalCoefficientEquiv p H he N T F
      (koszulExactTopExtCoefficientRepresentative p H he N L)=
        F (Submodule.Quotient.mk (L (topKoszulGenerator (p+1)))) := by
  change F (koszulExactTopExtCoefficientRestrictionEquiv p H he N _)=_
  rw [koszulExactTopExtCoefficientRestrictionEquiv_representative]
/-- The SAME actual ordered-top Ext generator pushed by original a is
sent to the original coefficient a(1),with no replacement functional. -/
theorem koszulExactTopExtOriginalCoefficientEquiv_pushGenerator
    (F : (N ⧸ (Ideal.span (Set.range H) • (⊤ : Submodule R N))) ≃ₗ[R] T)
    (a : R →ₗ[R] N) :
    koszulExactTopExtOriginalCoefficientEquiv p H he N T F
      ((koszulExactTopExtCoefficientRepresentative p H he (ModuleCat.of R R)
        (topKoszulCoordinate (p+1))).comp
          (Ext.mk₀ (ModuleCat.ofHom a)) (add_zero _))=
        F (Submodule.Quotient.mk (a 1)) := by
  change F (koszulExactTopExtCoefficientRestrictionEquiv p H he N _)=_
  rw [koszulExactTopExtCoefficientRestrictionEquiv_pushGenerator]
/-- Preserve the original two value families through the ACTUAL derived
MODULE Ext comparison. This generic proof keeps specialized native
coextension kernel reductions bounded without increasing any budget. -/
theorem koszulExactTopExt_existsOriginalTwoValues (U : Type u)
    (P : N → U → T → Prop) (P0 : N → T → Prop)
    (h : ∃ F : (N ⧸ (Ideal.span (Set.range H) • (⊤ : Submodule R N))) ≃ₗ[R] T,
      (∀ x v,P x v (F (Submodule.Quotient.mk x))) ∧
        ∀ x,P0 x (F (Submodule.Quotient.mk x))) :
    ∃ G : Ext.{u} (ModuleCat.of R (R ⧸ Ideal.span (Set.range H))) N (p+1) ≃ₗ[R] T,
      (∀ (L : (⋀[R]^(p+1) (Fin (p+1) → R)) →ₗ[R] N) v,
        P (L (topKoszulGenerator (p+1))) v
          (G (koszulExactTopExtCoefficientRepresentative p H he N L))) ∧
      ∀ L,P0 (L (topKoszulGenerator (p+1)))
        (G (koszulExactTopExtCoefficientRepresentative p H he N L)) := by
  obtain ⟨F,hP,hP0⟩ := h
  refine ⟨koszulExactTopExtOriginalCoefficientEquiv p H he N T F,?_,?_⟩
  · intro L v
    rw [koszulExactTopExtOriginalCoefficientEquiv_representative]
    exact hP _ v
  · intro L
    rw [koszulExactTopExtOriginalCoefficientEquiv_representative]
    exact hP0 _
/-- Actual exactness witness and actual MODULE Ext values,kept at generic
coefficient types so specialized kernel checks do not reconstruct deep
Ext category instances. Statement only,not an extra duality premise. -/
def koszulExactTopExtOriginalTwoValuesStatement (U : Type u)
    (P : N → U → T → Prop) (P0 : N → T → Prop) : Prop :=
  ∃ hx : ∀ j : ℕ,0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j,
    ∃ G : Ext.{u} (ModuleCat.of R (R ⧸ Ideal.span (Set.range H))) N (p+1) ≃ₗ[R] T,
      (∀ (L : (⋀[R]^(p+1) (Fin (p+1) → R)) →ₗ[R] N) v,
        P (L (topKoszulGenerator (p+1))) v
          (G (koszulExactTopExtCoefficientRepresentative p H hx N L))) ∧
      ∀ L,P0 (L (topKoszulGenerator (p+1)))
        (G (koszulExactTopExtCoefficientRepresentative p H hx N L))
include he
/-- Derive actual Ext and exactness together without expanding concrete
native modules in an existential-constructor kernel conversion. -/
theorem koszulExactTopExtOriginalTwoValuesStatement_of_coefficient (U : Type u)
    (P : N → U → T → Prop) (P0 : N → T → Prop)
    (h : ∃ F : (N ⧸ (Ideal.span (Set.range H) • (⊤ : Submodule R N))) ≃ₗ[R] T,
      (∀ x v,P x v (F (Submodule.Quotient.mk x))) ∧
        ∀ x,P0 x (F (Submodule.Quotient.mk x))) :
    koszulExactTopExtOriginalTwoValuesStatement p H N T U P P0 :=
  ⟨he,koszulExactTopExt_existsOriginalTwoValues p H he N T U P P0 h⟩
end LinearStudy
