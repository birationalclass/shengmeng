module
public import Linear.ShortExactInjectiveExtBoundaryAllDegrees
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CochainComplex.HomComplex
universe u v w
variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]

/-- Native boundary computed from ACTUAL component morphisms, with the
positive lift equations and no extra class identity premise. -/
theorem shortExactInjectiveExtBoundary_components
    (S : ShortComplex A) (hS : S.ShortExact) {N : A} (I : InjectiveResolution N)
    (q : ℕ) (a : S.X₁ ⟶ I.cochainComplex.X (q : ℤ))
    (ha : a ≫ I.cochainComplex.d (q : ℤ) ((q : ℤ)+1) = 0)
    (b : S.X₂ ⟶ I.cochainComplex.X (q : ℤ))
    (c : S.X₃ ⟶ I.cochainComplex.X ((q+1 : ℕ) : ℤ))
    (hc : c ≫ I.cochainComplex.d ((q+1 : ℕ) : ℤ) (((q+1 : ℕ) : ℤ)+1) = 0)
    (hb : S.f ≫ b = a)
    (hbc : b ≫ I.cochainComplex.d (q : ℤ) ((q+1 : ℕ) : ℤ) = S.g ≫ c) :
    Ext.δ hS q (q+1) rfl
      (I.extEquivCohomologyClass.symm (CohomologyClass.mk
        (Cocycle.fromSingleMk a (zero_add _) ((q : ℤ)+1) rfl ha))) =
      (I.extEquivCohomologyClass (n := q+1)).symm (CohomologyClass.mk
        (Cocycle.fromSingleMk c (zero_add _) (((q+1 : ℕ) : ℤ)+1) rfl hc)) := by
  apply shortExactInjectiveExtBoundary_allDegrees S hS I q _
    (Cochain.fromSingleMk b (zero_add _)) _
  · change (Cochain.ofHom _).comp (Cochain.fromSingleMk b (zero_add _)) _ =
      Cochain.fromSingleMk a (zero_add _)
    rw [← Cochain.fromSingleMk_precomp,hb]
  · change δ _ _ (Cochain.fromSingleMk b (zero_add _)) =
      (Cochain.ofHom _).comp (Cochain.fromSingleMk c (zero_add _)) _
    rw [Cochain.δ_fromSingleMk _ _ _ ((q+1 : ℕ) : ℤ) (zero_add _),hbc,
      Cochain.fromSingleMk_precomp]

end LinearStudy
