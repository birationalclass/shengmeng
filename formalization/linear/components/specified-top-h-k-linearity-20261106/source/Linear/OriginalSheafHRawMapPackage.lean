module
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian
universe w' w v u

/-- Package the exact native H group and its additive H.map together. -/
def originalSheafHRawMapPackage
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (s : HasSheafify J AddCommGrpCat.{w})
    (e : HasExt.{w'} (Sheaf J AddCommGrpCat.{w}))
    {F : Sheaf J AddCommGrpCat.{w}} (f : F ⟶ F) (n : ℕ) :
    Σ A : AddCommGrpCat.{w'}, A ⟶ A :=
  letI : HasSheafify J AddCommGrpCat.{w} := s
  letI : HasExt.{w'} (Sheaf J AddCommGrpCat.{w}) := e
  ⟨AddCommGrpCat.of (Sheaf.H.{w'} F n),
    AddCommGrpCat.ofHom (Sheaf.H.map.{w'} f n)⟩

/-- Equality of packages identifies their endomorphisms. -/
theorem originalSheafHRawMapPackage_snd_heq
    {P Q : Σ A : AddCommGrpCat.{w'}, A ⟶ A} (h : P = Q) :
    HEq P.2 Q.2 := by
  cases h
  rfl

end LinearStudy
#check LinearStudy.originalSheafHRawMapPackage
#print LinearStudy.originalSheafHRawMapPackage
#print axioms LinearStudy.originalSheafHRawMapPackage
#check LinearStudy.originalSheafHRawMapPackage_snd_heq
#print axioms LinearStudy.originalSheafHRawMapPackage_snd_heq
