module
public import Linear.MappedChainPresentationNamedExt
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
universe v u v' u'
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {B : Type u'} [Category.{v'} B] [Abelian B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesHomology]

/-- Explicit named-original comparison STATEMENT using the constructed
standard Ext and derived categories at an abstract boundary. -/
def standardMappedChainPresentationNamedExtLaw
    (p : mappedChainPresentationData F) (C : ChainComplex A ℕ) (hC : p.1 = C)
    (T : A) (e : cokernel (C.d 1 0) ≅ T) : Prop :=
  letI := HasExt.standard A
  letI := HasDerivedCategory.standard A
  letI := HasExt.standard B
  letI := HasDerivedCategory.standard B
  mappedChainPresentationNamedExtLaw F p C hC T e

/-- Construct all standard categorical prerequisites and PROVE the
actual named-original comparison,no new geometric premises. -/
theorem standardMappedChainPresentationNamedExtLaw_proof
    (p : mappedChainPresentationData F) (C : ChainComplex A ℕ) (hC : p.1 = C)
    (T : A) (e : cokernel (C.d 1 0) ≅ T) :
    standardMappedChainPresentationNamedExtLaw F p C hC T e := by
  letI := HasExt.standard A
  letI := HasDerivedCategory.standard A
  letI := HasExt.standard B
  letI := HasDerivedCategory.standard B
  exact mappedChainPresentationNamedExtLaw_proof F p C hC T e

end LinearStudy
