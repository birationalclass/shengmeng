module
public import Linear.AffineTildeFinitePresentationHomIso
public import Linear.KoszulTop
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u

/-- EVERY ORIGINAL finite-rank exterior Koszul term is finitely presented
over ANY original commutative ring. The original exterior basis supplies
finite/projective instances;no Noetherian or FP certificate assumed. -/
theorem affineKoszulTerm_finitePresentation (R : CommRingCat.{u}) (r j : ℕ) :
    Module.FinitePresentation R (⋀[R]^j (Fin r → R)) := by
  let b := (Pi.basisFun R (Fin r)).exteriorPower j
  letI := Module.Free.of_basis b
  letI := Module.Finite.of_basis b
  exact Module.finitePresentation_of_projective R (⋀[R]^j (Fin r → R))

/-- Apply the ACTUAL proved affine internal-Hom identification to
EVERY ORIGINAL exterior Koszul term and the ACTUAL structure unit.
The source FP condition is PROVED above;the original module/sheaf
objects are retained. Differential and global gluing are separate. -/
def affineKoszulTermInternalDualHomIso (R : CommRingCat.{u}) (r j : ℕ) :
    tilde (ModuleCat.of R (Module.Dual R (⋀[R]^j (Fin r → R)))) ≅
      schemeModuleHomModuleSheaf (tilde (ModuleCat.of R (⋀[R]^j (Fin r → R))))
        (SheafOfModules.unit.{u} (Spec R).ringCatSheaf) := by
  letI := affineKoszulTerm_finitePresentation R r j
  exact affineTildeFinitePresentationHomIso R (ModuleCat.of R (⋀[R]^j (Fin r → R))) (ModuleCat.of R R)

end LinearStudy
