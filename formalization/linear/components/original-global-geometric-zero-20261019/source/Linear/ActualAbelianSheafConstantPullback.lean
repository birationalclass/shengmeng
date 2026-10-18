module
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.CategoryTheory.Adjunction.Unique
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u

/-- ACTUAL abelian-sheaf direct image followed by ORIGINAL global sections
is the SAME original global-section functor on the source;preimage of the
whole space is definitionally the whole source. -/
def actualAbelianSheaf_pushforwardGlobalSectionsIso
    {X Y : TopCat.{u}} (f : X ⟶ Y) :
    TopCat.Sheaf.pushforward AddCommGrpCat.{u} f ⋙
        (sheafSections (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj (op ⊤) ≅
      (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op ⊤) :=
  Iso.refl _

/-- Construct the ACTUAL inverse-image/constant-sheaf comparison through
native left-adjoint uniqueness and the SAME original global-section identity.
This is a proved isomorphism,not a constant-preservation certificate. -/
def actualAbelianSheaf_pullbackConstantIso
    {X Y : TopCat.{u}} (f : X ⟶ Y) :
    constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} ⋙
        TopCat.Sheaf.pullback AddCommGrpCat.{u} f ≅
      constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (Adjunction.ofNatIsoRight
    ((constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{u} isTerminalTop).comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f))
    (actualAbelianSheaf_pushforwardGlobalSectionsIso f)).leftAdjointUniq
      (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop)

end LinearStudy
