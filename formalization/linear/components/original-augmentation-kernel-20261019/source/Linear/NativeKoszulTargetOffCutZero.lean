module
public import Linear.NativeKoszulOffCutCokernelZero
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
attribute [local irreducible] nativeProjectiveKoszulComplex nativeProjectiveKoszulTerm
/-- The SAME actual target of the original d1-cokernel vanishes on ANY
actual open where an ORIGINAL equation is invertible. No main chart,
Ext sheaf or adjunction unit is compared in this theorem. -/
theorem nativeProjectiveKoszul_target_openRestriction_isZero_offCut
    {J : Type} (b : J → S) (hb : ∀ t,b t ∈ B 1)
    (hgen : Algebra.adjoin K (Set.range b) = ⊤)
    {r q : ℕ} (H : Fin r → S) (hH : ∀ i,H i ∈ B q) (i : Fin r) (k : ℤ)
    (E : (Proj B).Modules)
    (e : cokernel ((nativeProjectiveKoszulComplex B H hH k).d 1 0) ≅ E)
    {Y : Scheme} (j : Y ⟶ Proj B) [IsOpenImmersion j]
    (hj : ∀ x : Y,j x ∈ Proj.basicOpen B (H i)) :
    IsZero (E.restrict j) := by
  have hz := nativeProjectiveKoszul_cokernel_openRestriction_isZero_offCut
    B b hb hgen H hH i k j hj
  exact hz.of_iso ((Scheme.Modules.restrictFunctor j).mapIso e).symm
end LinearStudy
