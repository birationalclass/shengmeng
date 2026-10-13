module
public import Linear.ModuleOrderedBaseCechExact
public import Linear.NativeProjectiveCechAffineIntersections
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {K S : Type u} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable {ι : Type u} [LinearOrder ι]
variable (a : ι → S) (ha : ∀ i, a i ∈ 𝓑 1)
variable {Y : Scheme.{u}} (π : AlgebraicGeometry.Proj 𝓑 ⟶ Y)

include ha in
/-- On the original native degree-one charts, the actual ordered Cech
functor carries any actual short exact sequence of quasicoherent modules
to a short exact sequence of complexes. Affine intersections are derived
from their homogeneous coordinate products, not assumed as certificates. -/
theorem nativeProjectiveOrderedCech_shortExact
    {T : ShortComplex (AlgebraicGeometry.Proj 𝓑).Modules} (hT : T.ShortExact)
    [T.X₁.IsQuasicoherent] [T.X₂.IsQuasicoherent] [T.X₃.IsQuasicoherent] :
    (T.map (Scheme.Modules.orderedBaseCechComplexFunctor π
      (fun i => Proj.basicOpen 𝓑 (a i)))).ShortExact :=
  hT.map_orderedBaseCechComplexFunctor_of_affine_intersections π
    (fun i => Proj.basicOpen 𝓑 (a i))
    (nativeProjective_cechIntersection_isAffine 𝓑 a ha)

include ha in
/-- The actual native Cech long exact sequence shifts the vanishing
obligation for the quotient from q to q+1 on the kernel. This is an
implication for a given sequence, not the eventual Serre vanishing theorem. -/
theorem nativeProjectiveOrderedCech_exactAt_quotient
    {T : ShortComplex (AlgebraicGeometry.Proj 𝓑).Modules} (hT : T.ShortExact)
    [T.X₁.IsQuasicoherent] [T.X₂.IsQuasicoherent] [T.X₃.IsQuasicoherent]
    (q : ℕ)
    (h₂ : (Scheme.Modules.orderedBaseCechComplex π T.X₂
      (fun i => Proj.basicOpen 𝓑 (a i))).ExactAt q)
    (h₁ : (Scheme.Modules.orderedBaseCechComplex π T.X₁
      (fun i => Proj.basicOpen 𝓑 (a i))).ExactAt (q+1)) :
    (Scheme.Modules.orderedBaseCechComplex π T.X₃
      (fun i => Proj.basicOpen 𝓑 (a i))).ExactAt q := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at h₁ h₂ ⊢
  let C := T.map (Scheme.Modules.orderedBaseCechComplexFunctor π
    (fun i => Proj.basicOpen 𝓑 (a i)))
  have hC : C.ShortExact := nativeProjectiveOrderedCech_shortExact 𝓑 a ha π hT
  exact (hC.homology_exact₃ q (q+1) (by simp [ComplexShape.up_Rel])).isZero_X₂
    (h₂.eq_of_src _ _) (h₁.eq_of_tgt _ _)

end LinearStudy
