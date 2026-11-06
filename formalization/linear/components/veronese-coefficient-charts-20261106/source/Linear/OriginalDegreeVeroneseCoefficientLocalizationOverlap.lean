module
public import Linear.OriginalDegreeVeroneseCoefficientFractionValues
public import Linear.LocalizedModuleAwayOverlapFraction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
universe u v w
variable {K : Type u} {S : Type v} {M : Type w}
variable [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (D : ℤ → Submodule K M)
variable (hD : ∀ (n : ℕ) (d : ℤ) (c : S), c ∈ B n →
  ∀ x : M, x ∈ D d → c • x ∈ D ((n : ℤ) + d))
variable (q : ℕ)
local notation "V" => originalDegreeVeroneseAlgebra B q
local notation "W" => originalDegreeVeroneseCoefficient B D hD q



/-- Restriction on an actual product chart is compatible with inclusion of
fractions whenever the numerator action and denominator powers agree. -/
theorem localizedModuleAwayOverlap_compare
    {R T X Y : Type*} [CommRing R] [CommRing T] [AddCommGroup X] [AddCommGroup Y]
    [Module R X] [Module T Y]
    (a b : R) (a' b' : T) (i : X → Y)
    (φ : LocalizedModule (Submonoid.powers a) X → LocalizedModule (Submonoid.powers a') Y)
    (ψ : LocalizedModule (Submonoid.powers (a*b)) X → LocalizedModule (Submonoid.powers (a'*b')) Y)
    (hφ : ∀ n (x : X), φ (LocalizedModule.mk x (⟨a^n,⟨n,rfl⟩⟩ : Submonoid.powers a)) =
      LocalizedModule.mk (i x) (⟨a'^n,⟨n,rfl⟩⟩ : Submonoid.powers a'))
    (hψ : ∀ n (x : X), ψ (LocalizedModule.mk x (⟨(a*b)^n,⟨n,rfl⟩⟩ : Submonoid.powers (a*b))) =
      LocalizedModule.mk (i x) (⟨(a'*b')^n,⟨n,rfl⟩⟩ : Submonoid.powers (a'*b')))
    (hi : ∀ n (x : X), i (b^n • x) = b'^n • i x)
    (z : LocalizedModule (Submonoid.powers a) X) :
    ψ (originalLocalizedModuleAwayOverlap a b z) =
      originalLocalizedModuleAwayOverlap a' b' (φ z) := by
  induction z using LocalizedModule.induction_on with
  | _ x s =>
    obtain ⟨n, hn⟩ := s.property
    have hs : s = (⟨a^n,⟨n,rfl⟩⟩ : Submonoid.powers a) := Subtype.ext hn.symm
    subst s
    rw [originalLocalizedModuleAwayOverlap_mk, hφ, hψ,
      originalLocalizedModuleAwayOverlap_mk, hi]

/-- Inclusion commutes with the actual product-chart restriction on all
localized coefficients, using the same denominator powers. -/
def originalDegreeVeroneseCoefficientLocalization_overlap (f g : V) :=
  @localizedModuleAwayOverlap_compare V S W M
    (inferInstanceAs (CommRing V)) (inferInstanceAs (CommRing S))
    (inferInstanceAs (AddCommGroup W)) (inferInstanceAs (AddCommGroup M))
    (Submodule.module W) (inferInstanceAs (Module S M))
    f g (f : S) (g : S) (fun a : W => (a : M))
    (originalDegreeVeroneseCoefficientLocalization B D hD q f)
    (originalDegreeVeroneseCoefficientLocalization B D hD q (f*g))
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl)

end LinearStudy
#check LinearStudy.originalDegreeVeroneseCoefficientLocalization_overlap
#print axioms LinearStudy.originalDegreeVeroneseCoefficientLocalization_overlap

