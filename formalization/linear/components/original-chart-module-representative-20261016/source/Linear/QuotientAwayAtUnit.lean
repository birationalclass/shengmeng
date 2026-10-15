module
public import Linear.AwayQuotientComparison
public import Mathlib.RingTheory.Ideal.Quotient.Operations
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
variable {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]

/-- Removing a denominator which is already a unit in the ACTUAL cut
quotient preserves that quotient as an algebra, including its nilpotents. -/
theorem quotientAwayAtUnit_exists_algEquiv
    (I J : Ideal R) (p : R) (hp : IsUnit (Ideal.Quotient.mk (I ⊔ J) p)) :
    Nonempty ((R ⧸ I ⊔ J) ≃ₐ[K]
      (Localization.Away (Ideal.Quotient.mk I p) ⧸
        (J.map (Ideal.Quotient.mk I)).map
          (algebraMap (R ⧸ I) (Localization.Away (Ideal.Quotient.mk I p))))) := by
  let Jb := J.map (Ideal.Quotient.mk I)
  let Cb := (R ⧸ I) ⧸ Jb
  let a : R ⧸ I := Ideal.Quotient.mk I p
  let b : Cb := Ideal.Quotient.mk Jb a
  let e := DoubleQuot.quotQuotEquivQuotSupₐ K I J
  have he : e b=Ideal.Quotient.mk (I ⊔ J) p :=
    DoubleQuot.quotQuotEquivQuotSup_quotQuotMk I J p
  have hb : IsUnit b := by
    have hh := hp.map e.symm.toRingHom
    rw [← he] at hh
    change IsUnit (e.symm (e b)) at hh
    exact (e.symm_apply_apply b) ▸ hh
  let eu := (IsLocalization.atUnit Cb (Localization.Away b) b hb).restrictScalars K
  exact ⟨(e.symm.trans eu).trans
    (awayQuotientBaseEquiv (K := K) Jb a).symm⟩

end LinearStudy
