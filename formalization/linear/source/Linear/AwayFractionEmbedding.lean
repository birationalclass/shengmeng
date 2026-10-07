module
public import Linear.GenericUnramifiedOpen
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
variable {K B : Type*} [Field K] [CommRing B] [IsDomain B] [Algebra K B]

def awayFractionEmbedding (a : B) (ha : a ≠ 0) :
    Localization.Away a →ₐ[K] FractionRing B :=
  IsLocalization.Away.liftAlgHom a
    (f := IsScalarTower.toAlgHom K B (FractionRing B))
    (isUnit_iff_ne_zero.mpr (fun hz => ha (IsFractionRing.injective B (FractionRing B)
      (by simpa using hz))))

theorem awayFractionEmbedding_algebraMap (a : B) (ha : a ≠ 0) (b : B) :
    awayFractionEmbedding (K := K) a ha (algebraMap B (Localization.Away a) b) =
      algebraMap B (FractionRing B) b := by
  simp [awayFractionEmbedding]

theorem awayFractionEmbedding_injective (a : B) (ha : a ≠ 0) :
    Function.Injective (awayFractionEmbedding (K := K) a ha) := by
  apply IsLocalization.injective_of_map_algebraMap_zero (M := Submonoid.powers a) (Localization.Away a)
    (awayFractionEmbedding (K := K) a ha).toRingHom
  intro b hb
  change awayFractionEmbedding (K := K) a ha (algebraMap B (Localization.Away a) b) = 0 at hb
  rw [awayFractionEmbedding_algebraMap] at hb
  have hz : b = 0 := IsFractionRing.injective B (FractionRing B) (by simpa using hb)
  simp [hz]

theorem awayFractionEmbedding_invSelf (a : B) (ha : a ≠ 0) :
    awayFractionEmbedding (K := K) a ha (IsLocalization.Away.invSelf a) =
      (algebraMap B (FractionRing B) a)⁻¹ := by
  have hn : algebraMap B (FractionRing B) a ≠ 0 :=
    fun hz => ha (IsFractionRing.injective B (FractionRing B) (by simpa using hz))
  apply mul_left_cancel₀ hn
  rw [mul_inv_cancel₀ hn]
  have h := congrArg (awayFractionEmbedding (K := K) a ha)
    (IsLocalization.Away.mul_invSelf (S := Localization.Away a) a)
  simpa only [map_mul, map_one, awayFractionEmbedding_algebraMap] using h

end LinearStudy
