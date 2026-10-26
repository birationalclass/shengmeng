module
public import Linear.NativeLocalizedUpperAlgebra
public import Linear.Vendor.CM.CohenMacaulayBasic
public import Mathlib.RingTheory.Localization.LocalizationLocalization
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (P : Submonoid R)
/-- The ACTUAL source localized along the base,then at an actual source
prime,has the ORIGINAL source local ring. No replacement source/action. -/
def nativeLocalizedSourcePointEquiv
    (p : Ideal (LocalizedModule P S)) [p.IsPrime] :
    Localization.AtPrime (p.comap (LocalizedModule.numeratorRingHom (S:=P) (A:=S))) ≃+*
      Localization.AtPrime p := by
  let A := LocalizedModule P S
  letI : Algebra S A := nativeLocalizedUpperAlgebra (S:=S) P
  letI : IsLocalization (Algebra.algebraMapSubmonoid S P) A :=
    nativeLocalizedUpperAlgebra_isLocalization (S:=S) P
  let L := Localization.AtPrime p
  letI : IsLocalization.AtPrime L (p.comap (algebraMap S A)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid S P) L p
  exact (IsLocalization.algEquiv (p.comap (algebraMap S A)).primeCompl
    (Localization.AtPrime (p.comap (algebraMap S A))) L).toRingEquiv
/-- The actual point comparison preserves EVERY original source numerator. -/
theorem nativeLocalizedSourcePointEquiv_numerator
    (p : Ideal (LocalizedModule P S)) [p.IsPrime] (a : S) :
    nativeLocalizedSourcePointEquiv P p
      (algebraMap S (Localization.AtPrime
        (p.comap (LocalizedModule.numeratorRingHom (S:=P) (A:=S)))) a)=
      algebraMap (LocalizedModule P S) (Localization.AtPrime p)
        (LocalizedModule.numeratorRingHom (S:=P) (A:=S) a) := by
  let A := LocalizedModule P S
  letI : Algebra S A := nativeLocalizedUpperAlgebra (S:=S) P
  letI : IsLocalization (Algebra.algebraMapSubmonoid S P) A :=
    nativeLocalizedUpperAlgebra_isLocalization (S:=S) P
  let L := Localization.AtPrime p
  letI : IsLocalization.AtPrime L (p.comap (algebraMap S A)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid S P) L p
  exact (IsLocalization.algEquiv (p.comap (algebraMap S A)).primeCompl
    (Localization.AtPrime (p.comap (algebraMap S A))) L).commutes a
/-- Krull dimension is preserved by the actual ORIGINAL point comparison. -/
theorem nativeLocalizedSourcePoint_ringKrullDim
    (p : Ideal (LocalizedModule P S)) [p.IsPrime] :
    ringKrullDim (Localization.AtPrime p)=ringKrullDim (Localization.AtPrime
      (p.comap (LocalizedModule.numeratorRingHom (S:=P) (A:=S)))) :=
  (nativeLocalizedSourcePointEquiv P p).ringKrullDim.symm
/-- LOCAL CM at the corresponding ORIGINAL source point transfers to the
actual localized source point. No global CM assumption. -/
theorem nativeLocalizedSourcePoint_localCM [IsNoetherianRing S]
    (p : Ideal (LocalizedModule P S)) [p.IsPrime]
    [IsCohenMacaulayLocalRing (Localization.AtPrime
      (p.comap (LocalizedModule.numeratorRingHom (S:=P) (A:=S))))] :
    IsCohenMacaulayLocalRing (Localization.AtPrime p) :=
  isCohenMacaulayLocalRing_of_ringEquiv (nativeLocalizedSourcePointEquiv P p)
end LinearStudy
