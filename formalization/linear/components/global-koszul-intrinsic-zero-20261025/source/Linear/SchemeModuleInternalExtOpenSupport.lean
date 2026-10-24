module
public import Linear.SchemeModuleHomZeroSourceSupport
public import Linear.SchemeModuleInjectiveInternalHomCycles
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
/-- ACTUAL derived SHEAF Ext vanishes on ANY original open where its
ACTUAL original source vanishes,for ALL coefficients and ALL degrees.
Use actual injective Hom cycles,proved local Hom support and the actual
epi onto homology;no quasicoherence,projectivity or exactness certificate. -/
theorem schemeModuleInternalExt_open_isZero_of_source
    {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (P N : X.Modules) (hP : IsZero (P.restrict j)) (q : ℕ) :
    IsZero ((schemeModuleInternalExt P N q).restrict j) := by
  let I := injectiveResolution N
  let K := schemeModuleInjectiveInternalHomComplex I P
  have hc : IsZero ((K.cycles q).restrict j) :=
    schemeModuleSubHom_open_isZero_of_source j P (I.cocomplex.X q)
      (K.cycles q) (K.iCycles q) hP
  have hh : IsZero ((K.homology q).restrict j) :=
    IsZero.of_epi ((Scheme.Modules.restrictFunctor j).map (K.homologyπ q)) hc
  exact hh.of_iso ((Scheme.Modules.restrictFunctor j).mapIso
    (schemeModuleInternalExtInjectiveResolutionIso P N q I))
end LinearStudy
