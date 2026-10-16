module
public import Linear.SchemeModuleInternalExtSourceBoundaryExact
public import Linear.SchemeModuleInternalExtSourceBoundaryNaturality
public import Linear.SchemeModuleFiniteFreeFrameInternalExt
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- The SAME actual source boundary is epi when the NEXT middle SHEAF Ext
vanishes. No desired surjectivity/cokernel property is an input. -/
theorem schemeModuleInternalExtSourceBoundary_epi
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (N : X.Modules)
    (I : InjectiveResolution N) (q : ℕ)
    (hB : IsZero (schemeModuleInternalExt S.X₂ N (q+1))) :
    Epi (schemeModuleInternalExtSourceBoundaryViaResolution S hS N I q) := by
  have hz : schemeModuleInternalExtSourceMap S.g N (q+1) = 0 := hB.eq_of_tgt _ _
  exact (schemeModuleInternalExtSourceBoundary_exact_after S hS N I q).epi_f hz

/-- Universal cokernel property of SAME actual connecting morphism. -/
def schemeModuleInternalExtSourceBoundaryIsCokernel
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (N : X.Modules)
    (I : InjectiveResolution N) (q : ℕ)
    (hB : IsZero (schemeModuleInternalExt S.X₂ N (q+1))) :
    IsColimit (CokernelCofork.ofπ
      (schemeModuleInternalExtSourceBoundaryViaResolution S hS N I q)
      (schemeModuleInternalExtSourceMap_comp_boundary S hS N I q)) := by
  letI := schemeModuleInternalExtSourceBoundary_epi S hS N I q hB
  exact (schemeModuleInternalExtSourceBoundary_exact_before S hS N I q).gIsCokernel

/-- ACTUAL higher SHEAF Ext is the cokernel of the SAME original source
map when the next middle term vanishes. This includes q=0. -/
def schemeModuleInternalExtSourceBoundaryCokernelIso
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (N : X.Modules)
    (I : InjectiveResolution N) (q : ℕ)
    (hB : IsZero (schemeModuleInternalExt S.X₂ N (q+1))) :
    cokernel (schemeModuleInternalExtSourceMap S.f N q) ≅
      schemeModuleInternalExt S.X₃ N (q+1) :=
  IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel (schemeModuleInternalExtSourceMap S.f N q))
    (schemeModuleInternalExtSourceBoundaryIsCokernel S hS N I q hB)

/-- The actual cokernel comparison retains SAME boundary,not an arbitrary iso. -/
theorem schemeModuleInternalExtSourceBoundaryCokernelIso_hom
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (N : X.Modules)
    (I : InjectiveResolution N) (q : ℕ)
    (hB : IsZero (schemeModuleInternalExt S.X₂ N (q+1))) :
    cokernel.π (schemeModuleInternalExtSourceMap S.f N q) ≫
        (schemeModuleInternalExtSourceBoundaryCokernelIso S hS N I q hB).hom =
      schemeModuleInternalExtSourceBoundaryViaResolution S hS N I q :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (cokernelIsCokernel (schemeModuleInternalExtSourceMap S.f N q))
    (schemeModuleInternalExtSourceBoundaryIsCokernel S hS N I q hB) .one

/-- SAME actual cokernel iso is independent of the coefficient resolution. -/
theorem schemeModuleInternalExtSourceBoundaryCokernelIso_independent
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (N : X.Modules)
    (I J : InjectiveResolution N) (q : ℕ)
    (hB : IsZero (schemeModuleInternalExt S.X₂ N (q+1))) :
    schemeModuleInternalExtSourceBoundaryCokernelIso S hS N I q hB =
      schemeModuleInternalExtSourceBoundaryCokernelIso S hS N J q hB := by
  apply Iso.ext
  apply (cancel_epi (cokernel.π (schemeModuleInternalExtSourceMap S.f N q))).1
  rw [schemeModuleInternalExtSourceBoundaryCokernelIso_hom,
    schemeModuleInternalExtSourceBoundaryCokernelIso_hom,
    schemeModuleInternalExtSourceBoundaryViaResolution_independent S hS N I J q]

/-- A genuine finite-free frame of the middle source DERIVES the needed
vanishing. No desired vanishing or Ext comparison is supplied. -/
def schemeModuleFiniteFreeSourceBoundaryCokernelIso
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (N : X.Modules)
    (I : InjectiveResolution N) (q : ℕ) (ι : Type u) [Finite ι]
    (e : S.X₂ ≅ SheafOfModules.free (R := X.ringCatSheaf) ι) :
    cokernel (schemeModuleInternalExtSourceMap S.f N q) ≅
      schemeModuleInternalExt S.X₃ N (q+1) :=
  schemeModuleInternalExtSourceBoundaryCokernelIso S hS N I q
    (schemeModuleFiniteFreeFrameInternalExt_succ N ι e q)

/-- The finite-free specialization still uses SAME actual source boundary. -/
theorem schemeModuleFiniteFreeSourceBoundaryCokernelIso_hom
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (N : X.Modules)
    (I : InjectiveResolution N) (q : ℕ) (ι : Type u) [Finite ι]
    (e : S.X₂ ≅ SheafOfModules.free (R := X.ringCatSheaf) ι) :
    cokernel.π (schemeModuleInternalExtSourceMap S.f N q) ≫
        (schemeModuleFiniteFreeSourceBoundaryCokernelIso S hS N I q ι e).hom =
      schemeModuleInternalExtSourceBoundaryViaResolution S hS N I q :=
  schemeModuleInternalExtSourceBoundaryCokernelIso_hom S hS N I q
    (schemeModuleFiniteFreeFrameInternalExt_succ N ι e q)

end LinearStudy
