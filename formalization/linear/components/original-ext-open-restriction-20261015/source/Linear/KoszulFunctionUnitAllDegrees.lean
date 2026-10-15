module
public import Linear.KoszulFunctionUnit
public import Linear.KoszulFunctionResolution
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
variable {R : Type*} [CommRing R]

/-- One ORIGINAL unit equation also kills DEGREE ZERO of the SAME actual
exterior Koszul complex. Reuse the existing actual H0=original ring quotient
isomorphism and prove the original equation ideal is top. -/
theorem functionKoszul_unit_exactAt_zero {r : ℕ} (H : Fin r → R)
    (i : Fin r) (hu : IsUnit (H i)) :
    (koszulComplex (Fintype.linearCombination R H)).ExactAt 0 := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have hI : Ideal.ofList (List.ofFn H) = ⊤ := by
    rw [ideal_ofFn]
    exact (Ideal.span (Set.range H)).eq_top_of_isUnit_mem (Ideal.subset_span (Set.mem_range_self i)) hu
  letI : Subsingleton (R ⧸ Ideal.ofList (List.ofFn H)) := by
    rw [hI]
    infer_instance
  have hz := ModuleCat.isZero_of_subsingleton (ModuleCat.of R (R ⧸ Ideal.ofList (List.ofFn H)))
  have h := hz.of_iso (koszulComplex.zeroHomologyOfListLinearEquiv (List.ofFn H)).toModuleIso
  letI : Subsingleton ((koszulComplex.ofList (List.ofFn H)).homology 0) :=
    ModuleCat.subsingleton_of_isZero h
  have hx := ModuleCat.isZero_of_subsingleton ((koszulComplex.ofList (List.ofFn H)).homology 0)
  simpa only [koszul_ofFn] using hx

/-- A unit among the SAME original equations gives exactness in ALL
nonnegative degrees,including H0,without a regular-sequence hypothesis. -/
theorem functionKoszul_unit_exactAt_all {r : ℕ} (H : Fin r → R)
    (i : Fin r) (hu : IsUnit (H i)) (p : ℕ) :
    (koszulComplex (Fintype.linearCombination R H)).ExactAt p := by
  cases p with
  | zero => exact functionKoszul_unit_exactAt_zero H i hu
  | succ p => exact functionKoszul_unit_exactAt H i hu (p+1) (by omega)

end LinearStudy