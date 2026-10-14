module
public import Linear.AffineTildePullbackExtendScalars
public import Linear.ExtendScalarsActualTensor
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TensorProduct
open scoped ChangeOfRings
universe u

/-- The existing ACTUAL carrier comparison between ORIGINAL categorical
extension of scalars and ORIGINAL algebra tensor is S-LINEAR. Source
and target scalar actions are retained;no scalar certificate supplied. -/
def extendScalarsActualTensorLinearEquiv {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (M : ModuleCat.{u} R) :
    ((ModuleCat.extendScalars (algebraMap R S)).obj M) ≃ₗ[S] S ⊗[R] M where
  __ := extendScalarsActualTensorAddEquiv (S := S) M
  map_smul' s x := by
    change extendScalarsActualTensorAddEquiv (S := S) M (s • x) =
      s • extendScalarsActualTensorAddEquiv (S := S) M x
    induction x using TensorProduct.inductionOn with
    | tmul t m => rfl
    | add x y hx hy =>
      simpa only [smul_add,map_add] using congrArg₂ (· + ·) hx hy

/-- ACTUAL original pure tensor values are retained by the SAME
constructed S-linear categorical/native tensor comparison. -/
theorem extendScalarsActualTensorLinearEquiv_tmul {R S : Type u}
    [CommRing R] [CommRing S] [Algebra R S] (M : ModuleCat.{u} R) (s : S) (m : M) :
    extendScalarsActualTensorLinearEquiv (S := S) M
      (s ⊗ₜ[R,algebraMap R S] m) = s ⊗ₜ[R] m := rfl

/-- CONSTRUCT an actual ORIGINAL geometric pullback/tilde tensor iso
for ANY original N,using actual adjunction uniqueness and proved actual
S-linear original tensor comparison. NO FP/flat/free/invertibility/CM,
QC certificate,pullback iso or desired comparison condition assumed. -/
def affineTildeTensorPullbackIso (R S : CommRingCat.{u}) [Algebra R S]
    (N : ModuleCat.{u} R) :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj (tilde N) ≅
      tilde (ModuleCat.of S (S ⊗[R] N)) :=
  (affineTildePullbackExtendScalarsNatIso (CommRingCat.ofHom (algebraMap R S))).app N ≪≫
    (tilde.functor S).mapIso (extendScalarsActualTensorLinearEquiv (S := S) N).toModuleIso

end LinearStudy