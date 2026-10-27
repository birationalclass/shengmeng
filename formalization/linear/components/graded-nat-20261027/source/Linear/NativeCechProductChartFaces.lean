module
public import Linear.OrderedCechDeleteValue
public import Linear.NativeFiniteGradedSourceAmbientCechFaces
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
universe u
variable {K R S ι : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [LinearOrder ι]
variable (A : ℕ → Submodule K R) [GradedAlgebra A]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
/-- The actual original coordinate-product open,with no module data. -/
def nativeCechProductOpen (a : ι → R) (p : ℕ) (t : OrderedCechIndex ι p) : (Proj A).Opens :=
  Proj.basicOpen A (∏ j : Fin (p+1),a (t.1 j))
/-- The actual original source image-product open. -/
def nativeBaseSourceCechProductOpen (a : ι → R) (p : ℕ) (t : OrderedCechIndex ι p) : (Proj B).Opens :=
  Proj.basicOpen B (algebraMap R S (∏ j : Fin (p+1),a (t.1 j)))
/-- The original inclusion of product opens after deleting one coordinate. -/
def nativeCechProductFace (a : ι → R) (p : ℕ) (k : Fin (p+2)) (t : OrderedCechIndex ι (p+1)) :
    nativeCechProductOpen A a (p+1) t ⟶ nativeCechProductOpen A a p (t.delete k) := homOfLE (by
  dsimp only [nativeCechProductOpen]
  rw [orderedCechIndex_delete_values,nativeCechCoordinateProduct_delete_mul a p t.1 k]
  exact ProjectiveSpectrum.basicOpen_mul_le_left A _ _)
/-- The same original inclusion on source image-product opens. -/
def nativeBaseSourceCechProductFace (a : ι → R) (p : ℕ) (k : Fin (p+2)) (t : OrderedCechIndex ι (p+1)) :
    nativeBaseSourceCechProductOpen B a (p+1) t ⟶ nativeBaseSourceCechProductOpen B a p (t.delete k) := homOfLE (by
  dsimp only [nativeBaseSourceCechProductOpen]
  rw [orderedCechIndex_delete_values,nativeCechCoordinateProduct_delete_mul a p t.1 k,map_mul]
  exact ProjectiveSpectrum.basicOpen_mul_le_left B _ _)
end LinearStudy
