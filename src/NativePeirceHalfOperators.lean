/- SPDX-License-Identifier: Apache-2.0 -/
module

public import PeirceHalfOperators
public import NativeJordanQuadratic
public import NativeAtomReflections
public import NativeMatrixTrace

/-! Exact native bindings for the algebraic zero/half Peirce action. All
products remain the literal compact Albert product, with no new carrier ring. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.NativeAnalysis

def nativeMultiplicationOperator (p : Albert) : Module.End ℝ Albert where
  toFun := jordanMul p
  map_add' := jordanMul_add_right p
  map_smul' := fun r x => jordanMul_smul_right r p x

theorem native_peirceZero_commute (p x z : Albert)
    (hp : jordanMul p p = p) (hx : jordanMul p x = 0) :
    jordanMul p (jordanMul x z) = jordanMul x (jordanMul p z) := by
  have hp' : NativeJordanElement.mk p * NativeJordanElement.mk p = NativeJordanElement.mk p := by
    apply nativeJordanEquiv.injective
    exact hp
  have hx' : NativeJordanElement.mk p * NativeJordanElement.mk x = 0 := by
    apply nativeJordanEquiv.injective
    exact hx
  exact congrArg NativeJordanElement.value
    (RealJordan.idempotent_mul_zero_commute (NativeJordanElement.mk p)
      (NativeJordanElement.mk x) (NativeJordanElement.mk z) hp' hx')

theorem native_peirceHalf_product (p x h : Albert) (hp : jordanMul p p = p)
    (hx : jordanMul p x = 0) (hh : jordanMul p h = (1 / 2 : ℝ) • h) :
    jordanMul p (jordanMul x h) = (1 / 2 : ℝ) • jordanMul x h := by
  rw [native_peirceZero_commute p x h hp hx, hh, jordanMul_smul_right]

theorem native_peirceHalf_square_action (p x h : Albert) (hp : jordanMul p p = p)
    (hx : jordanMul p x = 0) (hh : jordanMul p h = (1 / 2 : ℝ) • h) :
    jordanMul (jordanMul x x) h = (2 : ℝ) • jordanMul x (jordanMul x h) := by
  have hp' : NativeJordanElement.mk p * NativeJordanElement.mk p = NativeJordanElement.mk p := by
    apply nativeJordanEquiv.injective
    exact hp
  have hx' : NativeJordanElement.mk p * NativeJordanElement.mk x = 0 := by
    apply nativeJordanEquiv.injective
    exact hx
  have hh' : NativeJordanElement.mk p * NativeJordanElement.mk h =
      (1 / 2 : ℝ) • NativeJordanElement.mk h := by
    apply nativeJordanEquiv.injective
    exact hh
  exact congrArg NativeJordanElement.value
    (RealJordan.peirceHalf_square_action (NativeJordanElement.mk p)
      (NativeJordanElement.mk x) (NativeJordanElement.mk h) hp' hx' hh')

theorem native_peirceHalf_jordan_action (p x y h : Albert) (hp : jordanMul p p = p)
    (hx : jordanMul p x = 0) (hy : jordanMul p y = 0)
    (hh : jordanMul p h = (1 / 2 : ℝ) • h) :
    jordanMul (jordanMul x y) h = jordanMul x (jordanMul y h) + jordanMul y (jordanMul x h) := by
  have hp' : NativeJordanElement.mk p * NativeJordanElement.mk p = NativeJordanElement.mk p := by
    apply nativeJordanEquiv.injective
    exact hp
  have hx' : NativeJordanElement.mk p * NativeJordanElement.mk x = 0 := by
    apply nativeJordanEquiv.injective
    exact hx
  have hy' : NativeJordanElement.mk p * NativeJordanElement.mk y = 0 := by
    apply nativeJordanEquiv.injective
    exact hy
  have hh' : NativeJordanElement.mk p * NativeJordanElement.mk h =
      (1 / 2 : ℝ) • NativeJordanElement.mk h := by
    apply nativeJordanEquiv.injective
    exact hh
  exact congrArg NativeJordanElement.value
    (RealJordan.peirceHalf_jordan_action (NativeJordanElement.mk p)
      (NativeJordanElement.mk x) (NativeJordanElement.mk y) (NativeJordanElement.mk h)
      hp' hx' hy' hh')

def nativePolarizedQuadratic (a b : Albert) : Module.End ℝ Albert :=
  quadraticMapLinear (a + b) - quadraticMapLinear a - quadraticMapLinear b

theorem nativePolarizedQuadratic_apply (a b x : Albert) :
    nativePolarizedQuadratic a b x =
      (2 : ℝ) • (jordanMul a (jordanMul b x) + jordanMul b (jordanMul a x) - jordanMul (jordanMul a b) x) := by
  simp only [nativePolarizedQuadratic, LinearMap.sub_apply]
  change quadraticMap (a + b) x - quadraticMap a x - quadraticMap b x = _
  unfold quadraticMap
  simp only [jordanMul_add_left, jordanMul_add_right, jordanMul_comm b a]
  module

theorem nativePolarizedQuadratic_fundamental (a b c : Albert) :
    nativePolarizedQuadratic (quadraticMap a b) (quadraticMap a c) =
      (quadraticMapLinear a).comp ((nativePolarizedQuadratic b c).comp (quadraticMapLinear a)) := by
  ext x
  change quadraticMap (quadraticMap a b + quadraticMap a c) x -
      quadraticMap (quadraticMap a b) x - quadraticMap (quadraticMap a c) x =
    quadraticMap a (quadraticMap (b + c) (quadraticMap a x) -
      quadraticMap b (quadraticMap a x) - quadraticMap c (quadraticMap a x))
  rw [← quadraticMap_add_right, quadraticMap_fundamental, quadraticMap_fundamental,
    quadraticMap_fundamental]
  exact (map_sub (quadraticMapLinear a) _ _).trans
    (congrArg (fun y => y - quadraticMap a (quadraticMap c (quadraticMap a x)))
      (map_sub (quadraticMapLinear a) _ _)) |>.symm

end AlbertSequential.NativeAnalysis
