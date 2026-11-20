/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeCornerSpectralCoordinates
import Mathlib.Tactic.Module

/-! The one- and two-reflection formulas in the actual native Clifford action. -/
@[expose] public section
noncomputable section

open scoped Matrix

namespace AlbertSequential.NativeAnalysis

/-- The mixed product of traceless corner elements is their spin pairing times the corner unit. -/
theorem nativeCorner_traceless_product (p : Albert) (hp : IsAtom p)
    (x y : nativePeirceZero p) (hx : albertTrace x = 0) (hy : albertTrace y = 0) :
    nativeCornerProduct p hp.1 x y = (tracePairing x y / 2) • nativeCornerUnit p hp.1 := by
  apply Subtype.ext
  let a : Albert := x
  let b : Albert := y
  let u : Albert := nativeCornerUnit p hp.1
  change jordanMul a b = (tracePairing a b / 2) • u
  have hsum : albertTrace (x+y : nativePeirceZero p) = 0 := by
    change albertTrace (a+b) = 0
    rw [albertTrace_add, hx, hy, zero_add]
  have hab := nativeCorner_traceless_square p hp (x+y) hsum
  change jordanMul (a+b) (a+b) = (tracePairing (a+b) (a+b) / 2) • u at hab
  have haa := nativeCorner_traceless_square p hp x hx
  have hbb := nativeCorner_traceless_square p hp y hy
  change jordanMul a a = (tracePairing a a / 2) • u at haa
  change jordanMul b b = (tracePairing b b / 2) • u at hbb
  have hd : (2 : ℝ) • jordanMul a b = tracePairing a b • u := by
    calc
      _ = jordanMul (a+b) (a+b) - jordanMul a a - jordanMul b b := by
        rw [jordanMul_add_left, jordanMul_add_right, jordanMul_add_right, jordanMul_comm b a]
        module
      _ = _ := by
        rw [hab, haa, hbb, tracePairing_add_left, tracePairing_add_right, tracePairing_add_right,
          tracePairing_comm b a]
        module
  calc
    jordanMul a b = (1/2 : ℝ) • ((2 : ℝ) • jordanMul a b) := by module
    _ = _ := by rw [hd]; module

/-- The Clifford anticommutator uses twice the Euclidean pairing on the
traceless spin space. -/
theorem nativeHalfMatrix_traceless_anticommutator (p : Albert) (hp : IsAtom p)
    (v w : nativePeirceZero p) (hv : albertTrace v = 0) (hw : albertTrace w = 0) :
    nativeHalfMatrix p hp v * nativeHalfMatrix p hp w + nativeHalfMatrix p hp w * nativeHalfMatrix p hp v =
      tracePairing v w • (1 : NativeSpinorMatrix) := by
  let V := nativeHalfMatrix p hp v
  let W := nativeHalfMatrix p hp w
  have h := nativeHalfMatrix_jordan p hp v w
  rw [nativeCorner_traceless_product p hp v w hv hw, map_smul, nativeHalfMatrix_unit] at h
  change (tracePairing v w / 2) • (1 : NativeSpinorMatrix) = (1/2 : ℝ) • (V*W + W*V) at h
  change V*W + W*V = _
  calc
    _ = (2 : ℝ) • ((1/2 : ℝ) • (V*W+W*V)) := by module
    _ = _ := by rw [← h]; module

/-- A unit normal gives the printed `Ψ(v) Ψ(x) Ψ(v) = −Ψ(R_v x)` on traceless inputs. -/
theorem nativeHalfMatrix_traceless_reflection (p : Albert) (hp : IsAtom p)
    (v w : nativePeirceZero p) (hv : albertTrace v = 0) (hw : albertTrace w = 0)
    (hunit : tracePairing v v = 2) :
    nativeHalfMatrix p hp v * nativeHalfMatrix p hp w * nativeHalfMatrix p hp v =
      -nativeHalfMatrix p hp (w - tracePairing v w • v) := by
  let V := nativeHalfMatrix p hp v
  let W := nativeHalfMatrix p hp w
  have hV : V * V = 1 := by
    change nativeHalfMatrix p hp v * nativeHalfMatrix p hp v = 1
    rw [← nativeHalfMatrix_square, nativeCorner_traceless_product p hp v v hv hv, hunit,
      div_self (by norm_num : (2:ℝ) ≠ 0), one_smul, nativeHalfMatrix_unit]
  have hsum := nativeHalfMatrix_traceless_anticommutator p hp v w hv hw
  change V*W + W*V = _ at hsum
  have h := congrArg (fun X : NativeSpinorMatrix => X * V) hsum
  change (V*W + W*V) * V = (tracePairing v w • (1 : NativeSpinorMatrix)) * V at h
  rw [Matrix.add_mul, Matrix.mul_assoc W, hV, Matrix.mul_one, smul_mul_assoc, Matrix.one_mul] at h
  change V*W*V = _
  rw [map_sub, map_smul]
  change V*W*V = -(W - tracePairing v w • V)
  rw [← h]
  abel

/-- The hyperplane reflection in the printed Euclidean normalization. -/
def nativeCornerSpatialReflection (p : Albert) (v x : nativePeirceZero p) : nativePeirceZero p :=
  x - tracePairing v x • v

private theorem nativeCornerSpatialReflection_trace (p : Albert) (v x : nativePeirceZero p)
    (hv : albertTrace v = 0) : albertTrace (nativeCornerSpatialReflection p v x) = albertTrace x := by
  change albertTrace ((x : Albert) - tracePairing v x • (v : Albert)) = _
  rw [albertTrace_sub, albertTrace_smul, hv, mul_zero, sub_zero]

private theorem nativeHalfMatrix_unitNormal_square (p : Albert) (hp : IsAtom p)
    (v : nativePeirceZero p) (hv : albertTrace v = 0) (hn : tracePairing v v = 2) :
    nativeHalfMatrix p hp v * nativeHalfMatrix p hp v = 1 := by
  rw [← nativeHalfMatrix_square, nativeCorner_traceless_product p hp v v hv hv, hn,
    div_self (by norm_num : (2:ℝ) ≠ 0), one_smul, nativeHalfMatrix_unit]

/-- Two unit normals give the printed rotation on the traceless part and
leave the scalar part fixed. -/
theorem nativeHalfMatrix_two_reflections (p : Albert) (hp : IsAtom p)
    (v w x : nativePeirceZero p) (hv : albertTrace v = 0) (hw : albertTrace w = 0)
    (hx : albertTrace x = 0) (hvv : tracePairing v v = 2) (hww : tracePairing w w = 2) (t : ℝ) :
    let S := nativeHalfMatrix p hp v * nativeHalfMatrix p hp w
    let u := nativeCornerUnit p hp.1
    S * nativeHalfMatrix p hp (t • u + x) * S.transpose = nativeHalfMatrix p hp
      (t • u + nativeCornerSpatialReflection p v (nativeCornerSpatialReflection p w x)) := by
  intro S u
  let M := nativeHalfMatrix p hp
  let V := M v
  let W := M w
  have hs : S.transpose = W * V := by
    change (M v * M w).transpose = M w * M v
    rw [Matrix.transpose_mul, nativeHalfMatrix_symmetric, nativeHalfMatrix_symmetric]
  have hv2 : V * V = 1 := nativeHalfMatrix_unitNormal_square p hp v hv hvv
  have hw2 : W * W = 1 := nativeHalfMatrix_unitNormal_square p hp w hw hww
  have hso : S * S.transpose = 1 := by
    rw [hs]
    change (V*W)*(W*V) = 1
    rw [← Matrix.mul_assoc, Matrix.mul_assoc V, hw2, Matrix.mul_one, hv2]
  let r := nativeCornerSpatialReflection p w x
  let s := nativeCornerSpatialReflection p v r
  have hr := nativeHalfMatrix_traceless_reflection p hp w x hw hx hww
  have ht : albertTrace r = 0 := (nativeCornerSpatialReflection_trace p w x hw).trans hx
  have hh := nativeHalfMatrix_traceless_reflection p hp v r hv ht hvv
  have hc : S * M x * S.transpose = M s := by
    rw [hs]
    change (V*W)*M x*(W*V) = M s
    change W*M x*W = -M r at hr
    change V*M r*V = -M s at hh
    calc
      _ = V*(W*M x*W)*V := by simp only [Matrix.mul_assoc]
      _ = -(V*M r*V) := by rw [hr, Matrix.mul_neg, Matrix.neg_mul]
      _ = _ := by rw [hh, neg_neg]
  change S * M (t • u + x) * S.transpose = M (t • u + s)
  have hu : M u = 1 := nativeHalfMatrix_unit p hp
  simp only [map_add, map_smul, hu, Matrix.mul_add, Matrix.add_mul, mul_smul_comm, smul_mul_assoc,
    Matrix.mul_one, hso, hc]

end AlbertSequential.NativeAnalysis
