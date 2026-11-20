/- SPDX-License-Identifier: Apache-2.0 -/
module

public import FiveTest.RatAlbert
public import NativeAutomorphisms
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! The precise rational-coordinate involution in Appendix C.5. -/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace AlbertSequential.MatchingModels

open FiveTest NativeAnalysis
open scoped Quaternion

/-- Conjugation by the quaternion unit k. -/
def horizonGammaQuat (q : Quaternion ℝ) : Quaternion ℝ :=
  ⟨q.re, -q.imI, -q.imJ, q.imK⟩

theorem horizonGammaQuat_conjugation (q : Quaternion ℝ) :
    horizonGammaQuat q = (⟨0,0,0,1⟩ : Quaternion ℝ) * q *
      star (⟨0,0,0,1⟩ : Quaternion ℝ) := by
  apply Quaternion.ext <;> simp [horizonGammaQuat]

theorem horizonGammaQuat_involutive (q : Quaternion ℝ) :
    horizonGammaQuat (horizonGammaQuat q) = q := by
  apply Quaternion.ext <;> simp [horizonGammaQuat]

theorem horizonGammaQuat_add (q r : Quaternion ℝ) :
    horizonGammaQuat (q + r) = horizonGammaQuat q + horizonGammaQuat r := by
  apply Quaternion.ext <;> simp [horizonGammaQuat] <;> ring

private theorem horizonGammaQuat_sub (q r : Quaternion ℝ) :
    horizonGammaQuat (q - r) = horizonGammaQuat q - horizonGammaQuat r := by
  apply Quaternion.ext <;> simp [horizonGammaQuat] <;> ring

theorem horizonGammaQuat_smul (a : ℝ) (q : Quaternion ℝ) :
    horizonGammaQuat (a • q) = a • horizonGammaQuat q := by
  apply Quaternion.ext <;> simp [horizonGammaQuat, smul_eq_mul]

private theorem horizonGammaQuat_star (q : Quaternion ℝ) :
    horizonGammaQuat (star q) = star (horizonGammaQuat q) := by
  apply Quaternion.ext <;> simp [horizonGammaQuat]

private theorem horizonGammaQuat_mul (q r : Quaternion ℝ) :
    horizonGammaQuat (q * r) = horizonGammaQuat q * horizonGammaQuat r := by
  apply Quaternion.ext <;> simp [horizonGammaQuat] <;> ring

def horizonGammaOctEquiv : Octonion ≃ₗ[ℝ] Octonion where
  toFun x := (horizonGammaQuat x.1, horizonGammaQuat x.2)
  invFun x := (horizonGammaQuat x.1, horizonGammaQuat x.2)
  left_inv x := Prod.ext (horizonGammaQuat_involutive x.1) (horizonGammaQuat_involutive x.2)
  right_inv x := Prod.ext (horizonGammaQuat_involutive x.1) (horizonGammaQuat_involutive x.2)
  map_add' x y := Prod.ext (horizonGammaQuat_add x.1 y.1) (horizonGammaQuat_add x.2 y.2)
  map_smul' a x := Prod.ext (horizonGammaQuat_smul a x.1) (horizonGammaQuat_smul a x.2)

/-- The octonion automorphism acts separately on the two Cayley–Dickson coefficients. -/
def horizonGammaOct : OctonionAutomorphism where
  equiv := horizonGammaOctEquiv
  map_one := by
    apply Prod.ext
    · change horizonGammaQuat ⟨1,0,0,0⟩ = ⟨1,0,0,0⟩
      simp [horizonGammaQuat]
    · change horizonGammaQuat (0 : Quaternion ℝ) = 0
      apply Quaternion.ext <;> simp [horizonGammaQuat]
  map_mul x y := by
    apply Prod.ext
    · change horizonGammaQuat (x.1 * y.1 - star y.2 * x.2) =
        horizonGammaQuat x.1 * horizonGammaQuat y.1 -
          star (horizonGammaQuat y.2) * horizonGammaQuat x.2
      rw [horizonGammaQuat_sub, horizonGammaQuat_mul, horizonGammaQuat_mul, horizonGammaQuat_star]
    · change horizonGammaQuat (y.2 * x.1 + x.2 * star y.1) =
        horizonGammaQuat y.2 * horizonGammaQuat x.1 +
          horizonGammaQuat x.2 * star (horizonGammaQuat y.1)
      rw [horizonGammaQuat_add, horizonGammaQuat_mul, horizonGammaQuat_mul, horizonGammaQuat_star]

theorem horizonGammaOct_involutive (x : Octonion) :
    horizonGammaOct.equiv (horizonGammaOct.equiv x) = x :=
  horizonGammaOctEquiv.left_inv x

/-- The printed beta, conjugating the coefficientwise gamma by diag(1,−1,1). -/
def horizonRationalBeta : NativeAlbertAutomorphism :=
  nativeAutomorphismComposition
    (middleMoufangAlbertAuto (-octOne) (by rw [octNormSq_neg, octNormSq_one]))
    (octAutoToAlbertAuto horizonGammaOct)

theorem horizonRationalBeta_apply (x : Albert) :
    horizonRationalBeta.linearEquiv x =
      (x.1, ![-horizonGammaOct.equiv (x.2 0), horizonGammaOct.equiv (x.2 1),
        -horizonGammaOct.equiv (x.2 2)]) := by
  unfold horizonRationalBeta
  rw [nativeAutomorphismComposition_apply, middleMoufangAlbertAuto_apply]
  apply albert_ext'
  · rfl
  · rfl
  · rfl
  · change octonionMul (-octOne) (horizonGammaOct.equiv (x.2 0)) = _
    rw [octonionMul_neg_left, octonionMul_one_left]
    rfl
  · change octonionMul (octonionMul (-octOne) (horizonGammaOct.equiv (x.2 1))) (-octOne) = _
    rw [octonionMul_neg_left, octonionMul_one_left, octonionMul_neg_right,
      octonionMul_one_right, neg_neg]
    rfl
  · change octonionMul (horizonGammaOct.equiv (x.2 2)) (-octOne) = _
    rw [octonionMul_neg_right, octonionMul_one_right]
    rfl

theorem horizonRationalBeta_involutive (x : Albert) :
    horizonRationalBeta.linearEquiv (horizonRationalBeta.linearEquiv x) = x := by
  rw [horizonRationalBeta_apply, horizonRationalBeta_apply]
  apply albert_ext'
  · rfl
  · rfl
  · rfl
  · change -horizonGammaOct.equiv (-horizonGammaOct.equiv (x.2 0)) = x.2 0
    rw [map_neg, neg_neg, horizonGammaOct_involutive]
  · exact horizonGammaOct_involutive _
  · change -horizonGammaOct.equiv (-horizonGammaOct.equiv (x.2 2)) = x.2 2
    rw [map_neg, neg_neg, horizonGammaOct_involutive]

def rationalHorizonGammaQuat (q : QQ) : QQ :=
  ⟨q.re, -q.i, -q.j, q.k⟩

def rationalHorizonGammaOct (q : QO) : QO :=
  ⟨rationalHorizonGammaQuat q.fst, rationalHorizonGammaQuat q.snd⟩

/-- The action on the standard rational-coordinate Albert elements. -/
def rationalHorizonBeta (q : QA) : QA :=
  ⟨q.d0, q.d1, q.d2, (rationalHorizonGammaOct q.o0).smul (-1),
    rationalHorizonGammaOct q.o1, (rationalHorizonGammaOct q.o2).smul (-1)⟩

private theorem castQ_horizonGamma (q : QQ) :
    castQ (rationalHorizonGammaQuat q) = horizonGammaQuat (castQ q) := by
  apply Quaternion.ext <;> simp [rationalHorizonGammaQuat, horizonGammaQuat, castQ]

private theorem castO_horizonGamma (q : QO) :
    castO (rationalHorizonGammaOct q) = horizonGammaOct.equiv (castO q) :=
  Prod.ext (castQ_horizonGamma q.fst) (castQ_horizonGamma q.snd)

theorem castA_horizonBeta (q : QA) :
    castA (rationalHorizonBeta q) = horizonRationalBeta.linearEquiv (castA q) := by
  rw [horizonRationalBeta_apply]
  apply albert_ext'
  · rfl
  · rfl
  · rfl
  · change castO ((rationalHorizonGammaOct q.o0).smul (-1)) =
      -horizonGammaOct.equiv (castO q.o0)
    rw [castO_smul, castO_horizonGamma]
    norm_num
  · exact castO_horizonGamma q.o1
  · change castO ((rationalHorizonGammaOct q.o2).smul (-1)) =
      -horizonGammaOct.equiv (castO q.o2)
    rw [castO_smul, castO_horizonGamma]
    norm_num

end AlbertSequential.MatchingModels
