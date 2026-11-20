/- SPDX-License-Identifier: Apache-2.0 -/
module

public import LengthSeven.TableRules
public import RobustCert.Assembly
public import Mathlib.Analysis.Real.Sqrt

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace AlbertSequential.LengthSeven

/-- Scalar error bound with a common scale and a separate nonnegative budget. -/
def Within (d C a b : ℝ) : Prop := |a - b| ≤ C * d

namespace Within

theorem defect {d C a b : ℝ} (h : Within d C a b) :
    ∃ e : ℝ, a = b + e ∧ |e| ≤ C * d :=
  ⟨a - b, by ring, h⟩

theorem widen {d C D a b : ℝ} (h : Within d C a b) (hd : 0 ≤ d) (hCD : C ≤ D) :
    Within d D a b := le_trans h (mul_le_mul_of_nonneg_right hCD hd)

theorem add {d C D a b x y : ℝ} (h : Within d C a b) (h' : Within d D x y) :
    Within d (C + D) (a + x) (b + y) := by
  unfold Within at *
  rw [show a + x - (b + y) = (a - b) + (x - y) by ring, add_mul]
  exact (abs_add_le _ _).trans (add_le_add h h')

theorem neg {d C a b : ℝ} (h : Within d C a b) : Within d C (-a) (-b) := by
  simpa only [Within, neg_sub_neg, abs_sub_comm b a] using h

theorem sub {d C D a b x y : ℝ} (h : Within d C a b) (h' : Within d D x y) :
    Within d (C + D) (a - x) (b - y) := by
  simpa only [sub_eq_add_neg] using h.add h'.neg

theorem scale {d C a b : ℝ} (h : Within d C a b) (k : ℝ) :
    Within d (|k| * C) (k * a) (k * b) := by
  unfold Within at *
  rw [← mul_sub, abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

end Within

namespace WalkForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (W : WalkForm V)

theorem normSq_op_le (q : Outcome Letter) (x : V) :
    W.normSq (W.op q x) ≤ W.normSq x := by
  have h := W.psd (x - W.op q x)
  have hcross := W.op_selfAdj q (W.op q x) x
  rw [W.op_idem] at hcross
  simp only [normSq, map_sub, LinearMap.sub_apply, W.symm x (W.op q x), hcross] at h ⊢
  linarith

theorem normSq_seqL_le (u : Word Letter) (x : V) :
    W.normSq (W.seqL u x) ≤ W.normSq x := by
  induction u generalizing x with
  | nil => rfl
  | cons q u ih =>
    rw [W.seqL_cons_apply]
    exact (ih (W.op q x)).trans (W.normSq_op_le q x)

theorem abs_pair_le_of_sq {x y : V} {k : ℝ} (hk : 0 ≤ k)
    (hx : W.normSq x ≤ 1) (hy : W.normSq y ≤ k ^ 2) : |W.form x y| ≤ k := by
  rcases hk.eq_or_lt with rfl | hk
  · have hz : W.form y y = 0 := le_antisymm (by simpa [normSq] using hy) (W.psd y)
    rw [W.symm x y, W.null_pair y hz x, abs_zero]
  · have h₁ := Robust.amgm W x y k hk 1
    have h₂ := Robust.amgm W x y k hk (-1)
    norm_num at h₁ h₂
    have hb : W.normSq y / (2 * k) ≤ k / 2 := by
      apply (div_le_iff₀ (by positivity)).mpr
      convert hy using 1; ring
    have ha := mul_le_mul_of_nonneg_left hx (show 0 ≤ k / 2 by positivity)
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Closeness is on chronological, conditioned word probabilities. -/
def Approximates (S : Set (Word Letter)) (f : Word Letter → ℝ) (ε : ℝ) : Prop :=
  ∀ w ∈ S, |W.normSq (W.vec w) - f w| ≤ ε

variable {W} {τ : TraceData} {S : Set (Word Letter)} {f : Word Letter → ℝ} {ε : ℝ}

theorem Approximates.on (h : W.Approximates S f ε) (hT : TableValues τ f)
    (w : Word Letter) (hw : dropYesA w ∈ S) : |W.normSq (W.vec w) - f w| ≤ ε := by
  rw [← W.normSq_vec_dropYesA, ← hT.f_dropYesA w]
  exact h _ hw

/-- Three actual probabilities control the square of the actual vector defect.
The suffix is moved onto the test vector by adjointness. -/
theorem purity_pair_within (h : W.Approximates S f ε) (hT : TableValues τ f)
    (hε : 0 ≤ ε) (t : Word Letter) (q : Outcome Letter) (v : Word Letter) (c : ℝ)
    (hS : Covers S (purityWords t q v))
    (hf : f (t ++ [q] ++ v ++ purityMirror v ++ [q]) - 2 * c * f (t ++ [q] ++ v)
          + c ^ 2 * f (t ++ [q]) = 0)
    (r : Word Letter) (x : V) (hx : W.normSq x ≤ 1) :
    Within (Real.sqrt ε) (1 + |c|)
      (W.form (W.vec (t ++ [q] ++ v ++ purityMirror v ++ [q] ++ r)) x)
      (c * W.form (W.vec (t ++ [q] ++ r)) x) := by
  let a := t ++ [q] ++ v ++ purityMirror v ++ [q]
  let b := t ++ [q] ++ v
  let d := t ++ [q]
  have ha := h.on hT a (hS _ (by simp [a, purityWords]))
  have hb := h.on hT b (hS _ (by simp [b, purityWords]))
  have hd := h.on hT d (hS _ (by simp [d, purityWords]))
  have habs : |W.normSq (W.vec a) - 2 * c * W.normSq (W.vec b) + c ^ 2 * W.normSq (W.vec d)| ≤
      (1 + |c|) ^ 2 * ε := by
    have hzero : f a - 2 * c * f b + c ^ 2 * f d = 0 := hf
    rw [show W.normSq (W.vec a) - 2 * c * W.normSq (W.vec b) + c ^ 2 * W.normSq (W.vec d) =
      (W.normSq (W.vec a) - f a) - 2 * c * (W.normSq (W.vec b) - f b) +
        c ^ 2 * (W.normSq (W.vec d) - f d) by linarith only [hzero]]
    calc
      _ ≤ |W.normSq (W.vec a) - f a| + |2 * c| * |W.normSq (W.vec b) - f b|
          + |c ^ 2| * |W.normSq (W.vec d) - f d| := by
        rw [← abs_mul (2 * c), ← abs_mul (c ^ 2)]
        exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ ε + |2 * c| * ε + |c ^ 2| * ε :=
        add_le_add (add_le_add ha (mul_le_mul_of_nonneg_left hb (abs_nonneg _)))
          (mul_le_mul_of_nonneg_left hd (abs_nonneg _))
      _ = _ := by rw [abs_mul, abs_pow, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]; ring
  let z := W.vec a - c • W.vec d
  have hz : W.normSq z ≤ ((1 + |c|) * Real.sqrt ε) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hε]
    exact (W.purity_residual t q v c).trans_le ((le_abs_self _).trans habs)
  have hbnd := W.abs_pair_le_of_sq (by positivity)
    ((W.normSq_seqL_le r.reverse x).trans hx) hz
  unfold Within
  rw [show W.form (W.vec (a ++ r)) x - c * W.form (W.vec (d ++ r)) x =
    W.form (W.seqL r.reverse x) z by
      rw [W.vec_append a r, W.vec_append d r, W.seqL_adjoint, W.seqL_adjoint, W.symm (W.vec a),
        W.symm (W.vec d)]
      simp [z, map_sub, map_smul, smul_eq_mul]]
  exact hbnd

end WalkForm

end AlbertSequential.LengthSeven
