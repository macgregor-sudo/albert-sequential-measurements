/- SPDX-License-Identifier: Apache-2.0
   Machine-generated file. -/
module

public import RobustCert.Assembly
public import RobustCert.DataS1
public import RobustCert.DataS2
public import RobustCert.DataS3
public import RobustCert.DataS4
-- build order only: keeps large modules from compiling concurrently (memory)
import RobustCert.RobustM

/-! # thm:cer:seven(b) for `S`

Certificate vector: Φ_S^rob = Σ_s sgn(s)(w_C η^C_s + w_R η^R_s + w_H η^H_s), (w_C,w_R,w_H) = (3,14,−13) (B first), (4,15,−13) (B middle), (6,17,−15) (B last), as 18 path vectors `[w]` (`η^H_s = [xyz]`, `η^C_s = [xyzA]`,
`η^R_s = [xyzx]`).  `pairsS` holds a kernel-checked defect decomposition for each of the 324 ordered
pairs, along the printed derivation of lem:cer:gram7 (computing row: the `η^R` vector for RC/RH pairs,
the `η^C` vector for CH pairs, the first vector otherwise).  `θ = 3 / 2 ^ 20`.

Results (all computed by the kernel from the decomposition data, nothing copied):
* `lam2_nonneg_S`: `Λ''(g) ≥ 0` for the word values `g` of every `WalkForm`;
* `octVal_S`: on any table with `TableValues` at the traces of `S`, `Λ'' = −3 γ` with the paper's
  `γ = 412734271 / 18345885696` (`γ` is the constant from `e/3`; words here are read from `p_A`, which multiplies by 3);
* `counterT_S`, `counterW_S_*`: the counters `T` and `W_π` equal the printed totals;
* `l1_S`: the unmerged `ℓ¹` norm of `Λ''` is at most `19519 * 10 ^ 6` (the paper's bound
  `2892 * 10 ^ 7` uses `(1 + c_max)²` for every defect; the exact norm is smaller);
* `robust_S`: prop:robust(a): `3γ ≤ ‖λ''‖₁ δ` for every `WalkForm` within `δ` of the table on the
  support of `Λ''`. -/

set_option autoImplicit false
set_option maxRecDepth 100000
@[expose] public section
noncomputable section
namespace AlbertSequential.LengthSeven.Robust

open AlbertSequential AlbertSequential.LengthSeven

/-- The traces of `S`. -/
def tableS : TraceTable :=
  ⟨(1 / 2 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ), (1 / 9 : ℚ), (1 / 9 : ℚ), (1 / 18 : ℚ), (1 / 18 : ℚ), (1 / 18 : ℚ)⟩

def vecsS : List (ℚ × List Letter) := [((3 : ℚ), [1,2,3,0].map lt), ((14 : ℚ), [1,2,3,1].map lt), ((-13 : ℚ), [1,2,3].map lt), ((-3 : ℚ), [1,3,2,0].map lt), ((-14 : ℚ), [1,3,2,1].map lt), ((13 : ℚ), [1,3,2].map lt), ((-4 : ℚ), [2,1,3,0].map lt), ((-15 : ℚ), [2,1,3,2].map lt), ((13 : ℚ), [2,1,3].map lt), ((6 : ℚ), [2,3,1,0].map lt), ((17 : ℚ), [2,3,1,2].map lt), ((-15 : ℚ), [2,3,1].map lt), ((4 : ℚ), [3,1,2,0].map lt), ((15 : ℚ), [3,1,2,3].map lt), ((-13 : ℚ), [3,1,2].map lt), ((-6 : ℚ), [3,2,1,0].map lt), ((-17 : ℚ), [3,2,1,3].map lt), ((15 : ℚ), [3,2,1].map lt)]

def pairsS : List (ℚ × Entry) := pairsS1 ++ pairsS2 ++ pairsS3 ++ pairsS4

def thetaS : ℚ := 3 / 2 ^ 20

theorem thetaS_pos : 0 < thetaS := by norm_num [thetaS]

theorem pairsS_spec : pairsS.map (fun p => (p.1, p.2.u1, p.2.u2)) = pairSpec vecsS := by
  decide +kernel

theorem pairsS_ok : pairsS.all (fun p => p.2.ok) = true := by
  simp only [pairsS, List.all_append, pairsS1_ok, pairsS2_ok, pairsS3_ok, pairsS4_ok,
    Bool.and_self]

theorem octOk_S : octOk tableS pairsS = true := by decide +kernel

theorem octVal_S : octVal tableS thetaS pairsS = -(3 * (412734271 / 18345885696)) := by decide +kernel

theorem counterT_S : counterT pairsS = 21466321 / 1458 := by decide +kernel

theorem counterW_S_0 : counterW tableS pairsS (1) = 3099331/108 := by decide +kernel
theorem counterW_S_1 : counterW tableS pairsS (1/2) = 4065 := by decide +kernel
theorem counterW_S_2 : counterW tableS pairsS (1/3) = 73880/9 := by decide +kernel
theorem counterW_S_3 : counterW tableS pairsS (1/6) = 28534/3 := by decide +kernel
theorem counterW_S_4 : counterW tableS pairsS (1/9) = 191914/9 := by decide +kernel
theorem counterW_S_5 : counterW tableS pairsS (1/18) = 9674 := by decide +kernel
theorem counterW_S_6 : counterW tableS pairsS (1/27) = 56086/3 := by decide +kernel
theorem counterW_S_7 : counterW tableS pairsS (1/54) = 25290 := by decide +kernel
theorem counterW_S_8 : counterW tableS pairsS (1/81) = 29772 := by decide +kernel

theorem l1_S : l1 (lam2 tableS thetaS pairsS) ≤ 19519 * 10 ^ 6 := by decide +kernel

theorem l1_S_paper : l1 (lam2 tableS thetaS pairsS) ≤ 2892 * 10 ^ 7 :=
  le_trans l1_S (by norm_num)

/-- thm:cer:seven(b), positivity half: `Λ''(g) ≥ 0` in every `WalkForm`. -/
theorem lam2_nonneg_S {V : Type*} [AddCommGroup V] [Module ℝ V] (W : WalkForm V) :
    0 ≤ evalF (fun w => W.normSq (W.vec w)) (lam2 tableS thetaS pairsS) :=
  lam2_nonneg W tableS thetaS thetaS_pos vecsS pairsS pairsS_spec pairsS_ok

/-- thm:cer:seven(b), value half: on every table with `TableValues` at the traces of `S`,
`Λ'' = −3γ` (from `p_A`; `−γ` from `e/3`). -/
theorem lam2_oct_S {τ : TraceData} {f : Word Letter → ℝ} (h : tableS.Holds τ)
    (hT : TableValues τ f) :
    evalF f (lam2 tableS thetaS pairsS) = -(3 * (412734271 / 18345885696 : ℝ)) := by
  rw [evalF_oct tableS h hT thetaS pairsS octOk_S, octVal_S]
  push_cast
  ring

/-- prop:robust(a) with the constants of `S`: a `WalkForm` within `δ` of the table on the support of
`Λ''` has `3γ ≤ ‖λ''‖₁ δ`. -/
theorem robust_S {V : Type*} [AddCommGroup V] [Module ℝ V] (W : WalkForm V) {τ : TraceData}
    {f : Word Letter → ℝ} (h : tableS.Holds τ) (hT : TableValues τ f) (δ : ℝ)
    (hδ : ∀ m ∈ lam2 tableS thetaS pairsS, |W.normSq (W.vec m.2) - f m.2| ≤ δ) :
    3 * (412734271 / 18345885696 : ℝ) ≤ (l1 (lam2 tableS thetaS pairsS) : ℝ) * δ := by
  have := robust_margin W tableS h hT thetaS thetaS_pos vecsS pairsS pairsS_spec
    pairsS_ok octOk_S δ hδ
  rw [octVal_S] at this
  push_cast at this
  linarith

/-- Explicit margin: `δ ≥ 3γ / ‖λ''‖₁ > 3 · 115 / 10 ^ 14` (from `p_A`; the `e/3` margin is a third). -/
theorem robust_S_margin {V : Type*} [AddCommGroup V] [Module ℝ V] (W : WalkForm V)
    {τ : TraceData} {f : Word Letter → ℝ} (h : tableS.Holds τ) (hT : TableValues τ f) (δ : ℝ)
    (hδ : ∀ m ∈ lam2 tableS thetaS pairsS, |W.normSq (W.vec m.2) - f m.2| ≤ δ) :
    3 * (115 / 10 ^ 14 : ℝ) < δ := by
  have h1 := robust_S W h hT δ hδ
  have h2 : (l1 (lam2 tableS thetaS pairsS) : ℝ) ≤ 19519 * 10 ^ 6 := by exact_mod_cast l1_S
  have hpos : (0 : ℝ) < 3 * (412734271 / 18345885696 : ℝ) := by norm_num
  have hδ0 : 0 < δ := by
    by_contra hneg
    replace hneg := not_lt.mp hneg
    have hl0 : (0 : ℝ) ≤ (l1 (lam2 tableS thetaS pairsS) : ℝ) := by
      exact_mod_cast l1_nonneg _
    have := mul_nonpos_iff.mpr (Or.inl ⟨hl0, hneg⟩)
    linarith
  have h3 := mul_le_mul_of_nonneg_right h2 hδ0.le
  linarith

end AlbertSequential.LengthSeven.Robust

#print axioms AlbertSequential.LengthSeven.Robust.robust_S
#print axioms AlbertSequential.LengthSeven.Robust.robust_S_margin
#print axioms AlbertSequential.LengthSeven.Robust.lam2_nonneg_S
#print axioms AlbertSequential.LengthSeven.Robust.counterT_S
