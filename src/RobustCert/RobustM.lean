/- SPDX-License-Identifier: Apache-2.0
   Machine-generated file. -/
module

public import RobustCert.Assembly
public import RobustCert.DataM1
public import RobustCert.DataM2
public import RobustCert.DataM3
public import RobustCert.DataM4
-- build order only: keeps large modules from compiling concurrently (memory)
import RobustCert.DataS1

/-! # thm:cer:seven(b) for `M`

Certificate vector: Φ = 4κ_C + 10κ_R − 9κ_H, as 18 path vectors `[w]` (`η^H_s = [xyz]`, `η^C_s = [xyzA]`,
`η^R_s = [xyzx]`).  `pairsM` holds a kernel-checked defect decomposition for each of the 324 ordered
pairs, along the printed derivation of lem:cer:gram7 (computing row: the `η^R` vector for RC/RH pairs,
the `η^C` vector for CH pairs, the first vector otherwise).  `θ = 3 / 2 ^ 19`.

Results (all computed by the kernel from the decomposition data, nothing copied):
* `lam2_nonneg_M`: `Λ''(g) ≥ 0` for the word values `g` of every `WalkForm`;
* `octVal_M`: on any table with `TableValues` at the traces of `M`, `Λ'' = −3 γ` with the paper's
  `γ = 4588961 / 169869312` (`γ` is the constant from `e/3`; words here are read from `p_A`, which multiplies by 3);
* `counterT_M`, `counterW_M_*`: the counters `T` and `W_π` equal the printed totals;
* `l1_M`: the unmerged `ℓ¹` norm of `Λ''` is at most `4470 * 10 ^ 6` (the paper's bound
  `5268 * 10 ^ 6` uses `(1 + c_max)²` for every defect; the exact norm is smaller);
* `robust_M`: prop:robust(a): `3γ ≤ ‖λ''‖₁ δ` for every `WalkForm` within `δ` of the table on the
  support of `Λ''`. -/

set_option autoImplicit false
set_option maxRecDepth 100000
@[expose] public section
noncomputable section
namespace AlbertSequential.LengthSeven.Robust

open AlbertSequential AlbertSequential.LengthSeven

/-- The traces of `M`. -/
def tableM : TraceTable :=
  ⟨(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 9 : ℚ), (1 / 9 : ℚ), (1 / 9 : ℚ), (1 / 9 : ℚ), (1 / 27 : ℚ), (1 / 27 : ℚ), (1 / 27 : ℚ)⟩

def vecsM : List (ℚ × List Letter) := [((4 : ℚ), [1,2,3,0].map lt), ((10 : ℚ), [1,2,3,1].map lt), ((-9 : ℚ), [1,2,3].map lt), ((-4 : ℚ), [1,3,2,0].map lt), ((-10 : ℚ), [1,3,2,1].map lt), ((9 : ℚ), [1,3,2].map lt), ((-4 : ℚ), [2,1,3,0].map lt), ((-10 : ℚ), [2,1,3,2].map lt), ((9 : ℚ), [2,1,3].map lt), ((4 : ℚ), [2,3,1,0].map lt), ((10 : ℚ), [2,3,1,2].map lt), ((-9 : ℚ), [2,3,1].map lt), ((4 : ℚ), [3,1,2,0].map lt), ((10 : ℚ), [3,1,2,3].map lt), ((-9 : ℚ), [3,1,2].map lt), ((-4 : ℚ), [3,2,1,0].map lt), ((-10 : ℚ), [3,2,1,3].map lt), ((9 : ℚ), [3,2,1].map lt)]

def pairsM : List (ℚ × Entry) := pairsM1 ++ pairsM2 ++ pairsM3 ++ pairsM4

def thetaM : ℚ := 3 / 2 ^ 19

theorem thetaM_pos : 0 < thetaM := by norm_num [thetaM]

theorem pairsM_spec : pairsM.map (fun p => (p.1, p.2.u1, p.2.u2)) = pairSpec vecsM := by
  decide +kernel

theorem pairsM_ok : pairsM.all (fun p => p.2.ok) = true := by
  simp only [pairsM, List.all_append, pairsM1_ok, pairsM2_ok, pairsM3_ok, pairsM4_ok,
    Bool.and_self]

theorem octOk_M : octOk tableM pairsM = true := by decide +kernel

theorem octVal_M : octVal tableM thetaM pairsM = -(3 * (4588961 / 169869312)) := by decide +kernel

theorem counterT_M : counterT pairsM = 1738400 / 243 := by decide +kernel

theorem counterW_M_0 : counterW tableM pairsM (1) = 231377/18 := by decide +kernel
theorem counterW_M_1 : counterW tableM pairsM (1/3) = 17863/3 := by decide +kernel
theorem counterW_M_2 : counterW tableM pairsM (1/9) = 45542/3 := by decide +kernel
theorem counterW_M_3 : counterW tableM pairsM (1/27) = 14008 := by decide +kernel
theorem counterW_M_4 : counterW tableM pairsM (1/81) = 32064 := by decide +kernel

theorem l1_M : l1 (lam2 tableM thetaM pairsM) ≤ 4470 * 10 ^ 6 := by decide +kernel

theorem l1_M_paper : l1 (lam2 tableM thetaM pairsM) ≤ 5268 * 10 ^ 6 :=
  le_trans l1_M (by norm_num)

/-- thm:cer:seven(b), positivity half: `Λ''(g) ≥ 0` in every `WalkForm`. -/
theorem lam2_nonneg_M {V : Type*} [AddCommGroup V] [Module ℝ V] (W : WalkForm V) :
    0 ≤ evalF (fun w => W.normSq (W.vec w)) (lam2 tableM thetaM pairsM) :=
  lam2_nonneg W tableM thetaM thetaM_pos vecsM pairsM pairsM_spec pairsM_ok

/-- thm:cer:seven(b), value half: on every table with `TableValues` at the traces of `M`,
`Λ'' = −3γ` (from `p_A`; `−γ` from `e/3`). -/
theorem lam2_oct_M {τ : TraceData} {f : Word Letter → ℝ} (h : tableM.Holds τ)
    (hT : TableValues τ f) :
    evalF f (lam2 tableM thetaM pairsM) = -(3 * (4588961 / 169869312 : ℝ)) := by
  rw [evalF_oct tableM h hT thetaM pairsM octOk_M, octVal_M]
  push_cast
  ring

/-- prop:robust(a) with the constants of `M`: a `WalkForm` within `δ` of the table on the support of
`Λ''` has `3γ ≤ ‖λ''‖₁ δ`. -/
theorem robust_M {V : Type*} [AddCommGroup V] [Module ℝ V] (W : WalkForm V) {τ : TraceData}
    {f : Word Letter → ℝ} (h : tableM.Holds τ) (hT : TableValues τ f) (δ : ℝ)
    (hδ : ∀ m ∈ lam2 tableM thetaM pairsM, |W.normSq (W.vec m.2) - f m.2| ≤ δ) :
    3 * (4588961 / 169869312 : ℝ) ≤ (l1 (lam2 tableM thetaM pairsM) : ℝ) * δ := by
  have := robust_margin W tableM h hT thetaM thetaM_pos vecsM pairsM pairsM_spec
    pairsM_ok octOk_M δ hδ
  rw [octVal_M] at this
  push_cast at this
  linarith

/-- Explicit margin: `δ ≥ 3γ / ‖λ''‖₁ > 3 · 6 / 10 ^ 12` (from `p_A`; the `e/3` margin is a third). -/
theorem robust_M_margin {V : Type*} [AddCommGroup V] [Module ℝ V] (W : WalkForm V)
    {τ : TraceData} {f : Word Letter → ℝ} (h : tableM.Holds τ) (hT : TableValues τ f) (δ : ℝ)
    (hδ : ∀ m ∈ lam2 tableM thetaM pairsM, |W.normSq (W.vec m.2) - f m.2| ≤ δ) :
    3 * (6 / 10 ^ 12 : ℝ) < δ := by
  have h1 := robust_M W h hT δ hδ
  have h2 : (l1 (lam2 tableM thetaM pairsM) : ℝ) ≤ 4470 * 10 ^ 6 := by exact_mod_cast l1_M
  have hpos : (0 : ℝ) < 3 * (4588961 / 169869312 : ℝ) := by norm_num
  have hδ0 : 0 < δ := by
    by_contra hneg
    replace hneg := not_lt.mp hneg
    have hl0 : (0 : ℝ) ≤ (l1 (lam2 tableM thetaM pairsM) : ℝ) := by
      exact_mod_cast l1_nonneg _
    have := mul_nonpos_iff.mpr (Or.inl ⟨hl0, hneg⟩)
    linarith
  have h3 := mul_le_mul_of_nonneg_right h2 hδ0.le
  linarith

end AlbertSequential.LengthSeven.Robust

#print axioms AlbertSequential.LengthSeven.Robust.robust_M
#print axioms AlbertSequential.LengthSeven.Robust.robust_M_margin
#print axioms AlbertSequential.LengthSeven.Robust.lam2_nonneg_M
#print axioms AlbertSequential.LengthSeven.Robust.counterT_M
