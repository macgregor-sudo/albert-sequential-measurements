/- SPDX-License-Identifier: Apache-2.0 -/
module

public import LemmaB.Lemma
public import LemmaB.Traces
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Adjugate

@[expose] public section
noncomputable section

namespace LemmaB

open scoped Matrix

/-- The normalized Gram matrix of the three twisted directions, without the common factor D̂. -/
def twistedNormalizedGram (s : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => if i = j then 1 + (s i)^2 else -(1 + s i * s j)

/-- The literal coefficients adj(G)(1,1,1)ᵀ in the deposited negative vector. -/
def twistedNegativeCoefficients (s : Fin 3 → ℝ) : Fin 3 → ℝ :=
  Matrix.adjugate (twistedNormalizedGram s) *ᵥ (fun _ => 1)

private theorem twistedAdjugate_entries (s : Fin 3 → ℝ) :
    Matrix.adjugate (twistedNormalizedGram s) =
      let k (i j : Fin 3) := 1 + s i * s j
      let a (i j z : Fin 3) := k i z * k j z + k i j * k z z
      !![(s 1 - s 2)^2, a 0 1 2, a 0 2 1;
        a 1 0 2, (s 0 - s 2)^2, a 1 2 0;
        a 2 0 1, a 2 1 0, (s 0 - s 1)^2] := by
  rw [Matrix.adjugate_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twistedNormalizedGram] <;> ring

theorem twistedNegativeCoefficients_pos (s : Fin 3 → ℝ) (hs : ∀ i, 0 < s i) (i : Fin 3) :
    0 < twistedNegativeCoefficients s i := by
  rw [twistedNegativeCoefficients, twistedAdjugate_entries, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three]
  have h0 := hs 0
  have h1 := hs 1
  have h2 := hs 2
  fin_cases i <;> simp <;> positivity

theorem twistedNormalizedGram_det (s : Fin 3 → ℝ) :
    (twistedNormalizedGram s).det = -4 * (1 + s 0 * s 1) * (1 + s 0 * s 2) * (1 + s 1 * s 2) := by
  rw [Matrix.det_fin_three]
  simp [twistedNormalizedGram]
  ring

theorem twistedNormalizedGram_mulVec_negativeCoefficients (s : Fin 3 → ℝ) :
    (twistedNormalizedGram s) *ᵥ twistedNegativeCoefficients s =
      (twistedNormalizedGram s).det • (fun _ => (1 : ℝ)) := by
  rw [twistedNegativeCoefficients, Matrix.mulVec_mulVec, Matrix.mul_adjugate,
    Matrix.smul_mulVec, Matrix.one_mulVec]

/-- The slopes of the three vectors in the ordinary positive Gram model before twisting. -/
def twistedSlopes (p : Params ℝ) : Fin 3 → ℝ :=
  ![p.μB / Real.sqrt p.μ, p.μC / Real.sqrt p.μ, p.μD / Real.sqrt p.μ]

def normalizedXi (p : Params ℝ) (i : Fin 3) : V ℝ :=
  (2 * αv p i)⁻¹ • Xi p i

theorem normalizedXi_pairing (p : Params ℝ) (hτ : p.tau = 0)
    (hB : 0 < p.μB) (hC : 0 < p.μC) (hD : 0 < p.μD) (i j : Fin 3) :
    Q p (normalizedXi p i) (normalizedXi p j) =
      p.Dhat * twistedNormalizedGram (twistedSlopes p) i j := by
  have hμ : 0 < p.μ := mul_pos (mul_pos hB hC) hD
  have hsq := Real.sq_sqrt hμ.le
  have hsq' (x : ℝ) : (x / Real.sqrt p.μ)^2 = x^2 / p.μ := by
    rw [div_pow, hsq]
  have hprod (x y : ℝ) :
      x / Real.sqrt p.μ * (y / Real.sqrt p.μ) = x * y / p.μ := by
    rw [div_mul_div_comm, ← pow_two, hsq]
  have hmB : p.mB = p.μB + 1 := by simp [Params.μB]
  have hmC : p.mC = p.μC + 1 := by simp [Params.μC]
  have hmD : p.mD = p.μD + 1 := by simp [Params.μD]
  rw [normalizedXi, normalizedXi, Q_smul_left, Q_smul_right, gram_Xi p hτ]
  fin_cases i <;> fin_cases j
  all_goals simp [αv, gramXi, twistedNormalizedGram, twistedSlopes,
    hmB, hmC, hmD, Params.αB, Params.αC, Params.αD]
  all_goals first | rw [hsq'] | rw [hprod]
  all_goals simp only [Params.μ]
  all_goals field_simp [hB.ne', hC.ne', hD.ne']
  all_goals ring

/-- The paper's negative combination of the accessible normalized Ξ directions. -/
def twistedAdjugateNegativeVector (p : Params ℝ) : V ℝ :=
  ∑ i, twistedNegativeCoefficients (twistedSlopes p) i • normalizedXi p i

theorem twistedAdjugateNegativeVector_mem_accessible (p : Params ℝ)
    (hm : ∀ i, mOf p i ≠ 0) :
    twistedAdjugateNegativeVector p ∈ Submodule.span ℝ
      (Set.range (fun w : Fin 4 × Fin 7 => uhat p (wordFI w.1 w.2))) := by
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  apply Submodule.smul_mem
  rw [Xi_mem_span_uhat p hm i]
  apply Submodule.sum_mem
  intro f _
  apply Submodule.sum_mem
  intro j _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(f,j), rfl⟩)

theorem twistedAdjugateNegativeVector_pairing (p : Params ℝ) (hτ : p.tau = 0)
    (hB : 0 < p.μB) (hC : 0 < p.μC) (hD : 0 < p.μD) :
    Q p (twistedAdjugateNegativeVector p) (twistedAdjugateNegativeVector p) =
      p.Dhat * (twistedNormalizedGram (twistedSlopes p)).det *
        ∑ i, twistedNegativeCoefficients (twistedSlopes p) i := by
  let s := twistedSlopes p
  let u := twistedNegativeCoefficients s
  let G := twistedNormalizedGram s
  have hp : Q p (twistedAdjugateNegativeVector p) (twistedAdjugateNegativeVector p) =
      p.Dhat * ∑ i, u i * (G *ᵥ u) i := by
    simp only [twistedAdjugateNegativeVector, Fin.sum_univ_three, Q_add_left, Q_add_right,
      Q_smul_left, Q_smul_right, normalizedXi_pairing p hτ hB hC hD, Matrix.mulVec, dotProduct,
      s, u, G]
    ring
  rw [hp]
  rw [show G *ᵥ u = G.det • (fun _ => (1 : ℝ)) from
    twistedNormalizedGram_mulVec_negativeCoefficients s]
  simp only [Pi.smul_apply, smul_eq_mul, mul_one, Fin.sum_univ_three]
  ring

theorem twistedAdjugateNegativeVector_negative (p : Params ℝ) (hτ : p.tau = 0)
    (hB : 0 < p.μB) (hC : 0 < p.μC) (hD : 0 < p.μD) (hDhat : 0 < p.Dhat) :
    Q p (twistedAdjugateNegativeVector p) (twistedAdjugateNegativeVector p) < 0 := by
  have hμ : 0 < p.μ := mul_pos (mul_pos hB hC) hD
  have hsqrt := Real.sqrt_pos.mpr hμ
  have hs (i : Fin 3) : 0 < twistedSlopes p i := by
    fin_cases i
    · exact div_pos hB hsqrt
    · exact div_pos hC hsqrt
    · exact div_pos hD hsqrt
  have hs0 := hs 0
  have hs1 := hs 1
  have hs2 := hs 2
  have hdet : (twistedNormalizedGram (twistedSlopes p)).det < 0 := by
    rw [twistedNormalizedGram_det]
    exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (by norm_num) (by positivity)) (by positivity)) (by positivity)
  have hu : 0 < ∑ i, twistedNegativeCoefficients (twistedSlopes p) i :=
    Finset.sum_pos (fun i _ => twistedNegativeCoefficients_pos _ hs i) Finset.univ_nonempty
  rw [twistedAdjugateNegativeVector_pairing p hτ hB hC hD]
  exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hDhat hdet) hu

/-- The trace hypotheses of the deposited proof give the accessible adjugate direction. -/
theorem Traces.twistedAdjugateNegativeVector_accessible_and_negative
    (τd : Traces) (hTR : τd.TraceRelation) (hA : 0 < τd.Acal)
    (hB0 : 0 < τd.oAB) (hB1 : τd.oAB < 1)
    (hC0 : 0 < τd.oAC) (hC1 : τd.oAC < 1)
    (hD0 : 0 < τd.oAD) (hD1 : τd.oAD < 1) :
    let p := τd.toParams
    twistedAdjugateNegativeVector p ∈ Submodule.span ℝ
      (Set.range (fun w : Fin 4 × Fin 7 => uhat p (wordFI w.1 w.2))) ∧
    Q p (twistedAdjugateNegativeVector p) (twistedAdjugateNegativeVector p) < 0 := by
  let p := τd.toParams
  have hmB : 0 < p.mB := inv_pos.mpr hB0
  have hmC : 0 < p.mC := inv_pos.mpr hC0
  have hmD : 0 < p.mD := inv_pos.mpr hD0
  have hm (i : Fin 4) : mOf p i ≠ 0 := by
    fin_cases i
    · exact one_ne_zero
    · exact hmB.ne'
    · exact hmC.ne'
    · exact hmD.ne'
  have hpos : 0 < p.Dhat := by
    change 0 < τd.toParams.Dhat
    rw [τd.Dhat_toParams hB0.ne' hC0.ne' hD0.ne']
    exact mul_pos (pow_pos (mul_pos (mul_pos hmB hmC) hmD) _) hA
  have hμ {a : ℝ} (ha : 0 < a) (hb : a < 1) : 0 < a⁻¹ - 1 :=
    sub_pos.mpr ((one_lt_inv₀ ha).mpr hb)
  exact ⟨twistedAdjugateNegativeVector_mem_accessible p hm,
    twistedAdjugateNegativeVector_negative p (τd.tau_eq_zero hB0.ne' hC0.ne' hD0.ne' hTR)
      (hμ hB0 hB1) (hμ hC0 hC1) (hμ hD0 hD1) hpos⟩

end LemmaB
