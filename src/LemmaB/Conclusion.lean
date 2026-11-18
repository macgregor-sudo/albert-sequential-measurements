module

public import LemmaB.Lemma
public import LemmaB.Traces
public import LemmaB.PSD

/-!
# Lemma B, part 8: the abstract conclusion (the step of thm:cer:uniform(a) after the lemmas)

If a real module carries a symmetric positive semidefinite bilinear form `B` (for instance the
inner product of the real cyclic representation), and twenty-eight vectors `[w]`, `w ∈ 𝒲₂₈`,
have `B([w], [w']) = 𝒬(û(w), û(w'))` (the conclusion of lem:cer:gram28 composed with
lem:cer:tablemodel, an explicit hypothesis here), then `D̂ > 0` and `μ_x > 0` give a
contradiction: `e_x = Σ c_{x,w} [w]` has Gram matrix `gramXi`, of determinant
`-256 D̂³ μ³ m < 0`, against `gram_det_nonneg`.
-/

@[expose] public section

namespace LemmaB

/-- Gram matrix of the transported vectors equals the `𝒬`-Gram matrix of the `Ξ_x`. -/
theorem transport_gram (p : Params ℝ) {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (pv : Fin 28 → E)
    (hgram : ∀ k l, B (pv k) (pv l) = Q p (uhat p (word28 k)) (uhat p (word28 l)))
    (c : Fin 3 → Fin 28 → ℝ) (hc : ∀ x, Xi p x = ∑ k, c x k • uhat p (word28 k)) (x y : Fin 3) :
    B (∑ k, c x k • pv k) (∑ l, c y l • pv l) = Q p (Xi p x) (Xi p y) := by
  rw [hc x, hc y, ← Ql_apply]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hgram,
    Ql_apply]

/-- **Contradiction, parameter form.** Real parameters with `τ = 0`, `D̂ > 0` and `m_x > 1`
admit no symmetric positive semidefinite realisation of the Gram matrix of the twenty-eight path
vectors. -/
theorem no_psd_realisation (p : Params ℝ) (hτ : p.tau = 0) (hD : 0 < p.Dhat)
    (hB : 1 < p.mB) (hC : 1 < p.mC) (hDm : 1 < p.mD)
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hsymm : ∀ u v, B u v = B v u) (hpos : ∀ u, 0 ≤ B u u)
    (pv : Fin 28 → E)
    (hgram : ∀ k l, B (pv k) (pv l) = Q p (uhat p (word28 k)) (uhat p (word28 l))) : False := by
  obtain ⟨c, hc, hG, hdet⟩ :=
    lemmaB_model p hτ ⟨by linarith, by linarith, by linarith⟩
  have hnn := gram_det_nonneg B hsymm hpos (fun x => ∑ k, c x k • pv k)
  have hM : (Matrix.of fun i j => B (∑ k, c i k • pv k) (∑ l, c j l • pv l)) = gramXi p := by
    ext i j
    simp only [Matrix.of_apply, transport_gram p B pv hgram c hc, hG]
  rw [hM, hdet] at hnn
  have hμ : 0 < p.μ := by
    simp only [Params.μ, Params.μB, Params.μC, Params.μD]
    have := mul_pos (mul_pos (sub_pos.2 hB) (sub_pos.2 hC)) (sub_pos.2 hDm); linarith
  have hm : 0 < p.m := by
    simp only [Params.m]; positivity
  have : 0 < 256 * p.Dhat ^ 3 * p.μ ^ 3 * p.m := by positivity
  linarith

/-- **Contradiction, trace form** (the use of lem:cer:negative in thm:cer:uniform(a)).
Thirteen real traces with the trace relation, `𝒜 > 0` and `0 < o_Ax < 1` admit no symmetric
positive semidefinite realisation `[w]` of the Gram matrix `𝒬(û(w), û(w'))` on `𝒲₂₈`. -/
theorem no_psd_realisation_traces (τd : Traces) (hTR : τd.TraceRelation) (hA : 0 < τd.Acal)
    (hB0 : 0 < τd.oAB) (hB1 : τd.oAB < 1) (hC0 : 0 < τd.oAC) (hC1 : τd.oAC < 1)
    (hD0 : 0 < τd.oAD) (hD1 : τd.oAD < 1)
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hsymm : ∀ u v, B u v = B v u) (hpos : ∀ u, 0 ≤ B u u)
    (pv : Fin 28 → E)
    (hgram : ∀ k l, B (pv k) (pv l) =
      Q τd.toParams (uhat τd.toParams (word28 k)) (uhat τd.toParams (word28 l))) : False := by
  have one_lt : ∀ o : ℝ, 0 < o → o < 1 → 1 < o⁻¹ := fun o h0 h1 => by
    rw [lt_inv_comm₀ one_pos h0, inv_one]; exact h1
  refine no_psd_realisation τd.toParams
    (Traces.tau_eq_zero τd hB0.ne' hC0.ne' hD0.ne' hTR) ?_
    (one_lt _ hB0 hB1) (one_lt _ hC0 hC1) (one_lt _ hD0 hD1) B hsymm hpos pv hgram
  rw [Traces.Dhat_toParams τd hB0.ne' hC0.ne' hD0.ne']
  have : 0 < τd.toParams.m := by
    simp only [Traces.toParams, Params.m]; positivity
  positivity

end LemmaB
