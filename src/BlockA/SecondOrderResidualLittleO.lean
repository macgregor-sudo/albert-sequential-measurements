/- SPDX-License-Identifier: Apache-2.0 -/
module

public import BlockA.SecondOrderResidual
public import Mathlib.Analysis.Calculus.Taylor

/-! The same second-order residual with only two continuous derivatives. -/
@[expose] public section
noncomputable section
open Asymptotics Filter Set
open scoped Topology AlbertSequential.AppF

namespace AlbertSequential.AppF

theorem taylor_two_isLittleO_square {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : ContDiff ℝ 2 f) :
    (fun t => f t - (f 0 + t • deriv f 0 + (t ^ 2 / 2) • deriv (deriv f) 0)) =o[𝓝 0]
      (fun t => t ^ 2) := by
  have ht := taylor_isLittleO_univ (n := 2) (x₀ := 0) hf
  refine ht.congr' (Eventually.of_forall fun t => ?_) (Eventually.of_forall fun t => by simp)
  change f t - taylorWithinEval f 2 univ 0 t = _
  congr 1
  rw [taylorWithinEval_succ f 1 univ 0 t, taylorWithinEval_succ f 0 univ 0 t,
    taylor_within_zero_eval]
  norm_num [iteratedDerivWithin_univ, iteratedDeriv_one, iteratedDeriv_succ', div_eq_mul_inv]
  rw [mul_comm]

private theorem standardWindow_residual_jet {n : ℕ}
    (T : JTerm n) (hT : T.VanishesOnSpecialIdempotents)
    (p : Fin n → ℝ → Albert) (hp : ∀ k, ContDiffAt ℝ 2 (p k) 0)
    (hide : ∀ k t, jordanMul (p k t) (p k t) = p k t)
    (hbase : ∀ k, standardComplexWindow.Contains (p k 0)) :
    jet2 (fun t => T.evalAlbert (fun k => p k t)) ∈ Kso := by
  rw [jet2_evalAlbert hp T]
  exact term_value_mem_K T hT _ (fun k => jet2_mem_E2 (hbase k))
    (fun k => jet2_idempotent (hp k) (hide k))

private theorem jet2_linearEquiv (g : Albert ≃ₗ[ℝ] Albert) {f : ℝ → Albert}
    (hf : ContDiffAt ℝ 2 f 0) :
    jet2 (fun t => g (f t)) =
      (g (f 0), g (deriv f 0), g ((1 / 2 : ℝ) • deriv (deriv f) 0)) := by
  let G := g.toLinearMap.toContinuousLinearMap
  have hd {t : ℝ} {h : ℝ → Albert} (hh : DifferentiableAt ℝ h t) :
      deriv (fun s => g (h s)) t = g (deriv h t) :=
    (G.hasFDerivAt.comp_hasDerivAt t hh.hasDerivAt).deriv
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), deriv (fun s => g (f s)) t = g (deriv f t) := by
    filter_upwards [hf.eventually (by norm_num)] with t ht
    exact hd (ht.differentiableAt (by norm_num))
  have hd2 : deriv (deriv (fun t => g (f t))) 0 = g (deriv (deriv f) 0) := by
    rw [Filter.EventuallyEq.deriv_eq hnear]
    exact hd ((hf.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))
  simp only [jet2, hd (hf.differentiableAt (by norm_num)), hd2, map_smul]

/-- The two lower jets vanish and the quadratic coefficient is perpendicular to the
base complex window. The word effect and probability remainder are little-o of t². -/
theorem cor_so_residual_littleO {n : ℕ} (W : ComplexWindow)
    (c : Word (Fin n) →₀ ℝ) (hc : IsProjectiveEquality c)
    (p : Fin n → ℝ → Albert) (hp_diff : ∀ k, ContDiff ℝ 2 (p k))
    (hp_idem : ∀ k t, jordanMul (p k t) (p k t) = p k t)
    (hp_base : ∀ k, W.Contains (p k 0)) :
    let r : ℝ → Albert := fun t => nativeWordCombinationEffect c (fun k => p k t)
    let Q : Albert := (1 / 2 : ℝ) • deriv (deriv r) 0
    ContDiff ℝ 2 r ∧ r 0 = 0 ∧ deriv r 0 = 0 ∧
      (∀ w : Albert, W.Contains w → tracePairing w Q = 0) ∧
      ((fun t => r t - t ^ 2 • Q) =o[𝓝 0] (fun t => t ^ 2)) ∧
      (∀ l : Albert →ₗ[ℝ] ℝ, (fun t => l (r t - t ^ 2 • Q)) =o[𝓝 0] (fun t => t ^ 2)) ∧
      (∀ ρ : Albert, W.Contains ρ →
        (fun t => c.sum (fun w a => a * nativeWordProbability (fun k => p k t) ρ w)) =o[𝓝 0]
          (fun t => t ^ 2)) := by
  intro r Q
  let T := wordCombinationJTerm c
  have he (t : ℝ) : T.evalAlbert (fun k => p k t) = r t :=
    evalAlbert_wordCombinationJTerm c (fun k => p k t)
  have hr_diff : ContDiff ℝ 2 r := by
    rw [← funext he]
    exact contDiff_evalAlbert hp_diff T
  obtain ⟨g, hg⟩ := native_complexWindow_conjugate_standard W
  let pg : Fin n → ℝ → Albert := fun k t => g.linearEquiv (p k t)
  let G := g.linearEquiv.toLinearMap.toContinuousLinearMap
  have hpg_diff (k : Fin n) : ContDiffAt ℝ 2 (pg k) 0 :=
    (G.contDiff.comp (hp_diff k)).contDiffAt
  have hpg_idem (k : Fin n) (t : ℝ) : jordanMul (pg k t) (pg k t) = pg k t := by
    dsimp [pg]
    rw [← g.preserves_product, hp_idem]
  have hpg_base (k : Fin n) : standardComplexWindow.Contains (pg k 0) := by
    obtain ⟨M, hM⟩ := hp_base k
    exact ⟨M, by rw [← hg M, hM]⟩
  have hm : (fun t => T.evalAlbert (fun k => pg k t)) = (fun t => g.linearEquiv (r t)) := by
    funext t
    rw [evalAlbert_wordCombinationJTerm, ← map_nativeWordCombinationEffect g c (fun k => p k t)]
  have hj := standardWindow_residual_jet T ((isProjectiveEquality_iff_specialVanishing c).mp hc)
    pg hpg_diff hpg_idem hpg_base
  rw [hm, jet2_linearEquiv g.linearEquiv hr_diff.contDiffAt] at hj
  obtain ⟨h0, h1, h2⟩ := hj
  have hr0 : r 0 = 0 := g.linearEquiv.injective (h0.trans (map_zero g.linearEquiv).symm)
  have hr1 : deriv r 0 = 0 := g.linearEquiv.injective (h1.trans (map_zero g.linearEquiv).symm)
  have horth (w : Albert) (hw : W.Contains w) : tracePairing w Q = 0 := by
    obtain ⟨M, hM⟩ := hw
    have hgw : standardComplexWindow.Contains (g.linearEquiv w) := ⟨M, by rw [← hg M, hM]⟩
    rw [← g.map_tracePairing]
    exact mem_Wperp_implies_tracePairing_zero h2 hgw
  have hres : (fun t => r t - t ^ 2 • Q) =o[𝓝 0] (fun t => t ^ 2) := by
    have ht := taylor_two_isLittleO_square hr_diff
    refine ht.congr' (Eventually.of_forall fun t => ?_) (Eventually.of_forall fun _ => rfl)
    simp only [hr0, hr1, smul_zero, add_zero, zero_add]
    change r t - (t ^ 2 / 2) • deriv (deriv r) 0 = r t - t ^ 2 • ((1 / 2 : ℝ) • deriv (deriv r) 0)
    rw [smul_smul, div_eq_mul_one_div]
  have hlin (l : Albert →ₗ[ℝ] ℝ) :
      (fun t => l (r t - t ^ 2 • Q)) =o[𝓝 0] (fun t => t ^ 2) := by
    exact (l.toContinuousLinearMap.isBigO_comp _ _).trans_isLittleO hres
  refine ⟨hr_diff, hr0, hr1, horth, hres, hlin, fun ρ hρ => ?_⟩
  refine (hlin (tracePairingLM ρ)).congr' (Eventually.of_forall fun t => ?_)
    (Eventually.of_forall fun _ => rfl)
  dsimp only
  rw [tracePairingLM_apply, tracePairing_sub_right, tracePairing_smul_right,
    horth ρ hρ, mul_zero, sub_zero, tracePairing_nativeWordCombinationEffect]

theorem cor_so_residual_littleO_of_atoms {n : ℕ} (W : ComplexWindow)
    (c : Word (Fin n) →₀ ℝ) (hc : IsProjectiveEquality c)
    (p : Fin n → ℝ → Albert) (hp_diff : ∀ k, ContDiff ℝ 2 (p k))
    (hp_atom : ∀ k t, IsAtom (p k t)) (hp_base : ∀ k, W.Contains (p k 0)) :
    let r : ℝ → Albert := fun t => nativeWordCombinationEffect c (fun k => p k t)
    let Q : Albert := (1 / 2 : ℝ) • deriv (deriv r) 0
    ContDiff ℝ 2 r ∧ r 0 = 0 ∧ deriv r 0 = 0 ∧
      (∀ w : Albert, W.Contains w → tracePairing w Q = 0) ∧
      ((fun t => r t - t ^ 2 • Q) =o[𝓝 0] (fun t => t ^ 2)) ∧
      (∀ l : Albert →ₗ[ℝ] ℝ, (fun t => l (r t - t ^ 2 • Q)) =o[𝓝 0] (fun t => t ^ 2)) ∧
      (∀ ρ : Albert, W.Contains ρ →
        (fun t => c.sum (fun w a => a * nativeWordProbability (fun k => p k t) ρ w)) =o[𝓝 0]
          (fun t => t ^ 2)) :=
  cor_so_residual_littleO W c hc p hp_diff (fun k t => (hp_atom k t).1) hp_base

end AlbertSequential.AppF
