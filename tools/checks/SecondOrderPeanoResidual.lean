module

import BlockA.SecondOrderResidualLittleO

open Asymptotics AlbertSequential AlbertSequential.AppF
open scoped Topology AlbertSequential.AppF

example (W : ComplexWindow) {n : ℕ} (c : Word (Fin n) →₀ ℝ)
    (hc : IsProjectiveEquality c) (p : Fin n → ℝ → Albert)
    (hC : ∀ k, ContDiff ℝ 2 (p k)) (hatom : ∀ k t, IsAtom (p k t))
    (hbase : ∀ k, W.Contains (p k 0)) (ρ : Albert) (hρ : W.Contains ρ) :
    let r : ℝ → Albert := fun t => nativeWordCombinationEffect c (fun k => p k t)
    let Q := (1 / 2 : ℝ) • deriv (deriv r) 0
    r 0 = 0 ∧ deriv r 0 = 0 ∧ tracePairing ρ Q = 0 ∧
      ((fun t => r t - t ^ 2 • Q) =o[𝓝 0] (fun t => t ^ 2)) ∧
      ((fun t => c.sum (fun w a => a * nativeWordProbability (fun k => p k t) ρ w))
        =o[𝓝 0] (fun t => t ^ 2)) := by
  obtain ⟨_, h0, h1, hQ, hr, _, hp⟩ := cor_so_residual_littleO_of_atoms W c hc p hC hatom hbase
  exact ⟨h0, h1, hQ ρ hρ, hr, hp ρ hρ⟩

example (W : ComplexWindow) {n : ℕ} (c : Word (Fin n) →₀ ℝ)
    (hc : IsProjectiveEquality c) (p : Fin n → ℝ → Albert)
    (hC : ∀ k, ContDiff ℝ 2 (p k))
    (hide : ∀ k t, jordanMul (p k t) (p k t) = p k t)
    (hbase : ∀ k, W.Contains (p k 0)) (ℓ : Albert →ₗ[ℝ] ℝ) :
    let r : ℝ → Albert := fun t => nativeWordCombinationEffect c (fun k => p k t)
    (fun t => ℓ (r t - t ^ 2 • ((1 / 2 : ℝ) • deriv (deriv r) 0))) =o[𝓝 0] (fun t => t ^ 2) :=
  (cor_so_residual_littleO W c hc p hC hide hbase).2.2.2.2.2.1 ℓ

#print axioms AlbertSequential.AppF.taylor_two_isLittleO_square
#print axioms AlbertSequential.AppF.cor_so_residual_littleO
#print axioms AlbertSequential.AppF.cor_so_residual_littleO_of_atoms
