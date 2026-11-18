/- SPDX-License-Identifier: Apache-2.0 -/
module

public import LengthSeven.TableRules
public import HilbertProjectiveData
public import QuaternionicProjectiveData

/-! # From sequential projective representations to walk forms

`WalkForm.ofAlgebraic M h` is the walk form of the comparator class
`AlgebraicProjectiveData` (any star ring, idempotent self-adjoint projections,
positive normalised real state; no faithfulness or traciality), conditioned on a
yes on `A`: the carrier is the algebra itself, `⟨X, Y⟩ = φ(X*Y)/φ(P_A)`,
`P_i` is left multiplication, `ξ = P_A`.  No square root and no GNS construction
is used.  Real and complex Hilbert models (`HilbertProjectiveData`) and right
quaternionic models (`QuaternionicProjectiveData`) enter through their
`toAlgebraic` bridges. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.LengthSeven

open AlbertSequential

section Algebraic

variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
  [SMulCommClass ℝ A A] [StarModule ℝ A]

/-- The state pairing `X, Y ↦ κ φ(X* Y)` as a real bilinear form. -/
def algForm (M : AlgebraicProjectiveData Letter A) (κ : ℝ) : A →ₗ[ℝ] A →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun X Y => κ * M.state (star X * Y))
    (fun X X' Y => by rw [star_add, add_mul, map_add, mul_add])
    (fun c X Y => by
      rw [star_smul, star_trivial, smul_mul_assoc, map_smul, smul_eq_mul, smul_eq_mul]; ring)
    (fun X Y Y' => by rw [mul_add, map_add, mul_add])
    (fun c X Y => by rw [mul_smul_comm, map_smul, smul_eq_mul, smul_eq_mul]; ring)

theorem algForm_apply (M : AlgebraicProjectiveData Letter A) (κ : ℝ) (X Y : A) :
    algForm M κ X Y = κ * M.state (star X * Y) := rfl

theorem probability_yesA (M : AlgebraicProjectiveData Letter A) :
    M.probability [(0, true)] = M.state (star (M.projection 0) * M.projection 0) := by
  simp [AlgebraicProjectiveData.probability, wordOperator, wordAmplitude, algebraicOutcome]

/-- The conditioned walk form of an algebraic sequential representation. -/
def WalkForm.ofAlgebraic (M : AlgebraicProjectiveData Letter A)
    (h : 0 < M.probability [(0, true)]) : WalkForm A where
  form := algForm M (M.probability [(0, true)])⁻¹
  symm X Y := by
    simp only [algForm_apply]
    congr 1
    rw [← M.state_star (star X * Y), star_mul, star_star]
  psd X := by
    simp only [algForm_apply]
    exact mul_nonneg (inv_nonneg.mpr h.le) (M.state_positive X)
  P i := LinearMap.mulLeft ℝ (M.projection i)
  idem i X := by
    simp only [LinearMap.mulLeft_apply, ← mul_assoc, M.idempotent]
  selfAdj i X Y := by
    simp only [algForm_apply, LinearMap.mulLeft_apply, star_mul, M.selfAdjoint, mul_assoc]
  ξ := M.projection 0
  fixA := by simp only [LinearMap.mulLeft_apply, M.idempotent]
  unit := by
    simp only [algForm_apply, ← probability_yesA]
    exact inv_mul_cancel₀ h.ne'

namespace WalkForm

variable (M : AlgebraicProjectiveData Letter A) (h : 0 < M.probability [(0, true)])

theorem ofAlgebraic_op (a : Outcome Letter) (X : A) :
    (ofAlgebraic M h).op a X = algebraicOutcome M.projection a * X := by
  rcases a with ⟨i, b⟩
  cases b
  · simp [op, ofAlgebraic, algebraicOutcome, sub_mul]
  · simp [op, ofAlgebraic, algebraicOutcome]

theorem ofAlgebraic_seqL (u : Word Letter) (X : A) :
    (ofAlgebraic M h).seqL u X = u.foldl (fun Y a => algebraicOutcome M.projection a * Y) X := by
  induction u generalizing X with
  | nil => rfl
  | cons a u ih => rw [seqL_cons_apply, ih, ofAlgebraic_op, List.foldl_cons]

/-- Path vectors are word amplitudes after a leading yes on `A`. -/
theorem ofAlgebraic_vec (u : Word Letter) :
    (ofAlgebraic M h).vec u = wordAmplitude M.projection ((0, true) :: u) := by
  rw [vec, ofAlgebraic_seqL, wordAmplitude, List.foldl_cons]
  simp [algebraicOutcome, ofAlgebraic]

/-- Squares of path vectors are conditional word probabilities:
`‖[u]‖² = Pr((A, u)) / Pr(A)`. -/
theorem ofAlgebraic_normSq_vec (u : Word Letter) :
    (ofAlgebraic M h).normSq ((ofAlgebraic M h).vec u) =
      M.probability ((0, true) :: u) / M.probability [(0, true)] := by
  rw [ofAlgebraic_vec, normSq]
  change (M.probability [(0, true)])⁻¹ * M.state (star _ * _) = _
  rw [div_eq_inv_mul]
  rfl

/-- Reproduction of a table `f` (from `p_A`) on a word set, in probability form. -/
theorem ofAlgebraic_reproduces (S : Set (Word Letter)) (f : Word Letter → ℝ)
    (hf : ∀ u ∈ S, M.probability ((0, true) :: u) / M.probability [(0, true)] = f u) :
    (ofAlgebraic M h).Reproduces S f := fun u hu => by
  rw [ofAlgebraic_normSq_vec]; exact hf u hu

end WalkForm
end Algebraic

/-- Real or complex Hilbert-space model (bridge `HilbertProjectiveData.toAlgebraic`). -/
def WalkForm.ofHilbert {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [CompleteSpace H] (M : HilbertProjectiveData Letter 𝕜 H)
    (h : 0 < M.toAlgebraic.probability [(0, true)]) :
    WalkForm (HilbertOperatorAlgebra 𝕜 H) :=
  WalkForm.ofAlgebraic M.toAlgebraic h

/-- Right quaternionic Hilbert model (bridge `QuaternionicProjectiveData.toAlgebraic`). -/
def WalkForm.ofQuaternionic {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {Q : QuaternionicOperatorStructure H}
    (M : QuaternionicProjectiveData Letter Q)
    (h : 0 < M.toAlgebraic.probability [(0, true)]) : WalkForm Q.operatorAlgebra :=
  WalkForm.ofAlgebraic M.toAlgebraic h

theorem WalkForm.ofHilbert_normSq_vec {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H] (M : HilbertProjectiveData Letter 𝕜 H)
    (h : 0 < M.toAlgebraic.probability [(0, true)]) (u : Word Letter) :
    (WalkForm.ofHilbert M h).normSq ((WalkForm.ofHilbert M h).vec u) =
      M.toAlgebraic.probability ((0, true) :: u) / M.toAlgebraic.probability [(0, true)] :=
  WalkForm.ofAlgebraic_normSq_vec M.toAlgebraic h u

theorem WalkForm.ofQuaternionic_normSq_vec {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {Q : QuaternionicOperatorStructure H}
    (M : QuaternionicProjectiveData Letter Q)
    (h : 0 < M.toAlgebraic.probability [(0, true)]) (u : Word Letter) :
    (WalkForm.ofQuaternionic M h).normSq ((WalkForm.ofQuaternionic M h).vec u) =
      M.toAlgebraic.probability ((0, true) :: u) / M.toAlgebraic.probability [(0, true)] :=
  WalkForm.ofAlgebraic_normSq_vec M.toAlgebraic h u

end AlbertSequential.LengthSeven
