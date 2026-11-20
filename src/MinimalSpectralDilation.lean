/- SPDX-License-Identifier: Apache-2.0 -/
module
public import BinaryProjectionDilation
public import SharpDilationRank

@[expose] public section
noncomputable section
namespace AlbertSequential
open Matrix
open scoped ComplexOrder
variable {𝕜 n m : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The spectral defect rank counts the non-idempotent eigenvalue slots. -/
theorem rank_spectralDefect (U : unitary (Matrix n n 𝕜)) (a : n → ℝ) :
    (unitaryRealDiagonal U a - unitaryRealDiagonal U a ^ 2).rank =
      Fintype.card {i : n // a i - a i * a i ≠ 0} := by
  classical
  rw [pow_two, unitaryRealDiagonal_mul, unitaryRealDiagonal_sub]
  unfold unitaryRealDiagonal
  rw [Unitary.conjStarAlgAut_apply]
  have hu : IsUnit (U.val).det := (Unitary.isUnit_coe (U := U)).map Matrix.detMonoidHom
  have hs : IsUnit (star U.val).det := (Unitary.isUnit_coe (U := star U)).map Matrix.detMonoidHom
  rw [rank_mul_eq_left_of_isUnit_det _ _ hs, rank_mul_eq_right_of_isUnit_det _ _ hu, rank_diagonal]
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight fun i => by
    change ((a i - a i * a i : ℝ) : 𝕜) ≠ 0 ↔ a i - a i * a i ≠ 0
    exact not_congr RCLike.ofReal_eq_zero

/-- A selected row of the coordinate restriction, padded with zeros on unused ancillary coordinates. -/
def defectSelector (a : n → ℝ) (e : {i // a i - a i * a i ≠ 0} ↪ m) :
    Matrix m n 𝕜 := fun j i => if hi : a i - a i * a i ≠ 0 then
      if j = e ⟨i, hi⟩ then 1 else 0 else 0

omit [Fintype n] in
theorem defectSelector_gram (a : n → ℝ) (e : {i // a i - a i * a i ≠ 0} ↪ m) :
    (defectSelector (𝕜 := 𝕜) a e)ᴴ * defectSelector (𝕜 := 𝕜) a e =
      diagonal (fun i => if a i - a i * a i ≠ 0 then 1 else 0) := by
  classical
  ext i j
  by_cases hi : a i - a i * a i ≠ 0
  · by_cases hj : a j - a j * a j ≠ 0
    · by_cases hij : i = j
      · subst j
        simp [Matrix.mul_apply, Matrix.conjTranspose_apply, defectSelector, hi]
      · simp [Matrix.mul_apply, Matrix.conjTranspose_apply, defectSelector, hi, hj, hij, Ne.symm hij]
    · have hij : i ≠ j := fun h => hj (h ▸ hi)
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, defectSelector, hj, hij]
  · by_cases hij : i = j
    · subst j; simp [Matrix.mul_apply, Matrix.conjTranspose_apply, defectSelector, hi]
    · simp [Matrix.mul_apply, Matrix.conjTranspose_apply, defectSelector, hi, hij]


/-- Restriction to the defect eigenvectors in the original coordinates. -/
def spectralDefectRestriction (U : unitary (Matrix n n 𝕜)) (a : n → ℝ)
    (e : {i // a i - a i * a i ≠ 0} ↪ m) : Matrix m n 𝕜 :=
  defectSelector a e * U.valᴴ

def defectIndicator (a : n → ℝ) (i : n) : ℝ := if a i - a i * a i ≠ 0 then 1 else 0

theorem spectralDefectRestriction_gram (U : unitary (Matrix n n 𝕜)) (a : n → ℝ)
    (e : {i // a i - a i * a i ≠ 0} ↪ m) :
    (spectralDefectRestriction U a e)ᴴ * spectralDefectRestriction U a e =
      unitaryRealDiagonal U (defectIndicator a) := by
  unfold spectralDefectRestriction unitaryRealDiagonal
  rw [conjTranspose_mul, conjTranspose_conjTranspose, Unitary.conjStarAlgAut_apply,
    ← Matrix.mul_assoc (U.val * _) _ _, Matrix.mul_assoc U.val _ _, defectSelector_gram]
  congr 2
  ext i j
  by_cases h : i = j
  · subst j; by_cases hi : a i - a i * a i ≠ 0 <;> simp [defectIndicator, hi]
  · simp [h]

omit [DecidableEq m] in
/-- Projection-valued Gram matrices make rectangular frames partial isometries. -/
theorem frame_mul_gram_of_idempotent {V : Matrix m n 𝕜}
    (h : (Vᴴ * V) * (Vᴴ * V) = Vᴴ * V) : V * (Vᴴ * V) = V := by
  have hz : (Vᴴ * V) * (Vᴴ * V - 1) = 0 := by rw [Matrix.mul_sub, h, Matrix.mul_one, sub_self]
  have hv := (Matrix.conjTranspose_mul_self_mul_eq_zero V _).mp hz
  simpa only [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] using hv

/-- A branch frame has its primary block in the input space and its second block
only on the non-idempotent eigenvalue slots. -/
def reducedSpectralFrame (U : unitary (Matrix n n 𝕜)) (a : n → ℝ)
    (e : {i // a i - a i * a i ≠ 0} ↪ m) (f g : n → ℝ) : Matrix (n ⊕ m) n 𝕜 :=
  fromRows (unitaryRealDiagonal U f) (spectralDefectRestriction U a e * unitaryRealDiagonal U g)

private theorem unitaryRealDiagonal_add (U : unitary (Matrix n n 𝕜)) (f g : n → ℝ) :
    unitaryRealDiagonal U f + unitaryRealDiagonal U g = unitaryRealDiagonal U (fun i => f i + g i) := by
  unfold unitaryRealDiagonal
  rw [← map_add, Matrix.diagonal_add]
  congr 1
  ext i
  simp

theorem reducedSpectralFrame_cross (U : unitary (Matrix n n 𝕜)) (a : n → ℝ)
    (e : {i // a i - a i * a i ≠ 0} ↪ m) (f g h k : n → ℝ) :
    (reducedSpectralFrame U a e f g)ᴴ * reducedSpectralFrame U a e h k =
    unitaryRealDiagonal U (fun i => f i * h i + g i * (defectIndicator a i * k i)) := by
  simp only [reducedSpectralFrame, conjTranspose_fromRows_eq_fromCols_conjTranspose,
    fromCols_mul_fromRows, conjTranspose_mul, unitaryRealDiagonal_hermitian]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (spectralDefectRestriction U a e)ᴴ,
    spectralDefectRestriction_gram, unitaryRealDiagonal_mul, unitaryRealDiagonal_mul,
    unitaryRealDiagonal_mul, unitaryRealDiagonal_add]

/-- In a diagonal slot the two Grams are support indicators, and the cross Gram vanishes. -/
theorem reducedSpectralFrame_scalar (x : ℝ) (hx : 0 ≤ x) (hc : x ≤ 1) :
    let t : ℝ := if x - x*x ≠ 0 then 1 else 0
    let s := Real.sqrt x
    let c := Real.sqrt (1-x)
    (s*s + c*(t*c) = if x = 0 then 0 else 1) ∧
    (c*c + (-s)*(t*(-s)) = if x = 1 then 0 else 1) ∧ s*c + c*(t*(-s)) = 0 := by
  dsimp only
  by_cases h0 : x = 0
  · subst x; norm_num
  by_cases h1 : x = 1
  · subst x; norm_num
  have h : x - x*x ≠ 0 := by
    rw [show x-x*x = x*(1-x) by ring]
    exact mul_ne_zero h0 (sub_ne_zero.mpr (Ne.symm h1))
  simp only [h, h0, h1, ne_eq, not_false_eq_true, ite_true, ite_false, one_mul, mul_neg,
    neg_mul, neg_neg]
  have hs := Real.mul_self_sqrt hx
  have hcs := Real.mul_self_sqrt (sub_nonneg.mpr hc)
  constructor
  · linarith
  constructor
  · linarith
  · ring

theorem reducedSpectralFrame_partial {f g : n → ℝ} (U : unitary (Matrix n n 𝕜)) (a : n → ℝ)
    (e : {i // a i - a i * a i ≠ 0} ↪ m)
    (hid : ∀ i, let v := f i * f i + g i * (defectIndicator a i * g i); v * v = v) :
    let V := reducedSpectralFrame U a e f g
    V * (Vᴴ * V) = V := by
  apply frame_mul_gram_of_idempotent
  rw [reducedSpectralFrame_cross, unitaryRealDiagonal_mul]
  exact congrArg (unitaryRealDiagonal U) (funext hid)

theorem reducedSpectralFrame_data (U : unitary (Matrix n n 𝕜)) (a : n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hc : ∀ i, a i ≤ 1) (e : {i // a i - a i * a i ≠ 0} ↪ m) :
    let s := fun i => Real.sqrt (a i)
    let c := fun i => Real.sqrt (1-a i)
    let V := reducedSpectralFrame U a e s c
    let W := reducedSpectralFrame U a e c (fun i => -s i)
    let J : Matrix (n ⊕ m) n 𝕜 := fromRows 1 0
    V*(Vᴴ*V)=V ∧ W*(Wᴴ*W)=W ∧ Vᴴ*W=0 ∧
    Vᴴ*J=unitaryRealDiagonal U s ∧ Wᴴ*J=unitaryRealDiagonal U c ∧
    J=V*unitaryRealDiagonal U s + W*unitaryRealDiagonal U c := by
  dsimp only
  have scalar := fun i => reducedSpectralFrame_scalar (a i) (ha i) (hc i)
  refine ⟨reducedSpectralFrame_partial U a e ?_, reducedSpectralFrame_partial U a e ?_, ?_, ?_, ?_, ?_⟩
  · intro i; dsimp only [defectIndicator]; rw [(scalar i).1]; split <;> norm_num
  · intro i; dsimp only [defectIndicator]; rw [(scalar i).2.1]; split <;> norm_num
  · rw [reducedSpectralFrame_cross, ← unitaryRealDiagonal_zero U]
    exact congrArg (unitaryRealDiagonal U) (funext fun i => (scalar i).2.2)
  · simp [reducedSpectralFrame, conjTranspose_fromRows_eq_fromCols_conjTranspose,
      fromCols_mul_fromRows, unitaryRealDiagonal_hermitian]
  · simp [reducedSpectralFrame, conjTranspose_fromRows_eq_fromCols_conjTranspose,
      fromCols_mul_fromRows, unitaryRealDiagonal_hermitian]
  · simp only [reducedSpectralFrame, fromRows_mul, Matrix.mul_assoc, unitaryRealDiagonal_mul]
    let D := spectralDefectRestriction U a e
    have top : unitaryRealDiagonal U (fun i => Real.sqrt (a i) * Real.sqrt (a i)) +
        unitaryRealDiagonal U (fun i => Real.sqrt (1-a i) * Real.sqrt (1-a i)) = 1 := by
      rw [unitaryRealDiagonal_add, ← unitaryRealDiagonal_one U]
      apply congrArg (unitaryRealDiagonal U)
      funext i; rw [Real.mul_self_sqrt (ha i), Real.mul_self_sqrt (sub_nonneg.mpr (hc i))]; ring
    have bot : D * unitaryRealDiagonal U (fun i => Real.sqrt (1-a i) * Real.sqrt (a i)) +
        D * unitaryRealDiagonal U (fun i => -Real.sqrt (a i) * Real.sqrt (1-a i)) = 0 := by
      rw [← Matrix.mul_add, unitaryRealDiagonal_add]
      simp only [show (fun i => Real.sqrt (1-a i)*Real.sqrt (a i) +
        -Real.sqrt (a i)*Real.sqrt (1-a i)) = (fun _ => 0) by funext i; ring,
        unitaryRealDiagonal_zero, Matrix.mul_zero]
    ext i j; cases i with
    | inl i => exact congrFun (congrFun top.symm i) j
    | inr i => exact congrFun (congrFun bot.symm i) j

end AlbertSequential
