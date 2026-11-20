/- SPDX-License-Identifier: Apache-2.0 -/
module
public import FixedUnitaryHistories
public import Bridge.Matrix
public import ComplexPositiveFactor
public import BlockB.ElevenSupport

@[expose] public section
noncomputable section

namespace AlbertSequential.FixedUnitary
open Matrix
open scoped ComplexOrder
open AlbertChallenge.Bridge
variable {d n : ℕ}
local notation "Mat" => Matrix (Fin d) (Fin d) ℂ

/-- Chronological amplitude for a unitary applied before each test. -/
def interleaved (Y : Mat) (P : Fin n → Mat) (w : Word (Fin n)) : Mat :=
  w.foldl (fun A q => algebraicOutcome P q * (Y*A)) 1

private def leftUnitary (Y : unitary Mat) : Mat ≃ₗ[ℂ] Mat where
  toLinearMap := LinearMap.mulLeft ℂ (Y : Mat)
  invFun X := (Y : Mat)ᴴ * X
  left_inv X := by
    change (Y : Mat)ᴴ * ((Y : Mat)*X) = X
    rw [← Matrix.mul_assoc,show (Y : Mat)ᴴ * Y = 1 from Unitary.coe_star_mul_self Y,Matrix.one_mul]
  right_inv X := by
    change (Y : Mat) * ((Y : Mat)ᴴ*X) = X
    rw [← Matrix.mul_assoc,show (Y : Mat) * (Y : Mat)ᴴ = 1 from Unitary.coe_mul_star_self Y,Matrix.one_mul]

private theorem leftAnswer (P : Fin n → Mat) (q : Outcome (Fin n)) (X : Mat) :
    answer (fun i => LinearMap.mulLeft ℂ (P i)) q X = algebraicOutcome P q * X := by
  obtain ⟨i,b⟩ := q
  cases b
  · change X-P i*X = (1-P i)*X
    rw [Matrix.sub_mul, Matrix.one_mul]
  · rfl

private def mass (A : Mat) := (A*Aᴴ).trace

private theorem mass_unitary (Y : unitary Mat) (A : Mat) : mass ((Y : Mat)*A) = mass A := by
  unfold mass
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.trace_mul_comm (Y : Mat),
    Matrix.mul_assoc, Matrix.mul_assoc,show (Y : Mat)ᴴ * Y = 1 from Unitary.coe_star_mul_self Y, Matrix.mul_one]

/-- The reduction only needs zero opposite-repeat probabilities after every history. -/
theorem exists_projective_of_fixedUnitary_noSwitch (Y : unitary Mat) (P : Fin n → Mat)
    (hP : ∀ i, (P i).IsHermitian) (hPP : ∀ i, P i * P i = P i)
    (ρ : Mat) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (f : Word (Fin n) → ℝ) (zero : ∀ w i (b : Bool), f (w++[(i,b),(i,!b)]) = 0)
    (hm : ∀ w, ((interleaved Y P w * ρ) * (interleaved Y P w)ᴴ).trace = (f w : ℂ)) :
    ∃ M : AlbertChallenge.ProjectiveRepresentation n ℂ (EuclideanSpace ℂ (Fin d)),
      ∀ w, M.probability w = f w := by
  obtain ⟨B,hB⟩ := exists_complexPositiveFactor hρ
  let X := (Y : Mat)*B
  let T := fun i => LinearMap.mulLeft ℂ (P i)
  let U := leftUnitary Y
  have form (w : Word (Fin n)) : trajectory U T X w = (Y : Mat)*(interleaved Y P w * B) := by
    induction w using List.reverseRecOn with
    | nil => simp [trajectory,interleaved,X]
    | append_singleton w q ih =>
      rw [trajectory_snoc,ih,leftAnswer]
      change (Y : Mat) * _ = (Y : Mat) * _
      simp [interleaved,List.foldl_append,Matrix.mul_assoc]
  have prob (w : Word (Fin n)) : mass (trajectory U T X w) = (f w : ℂ) := by
    rw [form,mass_unitary,← hm w,hB]
    simp [mass,Matrix.mul_assoc]
  have kill (w : Word (Fin n)) (i : Fin n) (b : Bool) :
      answer T (i,!b) (U (answer T (i,b) (trajectory U T X w))) = 0 := by
    have hz := prob (w++[(i,b),(i,!b)])
    rw [zero] at hz
    have hn := Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp (show mass _ = 0 from hz)
    rw [show w++[(i,b),(i,!b)] = (w++[(i,b)])++[(i,!b)] by simp] at hn
    rw [trajectory_snoc,trajectory_snoc] at hn
    exact U.injective (hn.trans U.map_zero.symm)
  have pure (w : Word (Fin n)) : w.foldl (fun v q => answer T q v) X = wordAmplitude P w * X := by
    induction w using List.reverseRecOn with
    | nil => simp [wordAmplitude]
    | append_singleton w q ih =>
      rw [List.foldl_append]
      change answer T q _ = _
      rw [ih,leftAnswer]
      simp [wordAmplitude,List.foldl_append,Matrix.mul_assoc]
  have powers (k : ℕ) (A : Mat) : mass ((U.toLinearMap^k) A) = mass A := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ']
      exact (mass_unitary Y _).trans ih
  have ht : (X*Xᴴ).trace = 1 := (mass_unitary Y B).trans (by change (B*Bᴴ).trace = 1; rwa [← hB])
  refine ⟨matrixRepresentation P hP hPP (X*Xᴴ) (Matrix.posSemidef_self_mul_conjTranspose X) ht,?_⟩
  intro w
  rw [matrixRepresentation_probability]
  have he := prob w
  rw [remove_between U T X kill,powers,pure] at he
  have hcyc : mass (wordAmplitude P w * X) = ((X*Xᴴ) * wordOperator P w).trace := by
    unfold mass wordOperator
    rw [Matrix.conjTranspose_mul,Matrix.mul_assoc,Matrix.trace_mul_comm (wordAmplitude P w)]
    simp only [Matrix.mul_assoc, Matrix.star_eq_conjTranspose]
  exact congrArg Complex.re (hcyc.symm.trans he)

/-- A fixed pre-test unitary that reproduces an ideal Albert table can be
removed, retaining the same projections and rotating the initial density. -/
theorem exists_projective_of_fixedUnitary (Y : unitary Mat) (P : Fin n → Mat)
    (hP : ∀ i, (P i).IsHermitian) (hPP : ∀ i, P i * P i = P i)
    (ρ : Mat) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (p : Fin n → Albert) (s : Albert) (hp : ∀ i, jordanMul (p i) (p i) = p i)
    (hm : ∀ w, ((interleaved Y P w * ρ) * (interleaved Y P w)ᴴ).trace =
      (nativeWordProbability p s w : ℂ)) :
    ∃ M : AlbertChallenge.ProjectiveRepresentation n ℂ (EuclideanSpace ℂ (Fin d)),
      ∀ w, M.probability w = nativeWordProbability p s w := by
  have zero (w : Word (Fin n)) (i : Fin n) (b : Bool) :
      nativeWordProbability p s (w++[(i,b),(i,!b)]) = 0 := by
    unfold nativeWordProbability nativeBranchState
    rw [List.foldl_append]
    change albertTrace (quadraticMap (nativeOutcome p (i,!b))
      (quadraticMap (nativeOutcome p (i,b)) (nativeBranchState p s w))) = 0
    rw [BlockB.quadraticMap_nativeOutcome_opposite p hp i _ _ (by cases b <;> decide)]
    change (∑ _ : Fin 3, (0 : ℝ)) = 0
    simp
  exact exists_projective_of_fixedUnitary_noSwitch Y P hP hPP ρ hρ htr _ zero hm

end AlbertSequential.FixedUnitary
