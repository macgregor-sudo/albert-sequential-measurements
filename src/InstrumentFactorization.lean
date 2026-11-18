/- SPDX-License-Identifier: Apache-2.0 -/
module
public import KrausSupport
public import FiniteSpectralSupport

/-! Every finite Kraus operation factors through its positive square root,
followed by a channel. The channel is completed on the zero-effect subspace
by an explicit measure-and-prepare operation. All identities hold on ALL matrices. -/
@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder
namespace AlbertSequential

theorem krausAction_append {d : ℕ} (K L : List (ComplexMatrix d)) (X : ComplexMatrix d) :
    krausAction (K ++ L) X = krausAction K X + krausAction L X := by
  simp [krausAction]

theorem krausEffect_append {d : ℕ} (K L : List (ComplexMatrix d)) :
    krausEffect (K ++ L) = krausEffect K + krausEffect L := by
  simp [krausEffect]

theorem krausAction_right_multiply {d : ℕ} (K : List (ComplexMatrix d))
    (R X : ComplexMatrix d) :
    krausAction (K.map (fun V => V * R)) X = krausAction K (R * X * R.conjTranspose) := by
  induction K with
  | nil => simp [krausAction]
  | cons V K ih =>
      simpa only [List.map_cons, krausAction, List.sum_cons, Matrix.conjTranspose_mul,
        Matrix.mul_assoc] using congrArg (fun Y => (V * R) * X * (V * R).conjTranspose + Y) ih

theorem krausAction_support_compression {d : ℕ} (K : List (ComplexMatrix d))
    (P X : ComplexMatrix d) (hstar : P.conjTranspose = P)
    (hP : ∀ V ∈ K, V * P = V) : krausAction K (P * X * P) = krausAction K X := by
  unfold krausAction
  congr 1
  apply List.map_congr_left
  intro V hV
  have hp := hP V hV
  have hpstar : P * V.conjTranspose = V.conjTranspose := by
    simpa [Matrix.conjTranspose_mul, hstar] using congrArg Matrix.conjTranspose hp
  calc
    V * (P * X * P) * V.conjTranspose = (V * P) * X * (P * V.conjTranspose) := by
      simp only [Matrix.mul_assoc]
    _ = V * X * V.conjTranspose := by rw [hp, hpstar]

def completedKraus {d : ℕ} (K : List (ComplexMatrix d))
    (s : FiniteSpectralSupport (krausEffect K)) (B : ComplexMatrix d) :
    List (ComplexMatrix d) :=
  K.map (fun V => V * s.inverseRoot) ++ measurePrepareKraus B (1 - s.support)

theorem support_complement_hermitian {d : ℕ} {A : ComplexMatrix d}
    (s : FiniteSpectralSupport A) : (1 - s.support).conjTranspose = 1 - s.support := by
  simp [Matrix.conjTranspose_sub, s.support_hermitian]

theorem support_complement_idempotent {d : ℕ} {A : ComplexMatrix d}
    (s : FiniteSpectralSupport A) : (1 - s.support) * (1 - s.support) = 1 - s.support := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, s.support_sq]
  abel

theorem completedKraus_effect {d : ℕ} (K : List (ComplexMatrix d))
    (s : FiniteSpectralSupport (krausEffect K)) (B : ComplexMatrix d)
    (hB : Matrix.trace (B * B.conjTranspose) = 1) :
    krausEffect (completedKraus K s B) = 1 := by
  rw [completedKraus, krausEffect_append, krausEffect_right_multiply,
    s.inverse_hermitian, s.inverse_effect, measurePrepareKraus_effect, hB,
    one_smul, support_complement_hermitian, support_complement_idempotent]
  abel

/-- The printed channel formula, with no positivity restriction on its input. -/
theorem completedKraus_action {d : ℕ} (K : List (ComplexMatrix d))
    (s : FiniteSpectralSupport (krausEffect K)) (B Y : ComplexMatrix d) :
    krausAction (completedKraus K s B) Y =
      krausAction K (s.inverseRoot * Y * s.inverseRoot) +
        Matrix.trace ((1 - s.support) * Y) • (B * B.conjTranspose) := by
  rw [completedKraus, krausAction_append, krausAction_right_multiply,
    s.inverse_hermitian, measurePrepareKraus_action, support_complement_hermitian]
  congr 2
  rw [Matrix.trace_mul_cycle, support_complement_idempotent]

theorem completedKraus_factorization {d : ℕ} (K : List (ComplexMatrix d))
    (s : FiniteSpectralSupport (krausEffect K)) (B X : ComplexMatrix d) :
    krausAction (completedKraus K s B) (s.root * X * s.root) = krausAction K X := by
  rw [completedKraus_action]
  have hQR : (1 - s.support) * s.root = 0 := by
    simpa [Matrix.conjTranspose_mul, s.root_hermitian, s.support_hermitian] using
      congrArg Matrix.conjTranspose s.root_complement
  have hreset : (1 - s.support) * (s.root * X * s.root) = 0 := by
    calc
      _ = ((1 - s.support) * s.root) * X * s.root := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hQR]; simp
  rw [hreset, Matrix.trace_zero, zero_smul, add_zero]
  have hcompress : s.inverseRoot * (s.root * X * s.root) * s.inverseRoot =
      s.support * X * s.support := by
    calc
      _ = (s.inverseRoot * s.root) * X * (s.root * s.inverseRoot) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [s.inverse_root, s.root_inverse]
  rw [hcompress]
  exact krausAction_support_compression K s.support X s.support_hermitian
    (kraus_support_right K s.support s.effect_complement)

/-- An actual channel and positive root exist for every finite CP operation
and every density chosen to complete its zero-effect subspace. -/
theorem exists_kraus_channel_factorization {d : ℕ} (K : List (ComplexMatrix d))
    {τ : ComplexMatrix d} (hτ : IsMatrixDensity τ) :
    ∃ S : ComplexMatrix d, ∃ L : List (ComplexMatrix d),
      S.PosSemidef ∧ S * S = krausEffect K ∧ krausEffect L = 1 ∧
      ∀ X, krausAction L (S * X * S) = krausAction K X := by
  obtain ⟨B, hB⟩ := exists_complexPositiveFactor hτ.1
  let s := finiteSpectralSupport (krausEffect_positive K)
  refine ⟨s.root, completedKraus K s B, s.root_positive, s.root_sq, ?_, ?_⟩
  · exact completedKraus_effect K s B (hB ▸ hτ.2)
  · exact completedKraus_factorization K s B

#print axioms exists_kraus_channel_factorization
end AlbertSequential
