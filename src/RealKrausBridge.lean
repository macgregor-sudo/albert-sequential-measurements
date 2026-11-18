/- SPDX-License-Identifier: Apache-2.0 -/
module

public import RealSpectralSupport
public import LinearMapChoi
public import InstrumentFactorization

/-! Literal real Kraus action/effect and complexification on ALL complex
inputs. Realness lemmas use the existing completion formulas. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential
open scoped Matrix ComplexOrder BigOperators

def realKrausAction {d : ℕ} (K : List (Matrix (Fin d) (Fin d) ℝ))
    (Y : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  (K.map (fun V => V*Y*V.transpose)).sum

def realKrausEffect {d : ℕ} (K : List (Matrix (Fin d) (Fin d) ℝ)) :
    Matrix (Fin d) (Fin d) ℝ := (K.map (fun V => V.transpose*V)).sum

theorem complexify_realKrausAction {d : ℕ} (K : List (Matrix (Fin d) (Fin d) ℝ))
    (Y : Matrix (Fin d) (Fin d) ℝ) :
    complexifyMatrix (realKrausAction K Y) = krausAction (K.map complexifyMatrix) (complexifyMatrix Y) := by
  induction K with
  | nil => exact complexifyMatrix_zero
  | cons V K ih =>
    change complexifyMatrix (V*Y*V.transpose + realKrausAction K Y) =
      complexifyMatrix V * complexifyMatrix Y * (complexifyMatrix V).conjTranspose +
        krausAction (K.map complexifyMatrix) (complexifyMatrix Y)
    rw [complexifyMatrix_add, complexifyMatrix_mul, complexifyMatrix_mul,
      complexifyMatrix_transpose, ih]

theorem complexify_realKrausEffect {d : ℕ} (K : List (Matrix (Fin d) (Fin d) ℝ)) :
    complexifyMatrix (realKrausEffect K) = krausEffect (K.map complexifyMatrix) := by
  induction K with
  | nil => exact complexifyMatrix_zero
  | cons V K ih =>
    change complexifyMatrix (V.transpose*V + realKrausEffect K) =
      (complexifyMatrix V).conjTranspose * complexifyMatrix V + krausEffect (K.map complexifyMatrix)
    rw [complexifyMatrix_add, complexifyMatrix_mul, complexifyMatrix_transpose, ih]

/-- In particular this covers nonreal, non-Hermitian inputs; agreement only
on embedded real matrices would not be the stated complex map identity. -/
theorem complexifiedKrausAction_all_complex_inputs {d : ℕ}
    (K : List (Matrix (Fin d) (Fin d) ℝ)) (X : ComplexMatrix d) :
    krausAction (K.map complexifyMatrix) X =
      complexifyMatrix (realKrausAction K (realPartMatrix X)) +
        Complex.I • complexifyMatrix (realKrausAction K (imaginaryPartMatrix X)) := by
  let KC := K.map complexifyMatrix
  have hl : krausAction KC
      (complexifyMatrix (realPartMatrix X) + Complex.I • complexifyMatrix (imaginaryPartMatrix X)) =
      krausAction KC (complexifyMatrix (realPartMatrix X)) +
        Complex.I • krausAction KC (complexifyMatrix (imaginaryPartMatrix X)) := by
    have h := (choiLinearMap (krausChoi KC)).map_add
      (complexifyMatrix (realPartMatrix X)) (Complex.I • complexifyMatrix (imaginaryPartMatrix X))
    rw [map_smul] at h
    simpa only [choiLinearMap, LinearMap.coe_mk, AddHom.coe_mk, krausChoi_action] using h
  calc
    _ = krausAction KC
        (complexifyMatrix (realPartMatrix X) + Complex.I • complexifyMatrix (imaginaryPartMatrix X)) :=
      congrArg (krausAction KC) (complexMatrix_real_imaginary_decomposition X)
    _ = _ := hl
    _ = _ := by rw [← complexify_realKrausAction, ← complexify_realKrausAction]

theorem complexify_recovered_realKraus {d : ℕ} (K : List (ComplexMatrix d))
    (hK : ∀ V ∈ K, HasRealEntries V) : (K.map realPartMatrix).map complexifyMatrix = K := by
  rw [List.map_map]
  have h : K.map (fun V => complexifyMatrix (realPartMatrix V)) = K.map id := by
    apply List.map_congr_left
    intro V hV
    exact complexify_realPart_of_hasRealEntries V (hK V hV)
  simpa only [List.map_id, Function.comp_def] using h

theorem krausEffect_hasRealEntries {d : ℕ} (K : List (ComplexMatrix d))
    (hK : ∀ W ∈ K, HasRealEntries W) : HasRealEntries (krausEffect K) := by
  have he := complexify_realKrausEffect (K.map realPartMatrix)
  rw [complexify_recovered_realKraus K hK] at he
  rw [← he]
  exact complexifyMatrix_hasRealEntries _

theorem krausAction_hasRealEntries {d : ℕ} (K : List (ComplexMatrix d))
    (X : ComplexMatrix d) (hK : ∀ W ∈ K, HasRealEntries W)
    (hX : HasRealEntries X) : HasRealEntries (krausAction K X) := by
  have he := complexify_realKrausAction (K.map realPartMatrix) (realPartMatrix X)
  rw [complexify_recovered_realKraus K hK, complexify_realPart_of_hasRealEntries X hX] at he
  rw [← he]
  exact complexifyMatrix_hasRealEntries _

theorem real_smul_hasRealEntries {d : ℕ} (r : ℝ) (X : ComplexMatrix d)
    (hX : HasRealEntries X) : HasRealEntries (r • X) := by
  intro i j
  change (r • X i j).im = 0
  rw [Complex.real_smul, Complex.mul_im, hX i j]
  simp

theorem realEntries_mul {m n k : Type*} [Fintype n]
    (A : Matrix m n ℂ) (B : Matrix n k ℂ)
    (hA : ∀ i j, (A i j).im=0) (hB : ∀ i j, (B i j).im=0) :
    ∀ i j, ((A*B) i j).im=0 := by
  intro i j
  rw [← complexify_realPart_of_imag_eq_zero A hA,
    ← complexify_realPart_of_imag_eq_zero B hB, ← complexifyMatrix_mul]
  rfl

theorem realEntries_conjTranspose {m n : Type*} (A : Matrix m n ℂ)
    (hA : ∀ i j, (A i j).im=0) : ∀ i j, (A.conjTranspose i j).im=0 := by
  intro i j
  simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_im, hA, neg_zero]

theorem hasRealEntries_one (d : ℕ) : HasRealEntries (1 : ComplexMatrix d) := by
  intro i j
  by_cases h : i=j <;> simp [Matrix.one_apply, h]

theorem hasRealEntries_sub {d : ℕ} (A B : ComplexMatrix d)
    (hA : HasRealEntries A) (hB : HasRealEntries B) : HasRealEntries (A-B) := by
  intro i j
  change (A i j-B i j).im=0
  rw [Complex.sub_im, hA, hB, sub_self]

theorem measurePrepareMatrix_hasRealEntries {d : ℕ} (B Q : ComplexMatrix d)
    (hB : HasRealEntries B) (hQ : HasRealEntries Q) (a b : Fin d) :
    HasRealEntries (measurePrepareMatrix B Q a b) := by
  intro i j
  change (B i a * Q b j).im=0
  rw [Complex.mul_im, hB, hQ, mul_zero, zero_mul, add_zero]

theorem measurePrepareKraus_hasRealEntries {d : ℕ} (B Q : ComplexMatrix d)
    (hB : HasRealEntries B) (hQ : HasRealEntries Q) :
    ∀ W ∈ measurePrepareKraus B Q, HasRealEntries W := by
  intro W hW
  rcases List.mem_map.mp hW with ⟨k,hk,rfl⟩
  exact measurePrepareMatrix_hasRealEntries B Q hB hQ k.1 k.2

theorem completedKraus_hasRealEntries {d : ℕ} (K : List (ComplexMatrix d))
    (s : FiniteSpectralSupport (krausEffect K)) (B : ComplexMatrix d)
    (hK : ∀ W ∈ K, HasRealEntries W) (hR : HasRealEntries s.inverseRoot)
    (hP : HasRealEntries s.support) (hB : HasRealEntries B) :
    ∀ W ∈ completedKraus K s B, HasRealEntries W := by
  intro W hW
  rcases List.mem_append.mp hW with hleft | hright
  · rcases List.mem_map.mp hleft with ⟨V,hV,rfl⟩
    exact realEntries_mul V s.inverseRoot (hK V hV) hR
  · exact measurePrepareKraus_hasRealEntries B (1-s.support) hB
      (hasRealEntries_sub 1 s.support (hasRealEntries_one d) hP) W hright

/-- This is the literal lift-list expression used by the root construction.
No wrapper module for it is needed. -/
theorem isometricLift_list_hasRealEntries {d D : ℕ} (K : List (ComplexMatrix d))
    (ι V : Matrix (Fin D) (Fin d) ℂ) (hK : ∀ W ∈ K, HasRealEntries W)
    (hι : ∀ i j, (ι i j).im=0) (hV : ∀ i j, (V i j).im=0) :
    ∀ W ∈ K.map (fun A => ι*A*V.conjTranspose), HasRealEntries W := by
  intro W hW
  rcases List.mem_map.mp hW with ⟨A,hA,rfl⟩
  exact realEntries_mul (ι*A) V.conjTranspose (realEntries_mul ι A hι (hK A hA))
    (realEntries_conjTranspose V hV)

theorem isometricCompletion_list_hasRealEntries {d D : ℕ} (K : List (ComplexMatrix d))
    (ι V : Matrix (Fin D) (Fin d) ℂ) (B : ComplexMatrix D)
    (hK : ∀ W ∈ K, HasRealEntries W) (hι : ∀ i j, (ι i j).im=0)
    (hV : ∀ i j, (V i j).im=0) (hB : HasRealEntries B) :
    ∀ W ∈ K.map (fun A => ι*A*V.conjTranspose) ++
      measurePrepareKraus B (1-V*V.conjTranspose), HasRealEntries W := by
  intro W hW
  rcases List.mem_append.mp hW with hleft | hright
  · exact isometricLift_list_hasRealEntries K ι V hK hι hV W hleft
  · exact measurePrepareKraus_hasRealEntries B (1-V*V.conjTranspose) hB
      (hasRealEntries_sub _ _ (hasRealEntries_one D)
        (realEntries_mul V V.conjTranspose hV (realEntries_conjTranspose V hV))) W hright

/-- The same actual channel factorization can be chosen with real entries when
the input Kraus matrices and the reset density have real entries. Its action
identity still holds on every complex matrix. -/
theorem exists_real_kraus_channel_factorization {d : ℕ} (K : List (ComplexMatrix d))
    (hK : ∀ W ∈ K, HasRealEntries W) {τ : ComplexMatrix d}
    (hτ : IsMatrixDensity τ) (hτreal : HasRealEntries τ) :
    ∃ S : ComplexMatrix d, ∃ L : List (ComplexMatrix d),
      S.PosSemidef ∧ S*S = krausEffect K ∧ krausEffect L = 1 ∧ HasRealEntries S ∧
      (∀ W ∈ L, HasRealEntries W) ∧
      ∀ X, krausAction L (S*X*S) = krausAction K X := by
  let s := realFiniteSpectralSupport (krausEffect_positive K) (krausEffect_hasRealEntries K hK)
  obtain ⟨B, hBreal, hB⟩ := exists_real_positiveFactor hτ.1 hτreal
  have hs := realFiniteSpectralSupport_real (krausEffect_positive K) (krausEffect_hasRealEntries K hK)
  refine ⟨s.root, completedKraus K s B, s.root_positive, s.root_sq, ?_, hs.1, ?_, ?_⟩
  · exact completedKraus_effect K s B (by rw [hB]; exact hτ.2)
  · exact completedKraus_hasRealEntries K s B hK hs.2.1 hs.2.2 hBreal
  · exact completedKraus_factorization K s B

end AlbertSequential
