module

public import ChoiKrausEquivalence
public import DefaultChoiModel

/-! Ordinary finite matrix complete positivity, proved by all finite ancillas.
This explicit coordinate definition avoids importing a broader C*-algebra
framework or assuming the Choi theorem as an uninterpreted interface.
-/
@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder
namespace AlbertSequential

abbrev AncillaMatrix (n d : ℕ) :=
  Matrix (Fin n × Fin d) (Fin n × Fin d) ℂ

def matrixAmplification {d : ℕ} (Phi : ComplexMatrix d → ComplexMatrix d)
    (n : ℕ) (Y : AncillaMatrix n d) : AncillaMatrix n d :=
  fun ak bl => Phi (fun i j => Y (ak.1, i) (bl.1, j)) ak.2 bl.2

def IsCompletelyPositiveMatrixMap {d : ℕ} (Phi : ComplexMatrix d → ComplexMatrix d) : Prop :=
  ∀ n (Y : AncillaMatrix n d), Y.PosSemidef → (matrixAmplification Phi n Y).PosSemidef

def ancillaKrausMatrix {d : ℕ} (n : ℕ) (V : ComplexMatrix d) : AncillaMatrix n d :=
  fun ak bi => if ak.1 = bi.1 then V ak.2 bi.2 else 0

set_option backward.isDefEq.respectTransparency false in
theorem matrixAmplification_conjugation {d : ℕ} (n : ℕ)
    (V : ComplexMatrix d) (Y : AncillaMatrix n d) :
    matrixAmplification (fun X => V * X * V.conjTranspose) n Y =
      ancillaKrausMatrix n V * Y * (ancillaKrausMatrix n V).conjTranspose := by
  classical
  ext ⟨a, k⟩ ⟨b, l⟩
  simp [matrixAmplification, ancillaKrausMatrix, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, RCLike.star_def, apply_ite]

theorem matrixAmplification_zero {d : ℕ} (n : ℕ) (Y : AncillaMatrix n d) :
    matrixAmplification (fun _ : ComplexMatrix d => 0) n Y = 0 := rfl

theorem matrixAmplification_add {d : ℕ} (n : ℕ) (Y : AncillaMatrix n d)
    (Phi Psi : ComplexMatrix d → ComplexMatrix d) :
    matrixAmplification (fun X => Phi X + Psi X) n Y =
      matrixAmplification Phi n Y + matrixAmplification Psi n Y := rfl

theorem krausAction_completelyPositive {d : ℕ} (K : List (ComplexMatrix d)) :
    IsCompletelyPositiveMatrixMap (krausAction K) := by
  intro n Y hY
  induction K with
  | nil =>
      have heq : krausAction ([] : List (ComplexMatrix d)) = fun _ => 0 := by
        funext X
        rfl
      rw [heq, matrixAmplification_zero]
      exact Matrix.PosSemidef.zero
  | cons V K ih =>
      have hconj := hY.mul_mul_conjTranspose_same (ancillaKrausMatrix n V)
      rw [← matrixAmplification_conjugation] at hconj
      have heq : krausAction (V :: K) =
          fun X => V * X * V.conjTranspose + krausAction K X := by
        funext X
        rfl
      rw [heq, matrixAmplification_add]
      exact hconj.add ih

theorem choiAction_linear {d : ℕ} (C : ChoiMatrix d) :
    (∀ Y Z, choiAction C (Y + Z) = choiAction C Y + choiAction C Z) ∧
    (∀ (c : ℂ) Y, choiAction C (c • Y) = c • choiAction C Y) := by
  constructor
  · intro Y Z
    ext k l
    simp [choiAction, add_mul, Finset.sum_add_distrib]
  · intro c Y
    ext k l
    simp [choiAction, Finset.mul_sum, mul_assoc]

theorem choiAction_maximallyEntangled {d : ℕ} (C : ChoiMatrix d) :
    matrixAmplification (choiAction C) d (identityChoi d) = C := by
  classical
  ext ⟨a, k⟩ ⟨b, l⟩
  have hblock : (fun i j => identityChoi d (a, i) (b, j)) = Matrix.single a b 1 := by
    ext i j
    by_cases ha : a = i <;> by_cases hb : b = j <;>
      simp [identityChoi, Matrix.vecMulVec, ha, hb]
  change choiAction C (fun i j => identityChoi d (a, i) (b, j)) k l = _
  rw [hblock, choiAction_single]

theorem choi_positive_iff_completelyPositive {d : ℕ} (C : ChoiMatrix d) :
    C.PosSemidef ↔ IsCompletelyPositiveMatrixMap (choiAction C) := by
  constructor
  · intro hC
    obtain ⟨K, hK⟩ := (choi_positive_iff_kraus C).mp hC
    have hfun : choiAction C = krausAction K := funext hK
    rw [hfun]
    exact krausAction_completelyPositive K
  · intro hCP
    have h := hCP d (identityChoi d) (identityChoi_positive d)
    rwa [choiAction_maximallyEntangled] at h

end AlbertSequential
