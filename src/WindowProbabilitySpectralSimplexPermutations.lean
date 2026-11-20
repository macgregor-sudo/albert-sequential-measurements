/- SPDX-License-Identifier: Apache-2.0 -/
module
public import WindowProbabilitySpectralRadial
public import Mathlib.MeasureTheory.Group.Prod

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.WindowProbability

open Set MeasureTheory
open scoped Matrix Function ENNReal

/-- Exchange the last two entries of `(a,b,1−a−b)` in the two free coordinates. -/
def simplexSwapTrailing : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) where
  toEquiv := {
    toFun := fun p => (p.1, 1 - p.1 - p.2)
    invFun := fun p => (p.1, 1 - p.1 - p.2)
    left_inv := fun p => Prod.ext rfl (by dsimp; ring)
    right_inv := fun p => Prod.ext rfl (by dsimp; ring) }
  measurable_toFun := measurable_fst.prodMk ((measurable_const.sub measurable_fst).sub measurable_snd)
  measurable_invFun := measurable_fst.prodMk ((measurable_const.sub measurable_fst).sub measurable_snd)

theorem measurePreserving_simplexSwapTrailing : MeasurePreserving simplexSwapTrailing volume volume := by
  let ν := (volume : Measure ℝ)
  have hneg := (MeasurePreserving.id ν).prod (Measure.measurePreserving_neg ν)
  have hshear := measurePreserving_prod_sub ν ν
  have htranslate := (MeasurePreserving.id ν).prod (measurePreserving_add_left ν (1 : ℝ))
  rw [Measure.volume_eq_prod]
  convert htranslate.comp (hshear.comp hneg) using 1
  funext p
  apply Prod.ext
  · rfl
  · change 1 - p.1 - p.2 = 1 + (-p.2 - p.1)
    ring

/-- All six labellings of a three-component simplex point, once each. -/
def simplexRelabel (i : Fin 6) : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
  ![MeasurableEquiv.refl _, simplexSwapTrailing, MeasurableEquiv.prodComm,
    simplexSwapTrailing.trans MeasurableEquiv.prodComm,
    MeasurableEquiv.prodComm.trans simplexSwapTrailing,
    (MeasurableEquiv.prodComm.trans simplexSwapTrailing).trans MeasurableEquiv.prodComm] i

theorem simplexRelabel_apply (i : Fin 6) (p : ℝ × ℝ) : simplexRelabel i p =
    ![p, (p.1, 1 - p.1 - p.2), (p.2, p.1), (1 - p.1 - p.2, p.1),
      (p.2, 1 - p.1 - p.2), (1 - p.1 - p.2, p.2)] i := by
  fin_cases i <;> simp [simplexRelabel, simplexSwapTrailing, MeasurableEquiv.trans_apply,
    MeasurableEquiv.prodComm, Prod.swap] <;> ring

theorem measurePreserving_simplexRelabel (i : Fin 6) : MeasurePreserving (simplexRelabel i) volume volume := by
  have ht := measurePreserving_simplexSwapTrailing
  have hs : MeasurePreserving (MeasurableEquiv.prodComm : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ)) volume volume := by
    rw [Measure.volume_eq_prod]
    exact Measure.measurePreserving_swap
  fin_cases i
  · exact MeasurePreserving.id _
  · exact ht
  · exact hs
  · exact hs.comp ht
  · exact ht.comp hs
  · exact hs.comp (ht.comp hs)

/-- The descending chamber in the two free positive simplex coordinates. -/
def orderedSimplexInTwoCoordinates : Set (ℝ × ℝ) :=
  positiveEigenvalueSimplex ∩ {p : ℝ × ℝ | p.2 < p.1 ∧ 1 - p.1 - p.2 < p.2}

def labelledEigenvalueSimplex (i : Fin 6) : Set (ℝ × ℝ) := simplexRelabel i '' orderedSimplexInTwoCoordinates

def labelledSimplexOrder (i : Fin 6) (p : ℝ × ℝ) : Prop :=
  let r := 1 - p.1 - p.2
  ![p.2 < p.1 ∧ r < p.2, r < p.1 ∧ p.2 < r, p.1 < p.2 ∧ r < p.1,
    r < p.2 ∧ p.1 < r, p.1 < r ∧ p.2 < p.1, p.2 < r ∧ p.1 < p.2] i

theorem mem_labelledEigenvalueSimplex_iff (i : Fin 6) (p : ℝ × ℝ) :
    p ∈ labelledEigenvalueSimplex i ↔ p ∈ positiveEigenvalueSimplex ∧ labelledSimplexOrder i p := by
  suffices h : ∀ q : ℝ × ℝ,
      simplexRelabel i q ∈ positiveEigenvalueSimplex ∧ labelledSimplexOrder i (simplexRelabel i q) ↔
        q ∈ orderedSimplexInTwoCoordinates by
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact (h q).mpr hq
    · intro hp
      refine ⟨(simplexRelabel i).symm p, (h _).mp ?_, (simplexRelabel i).apply_symm_apply p⟩
      rwa [(simplexRelabel i).apply_symm_apply]
  intro q
  rw [simplexRelabel_apply]
  fin_cases i <;>
    simp only [orderedSimplexInTwoCoordinates, Set.mem_inter_iff, positiveEigenvalueSimplex,
      Set.mem_ofPred_eq, labelledSimplexOrder, Matrix.cons_val_zero', Matrix.cons_val_succ'] <;>
    constructor <;> rintro ⟨⟨h₁, h₂, h₃⟩, h₄, h₅⟩ <;>
    exact ⟨⟨by linarith, by linarith, by linarith⟩, by linarith, by linarith⟩

theorem labelledEigenvalueSimplex_measurable (i : Fin 6) : MeasurableSet (labelledEigenvalueSimplex i) := by
  unfold labelledEigenvalueSimplex
  apply (simplexRelabel i).measurableEmbedding.measurableSet_image.mpr
  have hp : MeasurableSet positiveEigenvalueSimplex :=
    (isOpen_lt continuous_const continuous_fst).measurableSet.inter
      ((isOpen_lt continuous_const continuous_snd).measurableSet.inter
        (isOpen_lt (continuous_fst.add continuous_snd) continuous_const).measurableSet)
  exact hp.inter ((isOpen_lt continuous_snd continuous_fst).measurableSet.inter
    (isOpen_lt ((continuous_const.sub continuous_fst).sub continuous_snd) continuous_snd).measurableSet)

theorem labelledEigenvalueSimplex_disjoint : Pairwise (Disjoint on labelledEigenvalueSimplex) := by
  intro i j hij
  apply disjoint_left.mpr
  intro p hp hq
  have hPi := ((mem_labelledEigenvalueSimplex_iff i p).mp hp).2
  have hPj := ((mem_labelledEigenvalueSimplex_iff j p).mp hq).2
  fin_cases i <;> fin_cases j <;> norm_num at hij <;>
    simp only [labelledSimplexOrder] at hPi hPj <;> linarith [hPi.1,hPi.2,hPj.1,hPj.2]

theorem mem_iUnion_labelledEigenvalueSimplex {p : ℝ × ℝ} (hp : p ∈ positiveEigenvalueSimplex)
    (h₁ : p.1 ≠ p.2) (h₂ : p.1 ≠ 1 - p.1 - p.2) (h₃ : p.2 ≠ 1 - p.1 - p.2) :
    p ∈ ⋃ i, labelledEigenvalueSimplex i := by
  apply mem_iUnion.mpr
  rcases lt_or_gt_of_ne h₁ with h₁ | h₁ <;>
    rcases lt_or_gt_of_ne h₂ with h₂ | h₂ <;>
    rcases lt_or_gt_of_ne h₃ with h₃ | h₃
  · exact ⟨5, (mem_labelledEigenvalueSimplex_iff 5 p).mpr ⟨hp,h₃,h₁⟩⟩
  · exact ⟨3, (mem_labelledEigenvalueSimplex_iff 3 p).mpr ⟨hp,h₃,h₂⟩⟩
  · exact False.elim (by linarith)
  · exact ⟨2, (mem_labelledEigenvalueSimplex_iff 2 p).mpr ⟨hp,h₁,h₂⟩⟩
  · exact ⟨4, (mem_labelledEigenvalueSimplex_iff 4 p).mpr ⟨hp,h₂,h₁⟩⟩
  · exact False.elim (by linarith)
  · exact ⟨1, (mem_labelledEigenvalueSimplex_iff 1 p).mpr ⟨hp,h₂,h₃⟩⟩
  · exact ⟨0, (mem_labelledEigenvalueSimplex_iff 0 p).mpr ⟨hp,h₁,h₃⟩⟩

end AlbertSequential.WindowProbability
