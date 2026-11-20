/- SPDX-License-Identifier: Apache-2.0 -/
module
public import NativeScalarAccess
public import BlockB.StateSupport
public import ThirteenTracesAndAform

@[expose] public section
noncomputable section
namespace AlbertSequential
open NativeAnalysis

/-- Conditional word values read from an arbitrary mixed-state table. -/
def conditionalFour (f : Word (Fin 4) → ℝ) (i : Fin 4) (w : Word (Fin 4)) : ℝ :=
  3 * f ((i,true)::w)

/-- The quadratic trace relation holds on every table agreeing with the
mixed Albert table through length four, including nontracial representations. -/
theorem matching_four_words_trace_relation (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (f : Word (Fin 4) → ℝ) (hm : ∀ w : Word (Fin 4), w.length ≤ 4 →
      f w = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w) :
    let o := fun i j => conditionalFour f i [(j,true)]
    let R := fun i j k => weightedWordScalar (conditionalFour f i) (accessWordTerms j [(k,true)]) / 2
    let t := fun i j k l => weightedWordScalar (conditionalFour f i) (doubleAccessWordTerms j k l) / 4
    t 0 1 2 3 + t 0 2 1 3 + t 0 3 1 2 =
      1/2 - 1/2*(o 0 1+o 0 2+o 0 3+o 1 2+o 1 3+o 2 3) +
      1/2*(o 0 1*o 2 3+o 0 2*o 1 3+o 0 3*o 1 2) +
      R 0 1 2+R 0 1 3+R 0 2 3+R 1 2 3 := by
  intro o R t
  have hcond (i : Fin 4) (w : Word (Fin 4)) (hw : w.length ≤ 3) :
      conditionalFour f i w = nativeWordProbability p (p i) w := by
    rw [conditionalFour,hm _ (by simp; omega),BlockB.nativeWordProbability_cons_yes_e3 p i (hp i)]
    ring
  have ho (i j : Fin 4) : o i j = fpOverlap p i j :=
    (hcond i _ (by simp)).trans (BlockB.nativeWordProbability_singleton_yes p (p i) j (hp j))
  have hs (i : Fin 4) (ts : List (ℝ × Word (Fin 4))) (h : ∀ z ∈ ts, z.2.length ≤ 3) :
      weightedWordScalar (conditionalFour f i) ts = weightedWordScalar (nativeWordProbability p (p i)) ts := by
    unfold weightedWordScalar
    congr 1
    apply List.map_congr_left
    intro z hz
    rw [hcond i z.2 (h z hz)]
  have hr (i j k : Fin 4) : R i j k = fpTriangle p i j k := by
    dsimp only [R]
    rw [hs, native_scalar_triangle_access p (fun a => (hp a).1),fpTriangle,tracePairing_associative]
    · ring
    · intro z hz
      simp [accessWordTerms,signedAccessChoices,accessPrefix] at hz
      rcases hz with rfl | rfl | rfl <;> simp
  have ht (i j k l : Fin 4) : t i j k l = tracePairing (jordanMul (p i) (p j)) (jordanMul (p k) (p l)) := by
    dsimp only [t]
    rw [hs,weightedWordScalar_native,weightedNativeEffect_doubleAccess p (fun a => (hp a).1),
      tracePairing_smul_right,tracePairing_associative]
    · ring
    · intro z hz
      simp [doubleAccessWordTerms,accessLiftWordTerms,scaleWordTerms,accessWordTerms,signedAccessChoices,accessPrefix] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  simp only [ho,hr,ht]
  exact albert_fourAtom_trace_relation p hp

end AlbertSequential
