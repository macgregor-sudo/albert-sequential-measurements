module

import ReflectedRobustFunctional

open AlbertSequential AlbertSequential.FiveTest
open AlbertSequential.LengthSeven AlbertSequential.LengthSeven.Robust

noncomputable section

example : (reflectedRobustVector.map (fun t => |t.1|)).sum = (713/9 : ℚ) := by
  decide +kernel

example : reflectedGramPairs.length = 484 := by decide +kernel

example : reflectedGramPairs.all (fun t => reflectedEntryCheck t.2) = true :=
  reflectedGramPairs_checked

/-- A change of coefficient in the first exact Gram entry fails the walk identity check. -/
example :
    ({ reflectedGram0.2 with tabs := [mkY 2 1 [1,2,3,0]] } : Entry).ok = false := by
  decide +kernel

example (w : Word (Fin 5)) (hw : w ∈ reflectedFiveTestFunctional.coefficients.support) :
    w.head? = some (0,true) ∧ w.length ≤ 11 :=
  reflectedFiveTestFunctional_support w hw

example :
    reflectedFiveTestFunctional.evaluate (nativeWordProbability pentadF ((1/3 : ℝ) • albertUnit)) ≤
      -(11/11664 : ℝ) :=
  reflectedFiveTestFunctional_native

example {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (M : HilbertProjectiveData (Fin 5) 𝕜 H) :
    ∃ w : Word (Fin 5), w.head? = some (0,true) ∧ w.length ≤ 11 ∧
      (9/10^21 : ℝ) < |M.probability w - nativeWordProbability pentadF ((1/3 : ℝ) • albertUnit) w| := by
  obtain ⟨w,ha,hl,h⟩ := reflectedFiveTest_robust_hilbert M
  exact ⟨w,ha,hl,reflectedFiveTestMargin_gt.trans h⟩

example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Q : QuaternionicOperatorStructure H} (M : QuaternionicProjectiveData (Fin 5) Q) :
    ∃ w : Word (Fin 5), w.head? = some (0,true) ∧ w.length ≤ 11 ∧
      (9/10^21 : ℝ) < |M.state (M.wordEffect w) - nativeWordProbability pentadF ((1/3 : ℝ) • albertUnit) w| := by
  obtain ⟨w,ha,hl,h⟩ := reflectedFiveTest_robust_quaternionic M
  exact ⟨w,ha,hl,reflectedFiveTestMargin_gt.trans h⟩

#print axioms reflectedGramPairs_checked
#print axioms reflectedGramPairs_spec
#print axioms reflectedGramPairs_value
#print axioms uniformReflectionPenalty_nonneg
#print axioms reflectedFiveTestFunctional_native
#print axioms reflectedFiveTestFunctional_nonneg
#print axioms reflectedFiveTestFunctional_support
#print axioms reflectedFiveTestFunctional_coefficientNorm
#print axioms reflectedFiveTestMargin_gt
#print axioms reflectedFiveTest_robust_hilbert
#print axioms reflectedFiveTest_robust_quaternionic
