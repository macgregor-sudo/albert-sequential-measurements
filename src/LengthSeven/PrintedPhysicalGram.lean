/- SPDX-License-Identifier: Apache-2.0 -/
module
public import LengthSeven.PrintedGramPermutation
public import LengthSeven.PhysicalScalarRules

@[expose] public section
noncomputable section
namespace AlbertSequential.LengthSeven

/-- All five three-letter families and all four two-letter families in
Appendix C.1, paired in chronological order against the actual conditioned form. -/
def HasPrintedGram {V : Type*} [AddCommGroup V] [Module ℝ V] (W : WalkForm V)
    (τ : TraceData) : Prop :=
  ∀ x y z, IsOrderingBCD x y z → ∀ i j,
    let uv := printedHistories x y z i j
    W.form (W.pathVec uv.1) (W.pathVec uv.2) = printedGramTable (printedTraces τ x y z) i j

theorem hasPrintedGram_of_scalarRules {V : Type*} [AddCommGroup V] [Module ℝ V]
    {W : WalkForm V} {τ : TraceData} (h : AlgebraicWalkRules τ W.L) : HasPrintedGram W τ := by
  intro x y z hs i j
  dsimp only
  rw [W.form_pathVec]
  exact printedGramTable_ordered h x y z hs i j

variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
  [SMulCommClass ℝ A A] [StarModule ℝ A]

theorem printedGram_e3 (M : AlgebraicProjectiveData Letter A)
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hm : ∀ w : Word Letter, w.length ≤ 7 → w.head? = some (0, true) →
      M.probability w = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w) :
    ∃ h : 0 < M.probability [(0, true)], HasPrintedGram (WalkForm.ofAlgebraic M h) (nativeTraceData p) := by
  obtain ⟨h,hs⟩ := lengthSeven_e3_scalarRules M p hp hm
  exact ⟨h,hasPrintedGram_of_scalarRules hs⟩

theorem printedGram_pA (M : AlgebraicProjectiveData Letter A)
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hm : ∀ w : Word Letter, w.length ≤ 6 →
      M.probability w = nativeWordProbability p (p 0) w) :
    ∃ h : 0 < M.probability [(0, true)], HasPrintedGram (WalkForm.ofAlgebraic M h) (nativeTraceData p) := by
  obtain ⟨h,hs⟩ := lengthSix_pA_scalarRules M p hp hm
  exact ⟨h,hasPrintedGram_of_scalarRules hs⟩

end AlbertSequential.LengthSeven
