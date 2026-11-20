/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ThirteenTracesAndAform

@[expose] public section
noncomputable section

namespace AlbertSequential

/-- The signed Gram matrix and oriented scalar in Lemma A.5, with the paper's positive anchors. -/
theorem sparseFourConfigOct_signedGram
    (B₀ B₁ C₀ C₁ C₂ C₃ D₀ : ℝ) (X Y : Octonion)
    (hB : 0 < B₀) (hC : 0 < C₀) (hD : 0 < D₀) :
    let p := sparseFourConfigOct B₀ B₁ C₀ C₁ C₂ C₃ D₀ X Y
    let z := octonionScalar C₁ + C₂ • octI
    let g₁ := octonionScalar (B₀ * C₀) + B₁ • z
    let g₂ := octonionScalar (B₀ * D₀) + B₁ • X
    let g₃ := octonionScalar (C₀ * D₀) + octonionMul (octonionConj z) X + C₃ • Y
    let u : Fin 3 → Octonion := ![octIm g₁, octIm g₂, octIm g₃]
    fpGramMatrix (fpOverlap p 0 1) (fpOverlap p 0 2) (fpOverlap p 0 3)
        (fpOverlap p 1 2) (fpOverlap p 1 3) (fpOverlap p 2 3)
        (fpTriangle p 0 1 2) (fpTriangle p 0 1 3) (fpTriangle p 0 2 3)
        (fpOmega1 p) (fpOmega2 p) (fpOmega3 p) B₀ C₀ D₀ =
      Matrix.of (fun k l => octDot (u k) (u l)) ∧
    fpGramTripleScalar (fpOverlap p 0 1) (fpOverlap p 0 2) (fpOverlap p 0 3)
        (fpOverlap p 1 2) (fpOverlap p 1 3) (fpOverlap p 2 3)
        (fpTriangle p 0 1 2) (fpTriangle p 0 1 3) (fpTriangle p 0 2 3) (fpTriangle p 1 2 3)
        (fpOmega1 p) (fpOmega2 p) (fpOmega3 p) B₀ C₀ D₀ =
      octDot (octCross (u 0) (u 2)) (u 1) := by
  dsimp only
  obtain ⟨oAB, oAC, oAD, oBC, oBD, oCD, RABC, RABD, RACD, RBCD, w₁, w₂, w₃⟩ :=
    sparseFourConfigOct_traces B₀ B₁ C₀ C₁ C₂ C₃ D₀ X Y
  rw [oAB, oAC, oAD, oBC, oBD, oCD, RABC, RABD, RACD, RBCD, w₁, w₂, w₃]
  let z := octonionScalar C₁ + C₂ • octI
  let a := octonionScalar (B₀ * C₀) + B₁ • z
  let b := octonionScalar (B₀ * D₀) + B₁ • X
  let c := octonionScalar (C₀ * D₀) + octonionMul (octonionConj z) X + C₃ • Y
  have hBC : B₀ * C₀ ≠ 0 := mul_ne_zero hB.ne' hC.ne'
  have hBD : B₀ * D₀ ≠ 0 := mul_ne_zero hB.ne' hD.ne'
  have hCD : C₀ * D₀ ≠ 0 := mul_ne_zero hC.ne' hD.ne'
  constructor
  · unfold fpGramMatrix
    simp only [mul_div_cancel_left₀ _ hBC, mul_div_cancel_left₀ _ hBD, mul_div_cancel_left₀ _ hCD]
    exact fpGramMatrixPoly_eq_octonion_gram a b c
  · unfold fpGramTripleScalar
    simp only [mul_div_cancel_left₀ _ hBC, mul_div_cancel_left₀ _ hBD, mul_div_cancel_left₀ _ hCD]
    refine Eq.trans ?_ (fpGramTriplePoly_eq_octonion_cross a b c)
    unfold fpGramTriplePoly
    ring

end AlbertSequential
