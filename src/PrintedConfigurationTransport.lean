/- SPDX-License-Identifier: Apache-2.0 -/
module

public import AssociativeDyadOverlap
public import ScheduleMatchingSectors
import FiveTest.PentadContinuousCoordinates
import BlockA.SecondOrderResidual
import AppF.ExactModel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! Basis and dyad convention transport for the actual printed configurations. -/
@[expose] public section
noncomputable section

namespace AlbertSequential

open NativeAnalysis

/-- Entrywise octonion automorphisms preserve the normalization and transport
all coordinates of the dyad. -/
theorem entrywiseAuto_normalizedOctDyad (α : OctonionAutomorphism) (v : Fin 3 → Octonion) :
    (octAutoToAlbertAuto α).linearEquiv (normalizedOctDyad v) =
      normalizedOctDyad (fun i => α.equiv (v i)) := by
  unfold normalizedOctDyad octColumnNormSq
  rw [map_smul, FiveTest.entrywiseAuto_dyad]
  simp only [α.map_normSq]

/-- The alternative convention is the standard dyad of the conjugated column.
The three displayed expressions are the entries in the three upper slots. -/
theorem normalizedOctDyad_conjugate_upper (v : Fin 3 → Octonion) :
    let q := normalizedOctDyad (fun i => octonionConj (v i))
    q.2 0 = (1 / octColumnNormSq v : ℝ) • octonionMul (octonionConj (v 0)) (v 1) ∧
      q.2 1 = (1 / octColumnNormSq v : ℝ) • octonionMul (octonionConj (v 0)) (v 2) ∧
      q.2 2 = (1 / octColumnNormSq v : ℝ) • octonionMul (octonionConj (v 1)) (v 2) := by
  have hn : octColumnNormSq (fun i => octonionConj (v i)) = octColumnNormSq v := by
    simp only [octColumnNormSq, octNormSq_conj]
  simp only [normalizedOctDyad, hn]
  refine ⟨?_, ?_, ?_⟩
  · change (1 / octColumnNormSq v : ℝ) • octonionMul (octonionConj (v 0)) (octonionConj (octonionConj (v 1))) = _
    rw [octonionConj_conj]
  · change (1 / octColumnNormSq v : ℝ) • octonionMul (octonionConj (v 0)) (octonionConj (octonionConj (v 2))) = _
    rw [octonionConj_conj]
  · change (1 / octColumnNormSq v : ℝ) • octonionMul (octonionConj (v 1)) (octonionConj (octonionConj (v 2))) = _
    rw [octonionConj_conj]

/-- The literal unnormalized columns of the two Albert models and both
quaternionic sectors. Choose `b=√2` or `b=1`. The fourth-column entries
`j,l` may be the third basic unit or a signed quaternionic combination. -/
def printedCertificateColumns (b : ℝ) (i j l : Octonion) : Fin 4 → Fin 3 → Octonion :=
  ![![octOne,0,0], ![octOne,octonionScalar b,0], ![octOne,i,octOne], ![octOne,j,l]]

def printedCertificateAtoms (b : ℝ) (i j l : Octonion) : Fin 4 → Albert :=
  fun k => normalizedOctDyad (printedCertificateColumns b i j l k)

theorem printedCertificateAtoms_entrywise_transport (α : OctonionAutomorphism) (b : ℝ)
    (i j l : Octonion) (k : Fin 4) :
    (octAutoToAlbertAuto α).linearEquiv (printedCertificateAtoms b i j l k) =
      printedCertificateAtoms b (α.equiv i) (α.equiv j) (α.equiv l) k := by
  unfold printedCertificateAtoms
  rw [entrywiseAuto_normalizedOctDyad]
  apply congrArg normalizedOctDyad
  funext r
  fin_cases k <;> fin_cases r <;> simp [printedCertificateColumns, α.map_one, α.map_scalar]

/-- All word probabilities are invariant under the exact configuration and
state transport, with no horizon cutoff. -/
theorem printedCertificateAtoms_entrywise_words (α : OctonionAutomorphism) (b : ℝ)
    (i j l : Octonion) (ρ : Albert) (w : Word (Fin 4)) :
    nativeWordProbability (printedCertificateAtoms b (α.equiv i) (α.equiv j) (α.equiv l))
      ((octAutoToAlbertAuto α).linearEquiv ρ) w =
    nativeWordProbability (printedCertificateAtoms b i j l) ρ w := by
  let g := octAutoToAlbertAuto α
  have hm : (fun k => g.linearEquiv (printedCertificateAtoms b i j l k)) =
      printedCertificateAtoms b (α.equiv i) (α.equiv j) (α.equiv l) :=
    funext (printedCertificateAtoms_entrywise_transport α b i j l)
  rw [← hm, nativeWordProbability_eq_pairing, nativeWordProbability_eq_pairing,
    ← AppF.map_nativeWordEffect, g.map_tracePairing]

/-- One explicit basic-triple change of basis transports the Albert model and
both signs of the literal quaternionic sector. -/
theorem exists_printedCertificate_basis_transport (i j l : Octonion)
    (hi : octonionReal i = 0) (hj : octonionReal j = 0) (hl : octonionReal l = 0)
    (hni : octNormSq i = 1) (hnj : octNormSq j = 1) (hnl : octNormSq l = 1)
    (hij : octDot i j = 0) (hil : octDot i l = 0) (hjl : octDot j l = 0)
    (hlij : octDot l (octonionMul i j) = 0) :
    ∃ g : NativeAlbertAutomorphism,
      (∀ b k, g.linearEquiv (printedCertificateAtoms b octI octJ octL k) =
        printedCertificateAtoms b i j l k) ∧
      (∀ (b d : ℝ) k, g.linearEquiv (printedCertificateAtoms b octI octJ (d • (octI + octJ)) k) =
        printedCertificateAtoms b i j (d • (i + j)) k) := by
  let α := octAutoOfBasicTriple i j l hi hj hl hni hnj hnl hij hil hjl hlij
  have hαi : α.equiv octI = i := octAutoOfBasicTriple_I ..
  have hαj : α.equiv octJ = j := octAutoOfBasicTriple_J ..
  have hαl : α.equiv octL = l := octAutoOfBasicTriple_L ..
  refine ⟨octAutoToAlbertAuto α, ?_, ?_⟩
  · intro b k
    simpa only [hαi, hαj, hαl] using
      printedCertificateAtoms_entrywise_transport α b octI octJ octL k
  · intro b d k
    simpa only [map_smul, map_add, hαi, hαj] using
      printedCertificateAtoms_entrywise_transport α b octI octJ (d • (octI + octJ)) k

private theorem octDyad_scaled_column (v : Fin 3 → Octonion) (r : ℝ) :
    octDyad (fun i => r • v i) = r^2 • octDyad v := by
  apply Prod.ext
  · funext i
    change octNormSq (r • v i) = r^2 * octNormSq (v i)
    exact octNormSq_smul r (v i)
  · have h (i j : Fin 3) :
        octonionMul (r • v i) (octonionConj (r • v j)) =
          r^2 • octonionMul (v i) (octonionConj (v j)) := by
      rw [octonionConj_smul, octonionMul_smul_left, octonionMul_smul_right, smul_smul, pow_two]
    funext i
    fin_cases i
    · exact h 0 1
    · exact h 0 2
    · exact h 1 2

private theorem normalizedOctDyad_eq_scaled_column (v : Fin 3 → Octonion) (r : ℝ)
    (hr : r^2 = 1 / octColumnNormSq v) :
    normalizedOctDyad v = octDyad (fun i => r • v i) := by
  rw [octDyad_scaled_column, hr, normalizedOctDyad]

private theorem norm_octScalar (t : ℝ) : octNormSq (octonionScalar t) = t^2 := by
  rw [octonionScalar_eq_smul, ← octOne_eq_scalar, octNormSq_smul, octNormSq_one, mul_one]

private theorem norm_octI : octNormSq octI = 1 := by
  rw [octNormSq_eq_coords]
  simp [octI]

private theorem norm_octJ : octNormSq octJ = 1 := by
  rw [octNormSq_eq_coords]
  simp [octJ]

private theorem norm_octL : octNormSq octL = 1 := by
  rw [octNormSq_eq_coords]
  simp [octL]

private theorem printedCertificateAtoms_eq_sparse (a b c : ℝ) (j l : Octonion)
    (ha : a^2 = 1 / (1+b^2)) (hc : c^2 = 1/3)
    (hj : octNormSq j = 1) (hl : octNormSq l = 1) :
    printedCertificateAtoms b octI j l = sparseFourConfigOct a (a*b) c 0 c c c (c • j) (c • l) := by
  have hzero : octNormSq 0 = 0 := (octNormSq_eq_zero 0).mpr rfl
  funext k
  fin_cases k
  · change normalizedOctDyad ![octOne, 0, 0] = octDyad ![octOne, 0, 0]
    have hn : octColumnNormSq ![octOne,0,0] = 1 := by
      simp [octColumnNormSq, Fin.sum_univ_three, octNormSq_one, hzero]
    rw [normalizedOctDyad, hn, div_self one_ne_zero, one_smul]
  · change normalizedOctDyad ![octOne, octonionScalar b, 0] =
      octDyad ![octonionScalar a, octonionScalar (a*b), 0]
    have hn : octColumnNormSq ![octOne,octonionScalar b,0] = 1 + b^2 := by
      simp [octColumnNormSq, Fin.sum_univ_three, octNormSq_one, norm_octScalar, hzero]
    rw [normalizedOctDyad_eq_scaled_column _ a (by rw [hn]; exact ha)]
    apply congrArg octDyad
    funext j
    fin_cases j <;> simp [octOne, ← octonionScalar_smul]
  · change normalizedOctDyad ![octOne, octI, octOne] =
      octDyad ![octonionScalar c, octonionScalar 0 + c • octI, octonionScalar c]
    have hn : octColumnNormSq ![octOne,octI,octOne] = 3 := by
      norm_num [octColumnNormSq, Fin.sum_univ_three, octNormSq_one, norm_octI]
    rw [normalizedOctDyad_eq_scaled_column _ c (by rw [hn]; exact hc)]
    apply congrArg octDyad
    funext j
    fin_cases j <;> simp [octOne, ← octonionScalar_smul, octonionScalar_zero]
  · change normalizedOctDyad ![octOne, j, l] = octDyad ![octonionScalar c, c • j, c • l]
    have hn : octColumnNormSq ![octOne,j,l] = 3 := by
      norm_num [octColumnNormSq, Fin.sum_univ_three, octNormSq_one, hj, hl]
    rw [normalizedOctDyad_eq_scaled_column _ c (by rw [hn]; exact hc)]
    apply congrArg octDyad
    funext k
    fin_cases k <;> simp [octOne, ← octonionScalar_smul]

/-- The frozen maximal configuration is the literal normalized four columns. -/
theorem printedCertificate_maximizer_eq :
    printedCertificateAtoms (Real.sqrt 2) octI octJ octL = maximizerConfig := by
  have h₃ : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h₂ : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hc : (1 / Real.sqrt 3 : ℝ)^2 = 1/3 := by rw [div_pow, one_pow, h₃]
  have ha : (1 / Real.sqrt 3 : ℝ)^2 = 1 / (1 + Real.sqrt 2 ^ 2) := by rw [hc, h₂]; norm_num
  rw [printedCertificateAtoms_eq_sparse _ _ _ _ _ ha hc norm_octJ norm_octL]
  unfold maximizerConfig sparseFourConfig
  rw [show 1 / Real.sqrt 3 * Real.sqrt 2 = Real.sqrt 2 / Real.sqrt 3 by ring]
  simp [octonionScalar_zero]

private theorem conj_imaginary (x : Octonion) (hx : octonionReal x = 0) : octonionConj x = -x := by
  have h : octIm x = x := by rw [octIm, hx, octonionScalar_zero, sub_zero]
  simpa only [h] using octConj_octIm x

/-- Conjugating each column implements the paper's sign convention change. -/
theorem printedCertificateColumns_conjugate (b : ℝ) (i j l : Octonion)
    (hi : octonionReal i = 0) (hj : octonionReal j = 0) (hl : octonionReal l = 0)
    (k : Fin 4) (r : Fin 3) :
    octonionConj (printedCertificateColumns b i j l k r) =
      printedCertificateColumns b (-i) (-j) (-l) k r := by
  have hI := conj_imaginary i hi
  have hJ := conj_imaginary j hj
  have hL := conj_imaginary l hl
  fin_cases k <;> fin_cases r <;>
    simp [printedCertificateColumns, octonionConj_one, octonionConj_scalar, hI, hJ, hL]

/-- Reversing the signs on a basic triple preserves its defining conditions. -/
theorem printedBasicTriple_neg (i j l : Octonion)
    (hi : octonionReal i = 0) (hj : octonionReal j = 0) (hl : octonionReal l = 0)
    (hni : octNormSq i = 1) (hnj : octNormSq j = 1) (hnl : octNormSq l = 1)
    (hij : octDot i j = 0) (hil : octDot i l = 0) (hjl : octDot j l = 0)
    (hlij : octDot l (octonionMul i j) = 0) :
    octonionReal (-i) = 0 ∧ octonionReal (-j) = 0 ∧ octonionReal (-l) = 0 ∧
    octNormSq (-i) = 1 ∧ octNormSq (-j) = 1 ∧ octNormSq (-l) = 1 ∧
    octDot (-i) (-j) = 0 ∧ octDot (-i) (-l) = 0 ∧ octDot (-j) (-l) = 0 ∧
    octDot (-l) (octonionMul (-i) (-j)) = 0 := by
  simp only [octonionReal_neg, octNormSq_neg, octDot_neg_left, octDot_neg_right,
    octonionMul_neg_left, octonionMul_neg_right, neg_neg, neg_eq_zero]
  exact ⟨hi, hj, hl, hni, hnj, hnl, hij, hil, hjl, hlij⟩

/-- The named rational configuration is exactly the four printed normalized dyads. -/
theorem printedCertificate_fixedS_eq :
    printedCertificateAtoms 1 octI octJ octL = fixedS := by
  have hzero : octNormSq 0 = 0 := (octNormSq_eq_zero 0).mpr rfl
  have hI : octonionConj octI = -octI := conj_imaginary _ rfl
  have hJ : octonionConj octJ = -octJ := conj_imaginary _ rfl
  have hL : octonionConj octL = -octL := conj_imaginary _ rfl
  funext k
  fin_cases k
  · change normalizedOctDyad ![octOne,0,0] = diagAtom 0
    have hn : octColumnNormSq ![octOne,0,0] = 1 := by
      simp [octColumnNormSq, Fin.sum_univ_three, octNormSq_one, hzero]
    rw [normalizedOctDyad, hn, div_self one_ne_zero, one_smul]
    apply AppF.albert_ext' <;>
      simp [octDyad, diagAtom, octNormSq_one, hzero, octonionMul_zero_right]
  · change normalizedOctDyad ![octOne,octOne,0] = atomB
    have hn : octColumnNormSq ![octOne,octOne,0] = 2 := by
      norm_num [octColumnNormSq, Fin.sum_univ_three, octNormSq_one, hzero]
    rw [normalizedOctDyad, hn, atomB]
    apply congrArg ((1/2 : ℝ) • ·)
    apply AppF.albert_ext' <;>
      simp [octDyad, octNormSq_one, hzero, octonionConj_one,
        octonionMul_one_left, octonionMul_zero_right, ← octOne_eq_scalar]
  · change normalizedOctDyad ![octOne,octI,octOne] = atomC
    have hn : octColumnNormSq ![octOne,octI,octOne] = 3 := by
      norm_num [octColumnNormSq, Fin.sum_univ_three, octNormSq_one, norm_octI]
    rw [normalizedOctDyad, hn, atomC]
    apply congrArg ((1/3 : ℝ) • ·)
    apply AppF.albert_ext' <;>
      simp [octDyad, octNormSq_one, norm_octI, hI, octonionConj_one,
        octonionMul_one_left, octonionMul_one_right, ← octOne_eq_scalar]
  · change normalizedOctDyad ![octOne,octJ,octL] = atomD
    have hn : octColumnNormSq ![octOne,octJ,octL] = 3 := by
      norm_num [octColumnNormSq, Fin.sum_univ_three, octNormSq_one, norm_octJ, norm_octL]
    rw [normalizedOctDyad, hn, atomD]
    apply congrArg ((1/3 : ℝ) • ·)
    apply AppF.albert_ext' <;>
      simp [octDyad, octNormSq_one, norm_octJ, norm_octL, hJ, hL,
        octonionMul_one_left, octonionMul_neg_right]

private theorem norm_octIJ (d : ℝ) (hd : d^2 = 1/2) : octNormSq (d • (octI + octJ)) = 1 := by
  rw [octNormSq_smul, hd, octNormSq_add, norm_octI, norm_octJ]
  have hij : octDot octI octJ = 0 := by
    rw [octDot_eq_coords]
    simp [octI, octJ]
  rw [hij]
  norm_num

/-- The literal plus/minus dyads agree with the named quaternionic sectors. -/
theorem printedCertificate_sector_eq (b d : ℝ) (hd : d^2 = 1/2) :
    printedCertificateAtoms b octI octJ (d • (octI + octJ)) =
      MatchingModels.horizonQuaternionicSector b d := by
  let a := MatchingModels.horizonB b
  let c := MatchingModels.horizonCD
  have hn : 0 ≤ 1 + b^2 := by positivity
  have ha : a^2 = 1 / (1+b^2) := by
    change ((Real.sqrt (1+b^2))⁻¹)^2 = _
    rw [inv_pow, Real.sq_sqrt hn, one_div]
  have hc : c^2 = 1/3 := by
    change ((Real.sqrt 3)⁻¹)^2 = _
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), one_div]
  rw [printedCertificateAtoms_eq_sparse a b c _ _ ha hc norm_octJ (norm_octIJ d hd)]
  funext i
  rw [MatchingModels.horizonQuaternionicSector_eq_octDyad]
  fin_cases i <;> apply congrArg octDyad <;> funext j <;> fin_cases j <;>
    simp [MatchingModels.horizonQuaternionicColumns, a, c,
      octonionScalar_zero, smul_add, smul_smul] <;>
    try rfl
  · have h : a * b = b * a := mul_comm _ _
    rw [h]
    rfl
  · rw [show octI = quatEmbed1 ⟨0, 1, 0, 0⟩ from rfl, ← map_smul]
    apply congrArg quatEmbed1
    apply Quaternion.ext <;> simp
  · rw [show octJ = quatEmbed1 ⟨0, 0, 1, 0⟩ from rfl, ← map_smul]
    apply congrArg quatEmbed1
    apply Quaternion.ext <;> simp
  · rw [show octI = quatEmbed1 ⟨0, 1, 0, 0⟩ from rfl,
      show octJ = quatEmbed1 ⟨0, 0, 1, 0⟩ from rfl, ← map_smul, ← map_smul, ← map_add]
    apply congrArg quatEmbed1
    apply Quaternion.ext <;> simp [mul_comm]

end AlbertSequential
