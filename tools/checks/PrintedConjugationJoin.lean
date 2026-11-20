/- SPDX-License-Identifier: Apache-2.0 -/
module

import PrintedConfigurationTransport

open AlbertSequential AlbertSequential.MatchingModels

theorem independent_conjugation_join (i j l : Octonion)
    (hi : octonionReal i = 0) (hj : octonionReal j = 0) (hl : octonionReal l = 0)
    (hni : octNormSq i = 1) (hnj : octNormSq j = 1) (hnl : octNormSq l = 1)
    (hij : octDot i j = 0) (hil : octDot i l = 0) (hjl : octDot j l = 0)
    (hlij : octDot l (octonionMul i j) = 0) :
    ∃ g : NativeAlbertAutomorphism,
      (∀ b k, g.linearEquiv (printedCertificateAtoms b octI octJ octL k) =
        normalizedOctDyad (fun r => octonionConj (printedCertificateColumns b i j l k r))) ∧
      (∀ (b d : ℝ), d ^ 2 = 1 / 2 → ∀ k, g.linearEquiv (horizonQuaternionicSector b d k) =
        normalizedOctDyad (fun r => octonionConj (printedCertificateColumns b i j (d • (i + j)) k r))) := by
  obtain ⟨hi', hj', hl', hni', hnj', hnl', hij', hil', hjl', hlij'⟩ :=
    printedBasicTriple_neg i j l hi hj hl hni hnj hnl hij hil hjl hlij
  obtain ⟨g, hA, hQ⟩ :=
    exists_printedCertificate_basis_transport (-i) (-j) (-l)
      hi' hj' hl' hni' hnj' hnl' hij' hil' hjl' hlij'
  refine ⟨g, ?_, ?_⟩
  · intro b k
    rw [show (fun r => octonionConj (printedCertificateColumns b i j l k r)) =
      printedCertificateColumns b (-i) (-j) (-l) k from
        funext (printedCertificateColumns_conjugate b i j l hi hj hl k)]
    exact hA b k
  · intro b d hd k
    have hdl : octonionReal (d • (i + j)) = 0 := by
      rw [octonionReal_smul, octonionReal_add, hi, hj, zero_add, mul_zero]
    rw [← printedCertificate_sector_eq b d hd]
    rw [show (fun r => octonionConj (printedCertificateColumns b i j (d • (i + j)) k r)) =
      printedCertificateColumns b (-i) (-j) (-(d • (i + j))) k from
        funext (printedCertificateColumns_conjugate b i j _ hi hj hdl k)]
    simpa only [← neg_add, smul_neg, printedCertificateAtoms] using hQ b d k

#print axioms independent_conjugation_join
