module

import PrintedConfigurationTransport

open AlbertSequential AlbertSequential.MatchingModels

example (i j l : Octonion)
    (hi : octonionReal i = 0) (hj : octonionReal j = 0) (hl : octonionReal l = 0)
    (hni : octNormSq i = 1) (hnj : octNormSq j = 1) (hnl : octNormSq l = 1)
    (hij : octDot i j = 0) (hil : octDot i l = 0) (hjl : octDot j l = 0)
    (hlij : octDot l (octonionMul i j) = 0) :
    ∃ g : NativeAlbertAutomorphism,
      (∀ k, g.linearEquiv (maximizerConfig k) = printedCertificateAtoms (Real.sqrt 2) i j l k) ∧
      (∀ k, g.linearEquiv (fixedS k) = printedCertificateAtoms 1 i j l k) ∧
      (∀ (b d : ℝ), d^2 = 1/2 → ∀ k, g.linearEquiv (horizonQuaternionicSector b d k) =
        printedCertificateAtoms b i j (d • (i+j)) k) := by
  obtain ⟨g,hA,hQ⟩ := exists_printedCertificate_basis_transport i j l hi hj hl hni hnj hnl hij hil hjl hlij
  refine ⟨g, ?_, ?_, ?_⟩
  · simpa only [printedCertificate_maximizer_eq] using hA (Real.sqrt 2)
  · simpa only [printedCertificate_fixedS_eq] using hA 1
  · intro b d hd
    simpa only [printedCertificate_sector_eq b d hd] using hQ b d

#print axioms entrywiseAuto_normalizedOctDyad
#print axioms normalizedOctDyad_conjugate_upper
#print axioms printedCertificateAtoms_entrywise_transport
#print axioms printedCertificateAtoms_entrywise_words
#print axioms exists_printedCertificate_basis_transport
#print axioms printedCertificateColumns_conjugate
#print axioms printedBasicTriple_neg
#print axioms printedCertificate_maximizer_eq
#print axioms printedCertificate_fixedS_eq
#print axioms printedCertificate_sector_eq
