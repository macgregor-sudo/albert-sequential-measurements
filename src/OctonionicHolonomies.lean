/- SPDX-License-Identifier: Apache-2.0 -/
module

public import MatchingModels.QuatPair
public import OctonionicHolonomyAlgebra

public section
noncomputable section

namespace AlbertSequential

open MatchingModels

structure OctonionicHolonomyData (q : Fin 4 → Albert) (h : Fin 3 → Octonion) : Prop where
  unit : ∀ i, octNormSq (h i) = 1
  c1 : tetraC1 (fpOverlap q) (fpTriangle q) = octonionReal (h 0)
  c2 : tetraC2 (fpOverlap q) (fpTriangle q) = octonionReal (h 1)
  c3 : tetraC3 (fpOverlap q) (fpTriangle q) = octonionReal (h 2)
  c4 : tetraC4 (fpOverlap q) (fpTriangle q) =
    octonionReal (octonionMul (octonionMul (h 0) (h 1)) (h 2))
  K12 : tetraK12 (fpOverlap q) (tVec q) = octonionReal (octonionMul (h 0) (h 1))
  K23 : tetraK23 (fpOverlap q) (tVec q) = octonionReal (octonionMul (h 1) (h 2))
  K31 : tetraK31 (fpOverlap q) (tVec q) = octonionReal (octonionMul (h 2) (h 0))
  gram : M_mat (fpOverlap q) (fpTriangle q) (tVec q) =
    Matrix.of (fun i j => octDot (octIm (h i)) (octIm (h j)))

namespace OctonionicHolonomyData

variable {q : Fin 4 → Albert} {h : Fin 3 → Octonion}

theorem unitary (hdata : OctonionicHolonomyData q h) (i : Fin 3) :
    octonionMul (octonionConj (h i)) (h i) = octOne ∧
      octonionMul (h i) (octonionConj (h i)) = octOne := by
  rw [octMul_conj_self, octMul_self_conj, hdata.unit i, octOne_eq_scalar]
  exact ⟨rfl, rfl⟩

theorem clifford (hdata : OctonionicHolonomyData q h) (i j : Fin 3) :
    octonionMul (octIm (h i)) (octIm (h j)) + octonionMul (octIm (h j)) (octIm (h i)) =
      (-2 * M_mat (fpOverlap q) (fpTriangle q) (tVec q) i j) • octOne := by
  rw [hdata.gram]
  exact octonionMul_imag_anticomm (octonionReal_octIm _) (octonionReal_octIm _)

theorem face (hdata : OctonionicHolonomyData q h) :
    let v := octonionMul (octonionMul (h 0) (h 1)) (h 2)
    (1 / 2 : ℝ) • (v + octonionConj v) =
      octonionScalar (tetraC4 (fpOverlap q) (fpTriangle q)) := by
  dsimp only
  rw [hdata.c4, octonion_hermitian_part]

theorem oriented_triple (hdata : OctonionicHolonomyData q h) :
    tetraC4 (fpOverlap q) (fpTriangle q) - tetraS (fpOverlap q) (fpTriangle q) (tVec q) =
      octonionReal (octonionMul (octonionMul (octIm (h 0)) (octIm (h 1))) (octIm (h 2))) ∧
    tetraC4 (fpOverlap q) (fpTriangle q) - tetraS (fpOverlap q) (fpTriangle q) (tVec q) =
      -octDot (octCross (octIm (h 0)) (octIm (h 1))) (octIm (h 2)) := by
  have ht : tetraC4 (fpOverlap q) (fpTriangle q) - tetraS (fpOverlap q) (fpTriangle q) (tVec q) =
      octonionReal (octonionMul (octonionMul (octIm (h 0)) (octIm (h 1))) (octIm (h 2))) := by
    unfold tetraS
    rw [hdata.c4, hdata.c1, hdata.c2, hdata.c3, hdata.gram, real_octonion_triple_expansion]
    simp only [Matrix.of_apply]
    ring
  exact ⟨ht, ht.trans (real_imaginary_octonion_triple (octonionReal_octIm _)
    (octonionReal_octIm _) (octonionReal_octIm _))⟩

theorem determinant (hdata : OctonionicHolonomyData q h) :
    Dtet (fpOverlap q) (fpTriangle q) (tVec q) =
      (1 / 4 : ℝ) * octNormSq (octAssociator (h 0) (h 1) (h 2)) := by
  change (M_mat (fpOverlap q) (fpTriangle q) (tVec q)).det -
    (tetraC4 (fpOverlap q) (fpTriangle q) - tetraS (fpOverlap q) (fpTriangle q) (tVec q)) ^ 2 = _
  rw [hdata.oriented_triple.2, hdata.gram, neg_sq]
  have hv : (![octIm (h 0), octIm (h 1), octIm (h 2)] : Fin 3 → Octonion) =
      fun i => octIm (h i) := by
    funext i
    fin_cases i <;> rfl
  have hh := harvey_lawson_for_holonomies (h 0) (h 1) (h 2)
  dsimp only at hh
  rw [hv] at hh
  exact hh

theorem determinant_imaginary (hdata : OctonionicHolonomyData q h) :
    Dtet (fpOverlap q) (fpTriangle q) (tVec q) =
      (1 / 4 : ℝ) * octNormSq (octAssociator (octIm (h 0)) (octIm (h 1)) (octIm (h 2))) := by
  rw [hdata.determinant, octAssociator_octIm]

end OctonionicHolonomyData

def sparseOctonionicHolonomies (B0 B1 C0 C1 C2 C3 D0 : ℝ) (X Y : Octonion) : Fin 3 → Octonion :=
  let z := octonionScalar C1 + C2 • octI
  let g1 := octonionScalar (B0 * C0) + B1 • z
  let g2 := octonionScalar (B0 * D0) + B1 • X
  let g3 := octonionScalar (C0 * D0) + octonionMul (octonionConj z) X + C3 • Y
  ![(1 / Real.sqrt (octNormSq g1)) • g1, (1 / Real.sqrt (octNormSq g3)) • g3,
    (1 / Real.sqrt (octNormSq g2)) • octonionConj g2]

private theorem normalized_octUnit (g : Octonion) (u : ℝ) (hu : 0 < u)
    (hNorm : u ^ 2 = octNormSq g) : octNormSq ((1/u : ℝ) • g) = 1 := by
  rw [octNormSq_smul, ← hNorm]
  field_simp

theorem sparseOctonionicHolonomies_data (B0 B1 C0 C1 C2 C3 D0 : ℝ) (X Y : Octonion)
    (hB : 0 < B0) (hC : 0 < C0) (hD : 0 < D0)
    (h12 : 0 < fpOverlap (sparseFourConfigOct B0 B1 C0 C1 C2 C3 D0 X Y) 1 2)
    (h13 : 0 < fpOverlap (sparseFourConfigOct B0 B1 C0 C1 C2 C3 D0 X Y) 1 3)
    (h23 : 0 < fpOverlap (sparseFourConfigOct B0 B1 C0 C1 C2 C3 D0 X Y) 2 3) :
    OctonionicHolonomyData (sparseFourConfigOct B0 B1 C0 C1 C2 C3 D0 X Y)
      (sparseOctonionicHolonomies B0 B1 C0 C1 C2 C3 D0 X Y) := by
  let q := sparseFourConfigOct B0 B1 C0 C1 C2 C3 D0 X Y
  let z := octonionScalar C1 + C2 • octI
  let g1 := octonionScalar (B0 * C0) + B1 • z
  let g2 := octonionScalar (B0 * D0) + B1 • X
  let g3 := octonionScalar (C0 * D0) + octonionMul (octonionConj z) X + C3 • Y
  let d := Real.sqrt (octNormSq g1)
  let f := Real.sqrt (octNormSq g3)
  let e := Real.sqrt (octNormSq g2)
  obtain ⟨o01,o02,o03,o12,o13,o23,r012,r013,r023,r123,w1,w2,w3⟩ :=
    sparseFourConfigOct_traces B0 B1 C0 C1 C2 C3 D0 X Y
  change fpOverlap q 1 2 = octNormSq g1 at o12
  change fpOverlap q 1 3 = octNormSq g2 at o13
  change fpOverlap q 2 3 = octNormSq g3 at o23
  have hd : 0 < d := Real.sqrt_pos.2 (o12 ▸ h12)
  have he : 0 < e := Real.sqrt_pos.2 (o13 ▸ h13)
  have hf : 0 < f := Real.sqrt_pos.2 (o23 ▸ h23)
  have hd2 := Real.sq_sqrt (show 0 ≤ octNormSq g1 from octNormSq_nonneg _)
  have he2 := Real.sq_sqrt (show 0 ≤ octNormSq g2 from octNormSq_nonneg _)
  have hf2 := Real.sq_sqrt (show 0 ≤ octNormSq g3 from octNormSq_nonneg _)
  obtain ⟨hgram,hc1,hc2,hc3,hk12,hk23,hk31⟩ := octonion_holonomy_gram_data
    (fpOverlap q) (fpOverlap_symm q) (fpTriangle q) (fpTriangle_swap23 q) (tVec q)
    B0 C0 D0 d e f hB hC hD hd he hf g1 g2 g3 o01 o02 o03 o12 o13 o23
    (hd2.trans o12.symm) (he2.trans o13.symm) (hf2.trans o23.symm) r012 r013 r023 w1 w2 w3
  have hν : Real.sqrt (fpOverlap q 1 2 * fpOverlap q 2 3 * fpOverlap q 3 1) = d * f * e := by
    rw [fpOverlap_symm q 3 1, o12, o13, o23, ← hd2, ← he2, ← hf2]
    rw [show d ^ 2 * f ^ 2 * e ^ 2 = (d * f * e)^2 by ring, Real.sqrt_sq (by positivity)]
  have hfour : tetraC4 (fpOverlap q) (fpTriangle q) =
      octonionReal (octonionMul (octonionMul g1 g3) (octonionConj g2)) / (d * f * e) := by
    unfold tetraC4
    rw [hν]
    exact congrArg (fun x : ℝ => x / (d * f * e)) r123
  change OctonionicHolonomyData q ![(1/d) • g1, (1/f) • g3, (1/e) • octonionConj g2]
  constructor
  · intro i
    fin_cases i
    · exact normalized_octUnit g1 d hd hd2
    · exact normalized_octUnit g3 f hf hf2
    · exact normalized_octUnit (octonionConj g2) e he (he2.trans (octNormSq_conj g2).symm)
  · rw [hc1]
    change _ = octonionReal ((1/d : ℝ) • g1)
    rw [octonionReal_smul, div_eq_mul_inv, one_div, mul_comm]
  · rw [hc2]
    change _ = octonionReal ((1/f : ℝ) • g3)
    rw [octonionReal_smul, div_eq_mul_inv, one_div, mul_comm]
  · rw [hc3]
    change _ = octonionReal ((1/e : ℝ) • octonionConj g2)
    rw [octonionReal_smul, octonionReal_conj, div_eq_mul_inv, one_div, mul_comm]
  · rw [hfour]
    change _ = octonionReal (octonionMul (octonionMul ((1/d : ℝ) • g1) ((1/f : ℝ) • g3))
      ((1/e : ℝ) • octonionConj g2))
    simp only [octonionMul_smul_left, octonionMul_smul_right, octonionReal_smul]
    field_simp
  · rw [hk12]
    change _ = octonionReal (octonionMul ((1/d : ℝ) • g1) ((1/f : ℝ) • g3))
    rw [octonionMul_smul_left, octonionMul_smul_right, octonionReal_smul, octonionReal_smul]
    field_simp
  · rw [hk23]
    change _ = octonionReal (octonionMul ((1/f : ℝ) • g3) ((1/e : ℝ) • octonionConj g2))
    have hc : octonionReal (octonionMul g3 (octonionConj g2)) =
        octonionReal (octonionMul g2 (octonionConj g3)) := by
      rw [← octonionReal_conj (octonionMul g2 (octonionConj g3)), octonionConj_mul, octonionConj_conj]
    rw [octonionMul_smul_left, octonionMul_smul_right, octonionReal_smul, octonionReal_smul, hc]
    field_simp
  · rw [hk31]
    change _ = octonionReal (octonionMul ((1/e : ℝ) • octonionConj g2) ((1/d : ℝ) • g1))
    rw [octonionMul_smul_left, octonionMul_smul_right, octonionReal_smul, octonionReal_smul,
      octonionReal_mul_comm (octonionConj g2) g1]
    field_simp
  · rw [hgram]
    congr 1
    have hv (i : Fin 3) : octIm (![ (1/d : ℝ) • g1, (1/f : ℝ) • g3,
        (1/e : ℝ) • octonionConj g2] i) =
        ![(1/d : ℝ) • octIm g1, (1/f : ℝ) • octIm g3, (-1/e : ℝ) • octIm g2] i := by
      fin_cases i
      · exact octIm_smul _ _
      · exact octIm_smul _ _
      · change octIm ((1/e : ℝ) • octonionConj g2) = (-1/e : ℝ) • octIm g2
        rw [octIm_smul, octIm_conjugate, smul_neg, neg_div, neg_smul]
    simp only [hv]

private theorem overlap_automorphism (g : NativeAlbertAutomorphism) (q : Fin 4 → Albert) :
    fpOverlap (fun i => g.linearEquiv (q i)) = fpOverlap q := by
  funext i j
  exact g.map_tracePairing (q i) (q j)

private theorem triangle_automorphism (g : NativeAlbertAutomorphism) (q : Fin 4 → Albert) :
    fpTriangle (fun i => g.linearEquiv (q i)) = fpTriangle q := by
  funext i j k
  unfold fpTriangle
  rw [← g.preserves_product, g.map_tracePairing]

private theorem double_pairs_automorphism (g : NativeAlbertAutomorphism) (q : Fin 4 → Albert) :
    tVec (fun i => g.linearEquiv (q i)) = tVec q := by
  funext i
  fin_cases i
  · change fpDoublePair1 (fun i => g.linearEquiv (q i)) = fpDoublePair1 q
    unfold fpDoublePair1
    rw [← g.preserves_product, ← g.preserves_product, g.map_tracePairing]
  · change fpDoublePair2 (fun i => g.linearEquiv (q i)) = fpDoublePair2 q
    unfold fpDoublePair2
    rw [← g.preserves_product, ← g.preserves_product, g.map_tracePairing]
  · change fpDoublePair3 (fun i => g.linearEquiv (q i)) = fpDoublePair3 q
    unfold fpDoublePair3
    rw [← g.preserves_product, ← g.preserves_product, g.map_tracePairing]

set_option maxHeartbeats 1000000 in
theorem native_octonionicHolonomies (q : Fin 4 → Albert) (hq : ∀ i, IsAtom (q i))
    (ho : ∀ i j : Fin 4, i ≠ j → 0 < fpOverlap q i j) :
    ∃ (g : NativeAlbertAutomorphism) (B0 B1 C0 C1 C2 C3 D0 : ℝ) (X Y : Octonion),
      (fun i => g.linearEquiv (q i)) = sparseFourConfigOct B0 B1 C0 C1 C2 C3 D0 X Y ∧
      OctonionicHolonomyData q (sparseOctonionicHolonomies B0 B1 C0 C1 C2 C3 D0 X Y) := by
  obtain ⟨g,B0,B1,C0,C1,C2,C3,D0,X,Y,_,_,_,_,_,_,_,_,Hn⟩ := lemma_A_normal_general q hq
  obtain ⟨hB,_,hC,_,_,hD,_,_,_,_,_,_,_,hc,_⟩ := Hn
  let p := sparseFourConfigOct B0 B1 C0 C1 C2 C3 D0 X Y
  have hcfg : (fun i => g.linearEquiv (q i)) = p := hc
  have hop : fpOverlap p = fpOverlap q := by rw [← hcfg, overlap_automorphism]
  have hrp : fpTriangle p = fpTriangle q := by rw [← hcfg, triangle_automorphism]
  have htp : tVec p = tVec q := by rw [← hcfg, double_pairs_automorphism]
  have h (i j : Fin 4) (hij : i ≠ j) : 0 < fpOverlap p i j := hop ▸ ho i j hij
  obtain ⟨hb,hc0,hd,_⟩ := sparseFourConfigOct_traces B0 B1 C0 C1 C2 C3 D0 X Y
  have hb' : 0 < B0 := by
    have hh : 0 < B0 ^ 2 := hb ▸ h 0 1 (by decide)
    exact lt_of_le_of_ne hB (by intro he; simp [← he] at hh)
  have hc' : 0 < C0 := by
    have hh : 0 < C0 ^ 2 := hc0 ▸ h 0 2 (by decide)
    exact lt_of_le_of_ne hC (by intro he; simp [← he] at hh)
  have hd' : 0 < D0 := by
    have hh : 0 < D0 ^ 2 := hd ▸ h 0 3 (by decide)
    exact lt_of_le_of_ne hD (by intro he; simp [← he] at hh)
  have H : OctonionicHolonomyData p (sparseOctonionicHolonomies B0 B1 C0 C1 C2 C3 D0 X Y) :=
    sparseOctonionicHolonomies_data B0 B1 C0 C1 C2 C3 D0 X Y hb' hc' hd'
      (h 1 2 (by decide)) (h 1 3 (by decide)) (h 2 3 (by decide))
  exact ⟨g,B0,B1,C0,C1,C2,C3,D0,X,Y,hc,H.unit,
    by simpa only [hop, hrp] using H.c1, by simpa only [hop, hrp] using H.c2,
    by simpa only [hop, hrp] using H.c3, by simpa only [hop, hrp] using H.c4,
    by simpa only [hop, htp] using H.K12, by simpa only [hop, htp] using H.K23,
    by simpa only [hop, htp] using H.K31, by simpa only [hop, hrp, htp] using H.gram⟩

end AlbertSequential
