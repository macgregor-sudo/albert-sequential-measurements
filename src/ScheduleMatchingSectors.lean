/- SPDX-License-Identifier: Apache-2.0 -/
module

public import MatchingModels.UniversalSix
public import MatchingModels.LMinSeven
public import ScheduleMatchingMixture
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace AlbertSequential.MatchingModels


def horizonB (b : ℝ) : ℝ := (Real.sqrt (1 + b ^ 2))⁻¹

def horizonCD : ℝ := (Real.sqrt 3)⁻¹

/-- The normalized quaternionic columns from Proposition 6.11. The unnormalized third
coordinate of D is `d i + d j`. -/
def horizonQuaternionicColumns (b d : ℝ) : Fin 4 → Fin 3 → Quaternion ℝ :=
  let a := horizonB b
  let c := horizonCD
  ![![1, 0, 0],
    ![⟨a, 0, 0, 0⟩, ⟨b * a, 0, 0, 0⟩, 0],
    ![⟨c, 0, 0, 0⟩, ⟨0, c, 0, 0⟩, ⟨c, 0, 0, 0⟩],
    ![⟨c, 0, 0, 0⟩, ⟨0, 0, c, 0⟩, ⟨0, d * c, d * c, 0⟩]]

private theorem horizonB_square_mul (b : ℝ) : horizonB b ^ 2 * (1 + b ^ 2) = 1 := by
  have hn : 0 < 1 + b ^ 2 := by positivity
  simp only [horizonB, inv_pow, Real.sq_sqrt hn.le]
  exact inv_mul_cancel₀ hn.ne'

private theorem horizonCD_square : horizonCD ^ 2 = 1 / 3 := by
  have h : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [horizonCD, inv_pow, h, one_div]

theorem horizonQuaternionicColumns_unit (b d : ℝ) (hd : d ^ 2 = 1 / 2) (i : Fin 4) :
    ∑ j : Fin 3, quatNormSq (horizonQuaternionicColumns b d i j) = 1 := by
  rw [Fin.sum_univ_three]
  fin_cases i
  · norm_num [horizonQuaternionicColumns, quatNormSq]
  · norm_num [horizonQuaternionicColumns, quatNormSq]
    calc
      _ = horizonB b ^ 2 * (1 + b ^ 2) := by ring
      _ = 1 := horizonB_square_mul b
  · norm_num [horizonQuaternionicColumns, quatNormSq, horizonCD_square]
  · norm_num [horizonQuaternionicColumns, quatNormSq]
    rw [mul_pow, hd, horizonCD_square]
    norm_num

def horizonHermitianDyad (u : Fin 3 → Quaternion ℝ) : QuatHermitian3 :=
  ⟨Matrix.of (fun i j => u i * star (u j)), by
    rw [selfAdjoint.mem_iff]
    ext i j <;> simp [Matrix.star_apply, star_mul]⟩

/-- The exact native sector with unnormalized D-coordinate `d i + d j`. -/
def horizonQuaternionicSector (b d : ℝ) (i : Fin 4) : Albert :=
  standardQuaternionicWindow.embedding (horizonHermitianDyad (horizonQuaternionicColumns b d i))

theorem horizonQuaternionicSector_mem (b d : ℝ) (i : Fin 4) :
    horizonQuaternionicSector b d i ∈ standardQuaternionicWindow.subalgebra.carrier := by
  rw [← standardQuaternionicWindow.range_eq]
  exact ⟨_, rfl⟩

theorem horizonQuaternionicSector_eq_octDyad (b d : ℝ) (i : Fin 4) :
    horizonQuaternionicSector b d i =
      octDyad (fun j => quatEmbed1 (horizonQuaternionicColumns b d i j)) := by
  rw [octDyad_eq_quatDyad quatEmbed1 quatEmbed1_isQuatEmbedding]
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [horizonQuaternionicSector, standardQuaternionicWindow, quatMatrixToAlbert,
      horizonHermitianDyad, quatDyad]

theorem horizonQuaternionicSector_isAtom (b d : ℝ) (hd : d ^ 2 = 1 / 2) (i : Fin 4) :
    IsAtom (horizonQuaternionicSector b d i) := by
  rw [horizonQuaternionicSector_eq_octDyad,
    octDyad_eq_quatDyad quatEmbed1 quatEmbed1_isQuatEmbedding]
  exact quatDyad_isAtom quatEmbed1 quatEmbed1_isQuatEmbedding _ 1 one_ne_zero
    (horizonQuaternionicColumns_unit b d hd i)

/-- The plus and minus sectors for M. -/
def horizonMSector (positive : Bool) : Fin 4 → Albert :=
  horizonQuaternionicSector (Real.sqrt 2)
    (if positive then (Real.sqrt 2)⁻¹ else -(Real.sqrt 2)⁻¹)

/-- The plus and minus sectors for S. -/
def horizonSSector (positive : Bool) : Fin 4 → Albert :=
  horizonQuaternionicSector 1 (if positive then (Real.sqrt 2)⁻¹ else -(Real.sqrt 2)⁻¹)

private theorem octScalar_embed (r : ℝ) :
    octonionScalar r = quatEmbed1 ⟨r, 0, 0, 0⟩ := rfl

private theorem octI_embed : octI = quatEmbed1 ⟨0, 1, 0, 0⟩ := rfl

private theorem octJ_embed : octJ = quatEmbed1 ⟨0, 0, 1, 0⟩ := rfl

private theorem octNorm_embed (q : Quaternion ℝ) : octNormSq (quatEmbed1 q) = quatNormSq q := by
  rw [octNormSq_eq_coords]
  change q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 +
    (0 : ℝ) ^ 2 + 0 ^ 2 + 0 ^ 2 + 0 ^ 2 = _
  norm_num [quatNormSq]

private theorem horizonSector_eq_sparse (b d : ℝ) :
    horizonQuaternionicSector b d =
      sparseFourConfigOct (horizonB b) (b * horizonB b)
        horizonCD 0 horizonCD horizonCD horizonCD (horizonCD • octJ)
        ((d * horizonCD) • octI + (d * horizonCD) • octJ) := by
  funext i
  rw [horizonQuaternionicSector_eq_octDyad]
  fin_cases i <;> apply congrArg octDyad <;> funext j <;> fin_cases j <;>
    simp [horizonQuaternionicColumns, octScalar_embed, octI_embed, octJ_embed,
      ← map_smul, ← map_add] <;>
    (apply congrArg quatEmbed1; apply Quaternion.ext; all_goals first | rfl | simp)

private theorem horizonB_square (b : ℝ) : horizonB b ^ 2 = 1 / (1 + b ^ 2) := by
  have hn : 1 + b ^ 2 ≠ 0 := by positivity
  exact (eq_div_iff hn).2 (horizonB_square_mul b)

/-- The coordinates of the thirteen shared-trace calculation in Proposition 6.11. -/
theorem horizonQuaternionicSector_traces (b d : ℝ) (hd : d ^ 2 = 1 / 2) :
    let q := horizonQuaternionicSector b d
    let n := 1 + b ^ 2
    fpOverlap q 0 1 = 1 / n ∧
    fpOverlap q 0 2 = 1 / 3 ∧ fpOverlap q 0 3 = 1 / 3 ∧
    fpOverlap q 1 2 = 1 / 3 ∧ fpOverlap q 1 3 = 1 / 3 ∧ fpOverlap q 2 3 = 1 / 3 ∧
    fpTriangle q 0 1 2 = 1 / (3 * n) ∧ fpTriangle q 0 1 3 = 1 / (3 * n) ∧
    fpTriangle q 0 2 3 = 1 / 9 ∧ fpTriangle q 1 2 3 = 1 / 9 ∧
    fpDoublePair1 q = 1 / (9 * n) ∧
    fpDoublePair2 q = 1 / (9 * n) + b * d / (18 * n) ∧
    fpDoublePair3 q = 1 / (9 * n) - b * d / (18 * n) := by
  let a := horizonB b
  let c := horizonCD
  let X : Octonion := c • octJ
  let Y : Octonion := (d * c) • octI + (d * c) • octJ
  let z : Octonion := octonionScalar 0 + c • octI
  let g1 : Octonion := octonionScalar (a * c) + (b * a) • z
  let g2 : Octonion := octonionScalar (a * c) + (b * a) • X
  let g3 : Octonion := octonionScalar (c * c) + octonionMul (octonionConj z) X + c • Y
  have hg1 : g1 = quatEmbed1 ⟨a * c, b * a * c, 0, 0⟩ := by
    simp only [g1, z, octScalar_embed, octI_embed, ← map_smul, ← map_add]
    apply congrArg quatEmbed1
    apply Quaternion.ext <;> simp [smul_eq_mul]
  have hg2 : g2 = quatEmbed1 ⟨a * c, 0, b * a * c, 0⟩ := by
    simp only [g2, X, octScalar_embed, octJ_embed, ← map_smul, ← map_add]
    apply congrArg quatEmbed1
    apply Quaternion.ext <;> simp [smul_eq_mul]
  have hg3 : g3 = quatEmbed1 ⟨c ^ 2, d * c ^ 2, d * c ^ 2, -(c ^ 2)⟩ := by
    simp only [g3, z, X, Y, octScalar_embed, octI_embed, octJ_embed, ← map_smul, ← map_add,
      ← quatEmbed1_isQuatEmbedding.map_mul, ← quatEmbed1_isQuatEmbedding.map_star]
    apply congrArg quatEmbed1
    apply Quaternion.ext <;> simp [smul_eq_mul] <;> ring
  have hs := sparseFourConfigOct_traces a (b * a) c 0 c c c X Y
  rw [← horizonSector_eq_sparse b d] at hs
  change fpOverlap (horizonQuaternionicSector b d) 0 1 = a ^ 2 ∧
    fpOverlap (horizonQuaternionicSector b d) 0 2 = c ^ 2 ∧
    fpOverlap (horizonQuaternionicSector b d) 0 3 = c ^ 2 ∧
    fpOverlap (horizonQuaternionicSector b d) 1 2 = octNormSq g1 ∧
    fpOverlap (horizonQuaternionicSector b d) 1 3 = octNormSq g2 ∧
    fpOverlap (horizonQuaternionicSector b d) 2 3 = octNormSq g3 ∧
    fpTriangle (horizonQuaternionicSector b d) 0 1 2 = a * c * octonionReal g1 ∧
    fpTriangle (horizonQuaternionicSector b d) 0 1 3 = a * c * octonionReal g2 ∧
    fpTriangle (horizonQuaternionicSector b d) 0 2 3 = c * c * octonionReal g3 ∧
    fpTriangle (horizonQuaternionicSector b d) 1 2 3 =
      octonionReal (octonionMul (octonionMul g1 g3) (octonionConj g2)) ∧
    fpOmega1 (horizonQuaternionicSector b d) =
      c * c * octonionReal (octonionMul g1 (octonionConj g2)) ∧
    fpOmega2 (horizonQuaternionicSector b d) =
      a * c * octonionReal (octonionMul g1 g3) ∧
    fpOmega3 (horizonQuaternionicSector b d) =
      a * c * octonionReal (octonionMul g2 (octonionConj g3)) at hs
  rw [hg1, hg2, hg3] at hs
  rcases hs with ⟨ho01, ho02, ho03, ho12, ho13, ho23, hR012, hR013, hR023, hR123, hω1, hω2, hω3⟩
  have hn : 1 + b ^ 2 ≠ 0 := by positivity
  obtain ⟨ha, hc⟩ : a ^ 2 * (1 + b ^ 2) = 1 ∧ c ^ 2 = 1 / 3 :=
    ⟨horizonB_square_mul b, horizonCD_square⟩
  have ha' : a ^ 2 = 1 / (1 + b ^ 2) := horizonB_square b
  have hden (r : ℝ) (hr : r ≠ 0) : a ^ 2 / r = 1 / (r * (1 + b ^ 2)) := by
    rw [ha']
    field_simp
  have hout : fpOverlap (horizonQuaternionicSector b d) 1 2 = 1 / 3 := by
    rw [ho12]
    norm_num [octNorm_embed, quatNormSq]
    calc
      _ = a ^ 2 * (1 + b ^ 2) * c ^ 2 := by ring
      _ = _ := by rw [ha, hc, one_mul]
  have h1 : fpOmega1 (horizonQuaternionicSector b d) = a ^ 2 / 9 := by
    rw [hω1]
    simp only [← quatEmbed1_isQuatEmbedding.map_mul, ← quatEmbed1_isQuatEmbedding.map_star,
      quatEmbed1_isQuatEmbedding.map_re, Quaternion.re_mul, Quaternion.re_star, Quaternion.imI_star,
      Quaternion.imJ_star, Quaternion.imK_star, zero_mul, sub_zero]
    calc
      _ = a ^ 2 * (c ^ 2) ^ 2 := by ring
      _ = _ := by rw [hc]; ring
  have h2 : fpOmega2 (horizonQuaternionicSector b d) = (1 - b * d) * (a ^ 2 / 9) := by
    rw [hω2]
    simp only [← quatEmbed1_isQuatEmbedding.map_mul, quatEmbed1_isQuatEmbedding.map_re,
      Quaternion.re_mul, zero_mul, sub_zero]
    calc
      _ = (1 - b * d) * a ^ 2 * (c ^ 2) ^ 2 := by ring
      _ = _ := by rw [hc]; ring
  have h3 : fpOmega3 (horizonQuaternionicSector b d) = (1 + b * d) * (a ^ 2 / 9) := by
    rw [hω3]
    simp only [← quatEmbed1_isQuatEmbedding.map_mul, ← quatEmbed1_isQuatEmbedding.map_star,
      quatEmbed1_isQuatEmbedding.map_re, Quaternion.re_mul, Quaternion.re_star, Quaternion.imI_star,
      Quaternion.imJ_star, Quaternion.imK_star, zero_mul, sub_zero]
    calc
      _ = (1 + b * d) * a ^ 2 * (c ^ 2) ^ 2 := by ring
      _ = _ := by rw [hc]; ring
  simp only [fpOmega1, fpOmega2, fpOmega3] at h1 h2 h3
  have hf1 : fpDoublePair1 (horizonQuaternionicSector b d) = a ^ 2 / 9 := by
    linarith
  have hf2 : fpDoublePair2 (horizonQuaternionicSector b d) = a ^ 2 / 9 + b * d * (a ^ 2 / 18) := by
    linarith
  have hf3 : fpDoublePair3 (horizonQuaternionicSector b d) = a ^ 2 / 9 - b * d * (a ^ 2 / 18) := by
    linarith
  refine ⟨ho01.trans ha', ho02.trans hc, ho03.trans hc, hout, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ho13]
    norm_num [octNorm_embed, quatNormSq]
    calc
      _ = a ^ 2 * (1 + b ^ 2) * c ^ 2 := by ring
      _ = _ := by rw [ha, hc, one_mul]
  · rw [ho23]
    norm_num [octNorm_embed, quatNormSq]
    calc
      _ = (2 + 2 * d ^ 2) * (c ^ 2) ^ 2 := by ring
      _ = _ := by rw [hd, hc]; norm_num
  · rw [hR012]
    change a * c * (a * c) = _
    calc
      _ = a ^ 2 / 3 := by calc
        _ = a ^ 2 * c ^ 2 := by ring
        _ = _ := by rw [hc]; ring
      _ = _ := hden 3 (by norm_num)
  · rw [hR013]
    change a * c * (a * c) = _
    calc
      _ = a ^ 2 / 3 := by calc
        _ = a ^ 2 * c ^ 2 := by ring
        _ = _ := by rw [hc]; ring
      _ = _ := hden 3 (by norm_num)
  · rw [hR023]
    change c * c * c ^ 2 = _
    rw [← pow_two, hc]
    norm_num
  · rw [hR123]
    simp only [← quatEmbed1_isQuatEmbedding.map_mul, ← quatEmbed1_isQuatEmbedding.map_star,
      quatEmbed1_isQuatEmbedding.map_re, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_star, Quaternion.imI_star,
      Quaternion.imJ_star, Quaternion.imK_star, zero_mul, add_zero, sub_zero]
    calc
      _ = a ^ 2 * (1 + b ^ 2) * (c ^ 2) ^ 2 := by ring
      _ = _ := by rw [ha, hc]; norm_num
  · rw [hf1, hden 9 (by norm_num)]
  · rw [hf2, hden 9 (by norm_num), hden 18 (by norm_num), mul_one_div]
  · rw [hf3, hden 9 (by norm_num), hden 18 (by norm_num), mul_one_div]

private def HorizonOverlapTriangleTable (p : Fin 4 → Albert) (n : ℝ) : Prop :=
  fpOverlap p 0 1 = 1 / n ∧ fpOverlap p 0 2 = 1 / 3 ∧ fpOverlap p 0 3 = 1 / 3 ∧
  fpOverlap p 1 2 = 1 / 3 ∧ fpOverlap p 1 3 = 1 / 3 ∧ fpOverlap p 2 3 = 1 / 3 ∧
  fpTriangle p 0 1 2 = 1 / (3 * n) ∧ fpTriangle p 0 1 3 = 1 / (3 * n) ∧
  fpTriangle p 0 2 3 = 1 / 9 ∧ fpTriangle p 1 2 3 = 1 / 9

private theorem strictlyOrderedPairs : ∀ i j : Fin 4, i < j →
    (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨
      (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 3) ∨ (i = 2 ∧ j = 3) := by decide

private theorem strictlyOrderedTriples : ∀ i j k : Fin 4, i < j → j < k →
    (i = 0 ∧ j = 1 ∧ k = 2) ∨ (i = 0 ∧ j = 1 ∧ k = 3) ∨
      (i = 0 ∧ j = 2 ∧ k = 3) ∨ (i = 1 ∧ j = 2 ∧ k = 3) := by decide

private theorem horizonTables_eq {p q : Fin 4 → Albert} {n : ℝ}
    (hp : ∀ i, IsAtom (p i)) (hq : ∀ i, IsAtom (q i))
    (hP : HorizonOverlapTriangleTable p n) (hQ : HorizonOverlapTriangleTable q n) :
    (∀ i j, fpOverlap p i j = fpOverlap q i j) ∧
      (∀ i j k, fpTriangle p i j k = fpTriangle q i j k) := by
  rcases hP with ⟨p01, p02, p03, p12, p13, p23, p012, p013, p023, p123⟩
  rcases hQ with ⟨q01, q02, q03, q12, q13, q23, q012, q013, q023, q123⟩
  have hop (i j : Fin 4) (hij : i < j) : fpOverlap p i j = fpOverlap q i j := by
    rcases strictlyOrderedPairs i j hij with
      ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact p01.trans q01.symm
    · exact p02.trans q02.symm
    · exact p03.trans q03.symm
    · exact p12.trans q12.symm
    · exact p13.trans q13.symm
    · exact p23.trans q23.symm
  have ho (i j : Fin 4) : fpOverlap p i j = fpOverlap q i j := by
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · exact hop i j hlt
    · unfold fpOverlap tracePairing
      rw [(hp i).1, (hq i).1, (hp i).2, (hq i).2]
    · rw [fpOverlap_symm p, fpOverlap_symm q]
      exact hop j i hgt
  have hrep (i j : Fin 4) : fpTriangle p i i j = fpTriangle q i i j := by
    unfold fpTriangle
    rw [(hp i).1, (hq i).1]
    exact ho i j
  have hs (i j k : Fin 4) (hij : i < j) (hjk : j < k) :
      fpTriangle p i j k = fpTriangle q i j k := by
    rcases strictlyOrderedTriples i j k hij hjk with
      ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
    · exact p012.trans q012.symm
    · exact p013.trans q013.symm
    · exact p023.trans q023.symm
    · exact p123.trans q123.symm
  have hs' (i j k : Fin 4) (hij : i < j) :
      fpTriangle p i j k = fpTriangle q i j k := by
    rcases lt_trichotomy j k with hjk | rfl | hkj
    · exact hs i j k hij hjk
    · rw [fpTriangle_swap12 p, fpTriangle_swap12 q, fpTriangle_swap23 p, fpTriangle_swap23 q]
      exact hrep j i
    · rcases lt_trichotomy i k with hik | rfl | hki
      · rw [fpTriangle_swap23 p, fpTriangle_swap23 q]
        exact hs i k j hik hkj
      · rw [fpTriangle_swap23 p, fpTriangle_swap23 q]
        exact hrep i j
      · rw [fpTriangle_swap23 p, fpTriangle_swap23 q, fpTriangle_swap12 p, fpTriangle_swap12 q]
        exact hs k i j hki hij
  refine ⟨ho, ?_⟩
  intro i j k
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact hs' i j k hij
  · exact hrep i k
  · rw [fpTriangle_swap12 p, fpTriangle_swap12 q]
    exact hs' j i k hji

private theorem horizonSectorTables (b d : ℝ) (hd : d ^ 2 = 1 / 2) :
    HorizonOverlapTriangleTable (horizonQuaternionicSector b d) (1 + b ^ 2) ∧
    fpDoublePair1 (horizonQuaternionicSector b d) = 1 / (9 * (1 + b ^ 2)) ∧
    fpDoublePair2 (horizonQuaternionicSector b d) = 1 / (9 * (1 + b ^ 2)) + b*d / (18 * (1 + b ^ 2)) ∧
    fpDoublePair3 (horizonQuaternionicSector b d) = 1 / (9 * (1 + b ^ 2)) - b*d / (18 * (1 + b ^ 2)) := by
  obtain ⟨h01, h02, h03, h12, h13, h23, h012, h013, h023, h123, ht1, ht2, ht3⟩ :=
    horizonQuaternionicSector_traces b d hd
  exact ⟨⟨h01, h02, h03, h12, h13, h23, h012, h013, h023, h123⟩, ht1, ht2, ht3⟩

private theorem horizon_midpoint_le_six (p : Fin 4 → Albert)
    (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p) (b d : ℝ) (hd : d ^ 2 = 1 / 2)
    (hT : HorizonOverlapTriangleTable p (1 + b ^ 2))
    (ht1 : fpDoublePair1 p = 1 / (9 * (1 + b ^ 2)))
    (ht2 : fpDoublePair2 p = 1 / (9 * (1 + b ^ 2)))
    (ht3 : fpDoublePair3 p = 1 / (9 * (1 + b ^ 2))) (w : Word (Fin 4)) (hw : w.length ≤ 6) :
    nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w =
      (1 / 2 : ℝ) * nativeWordProbability (horizonQuaternionicSector b d) ((1 / 3 : ℝ) • albertUnit) w +
      (1 / 2 : ℝ) * nativeWordProbability (horizonQuaternionicSector b (-d)) ((1 / 3 : ℝ) • albertUnit) w := by
  have hd' : (-d) ^ 2 = 1 / 2 := by rwa [neg_sq]
  obtain ⟨hTplus, hP1, hP2, hP3⟩ := horizonSectorTables b d hd
  obtain ⟨hTminus, hM1, hM2, hM3⟩ := horizonSectorTables b (-d) hd'
  have hP := horizonQuaternionicSector_isAtom b d hd
  have hM := horizonQuaternionicSector_isAtom b (-d) hd'
  obtain ⟨hoP, hRP⟩ := horizonTables_eq hp hP hT hTplus
  obtain ⟨hoM, hRM⟩ := horizonTables_eq hp hM hT hTminus
  have h1 : fpDoublePair1 p =
      (1 / 2 : ℝ) * fpDoublePair1 (horizonQuaternionicSector b d) +
      (1 - 1 / 2 : ℝ) * fpDoublePair1 (horizonQuaternionicSector b (-d)) := by
    rw [ht1, hP1, hM1]
    ring
  have h2 : fpDoublePair2 p =
      (1 / 2 : ℝ) * fpDoublePair2 (horizonQuaternionicSector b d) +
      (1 - 1 / 2 : ℝ) * fpDoublePair2 (horizonQuaternionicSector b (-d)) := by
    rw [ht2, hP2, hM2, mul_neg, neg_div]
    ring
  have h3 : fpDoublePair3 p =
      (1 / 2 : ℝ) * fpDoublePair3 (horizonQuaternionicSector b d) +
      (1 - 1 / 2 : ℝ) * fpDoublePair3 (horizonQuaternionicSector b (-d)) := by
    rw [ht3, hP3, hM3, mul_neg, neg_div]
    ring
  have h := nativeWordProbability_e3_affine_le_six hp hP hM hA
    (fun i j => ⟨hoP i j, hoM i j⟩) (fun i j k => ⟨hRP i j k, hRM i j k⟩) h1 h2 h3 w hw
  rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num] at h
  exact h

theorem horizon_sign_square : ((Real.sqrt 2)⁻¹) ^ 2 = 1 / 2 := by
  have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [inv_pow, h, one_div]

/-- The named M sectors at equal weights match every signed word of length at most six. -/
theorem horizon_M_native (w : Word (Fin 4)) (hw : w.length ≤ 6) :
    nativeWordProbability maximizerConfig ((1 / 3 : ℝ) • albertUnit) w =
      (1 / 2 : ℝ) * nativeWordProbability (horizonMSector true) ((1 / 3 : ℝ) • albertUnit) w +
      (1 / 2 : ℝ) * nativeWordProbability (horizonMSector false) ((1 / 3 : ℝ) • albertUnit) w := by
  have hA : 0 < fourPointInvariant maximizerConfig := by
    rw [fourPointInvariant_maximizerConfig]
    norm_num
  have hSq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  obtain ⟨ho, hR, h1, h2, h3, _⟩ := maximizerConfig_traces (Equiv.refl _)
  have hT : HorizonOverlapTriangleTable maximizerConfig (1 + Real.sqrt 2 ^ 2) := by
    unfold HorizonOverlapTriangleTable
    norm_num [hSq, ho, hR]
  exact horizon_midpoint_le_six _ maximizerConfig_isAtom hA _ _ horizon_sign_square hT
    (by rw [h1]; norm_num [hSq]) (by rw [h2]; norm_num [hSq]) (by rw [h3]; norm_num [hSq]) w hw

/-- The named S sectors at equal weights match every signed word of length at most six. -/
theorem horizon_S_native (w : Word (Fin 4)) (hw : w.length ≤ 6) :
    nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) w =
      (1 / 2 : ℝ) * nativeWordProbability (horizonSSector true) ((1 / 3 : ℝ) • albertUnit) w +
      (1 / 2 : ℝ) * nativeWordProbability (horizonSSector false) ((1 / 3 : ℝ) • albertUnit) w := by
  have hA : 0 < fourPointInvariant fixedS := by rw [fourPointInvariant_fixedS]; norm_num
  have ho (i j : Fin 4) :
      fpOverlap fixedS i j = nativeOverlaps fixedS i j := rfl
  have hT : HorizonOverlapTriangleTable fixedS (1 + (1 : ℝ) ^ 2) := by
    unfold HorizonOverlapTriangleTable
    norm_num [ho, nativeOverlaps_fixedS_eq, fpTriangle_eq_nativeTriangles,
      nativeTriangles_fixedS_eq, fixedSTriangleVal]
  have hQ := nativeCornerQ_eq_fpOmega fixedS
  rw [nativeCornerQ_fixedS] at hQ
  have hω1 : fpOmega1 fixedS = 1 / 18 := by simpa using congrFun hQ.symm 2
  have hω2 : fpOmega2 fixedS = 1 / 18 := by simpa using congrFun hQ.symm 0
  have hω3 : fpOmega3 fixedS = 1 / 18 := by simpa using congrFun hQ.symm 1
  simp only [fpOmega1, fpOmega2, fpOmega3] at hω1 hω2 hω3
  apply horizon_midpoint_le_six _ fixedS_isAtom hA _ _ horizon_sign_square hT
    _ _ _ w hw
  all_goals (norm_num; linarith)

private theorem horizon_roundTrip_diff (p : Fin 4 → Albert)
    (hp : ∀ i, IsAtom (p i)) (b d : ℝ) (hd : d ^ 2 = 1 / 2) (front : Word (Fin 4))
    (hfront : front = [(0,true),(2,false),(1,false)])
    (havg : nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) (front ++ [(3, true)]) =
      (1 / 2 : ℝ) * nativeWordProbability (horizonQuaternionicSector b d)
          ((1 / 3 : ℝ) • albertUnit) (front ++ [(3, true)]) +
      (1 / 2 : ℝ) * nativeWordProbability (horizonQuaternionicSector b (-d))
          ((1 / 3 : ℝ) • albertUnit) (front ++ [(3, true)])) :
    (1 / 2 : ℝ) * nativeWordProbability (horizonQuaternionicSector b d)
        ((1 / 3 : ℝ) • albertUnit) (scheduleRoundTrip front 3) +
      (1 / 2 : ℝ) * nativeWordProbability (horizonQuaternionicSector b (-d))
        ((1 / 3 : ℝ) • albertUnit) (scheduleRoundTrip front 3) -
        nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) (scheduleRoundTrip front 3) =
      3 * ((4 / 3 : ℝ) * (b * d / (18 * (1 + b ^ 2)))) ^ 2 := by
  subst front
  have hd' : (-d) ^ 2 = 1 / 2 := by simpa only [neg_sq] using hd
  have hP := horizonQuaternionicSector_isAtom b d hd
  have hM := horizonQuaternionicSector_isAtom b (-d) hd'
  obtain ⟨hTP, _, htP, _⟩ := horizonSectorTables b d hd
  obtain ⟨hTM, _, htM, _⟩ := horizonSectorTables b (-d) hd'
  obtain ⟨ho, hR⟩ := horizonTables_eq hP hM hTP hTM
  let word : Word (Fin 4) := [(0,true),(2,false),(1,false),(3,true)]
  let x := nativeWordProbability (horizonQuaternionicSector b d) ((1 / 3 : ℝ) • albertUnit) word
  let y := nativeWordProbability (horizonQuaternionicSector b (-d)) ((1 / 3 : ℝ) • albertUnit) word
  change nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) word =
    (1 / 2 : ℝ) * x + (1 / 2 : ℝ) * y at havg
  have hdiff : x - y = (8 / 3 : ℝ) * (b * d / (18 * (1 + b ^ 2))) := by
    have hx := schedule_signed_four_probability _ hP 0 2 1 3
    have hy := schedule_signed_four_probability _ hM 0 2 1 3
    change 3 * x = 4 * fpDoublePair2 (horizonQuaternionicSector b d) + _ at hx
    change 3 * y = 4 * fpDoublePair2 (horizonQuaternionicSector b (-d)) + _ at hy
    simp only [htP, ho, hR] at hx
    simp only [htM, mul_neg, neg_div] at hy
    linarith
  rw [scheduleRoundTrip_probability _ _ _ (hP 3), scheduleRoundTrip_probability _ _ _ (hM 3),
    scheduleRoundTrip_probability _ _ _ (hp 3)]
  change (1 / 2 : ℝ) * (3 * x^2) + (1 / 2 : ℝ) * (3 * y^2) -
    3 * nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) word ^ 2 = _
  rw [havg]
  calc
    _ = (3 / 4 : ℝ) * (x - y) ^ 2 := by ring
    _ = _ := by rw [hdiff]; ring

/-- Seven-step excess of the explicitly named M sectors. -/
theorem horizon_M_native_roundTrip_excess :
    (1 / 2 : ℝ) * nativeWordProbability (horizonMSector true)
        ((1 / 3 : ℝ) • albertUnit) scheduleFirstRoundTrip +
      (1 / 2 : ℝ) * nativeWordProbability (horizonMSector false)
        ((1 / 3 : ℝ) • albertUnit) scheduleFirstRoundTrip -
      nativeWordProbability maximizerConfig ((1 / 3 : ℝ) • albertUnit) scheduleFirstRoundTrip =
      4 / 2187 := by
  rw [scheduleFirstRoundTrip, horizonMSector, horizonMSector]
  simp only [↓reduceIte, Bool.false_eq_true]
  rw [horizon_roundTrip_diff _ maximizerConfig_isAtom _ _ horizon_sign_square _ rfl
    (horizon_M_native _ (by decide))]
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hinv : Real.sqrt 2 * (Real.sqrt 2)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
  rw [hs, hinv]
  norm_num

/-- Seven-step excess of the explicitly named S sectors. -/
theorem horizon_S_native_roundTrip_excess :
    (1 / 2 : ℝ) * nativeWordProbability (horizonSSector true)
        ((1 / 3 : ℝ) • albertUnit) scheduleFirstRoundTrip +
      (1 / 2 : ℝ) * nativeWordProbability (horizonSSector false)
        ((1 / 3 : ℝ) • albertUnit) scheduleFirstRoundTrip -
      nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) scheduleFirstRoundTrip =
      1 / 486 := by
  rw [scheduleFirstRoundTrip, horizonSSector, horizonSSector]
  simp only [↓reduceIte, Bool.false_eq_true]
  rw [horizon_roundTrip_diff _ fixedS_isAtom _ _ horizon_sign_square _ rfl
    (horizon_S_native _ (by decide))]
  rw [show (3 * ((4 / 3 : ℝ) * (1 * (Real.sqrt 2)⁻¹ / (18 * (1 + 1 ^ 2)))) ^ 2) =
      (2 / 486 : ℝ) * ((Real.sqrt 2)⁻¹) ^ 2 by ring]
  rw [horizon_sign_square]
  norm_num

theorem horizon_M_lMin : lMin maximizerConfig = 7 :=
  lMin_eq_seven _ maximizerConfig_isAtom (by rw [fourPointInvariant_maximizerConfig]; norm_num)

theorem horizon_S_lMin : lMin fixedS = 7 :=
  lMin_eq_seven _ fixedS_isAtom (by rw [fourPointInvariant_fixedS]; norm_num)

end AlbertSequential.MatchingModels
