/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CompanionQuadrangleTopology
public import MatchingModels.UniversalSixAffinity
import Mathlib.Tactic.NormNum

@[expose] public section
noncomputable section

namespace AlbertSequential.ProjectiveMetricInvariant

open NativeAnalysis WindowProbability
open scoped WindowProbability

/-- Every two distinct points define a unique projective line, represented by its polar. -/
theorem existsUnique_polar_through_distinct (a b : AlbertAtomSpace) (hab : a ≠ b) :
    ∃! q : AlbertAtomSpace, tracePairing q.val a.val = 0 ∧ tracePairing q.val b.val = 0 := by
  have hp : ∀ i : Fin 3, IsAtom (![a.val, b.val, a.val] i) := by
    intro i
    fin_cases i
    · exact a.property
    · exact b.property
    · exact a.property
  obtain ⟨g, ha, ⟨r, s, c, _, _, _, _, _, hb⟩, _⟩ :=
    lemma_A_three ![a.val, b.val, a.val] hp
  let q : AlbertAtomSpace :=
    ⟨g.symm.linearEquiv (diagAtom 2), g.symm.map_isAtom (diagAtom_isAtom 2)⟩
  have hgq : g.linearEquiv q.val = diagAtom 2 := g.linearEquiv.apply_symm_apply _
  have hqa : tracePairing q.val a.val = 0 := by
    change g.linearEquiv a.val = diagAtom 0 at ha
    rw [← g.map_tracePairing, hgq, ha, tracePairing_diagAtom]
    rfl
  have hqb : tracePairing q.val b.val = 0 := by
    change g.linearEquiv b.val = _ at hb
    rw [← g.map_tracePairing, hgq, hb, tracePairing_diagAtom]
    change r * (diagAtom 0).1 2 + s * (diagAtom 1).1 2 + (slotElem01 (octonionScalar c)).1 2 = 0
    have h0 : (diagAtom 0).1 2 = 0 := rfl
    have h1 : (diagAtom 1).1 2 = 0 := rfl
    have hs : (slotElem01 (octonionScalar c)).1 2 = 0 := rfl
    simp only [h0, h1, hs, mul_zero, add_zero]
  exact ⟨q, ⟨hqa, hqb⟩, fun _ hr => polar_unique_of_two_distinct hab hr.1 hr.2 hqa hqb⟩

theorem cubicNorm_eq_zero_of_common_polar (a b c q : AlbertAtomSpace)
    (ha : tracePairing q.val a.val = 0) (hb : tracePairing q.val b.val = 0)
    (hc : tracePairing q.val c.val = 0) :
    albertCubicNorm (a.val + b.val + c.val) = 0 := by
  obtain ⟨g, hg⟩ := nativeAtomNormalizer_first q.val q.property
  have hz (x : AlbertAtomSpace) (hx : tracePairing q.val x.val = 0) :
      (g.linearEquiv x.val).1 0 = 0 ∧
      (g.linearEquiv x.val).2 0 = 0 ∧ (g.linearEquiv x.val).2 1 = 0 := by
    have h := hx
    rw [← g.map_tracePairing, hg, tracePairing_diagAtom] at h
    exact ⟨h, isAtom_zero_row0 (g.map_isAtom x.property) h⟩
  obtain ⟨ha0, ha01, ha02⟩ := hz a ha
  obtain ⟨hb0, hb01, hb02⟩ := hz b hb
  obtain ⟨hc0, hc01, hc02⟩ := hz c hc
  let p := g.linearEquiv a.val + g.linearEquiv b.val + g.linearEquiv c.val
  have h0 : p.1 0 = 0 := by
    change (g.linearEquiv a.val).1 0 + (g.linearEquiv b.val).1 0 + (g.linearEquiv c.val).1 0 = 0
    rw [ha0, hb0, hc0, zero_add, zero_add]
  have h01 : p.2 0 = 0 := by
    change (g.linearEquiv a.val).2 0 + (g.linearEquiv b.val).2 0 + (g.linearEquiv c.val).2 0 = 0
    rw [ha01, hb01, hc01, zero_add, zero_add]
  have h02 : p.2 1 = 0 := by
    change (g.linearEquiv a.val).2 1 + (g.linearEquiv b.val).2 1 + (g.linearEquiv c.val).2 1 = 0
    rw [ha02, hb02, hc02, zero_add, zero_add]
  rw [← g.map_cubicNorm, map_add, map_add]
  change albertCubicNorm p = 0
  have hn : octNormSq 0 = 0 := (octNormSq_eq_zero _).mpr rfl
  simp [albertCubicNorm, h0, h01, h02, hn, octonionMul_zero_left,
    octDot_zero_right]

/-- The maximizing metric configuration is an actual projective quadrangle. -/
theorem maximizerConfig_mem_quadrangleLocus :
    (fun i => (⟨maximizerConfig i, maximizerConfig_isAtom i⟩ : AlbertAtomSpace)) ∈ quadrangleLocus := by
  intro t
  rintro ⟨q, hq⟩
  let p (i : Fin 4) : AlbertAtomSpace := ⟨maximizerConfig i, maximizerConfig_isAtom i⟩
  have hz := cubicNorm_eq_zero_of_common_polar (p (t 0)) (p (t 1)) (p (t 2)) q
    (by rw [tracePairing_comm]; exact hq 0) (by rw [tracePairing_comm]; exact hq 1)
    (by rw [tracePairing_comm]; exact hq 2)
  rw [MatchingModels.albertCubicNorm_three_atoms (p (t 0)).property (p (t 1)).property
    (p (t 2)).property] at hz
  obtain ⟨ho, hR, _⟩ := maximizerConfig_traces 1
  have h01 := t.injective.ne (by decide : (0 : Fin 3) ≠ 1)
  have h02 := t.injective.ne (by decide : (0 : Fin 3) ≠ 2)
  have h12 := t.injective.ne (by decide : (1 : Fin 3) ≠ 2)
  change 1 - fpOverlap maximizerConfig (t 0) (t 1) - fpOverlap maximizerConfig (t 0) (t 2) -
    fpOverlap maximizerConfig (t 1) (t 2) +
      2 * tracePairing (maximizerConfig (t 0)) (jordanMul (maximizerConfig (t 1)) (maximizerConfig (t 2))) = 0 at hz
  have htr := hR _ _ _ h01 h02 h12
  unfold fpTriangle at htr
  rw [NativeAnalysis.tracePairing_associative] at htr
  rw [ho _ _ h01, ho _ _ h02, ho _ _ h12, htr] at hz
  norm_num at hz

def balancedRealAtom : AlbertAtomSpace :=
  ⟨(albertTrace (chartDyad octOne octOne))⁻¹ • chartDyad octOne octOne,
    chartDyad_normalize_isAtom octOne octOne⟩

def quadrangleAxis (i : Fin 3) : AlbertAtomSpace :=
  ⟨diagAtom i, diagAtom_isAtom i⟩

/-- The three axes and the ray of the real column (1,1,1). -/
def standardRealQuadrangle : Fin 4 → AlbertAtomSpace :=
  ![quadrangleAxis 0, quadrangleAxis 1, quadrangleAxis 2, balancedRealAtom]

private theorem balancedRealAtom_diagonal (i : Fin 3) :
    balancedRealAtom.val.1 i = 1 / 3 := by
  have htr : albertTrace (chartDyad octOne octOne) = 3 := by
    rw [chartDyad_trace, octNormSq_one]
    norm_num
  change (albertTrace (chartDyad octOne octOne))⁻¹ * (chartDyad octOne octOne).1 i = 1 / 3
  rw [htr]
  have hval : (chartDyad octOne octOne).1 i = 1 := by
    fin_cases i <;> exact octNormSq_one
  rw [hval, mul_one, one_div]

private theorem axes_distinct {i j : Fin 3} (h : i ≠ j) : quadrangleAxis i ≠ quadrangleAxis j := by
  intro he
  have hd := congrArg (fun a : AlbertAtomSpace => a.val.1 i) he
  change (if i = i then (1 : ℝ) else 0) = (if i = j then 1 else 0) at hd
  simp [h] at hd

private theorem axes_incidence {i j : Fin 3} (h : i ≠ j) :
    tracePairing (quadrangleAxis i).val (quadrangleAxis j).val = 0 := by
  change tracePairing (diagAtom i) (diagAtom j) = 0
  rw [tracePairing_diagAtom]
  change (if i = j then (1 : ℝ) else 0) = 0
  exact ite_eq_right h

private theorem axes_polar_excludes_balanced (q : AlbertAtomSpace) {i j k : Fin 3}
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (hi : tracePairing q.val (quadrangleAxis i).val = 0) (hj : tracePairing q.val (quadrangleAxis j).val = 0)
    (hb : tracePairing q.val balancedRealAtom.val = 0) : False := by
  have hq := polar_unique_of_two_distinct (axes_distinct hij) hi hj (axes_incidence hki) (axes_incidence hkj)
  rw [hq] at hb
  change tracePairing (diagAtom k) balancedRealAtom.val = 0 at hb
  rw [tracePairing_diagAtom, balancedRealAtom_diagonal] at hb
  norm_num at hb

private theorem triple_kind (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    let l : Finset (Fin 4) := {i, j, k}
    (0 ∈ l ∧ 1 ∈ l ∧ 2 ∈ l) ∨
      (3 ∈ l ∧ ((0 ∈ l ∧ 1 ∈ l) ∨ (0 ∈ l ∧ 2 ∈ l) ∨ (1 ∈ l ∧ 2 ∈ l))) := by
  have h : ∀ (i j k : Fin 4), i ≠ j → i ≠ k → j ≠ k →
    let l : Finset (Fin 4) := {i, j, k}
    (0 ∈ l ∧ 1 ∈ l ∧ 2 ∈ l) ∨
      (3 ∈ l ∧ ((0 ∈ l ∧ 1 ∈ l) ∨ (0 ∈ l ∧ 2 ∈ l) ∨ (1 ∈ l ∧ 2 ∈ l))) := by decide +kernel
  exact h i j k hij hik hjk

theorem standardRealQuadrangle_mem : standardRealQuadrangle ∈ quadrangleLocus := by
  intro t
  rintro ⟨q, h⟩
  let l : Finset (Fin 4) := {t 0, t 1, t 2}
  have hinc (i : Fin 4) (hi : i ∈ l) : tracePairing q.val (standardRealQuadrangle i).val = 0 := by
    change i ∈ ({t 0, t 1, t 2} : Finset (Fin 4)) at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl <;> rw [tracePairing_comm]
    · exact h 0
    · exact h 1
    · exact h 2
  rcases triple_kind (t 0) (t 1) (t 2) (t.injective.ne (by decide))
      (t.injective.ne (by decide)) (t.injective.ne (by decide)) with H | ⟨h3, H⟩
  · have h0 := hinc 0 H.1
    have h1 := hinc 1 H.2.1
    have h2 := hinc 2 H.2.2
    change tracePairing q.val (diagAtom 0) = 0 at h0
    change tracePairing q.val (diagAtom 1) = 0 at h1
    change tracePairing q.val (diagAtom 2) = 0 at h2
    rw [tracePairing_comm, tracePairing_diagAtom] at h0 h1 h2
    have ht := q.property.2
    rw [albertTrace, Fin.sum_univ_three, h0, h1, h2, zero_add, zero_add] at ht
    exact zero_ne_one ht
  · have hb : tracePairing q.val balancedRealAtom.val = 0 := hinc 3 h3
    rcases H with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩
    · exact axes_polar_excludes_balanced q (i := 0) (j := 1) (k := 2)
        (by decide) (by decide) (by decide) (hinc 0 hi) (hinc 1 hj) hb
    · exact axes_polar_excludes_balanced q (i := 0) (j := 2) (k := 1)
        (by decide) (by decide) (by decide) (hinc 0 hi) (hinc 2 hj) hb
    · exact axes_polar_excludes_balanced q (i := 1) (j := 2) (k := 0)
        (by decide) (by decide) (by decide) (hinc 1 hi) (hinc 2 hj) hb

theorem standardRealQuadrangle_invariant_zero :
    fourPointInvariant (fun i => (standardRealQuadrangle i).val) = 0 := by
  apply lemma_A_zero_of_quat standardQuaternionicWindow _ (fun i => (standardRealQuadrangle i).property)
  intro i
  rw [mem_standardQuaternionicWindow_iff]
  fin_cases i
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩
  · have h (j : Fin 3) : (balancedRealAtom.val.2 j).2 = 0 := by
      change (albertTrace (chartDyad octOne octOne))⁻¹ • ((chartDyad octOne octOne).2 j).2 = 0
      have hz : ((chartDyad octOne octOne).2 j).2 = 0 := by
        fin_cases j <;> simp [chartDyad, octDyad, octOne, octonionScalar, octonionConj, octonionMul]
      rw [hz, smul_zero]
    exact ⟨h 0, h 1, h 2⟩

/-- The metric four-point invariant takes distinct values on actual projective quadrangles. -/
theorem fourPointInvariant_not_constant_on_quadrangles :
    ∃ p ∈ quadrangleLocus, ∃ q ∈ quadrangleLocus,
      fourPointInvariant (fun i => (p i).val) ≠ fourPointInvariant (fun i => (q i).val) := by
  refine ⟨standardRealQuadrangle, standardRealQuadrangle_mem,
    (fun i => ⟨maximizerConfig i, maximizerConfig_isAtom i⟩), maximizerConfig_mem_quadrangleLocus, ?_⟩
  rw [standardRealQuadrangle_invariant_zero]
  change (0 : ℝ) ≠ fourPointInvariant maximizerConfig
  rw [fourPointInvariant_maximizerConfig]
  norm_num

end AlbertSequential.ProjectiveMetricInvariant
