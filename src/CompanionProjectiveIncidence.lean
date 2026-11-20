/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CompanionProjectiveTriples

@[expose] public section
noncomputable section

namespace AlbertSequential.ProjectiveMetricInvariant

open NativeAnalysis WindowProbability

theorem CubicRayEquiv.pointMap_collinear_iff (g : CubicRayEquiv) (p : Fin 3 → AlbertAtomSpace) :
    (∃ q : AlbertAtomSpace, ∀ i, tracePairing (g.pointMap (p i)).val q.val = 0) ↔
      ∃ q : AlbertAtomSpace, ∀ i, tracePairing (p i).val q.val = 0 := by
  rw [← cubicNorm_weightedAtoms_eq_zero_iff (fun i => g.pointMap (p i))
    (fun i => albertTrace (g.linearEquiv (p i).val)) (fun i => g.trace_pos (p i))]
  rw [← cubicNorm_weightedAtoms_eq_zero_iff p (fun _ => 1) (fun _ => zero_lt_one)]
  simp only [← g.raw_pointMap, ← map_sum, g.map_norm, one_smul, mul_eq_zero,
    g.scale_pos.ne', false_or]

private theorem exists_two_distinct_points_on_line (q : AlbertAtomSpace) :
    ∃ a b : AlbertAtomSpace, a ≠ b ∧
      tracePairing q.val a.val = 0 ∧ tracePairing q.val b.val = 0 := by
  obtain ⟨g, hg⟩ := nativeAtomNormalizer_first q.val q.property
  let a : AlbertAtomSpace := ⟨g.symm.linearEquiv (diagAtom 1), g.symm.map_isAtom (diagAtom_isAtom 1)⟩
  let b : AlbertAtomSpace := ⟨g.symm.linearEquiv (diagAtom 2), g.symm.map_isAtom (diagAtom_isAtom 2)⟩
  have hga : g.linearEquiv a.val = diagAtom 1 := g.linearEquiv.apply_symm_apply _
  have hgb : g.linearEquiv b.val = diagAtom 2 := g.linearEquiv.apply_symm_apply _
  refine ⟨a, b, ?_, ?_, ?_⟩
  · intro h
    have h' : diagAtom 1 = diagAtom 2 := hga.symm.trans ((congrArg
      (fun p : AlbertAtomSpace => g.linearEquiv p.val) h).trans hgb)
    have h'' := congrArg (fun x : Albert => x.1 1) h'
    change (1 : ℝ) = 0 at h''
    exact one_ne_zero h''
  · rw [← g.map_tracePairing, hg, hga, tracePairing_diagAtom]
    rfl
  · rw [← g.map_tracePairing, hg, hgb, tracePairing_diagAtom]
    rfl

/-- A projective change sends the full set of points incident with a line to a line. -/
theorem CubicRayEquiv.existsUnique_lineMap (g : CubicRayEquiv) (q : AlbertAtomSpace) :
    ∃! r : AlbertAtomSpace, ∀ x : AlbertAtomSpace,
      tracePairing r.val (g.pointMap x).val = 0 ↔ tracePairing q.val x.val = 0 := by
  obtain ⟨a, b, hab, hqa, hqb⟩ := exists_two_distinct_points_on_line q
  have hab' : g.pointMap a ≠ g.pointMap b := by
    intro h
    apply hab
    simpa only [g.symm_pointMap] using congrArg g.symm.pointMap h
  obtain ⟨r, ⟨ha, hb⟩, _⟩ := existsUnique_polar_through_distinct
    (g.pointMap a) (g.pointMap b) hab'
  refine ⟨r, ?_, fun z hz => polar_unique_of_two_distinct hab' ((hz a).mpr hqa)
    ((hz b).mpr hqb) ha hb⟩
  intro x
  let p : Fin 3 → AlbertAtomSpace := ![a,b,x]
  have hsource : (∃ z : AlbertAtomSpace, ∀ i, tracePairing (p i).val z.val = 0) ↔
      tracePairing q.val x.val = 0 := by
    constructor
    · rintro ⟨z, hz⟩
      have hza : tracePairing z.val a.val = 0 := by rw [tracePairing_comm]; exact hz 0
      have hzb : tracePairing z.val b.val = 0 := by rw [tracePairing_comm]; exact hz 1
      rw [← polar_unique_of_two_distinct hab hza hzb hqa hqb, tracePairing_comm]
      exact hz 2
    · intro hx
      refine ⟨q, fun i => ?_⟩
      rw [tracePairing_comm]
      fin_cases i
      · exact hqa
      · exact hqb
      · exact hx
  have htarget : (∃ z : AlbertAtomSpace, ∀ i, tracePairing (g.pointMap (p i)).val z.val = 0) ↔
      tracePairing r.val (g.pointMap x).val = 0 := by
    constructor
    · rintro ⟨z, hz⟩
      have hza : tracePairing z.val (g.pointMap a).val = 0 := by rw [tracePairing_comm]; exact hz 0
      have hzb : tracePairing z.val (g.pointMap b).val = 0 := by rw [tracePairing_comm]; exact hz 1
      rw [← polar_unique_of_two_distinct hab' hza hzb ha hb, tracePairing_comm]
      exact hz 2
    · intro hx
      refine ⟨r, fun i => ?_⟩
      rw [tracePairing_comm]
      fin_cases i
      · exact ha
      · exact hb
      · exact hx
  exact htarget.symm.trans ((g.pointMap_collinear_iff p).trans hsource)

end AlbertSequential.ProjectiveMetricInvariant
