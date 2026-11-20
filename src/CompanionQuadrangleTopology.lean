/- SPDX-License-Identifier: Apache-2.0 -/
module
public import WindowProbabilityAlbertInvariance
public import CompanionProjectiveMetricInvariant
public import SubalgebraCoordsAndLine
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Maps.Proper.Basic

@[expose] public section
noncomputable section
set_option maxHeartbeats 800000
namespace AlbertSequential.ProjectiveMetricInvariant
open NativeAnalysis WindowProbability MeasureTheory
open scoped WindowProbability
local instance : NormedAddCommGroup Octonion := inferInstanceAs (NormedAddCommGroup (Quaternion ℝ × Quaternion ℝ))
local instance : NormedSpace ℝ Octonion := inferInstanceAs (NormedSpace ℝ (Quaternion ℝ × Quaternion ℝ))
local instance : NormedAddCommGroup Albert := inferInstanceAs (NormedAddCommGroup ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
local instance : NormedSpace ℝ Albert := inferInstanceAs (NormedSpace ℝ ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
local instance : FiniteDimensional ℝ Albert := recoveredCoordinateEquiv.symm.finiteDimensional

def atomOrbitMap (g : AlbertAutomorphismGroup) : AlbertAtomSpace :=
  g • (⟨diagAtom 0, diagAtom_isAtom 0⟩ : AlbertAtomSpace)

theorem continuous_atomOrbitMap : Continuous atomOrbitMap := by
  apply Continuous.subtype_mk
  exact recoveredCoordinateEquiv.symm.toLinearMap.continuous_of_finiteDimensional.comp
    (AlbertAutomorphismGroup.continuous_evaluation.comp (continuous_id.prodMk continuous_const))

theorem nativeAtomSpace_compact : CompactSpace AlbertAtomSpace :=
  Function.Surjective.compactSpace continuous_atomOrbitMap albertAtomAction_transitive

/-- An ordered quadrangle has no triple on a common octonionic projective line. -/
def tripleNoncollinear (t : Fin 3 ↪ Fin 4) : Set (Fin 4 → AlbertAtomSpace) :=
  {p | ¬ ∃ q : AlbertAtomSpace, ∀ j, tracePairing (p (t j)).val q.val = 0}

def quadrangleLocus : Set (Fin 4 → AlbertAtomSpace) :=
  {p | ∀ t : Fin 3 ↪ Fin 4, ¬ ∃ q : AlbertAtomSpace, ∀ j, tracePairing (p (t j)).val q.val = 0}

private theorem quadrangleLocus_eq_iInter :
    quadrangleLocus = ⋂ t : Fin 3 ↪ Fin 4, tripleNoncollinear t := by
  apply Set.ext
  intro p
  change (∀ t, p ∈ tripleNoncollinear t) ↔ p ∈ ⋂ t, tripleNoncollinear t
  exact (Set.mem_iInter (s := tripleNoncollinear) (x := p)).symm

theorem tripleNoncollinear_isOpen (t : Fin 3 ↪ Fin 4) : IsOpen (tripleNoncollinear t) := by
  let _ := nativeAtomSpace_compact
  let X := (Fin 4 → AlbertAtomSpace) × AlbertAtomSpace
  let pair (j : Fin 3) : X → Albert × Albert := fun z => ((z.1 (t j)).val, z.2.val)
  let scalar (j : Fin 3) : X → ℝ := (fun xy : Albert × Albert => tracePairing xy.1 xy.2) ∘ pair j
  let bad (j : Fin 3) : Set X := (scalar j) ⁻¹' ({0} : Set ℝ)
  have hc (j : Fin 3) : IsClosed (bad j) := by
    have hv : Continuous (Subtype.val : AlbertAtomSpace → Albert) := continuous_subtype_val
    have hproj : Continuous (Prod.fst : X → Fin 4 → AlbertAtomSpace) := continuous_fst
    have heval : Continuous (fun p : Fin 4 → AlbertAtomSpace => p (t j)) := continuous_apply (t j)
    have hl : Continuous (fun z : X => (z.1 (t j)).val) := hv.comp (heval.comp hproj)
    have hr : Continuous (fun z : X => z.2.val) :=
      hv.comp (continuous_snd : Continuous (Prod.snd : X → AlbertAtomSpace))
    have hpair : Continuous (pair j) := hl.prodMk hr
    have hscalar : Continuous (scalar j) := continuous_tracePairing.comp hpair
    exact isClosed_singleton.preimage hscalar
  have he : tripleNoncollinear t = (Prod.fst '' (⋂ j, bad j))ᶜ := by
    apply Set.ext
    intro p
    change (¬ ∃ q : AlbertAtomSpace, ∀ j, tracePairing (p (t j)).val q.val = 0) ↔ _
    simp only [Set.mem_compl_iff, Set.mem_image, Prod.exists, Set.mem_iInter, bad, scalar, pair, Set.mem_preimage, Set.mem_singleton_iff, Function.comp_apply]
    constructor
    · rintro h ⟨p', q, hq, rfl⟩
      exact h ⟨q, hq⟩
    · rintro h ⟨q, hq⟩
      exact h ⟨p, q, hq, rfl⟩
  have hmap : IsClosedMap (Prod.fst : X → Fin 4 → AlbertAtomSpace) :=
    isClosedMap_fst_of_compactSpace
  have hclosed : IsClosed (Prod.fst '' (⋂ j, bad j)) := hmap _ (isClosed_iInter hc)
  exact he.symm ▸ hclosed.isOpen_compl

theorem quadrangleLocus_isOpen : IsOpen quadrangleLocus := by
  rw [quadrangleLocus_eq_iInter]
  exact isOpen_iInter_of_finite tripleNoncollinear_isOpen

/-- A fixed octonionic projective line has measure zero for the invariant atom law. -/
theorem ae_off_polar_line (q : AlbertAtomSpace) :
    ∀ᵐ p ∂albertChartAtomMeasure, 0 < tracePairing q.val p := by
  obtain ⟨g,hg⟩ := nativeAtomNormalizer_first q.val q.property
  have h := ae_albertChartAtomMeasure_firstDiagonal_pos
  rw [← map_nativeAutomorphism_albertChartAtomMeasure g] at h
  have hm : Measurable g.linearEquiv := g.linearEquiv.toLinearMap.continuous_of_finiteDimensional.measurable
  have hfst : Continuous (fun p : Albert => p.1 0) :=
    (continuous_apply (0 : Fin 3)).comp (continuous_fst : Continuous (fun p : Albert => p.1))
  have hmfst : Measurable (fun p : Albert => p.1 0) := hfst.measurable
  have hset : MeasurableSet {p : Albert | 0 < p.1 0} :=
    measurableSet_lt measurable_const hmfst
  filter_upwards [(ae_map_iff hm.aemeasurable hset).mp h] with p hp
  rw [← g.map_tracePairing, hg, tracePairing_diagAtom]
  exact hp

theorem dense_off_polar_line (q : AlbertAtomSpace) :
    Dense {p : AlbertAtomSpace | 0 < tracePairing q.val p.val} := by
  let μ := albertChartAtomMeasure.comap (Subtype.val : AlbertAtomSpace → Albert)
  have hm : μ = AlbertAutomorphismGroup.orbitAveragingMeasure.map atomOrbitMap :=
    atomMeasure_comap_orbitAveraging _ ae_albertChartAtomMeasure_isAtom
      map_nativeAutomorphism_albertChartAtomMeasure
  have hopen : AlbertAutomorphismGroup.orbitAveragingMeasure.IsOpenPosMeasure := by
    unfold AlbertAutomorphismGroup.orbitAveragingMeasure Measure.inv
    exact (Homeomorph.inv AlbertAutomorphismGroup).continuous.isOpenPosMeasure_map
      (Homeomorph.inv AlbertAutomorphismGroup).surjective
  have : μ.IsOpenPosMeasure := hm ▸ continuous_atomOrbitMap.isOpenPosMeasure_map albertAtomAction_transitive
  apply μ.dense_of_ae
  have hmap : μ.map Subtype.val = albertChartAtomMeasure :=
    (map_comap_subtype_coe measurableSet_atomSet _).trans
      (Measure.restrict_eq_self_of_ae_mem ae_albertChartAtomMeasure_isAtom)
  have h := ae_off_polar_line q
  rw [← hmap] at h
  exact (ae_map_iff measurable_subtype_coe.aemeasurable
    (measurableSet_lt measurable_const
      ((continuous_tracePairing.comp (continuous_const.prodMk continuous_id)).measurable))).mp h

theorem polar_unique_of_two_distinct {a b q r : AlbertAtomSpace} (hab : a ≠ b)
    (hqa : tracePairing q.val a.val = 0) (hqb : tracePairing q.val b.val = 0)
    (hra : tracePairing r.val a.val = 0) (hrb : tracePairing r.val b.val = 0) : q = r := by
  have hzero (p x : AlbertAtomSpace) (h : tracePairing p.val x.val = 0) :
      jordanMul p.val x.val = 0 :=
    (support_of_atom_zero_pairing acceptedAtomAndRankOneBridge p.property ⟨x.val,x.property.1.symm⟩ h).1
  have hsupport (p : AlbertAtomSpace) (ha : tracePairing p.val a.val = 0)
      (hb : tracePairing p.val b.val = 0) :=
    (eq_fiv_support _ _ _ p.property a.property b.property (hzero p a ha) (hzero p b hb)
      (fun he => hab (Subtype.ext he))).2
  exact Subtype.ext (sub_right_inj.mp ((hsupport q hqa hqb).trans (hsupport r hra hrb).symm))

private theorem exists_incident_polar (a : AlbertAtomSpace) :
    ∃ q : AlbertAtomSpace, tracePairing q.val a.val = 0 := by
  obtain ⟨g,hg⟩ := nativeAtomNormalizer_first a.val a.property
  refine ⟨⟨g.symm.linearEquiv (diagAtom 1), g.symm.map_isAtom (diagAtom_isAtom 1)⟩, ?_⟩
  rw [← g.map_tracePairing, hg]
  change tracePairing (g.linearEquiv (g.linearEquiv.symm (diagAtom 1))) (diagAtom 0) = 0
  rw [LinearEquiv.apply_symm_apply,tracePairing_diagAtom]
  rfl

private theorem exists_third (a b : AlbertAtomSpace) (hab : a ≠ b)
    (U : Set AlbertAtomSpace) (ho : IsOpen U) (hne : U.Nonempty) :
    ∃ c ∈ U, ¬ ∃ q : AlbertAtomSpace, tracePairing q.val a.val = 0 ∧
      tracePairing q.val b.val = 0 ∧ tracePairing q.val c.val = 0 := by
  by_cases h : ∃ q : AlbertAtomSpace, tracePairing q.val a.val = 0 ∧ tracePairing q.val b.val = 0
  · obtain ⟨q,hqa,hqb⟩ := h
    obtain ⟨c,hc,hU⟩ := (dense_off_polar_line q).exists_mem_open ho hne
    refine ⟨c,hU,?_⟩
    rintro ⟨r,hra,hrb,hrc⟩
    have he := polar_unique_of_two_distinct hab hqa hqb hra hrb
    exact (ne_of_gt hc) (he ▸ hrc)
  · obtain ⟨c,hc⟩ := hne
    exact ⟨c,hc,fun ⟨q,ha,hb,_⟩ => h ⟨q,ha,hb⟩⟩

theorem tripleNoncollinear_dense (t : Fin 3 ↪ Fin 4) : Dense (tripleNoncollinear t) := by
  classical
  apply dense_iff_inter_open.mpr
  rintro U hU ⟨p,hp⟩
  obtain ⟨V,hV,hVU⟩ := isOpen_pi_iff'.mp hU p hp
  let a := p (t 0)
  obtain ⟨q,hq⟩ := exists_incident_polar a
  obtain ⟨b,hb,hbV⟩ := (dense_off_polar_line q).exists_mem_open
    (hV (t 1)).1 ⟨_,(hV (t 1)).2⟩
  have hab : a ≠ b := fun he => (ne_of_gt hb) (he ▸ hq)
  obtain ⟨c,hcV,hc⟩ := exists_third a b hab _ (hV (t 2)).1 ⟨_,(hV (t 2)).2⟩
  let f := Function.update (Function.update p (t 1) b) (t 2) c
  have h0 : f (t 0) = a := by simp [f,a,t.injective.ne (by decide : (0 : Fin 3) ≠ 1),
    t.injective.ne (by decide : (0 : Fin 3) ≠ 2)]
  have h1 : f (t 1) = b := by simp [f,t.injective.ne (by decide : (1 : Fin 3) ≠ 2)]
  have h2 : f (t 2) = c := by simp [f]
  refine ⟨f,hVU (fun i _ => ?_),?_⟩
  · by_cases hi : i = t 2
    · subst i; simpa only [h2] using hcV
    by_cases hj : i = t 1
    · subst i; simpa only [h1] using hbV
    simpa [f,Function.update_of_ne hi,Function.update_of_ne hj] using (hV i).2
  · rintro ⟨r,hr⟩
    apply hc
    refine ⟨r,?_,?_,?_⟩
    · rw [tracePairing_comm, ← h0]
      exact hr 0
    · rw [tracePairing_comm, ← h1]
      exact hr 1
    · rw [tracePairing_comm, ← h2]
      exact hr 2

theorem quadrangleLocus_dense : Dense quadrangleLocus := by
  let _ := nativeAtomSpace_compact
  rw [quadrangleLocus_eq_iInter]
  exact dense_iInter_of_isOpen tripleNoncollinear_isOpen tripleNoncollinear_dense

end AlbertSequential.ProjectiveMetricInvariant
