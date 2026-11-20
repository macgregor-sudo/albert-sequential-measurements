/- SPDX-License-Identifier: Apache-2.0 -/
module

public import AcceptedRootAtomAdapter
public import NativeAtomReflections
public import NativeIdempotentClassification
public import NativeAtomSpanning
public import WindowProbabilityTransport
public import WindowProbabilityInvariant
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Topology.Maps.Proper.Basic

/-! The compact measurable group of the pinned Albert automorphisms.
Its topology is the verified topology of their basis images. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open MeasureTheory Set
open scoped AlbertSequential.WindowProbability

/-- The automorphism carrier equipped with group and topology instances. -/
def AlbertAutomorphismGroup := Glennie.CompactAutomorphism

namespace AlbertAutomorphismGroup

theorem aut_eq_of_apply_eq {g h : AlbertAutomorphismGroup} (e : ∀ x, g.equiv x = h.equiv x) : g = h := by
  have he : g.equiv = h.equiv := LinearEquiv.ext e
  rcases g with ⟨g, hg, ht⟩
  rcases h with ⟨h, hh, hu⟩
  change g = h at he
  subst h
  rfl

instance : Group AlbertAutomorphismGroup where
  one := Glennie.CompactAutomorphism.refl
  mul := Glennie.CompactAutomorphism.comp
  inv := Glennie.CompactAutomorphism.symm
  mul_assoc _ _ _ := aut_eq_of_apply_eq fun _ => rfl
  one_mul _ := aut_eq_of_apply_eq fun _ => rfl
  mul_one _ := aut_eq_of_apply_eq fun _ => rfl
  inv_mul_cancel g := aut_eq_of_apply_eq fun x => g.equiv.symm_apply_apply x

def columns (g : AlbertAutomorphismGroup) : Glennie.AutomorphismColumns :=
  Glennie.CompactAutomorphism.columns g

instance : TopologicalSpace AlbertAutomorphismGroup := TopologicalSpace.induced columns inferInstance

private def columnEquiv : AlbertAutomorphismGroup ≃ ↥Glennie.automorphismMaps where
  toFun g := ⟨columns g, g.columns_mem⟩
  invFun v := Glennie.compactAutomorphismOfMap v.1 v.2
  left_inv g := by
    apply aut_eq_of_apply_eq
    intro x
    let g' : Glennie.CompactAutomorphism := g
    change (Glennie.compactAutomorphismOfMap g'.columns g'.columns_mem).equiv x = g'.equiv x
    exact (Glennie.compactAutomorphismOfMap_apply g'.columns g'.columns_mem x).trans (g'.columns_apply x)
  right_inv v := by
    apply Subtype.ext
    funext i
    change (Glennie.compactAutomorphismOfMap v.1 v.2).equiv (Glennie.automorphismBasis i) = v.1 i
    rw [Glennie.compactAutomorphismOfMap_apply, Glennie.columnMap_basis]

private def columnHomeomorph : AlbertAutomorphismGroup ≃ₜ ↥Glennie.automorphismMaps where
  toEquiv := columnEquiv
  continuous_toFun := continuous_induced_dom.subtype_mk _
  continuous_invFun := continuous_induced_rng.mpr (by
    have h : columns ∘ columnEquiv.symm = Subtype.val := by
      funext v
      exact congrArg Subtype.val (columnEquiv.apply_symm_apply v)
    change Continuous (columns ∘ (columnEquiv.symm : ↥Glennie.automorphismMaps → AlbertAutomorphismGroup))
    rw [h]
    exact continuous_subtype_val)

instance : CompactSpace AlbertAutomorphismGroup := by
  let := isCompact_iff_compactSpace.mp Glennie.automorphismMaps_compact
  exact columnHomeomorph.symm.compactSpace

instance : T2Space AlbertAutomorphismGroup := columnHomeomorph.symm.t2Space

private theorem continuous_columnAction :
    Continuous (fun p : Glennie.AutomorphismColumns × Glennie.Albert => Glennie.columnMap p.1 p.2) := by
  simp_rw [Glennie.columnMap_apply]
  apply continuous_finsetSum
  intro i _
  have h :
      Continuous (fun x : Glennie.Albert => Glennie.automorphismBasis.equivFun x i) :=
    ((LinearMap.proj i).comp Glennie.automorphismBasis.equivFun.toLinearMap).continuous_of_finiteDimensional
  exact (h.comp continuous_snd).smul ((continuous_apply i).comp continuous_fst)

theorem continuous_evaluation :
    Continuous (fun p : AlbertAutomorphismGroup × Glennie.Albert => p.1.equiv p.2) := by
  have hcols : Continuous columns := continuous_induced_dom
  have h := continuous_columnAction.comp ((hcols.comp continuous_fst).prodMk continuous_snd)
  exact h.congr fun p => Glennie.CompactAutomorphism.columns_apply p.1 p.2

instance : ContinuousMul AlbertAutomorphismGroup where
  continuous_mul := continuous_induced_rng.mpr (by
    change Continuous (fun p : AlbertAutomorphismGroup × AlbertAutomorphismGroup => columns (p.1 * p.2))
    apply continuous_pi
    intro i
    change Continuous (fun p : AlbertAutomorphismGroup × AlbertAutomorphismGroup =>
      p.1.equiv (p.2.equiv (Glennie.automorphismBasis i)))
    exact continuous_evaluation.comp (continuous_fst.prodMk
      (continuous_evaluation.comp (continuous_snd.prodMk continuous_const))))

instance : IsTopologicalGroup AlbertAutomorphismGroup where
  continuous_inv := by
    apply continuous_of_isClosed_graph
    have h : (fun g : AlbertAutomorphismGroup => g⁻¹).graph =
        {p : AlbertAutomorphismGroup × AlbertAutomorphismGroup | p.1 * p.2 = 1} := by
      ext p
      change p.1⁻¹ = p.2 ↔ p.1 * p.2 = 1
      exact mul_eq_one_iff_inv_eq.symm
    rw [h]
    exact isClosed_eq (continuous_fst.mul continuous_snd) continuous_const

instance : MeasurableSpace AlbertAutomorphismGroup := borel _
instance : BorelSpace AlbertAutomorphismGroup := ⟨rfl⟩

def allAutomorphisms : TopologicalSpace.PositiveCompacts AlbertAutomorphismGroup :=
  ⟨⟨univ, isCompact_univ⟩, by simp⟩

/-- Haar probability with right invariance, obtained by inversion of the
Haar measure normalized on the entire compact group. -/
def orbitAveragingMeasure : Measure AlbertAutomorphismGroup :=
  (Measure.haarMeasure allAutomorphisms).inv

instance : IsProbabilityMeasure orbitAveragingMeasure := by
  have : IsProbabilityMeasure (Measure.haarMeasure allAutomorphisms) :=
    ⟨Measure.haarMeasure_self (K₀ := allAutomorphisms)⟩
  unfold orbitAveragingMeasure Measure.inv
  infer_instance

instance : orbitAveragingMeasure.IsMulRightInvariant := by
  unfold orbitAveragingMeasure
  infer_instance

end AlbertAutomorphismGroup

/-- The atom carrier with the Borel subspace measurable structure. -/
abbrev AlbertAtomSpace := {p : Albert // IsAtom p}

open NativeAnalysis

local instance : NormedAddCommGroup Octonion :=
  inferInstanceAs (NormedAddCommGroup (Quaternion ℝ × Quaternion ℝ))
local instance : NormedSpace ℝ Octonion :=
  inferInstanceAs (NormedSpace ℝ (Quaternion ℝ × Quaternion ℝ))
local instance : NormedAddCommGroup Albert :=
  inferInstanceAs (NormedAddCommGroup ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
local instance : NormedSpace ℝ Albert :=
  inferInstanceAs (NormedSpace ℝ ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
local instance : FiniteDimensional ℝ Albert := recoveredCoordinateEquiv.symm.finiteDimensional

/-- The compact group's action on the pinned native Albert coordinates. -/
def albertAutAction (g : AlbertAutomorphismGroup) (x : Albert) : Albert :=
  recoveredCoordinateEquiv.symm (g.equiv (recoveredCoordinateEquiv x))

theorem albertAutAction_eq_nativeAuto (g : AlbertAutomorphismGroup) (x : Albert) :
    albertAutAction g x = (compactAutoToNativeAuto g).linearEquiv x := rfl

instance : MulAction AlbertAutomorphismGroup AlbertAtomSpace where
  smul g p := ⟨albertAutAction g p.val, (compactAutoToNativeAuto g).map_isAtom p.property⟩
  one_smul p := Subtype.ext (recoveredCoordinateEquiv.symm_apply_apply p.val)
  mul_smul g h p := by
    apply Subtype.ext
    change recoveredCoordinateEquiv.symm (g.equiv (h.equiv (recoveredCoordinateEquiv p.val))) =
      recoveredCoordinateEquiv.symm (g.equiv (recoveredCoordinateEquiv
        (recoveredCoordinateEquiv.symm (h.equiv (recoveredCoordinateEquiv p.val)))))
    rw [LinearEquiv.apply_symm_apply]

theorem measurable_albertAutAction :
    Measurable (fun p : AlbertAutomorphismGroup × Albert => albertAutAction p.1 p.2) := by
  have h : Continuous recoveredCoordinateEquiv :=
    recoveredCoordinateEquiv.toLinearMap.continuous_of_finiteDimensional
  have hi : Continuous recoveredCoordinateEquiv.symm :=
    recoveredCoordinateEquiv.symm.toLinearMap.continuous_of_finiteDimensional
  exact (hi.comp (AlbertAutomorphismGroup.continuous_evaluation.comp
    (continuous_fst.prodMk (h.comp continuous_snd)))).measurable

theorem measurable_albertAtomAction :
    Measurable (fun p : AlbertAutomorphismGroup × AlbertAtomSpace => p.1 • p.2) :=
  (measurable_albertAutAction.comp
    (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))).subtype_mk

theorem albertAtomAction_transitive (p : AlbertAtomSpace) :
    ∃ g : AlbertAutomorphismGroup, g • (⟨diagAtom 0, diagAtom_isAtom 0⟩ : AlbertAtomSpace) = p := by
  obtain ⟨f, hf⟩ := nativeAtomNormalizer_first p.val p.property
  use nativeAutoToCompactAuto f.symm
  apply Subtype.ext
  change recoveredCoordinateEquiv.symm ((nativeAutoToCompactAuto f.symm).equiv
    (recoveredCoordinateEquiv (diagAtom 0))) = p.val
  simp only [nativeAutoToCompactAuto_apply, LinearEquiv.symm_apply_apply]
  change f.linearEquiv.symm (diagAtom 0) = p.val
  rw [← hf, LinearEquiv.symm_apply_apply]

theorem atomMeasure_comap_orbitAveraging
    (μ : Measure Albert) [IsProbabilityMeasure μ] (hμ : ∀ᵐ p ∂μ, IsAtom p)
    (hinv : ∀ g : NativeAlbertAutomorphism, μ.map g.linearEquiv = μ) :
    μ.comap (Subtype.val : AlbertAtomSpace → Albert) =
      AlbertAutomorphismGroup.orbitAveragingMeasure.map
        (fun g : AlbertAutomorphismGroup => g • (⟨diagAtom 0, diagAtom_isAtom 0⟩ : AlbertAtomSpace)) := by
  let ι : AlbertAtomSpace → Albert := Subtype.val
  let μA := μ.comap ι
  have hι : MeasurableEmbedding ι := MeasurableEmbedding.subtype_coe measurableSet_atomSet
  have hmap : μA.map ι = μ := by
    exact (map_comap_subtype_coe measurableSet_atomSet μ).trans
      (Measure.restrict_eq_self_of_ae_mem hμ)
  have : IsProbabilityMeasure μA :=
    (Measure.isProbabilityMeasure_map_iff hι.measurable.aemeasurable).mp (hmap ▸ ‹IsProbabilityMeasure μ›)
  apply invariantProbability_eq_orbitMap measurable_albertAtomAction _
    albertAtomAction_transitive AlbertAutomorphismGroup.orbitAveragingMeasure μA
  intro g
  have hm : Measurable (fun p : AlbertAtomSpace => g • p) :=
    measurable_albertAtomAction.comp measurable_prodMk_left
  refine ⟨hm, hι.map_injective ?_⟩
  have hn : Measurable (fun p : Albert => albertAutAction g p) :=
    measurable_albertAutAction.comp measurable_prodMk_left
  rw [Measure.map_map hι.measurable hm]
  change μA.map ((fun p : Albert => albertAutAction g p) ∘ ι) = _
  rw [← Measure.map_map hn hι.measurable, hmap]
  exact hinv (compactAutoToNativeAuto g)

/-- Two invariant probability laws supported on the native Albert atoms
coincide. -/
theorem invariantAlbertAtomMeasure_unique
    (μ ν : Measure Albert) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ p ∂μ, IsAtom p) (hν : ∀ᵐ p ∂ν, IsAtom p)
    (hμinv : ∀ g : NativeAlbertAutomorphism, μ.map g.linearEquiv = μ)
    (hνinv : ∀ g : NativeAlbertAutomorphism, ν.map g.linearEquiv = ν) :
    μ = ν := by
  have h := (atomMeasure_comap_orbitAveraging μ hμ hμinv).trans
    (atomMeasure_comap_orbitAveraging ν hν hνinv).symm
  have h' := congrArg (fun η : Measure AlbertAtomSpace => η.map (Subtype.val : AlbertAtomSpace → Albert)) h
  have hm : (μ.comap (Subtype.val : AlbertAtomSpace → Albert)).map Subtype.val = μ :=
    (map_comap_subtype_coe measurableSet_atomSet μ).trans (Measure.restrict_eq_self_of_ae_mem hμ)
  have hn : (ν.comap (Subtype.val : AlbertAtomSpace → Albert)).map Subtype.val = ν :=
    (map_comap_subtype_coe measurableSet_atomSet ν).trans (Measure.restrict_eq_self_of_ae_mem hν)
  exact hm.symm.trans (h'.trans hn)

private theorem albertTrace_univ_sum {ι : Type*} [Fintype ι] (p : ι → Albert) :
    albertTrace (∑ i, p i) = ∑ i, albertTrace (p i) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp [albertTrace_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, albertTrace_add, ih]

/-- Trace preservation follows from the unital Jordan-automorphism
hypotheses on the native Albert algebra. -/
theorem native_jordanAutomorphism_preserves_trace (f : Albert ≃ₗ[ℝ] Albert)
    (hprod : ∀ x y, f (jordanMul x y) = jordanMul (f x) (f y))
    (hunit : f albertUnit = albertUnit) (x : Albert) :
    albertTrace (f x) = albertTrace x := by
  obtain ⟨g, d, hg⟩ := nativeDiagonalization x
  let p := fun i : Fin 3 => g.linearEquiv.symm (diagAtom i)
  have hp (i : Fin 3) : IsAtom (p i) := g.symm.map_isAtom (diagAtom_isAtom i)
  have hsum : ∑ i, p i = albertUnit := by
    apply g.linearEquiv.injective
    rw [map_sum, g.preserves_unit]
    simp only [p, LinearEquiv.apply_symm_apply]
    have h := diagonalElement_eq_sum_atoms (fun _ => 1)
    simpa [diagonalElement, albertUnit] using h.symm
  have hx : x = ∑ i, d i • p i := by
    apply g.linearEquiv.injective
    rw [hg, map_sum]
    simp only [map_smul, p, LinearEquiv.apply_symm_apply]
    exact diagonalElement_eq_sum_atoms d
  have htrace : ∑ i, albertTrace (f (p i)) = 3 := by
    rw [← albertTrace_univ_sum, ← map_sum, hsum, hunit]
    norm_num [albertTrace, albertUnit]
  have hmin (i : Fin 3) : 1 ≤ albertTrace (f (p i)) := by
    have hid : jordanMul (f (p i)) (f (p i)) = f (p i) := by
      rw [← hprod, (hp i).1]
    rcases native_idempotent_trace_cases (f (p i)) hid with hzero | h | h | h
    · have hz := (isPositive_trace_eq_zero _ (isPositive_idempotent _ hid)).mp hzero
      have hz' : p i = 0 := f.injective (hz.trans f.map_zero.symm)
      have he := (hp i).2
      rw [hz', albertTrace_zero] at he
      norm_num at he
    all_goals linarith
  have hi (i : Fin 3) : albertTrace (f (p i)) = 1 := by
    rw [Fin.sum_univ_three] at htrace
    have h0 := hmin 0
    have h1 := hmin 1
    have h2 := hmin 2
    fin_cases i
    · change albertTrace (f (p 0)) = 1
      linarith
    · change albertTrace (f (p 1)) = 1
      linarith
    · change albertTrace (f (p 2)) = 1
      linarith
  rw [hx, map_sum, albertTrace_univ_sum, albertTrace_univ_sum]
  simp only [map_smul, albertTrace_smul, hi, mul_one]
  exact Finset.sum_congr rfl fun i _ => by rw [(hp i).2, mul_one]

end AlbertSequential.WindowProbability
