/- SPDX-License-Identifier: Apache-2.0 -/
module

public import AcceptedRootAtomAdapter
public import ComplexWindowDeterminantAndMax

@[expose] public section
noncomputable section

namespace AlbertSequential
namespace ProjectiveMetricInvariant

open NativeAnalysis

private theorem extCoords {x y : Albert} (h0 : x.1 0 = y.1 0) (h1 : x.1 1 = y.1 1)
    (h2 : x.1 2 = y.1 2) (h3 : x.2 0 = y.2 0) (h4 : x.2 1 = y.2 1)
    (h5 : x.2 2 = y.2 2) : x = y := by
  apply Prod.ext <;> funext i <;> fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

def diagScale (u v : ℝ) (x : Albert) : Albert :=
  (![x.1 0, u^2 * x.1 1, v^2 * x.1 2], ![u • x.2 0, v • x.2 1, (u*v) • x.2 2])

private theorem diagScale_comp (a b c d : ℝ) (x : Albert) :
    diagScale a b (diagScale c d x) = diagScale (a*c) (b*d) x := by
  apply extCoords <;> simp [diagScale, smul_smul] <;> ring_nf

private theorem diagScale_one (x : Albert) : diagScale 1 1 x = x := by
  apply extCoords <;> simp [diagScale]

def diagonalCongruence (u v : ℝ) (hu : u ≠ 0) (hv : v ≠ 0) : Albert ≃ₗ[ℝ] Albert where
  toFun := diagScale u v
  invFun := diagScale u⁻¹ v⁻¹
  left_inv x := by rw [diagScale_comp, inv_mul_cancel₀ hu, inv_mul_cancel₀ hv, diagScale_one]
  right_inv x := by rw [diagScale_comp, mul_inv_cancel₀ hu, mul_inv_cancel₀ hv, diagScale_one]
  map_add' x y := by
    apply extCoords
    · rfl
    · exact mul_add _ _ _
    · exact mul_add _ _ _
    · exact smul_add _ _ _
    · exact smul_add _ _ _
    · exact smul_add _ _ _
  map_smul' a x := by
    apply extCoords
    · rfl
    · change u^2 * (a * x.1 1) = a * (u^2 * x.1 1); ring
    · change v^2 * (a * x.1 2) = a * (v^2 * x.1 2); ring
    · exact smul_comm u a (x.2 0)
    · exact smul_comm v a (x.2 1)
    · exact smul_comm (u*v) a (x.2 2)

/-- The diagonal congruence `diag(1,2,1/2)` on the native Albert matrices. -/
def rescale : Albert ≃ₗ[ℝ] Albert := diagonalCongruence 2 (1/2) (by norm_num) (by norm_num)

theorem rescale_cubicNorm (x : Albert) : albertCubicNorm (rescale x) = albertCubicNorm x := by
  change albertCubicNorm (diagScale 2 (1/2) x) = _
  simp [albertCubicNorm, diagScale, octNormSq_smul, octonionMul_smul_left,
    octDot_smul_left, octDot_smul_right]
  ring

private theorem rescale_sharp (x : Albert) :
    albertSharp (rescale x) = rescale.symm (albertSharp x) := by
  change albertSharp (diagScale 2 (1/2) x) = diagScale (2 : ℝ)⁻¹ (1/2 : ℝ)⁻¹ (albertSharp x)
  apply extCoords <;> norm_num [albertSharp, diagScale, octNormSq_smul, octonionConj_smul,
    octonionMul_smul_left, octonionMul_smul_right, smul_smul, smul_sub]
  case h0 => ring
  case h1 => ring
  case h2 => ring
  all_goals module

private theorem positive_trace_rescale {p : Albert} (hp : IsAtom p) : 0 < albertTrace (rescale p) := by
  have ht := hp.2
  rw [albertTrace, Fin.sum_univ_three] at ht
  change 0 < albertTrace (diagScale 2 (1/2) p)
  simp [albertTrace, Fin.sum_univ_three, diagScale]
  linarith [isAtom_diag_nonneg hp 0, isAtom_diag_nonneg hp 1]

private theorem isAtom_of_sharp_zero_trace_one {p : Albert} (hs : albertSharp p = 0)
    (ht : albertTrace p = 1) : IsAtom p := by
  let s := (1 / 2 : ℝ) * (1 - albertTrace (jordanMul p p))
  have he : (0 : Albert) = jordanMul p p - p + s • albertUnit := by
    simpa [tracePairing, s, ht, hs] using albertSharp_eq_jordanMul p
  have h := congrArg albertTrace he
  have hu : albertTrace albertUnit = 3 := by norm_num [albertTrace, Fin.sum_univ_three, albertUnit]
  rw [albertTrace_add, albertTrace_sub, albertTrace_smul, ht, hu] at h
  have hz : albertTrace (0 : Albert) = 0 := by simp [albertTrace, show ((0 : Albert).1) = 0 from rfl]
  rw [hz] at h
  have hs0 : s = 0 := by linarith [show s = (1 / 2 : ℝ) * (1 - albertTrace (jordanMul p p)) from rfl]
  rw [hs0, zero_smul, add_zero] at he
  exact ⟨sub_eq_zero.mp he.symm, ht⟩

/-- The action on the trace-one representatives of positive rank-one rays. -/
def rescaledAtom (p : Albert) : Albert := (albertTrace (rescale p))⁻¹ • rescale p

theorem rescaledAtom_isAtom {p : Albert} (hp : IsAtom p) : IsAtom (rescaledAtom p) := by
  apply isAtom_of_sharp_zero_trace_one
  · rw [rescaledAtom, albertSharp_smul, rescale_sharp, albertSharp_atom_eq_zero p hp, map_zero, smul_zero]
  · rw [rescaledAtom, albertTrace_smul, inv_mul_cancel₀ (positive_trace_rescale hp).ne']

/-- The contragredient action on the trace-one normals to rank-two supports. -/
def dualRescaledAtom (q : Albert) : Albert := (albertTrace (rescale.symm q))⁻¹ • rescale.symm q

private theorem positive_trace_dualRescale {q : Albert} (hq : IsAtom q) :
    0 < albertTrace (rescale.symm q) := by
  have ht := hq.2
  rw [albertTrace, Fin.sum_univ_three] at ht
  change 0 < albertTrace (diagScale (2 : ℝ)⁻¹ (1/2 : ℝ)⁻¹ q)
  norm_num [albertTrace, Fin.sum_univ_three, diagScale]
  linarith [isAtom_diag_nonneg hq 0, isAtom_diag_nonneg hq 2]

theorem dualRescaledAtom_isAtom {q : Albert} (hq : IsAtom q) : IsAtom (dualRescaledAtom q) := by
  apply isAtom_of_sharp_zero_trace_one
  · have hs := congrArg rescale (rescale_sharp (rescale.symm q))
    simp only [LinearEquiv.apply_symm_apply] at hs
    rw [dualRescaledAtom, albertSharp_smul, ← hs, albertSharp_atom_eq_zero q hq, map_zero, smul_zero]
  · rw [dualRescaledAtom, albertTrace_smul, inv_mul_cancel₀ (positive_trace_dualRescale hq).ne']

private theorem normalized_inverse (g : Albert ≃ₗ[ℝ] Albert) (p : Albert)
    (hp : albertTrace p = 1) (hg : albertTrace (g p) ≠ 0) :
    let q := (albertTrace (g p))⁻¹ • g p
    (albertTrace (g.symm q))⁻¹ • g.symm q = p := by
  dsimp only
  rw [map_smul, LinearEquiv.symm_apply_apply, albertTrace_smul, hp, mul_one,
    inv_inv, smul_smul, mul_inv_cancel₀ hg, one_smul]

def atomRayRescaling : {p : Albert // IsAtom p} ≃ {p : Albert // IsAtom p} where
  toFun p := ⟨rescaledAtom p, rescaledAtom_isAtom p.property⟩
  invFun q := ⟨dualRescaledAtom q, dualRescaledAtom_isAtom q.property⟩
  left_inv p := by
    apply Subtype.ext
    exact normalized_inverse rescale p p.property.2 (positive_trace_rescale p.property).ne'
  right_inv q := by
    apply Subtype.ext
    exact normalized_inverse rescale.symm q q.property.2 (positive_trace_dualRescale q.property).ne'

private theorem rescale_dual_tracePairing (p q : Albert) :
    tracePairing (rescale p) (rescale.symm q) = tracePairing p q := by
  change tracePairing (diagScale 2 (1/2) p) (diagScale (2 : ℝ)⁻¹ (1/2 : ℝ)⁻¹ q) = _
  rw [tracePairing_eq_coords, tracePairing_eq_coords p q]
  norm_num [diagScale, octDot_smul_left, octDot_smul_right]
  ring

/-- Incidence with the rank-two support orthogonal to `q` is preserved by
rescaling the point and applying the dual rescaling to the line normal. -/
theorem rescaledAtom_incidence_iff {p q : Albert} (hp : IsAtom p) (hq : IsAtom q) :
    tracePairing (rescaledAtom p) (dualRescaledAtom q) = 0 ↔ tracePairing p q = 0 := by
  rw [rescaledAtom, dualRescaledAtom, tracePairing_smul_left, tracePairing_smul_right, rescale_dual_tracePairing]
  rw [mul_eq_zero, or_iff_right (inv_ne_zero (positive_trace_rescale hp).ne'),
    mul_eq_zero, or_iff_right (inv_ne_zero (positive_trace_dualRescale hq).ne')]

theorem compactAutomorphism_invariant (g : NativeAlbertAutomorphism) (p : Fin 4 → Albert) :
    fourPointInvariant (fun i => g.linearEquiv (p i)) = fourPointInvariant p :=
  fourPointInvariant_automorphism_invariant g p

private theorem octNormSq_scalar_eq (r : ℝ) : octNormSq (octonionScalar r) = r ^ 2 := by
  rw [octNormSq_eq_coords]
  simp [octonionScalar]

private theorem normSq_zero : octNormSq 0 = 0 := (octNormSq_eq_zero 0).mpr rfl

private theorem maximalMenu_zero : maximizerConfig 0 = diagAtom 0 := by
  change octDyad ![octonionScalar 1, 0, 0] = _
  apply extCoords <;> simp [octDyad, diagAtom, octNormSq_scalar_eq, normSq_zero,
    octonionConj_zero, octonionMul_zero_right]

private theorem maximalMenu_one_diag : (maximizerConfig 1).1 0 = 1/3 ∧
    (maximizerConfig 1).1 1 = 2/3 ∧ (maximizerConfig 1).1 2 = 0 := by
  change octNormSq (octonionScalar (1 / Real.sqrt 3)) = 1/3 ∧
    octNormSq (octonionScalar (Real.sqrt 2 / Real.sqrt 3)) = 2/3 ∧ octNormSq 0 = 0
  rw [octNormSq_scalar_eq, octNormSq_scalar_eq, normSq_zero, div_pow, div_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

private theorem rescaled_maximalMenu_zero : rescaledAtom (maximizerConfig 0) = diagAtom 0 := by
  rw [maximalMenu_zero, rescaledAtom]
  have he : rescale (diagAtom 0) = diagAtom 0 := by
    change diagScale 2 (1/2) (diagAtom 0) = diagAtom 0
    apply extCoords <;> norm_num [diagScale, diagAtom]
  rw [he, (diagAtom_isAtom 0).2, inv_one, one_smul]

theorem rescaled_maximalMenu_overlap :
    tracePairing (rescaledAtom (maximizerConfig 0)) (rescaledAtom (maximizerConfig 1)) = 1/9 := by
  obtain ⟨h0, h1, h2⟩ := maximalMenu_one_diag
  rw [rescaled_maximalMenu_zero, tracePairing_diagAtom, rescaledAtom]
  change (albertTrace (diagScale 2 (1/2) (maximizerConfig 1)))⁻¹ * (maximizerConfig 1).1 0 = _
  norm_num [albertTrace, Fin.sum_univ_three, diagScale, h0, h1, h2]

/-- The four-point invariant changes under the induced action of a literal
cubic-norm-preserving linear equivalence on rank-one rays. -/
theorem rescaled_maximalMenu_invariant_lt :
    fourPointInvariant (rescaledAtom ∘ maximizerConfig) < fourPointInvariant maximizerConfig := by
  let p := rescaledAtom ∘ maximizerConfig
  have hp : ∀ i, IsAtom (p i) := fun i => rescaledAtom_isAtom (maximizerConfig_isAtom i)
  rw [fourPointInvariant_maximizerConfig]
  refine lt_of_le_of_ne (prop_max.1 p hp).2 ?_
  intro he
  obtain ⟨g, hg⟩ := (prop_max.2.1 p hp).mp he
  have hpair := g.map_tracePairing (p 0) (p 1)
  rw [hg 0, hg 1] at hpair
  change fpOverlap maximizerConfig 0 1 = _ at hpair
  rw [(maximizerConfig_traces 1).1 0 1 (by decide)] at hpair
  change (1/3 : ℝ) = tracePairing (rescaledAtom (maximizerConfig 0))
    (rescaledAtom (maximizerConfig 1)) at hpair
  rw [rescaled_maximalMenu_overlap] at hpair
  norm_num at hpair

/-- The conclusion of the projective argument once density and constancy on
the quadrangle locus are established for the action in question. -/
theorem constant_of_dense_locus {X : Type*} [TopologicalSpace X] (quadrangles : Set X)
    (hd : Dense quadrangles) (f : X → ℝ) (hf : Continuous f) (c : ℝ)
    (h : ∀ x ∈ quadrangles, f x = c) : ∀ x, f x = c := by
  intro x
  have hsub : quadrangles ⊆ {y | f y = c} := fun _ hy => h _ hy
  exact closure_minimal hsub (isClosed_eq hf continuous_const) (hd x)

theorem invariant_constant_of_dense_transitive_locus {X G : Type*} [TopologicalSpace X]
    [Group G] [MulAction G X] (quadrangles : Set X) (hd : Dense quadrangles)
    (ht : ∀ x ∈ quadrangles, ∀ y ∈ quadrangles, ∃ g : G, g • x = y)
    (f : X → ℝ) (hf : Continuous f) (hi : ∀ (g : G) (x : X), f (g • x) = f x) :
    ∀ x y, f x = f y := by
  intro x y
  have : Nonempty X := ⟨x⟩
  obtain ⟨q, hq⟩ := hd.nonempty
  have hc := constant_of_dense_locus quadrangles hd f hf (f q) (fun z hz => by
    obtain ⟨g, rfl⟩ := ht q hq z hz
    exact hi g q)
  exact (hc x).trans (hc y).symm

end ProjectiveMetricInvariant
end AlbertSequential
