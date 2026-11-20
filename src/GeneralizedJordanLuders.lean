/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ClassicalDensityRegister
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic.Linarith

/-! The positive square root and generalized Lüders instrument on a finite formally real Jordan algebra. -/
@[expose] public section
noncomputable section

open scoped BigOperators
namespace AlbertSequential.UnitalJordanProduct

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  (P : UnitalJordanProduct E) (hfr : P.FormallyReal)
local notation "τ" => P.canonicalTraceOfFormallyReal hfr
local notation "B" => P.canonicalTraceFormOfFormallyReal hfr

include hfr

theorem exists_positiveSquareRoot (a : E) (ha : a ∈ P.squareCone) :
    ∃ r ∈ P.squareCone, P.product r r = a := by
  obtain ⟨y, rfl⟩ := ha
  obtain ⟨n, lam, c, _, hc, horth, _, hy⟩ := P.spectral_resolution_of_formallyReal hfr y
  have hidem (i : Fin n) : P.product (c i) (c i) = c i := (hc i).2
  let r : E := ∑ i, |lam i| • c i
  refine ⟨r, ⟨∑ i, Real.sqrt |lam i| • c i, ?_⟩, ?_⟩
  · rw [P.square_of_orthogonal_expansion _ _ hidem horth]
    simp only [Real.sq_sqrt (abs_nonneg _), r]
  · calc
      P.product r r = ∑ i, (|lam i|)^2 • c i :=
        P.square_of_orthogonal_expansion _ _ hidem horth
      _ = ∑ i, (lam i)^2 • c i := by simp
      _ = P.product y y := by rw [hy, P.square_of_orthogonal_expansion _ _ hidem horth]

private theorem positiveElement_form_nonneg_on_square (u : E) (hu : u ∈ P.squareCone) (x : E) :
    0 ≤ B u (P.product x x) := by
  have hre : u = P.canonicalTraceRepresentative hfr (B u) :=
    P.canonicalTraceRepresentative_unique hfr (B u) u fun _ => rfl
  exact (P.canonicalTraceRepresentative_positive_iff hfr (B u)).mp (hre ▸ hu) x

private theorem positiveElement_form_null_pairing (u d : E) (hu : u ∈ P.squareCone)
    (hd : B u (P.product d d) = 0) : B u d = 0 := by
  have hunit (x : E) : P.product x P.unit = x := (P.commutative x _).trans (P.unit_left x)
  have hquad (t : ℝ) : 0 ≤ B u P.unit * (t * t) + (2 * B u d) * t + 0 := by
    have h := P.positiveElement_form_nonneg_on_square hfr u hu (d + t • P.unit)
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
      P.unit_left, hunit, smul_eq_mul, hd] at h
    linarith [show B u P.unit * (t * t) = t * (t * B u P.unit) by ring]
  have hdiscrim := discrim_le_zero hquad
  apply mul_self_eq_zero.mp
  unfold discrim at hdiscrim
  nlinarith [sq_nonneg (B u d)]

/-- The nonnegative square root is unique for the actual cone of squares. -/
theorem positiveSquareRoot_unique {u v : E} (hu : u ∈ P.squareCone) (hv : v ∈ P.squareCone)
    (hsq : P.product u u = P.product v v) : u = v := by
  let d : E := u - v
  have hprod : P.product (u + v) d = 0 := by
    simp only [d, map_add, LinearMap.add_apply, map_sub, P.commutative v u, hsq]
    abel
  have hsplit : B u (P.product d d) + B v (P.product d d) = 0 := by
    calc
      B u (P.product d d) + B v (P.product d d) = B (u + v) (P.product d d) := by
        rw [map_add, LinearMap.add_apply]
      _ = B (P.product (u + v) d) d := (P.canonicalTraceFormOfFormallyReal_associative hfr _ _ _).symm
      _ = 0 := by rw [hprod, map_zero, LinearMap.zero_apply]
  have hnu := P.positiveElement_form_nonneg_on_square hfr u hu d
  have hnv := P.positiveElement_form_nonneg_on_square hfr v hv d
  have hzu : B u (P.product d d) = 0 := by linarith
  have hzv : B v (P.product d d) = 0 := by linarith
  have hz : B d d = 0 := by
    calc
      B d d = B u d - B v d := LinearMap.congr_fun (map_sub B u v) d
      _ = 0 := by
        rw [P.positiveElement_form_null_pairing hfr u d hu hzu,
          P.positiveElement_form_null_pairing hfr v d hv hzv, sub_self]
  apply sub_eq_zero.mp
  by_contra hd
  exact (P.canonicalTraceFormOfFormallyReal_positive hfr d hd).ne' hz

def positiveSquareRoot (a : E) (ha : a ∈ P.squareCone) : E :=
  Classical.choose (P.exists_positiveSquareRoot hfr a ha)

theorem positiveSquareRoot_mem (a : E) (ha : a ∈ P.squareCone) :
    P.positiveSquareRoot hfr a ha ∈ P.squareCone :=
  (Classical.choose_spec (P.exists_positiveSquareRoot hfr a ha)).1

theorem positiveSquareRoot_square (a : E) (ha : a ∈ P.squareCone) :
    P.product (P.positiveSquareRoot hfr a ha) (P.positiveSquareRoot hfr a ha) = a :=
  (Classical.choose_spec (P.exists_positiveSquareRoot hfr a ha)).2

/-- The branch associated to an arbitrary positive effect uses its positive square root. -/
def generalizedLudersUpdate (a : E) (ha : a ∈ P.squareCone) : E →ₗ[ℝ] E :=
  P.quadraticRepresentation (P.positiveSquareRoot hfr a ha)

theorem generalizedLudersUpdate_of_idempotent (p : E) (hp : P.product p p = p) :
    P.generalizedLudersUpdate hfr p ⟨p, hp.symm⟩ = P.quadraticRepresentation p := by
  have hr := P.positiveSquareRoot_unique hfr
    (P.positiveSquareRoot_mem hfr p ⟨p, hp.symm⟩) ⟨p, hp.symm⟩
    ((P.positiveSquareRoot_square hfr p ⟨p, hp.symm⟩).trans hp.symm)
  exact congrArg (fun q => P.quadraticRepresentation q) hr

theorem generalizedLudersUpdate_positive (a : E) (ha : a ∈ P.squareCone)
    (x : E) (hx : x ∈ P.squareCone) : P.generalizedLudersUpdate hfr a ha x ∈ P.squareCone :=
  CanonicalInstruments.quadraticRepresentation_preserves_squareCone P hfr _ x hx

theorem generalizedLudersUpdate_trace (a : E) (ha : a ∈ P.squareCone) (x : E) :
    τ (P.generalizedLudersUpdate hfr a ha x) = B x a := by
  let r := P.positiveSquareRoot hfr a ha
  change τ (P.quadraticRepresentation r x) = B x a
  rw [P.quadraticRepresentation_apply, map_sub, map_smul]
  change 2 * τ (P.product r (P.product r x)) - τ (P.product (P.product r r) x) = τ (P.product x a)
  rw [← P.canonicalTraceOfFormallyReal_associative hfr r r x,
    show P.product r r = a from P.positiveSquareRoot_square hfr a ha, P.commutative a x]
  ring

theorem generalizedLudersUpdate_measuredEffect (a : E) (ha : a ∈ P.squareCone) :
    CanonicalInstruments.measuredEffect P hfr (P.generalizedLudersUpdate hfr a ha) = a :=
  (CanonicalInstruments.measuredEffect_unique P hfr _ a (P.generalizedLudersUpdate_trace hfr a ha)).symm

/-- Any finite positive decomposition of the unit gives an instrument with the assigned effects. -/
theorem generalizedLudersInstrument_normalized {ι : Type*} [Fintype ι]
    (a : ι → E) (ha : ∀ i, a i ∈ P.squareCone) (hsum : ∑ i, a i = P.unit) (x : E) :
    τ (∑ i, P.generalizedLudersUpdate hfr (a i) (ha i) x) = τ x := by
  rw [map_sum]
  simp only [P.generalizedLudersUpdate_trace hfr]
  rw [← map_sum, hsum, P.canonicalTraceFormOfFormallyReal_unit]

/-- The binary specialization has a normalized classical register with the same state updates
and chronological word probabilities. -/
theorem exists_classical_register_for_generalizedLuders {ι : Type*}
    (a : Outcome ι → E) (ha : ∀ b, a b ∈ P.squareCone)
    (hsum : ∀ i, a (i, true) + a (i, false) = P.unit) :
    let T (b : Outcome ι) := P.generalizedLudersUpdate hfr (a b) (ha b)
    ∃ R : ClassicalBinaryRegister ι {x : E // P.IsCanonicalDensity hfr x},
      (∀ b s, R.probability b s = B s.val (a b)) ∧
      (∀ b s, R.probability b s • (R.next b s).val = T b s.val) ∧
      (∀ s w, R.wordProbability s w = τ (w.foldl (fun x b => T b x) s.val)) := by
  intro T
  have hnorm (i : ι) (x : E) : τ (T (i, true) x + T (i, false) x) = τ x := by
    change τ (P.generalizedLudersUpdate hfr (a (i, true)) (ha _) x +
      P.generalizedLudersUpdate hfr (a (i, false)) (ha _) x) = _
    rw [map_add, P.generalizedLudersUpdate_trace hfr, P.generalizedLudersUpdate_trace hfr,
      ← map_add, hsum i, P.canonicalTraceFormOfFormallyReal_unit]
  obtain ⟨R, hp, hraw, hwords⟩ := P.exists_classical_density_register hfr T
    (fun b x hx => P.generalizedLudersUpdate_positive hfr (a b) (ha b) x hx) hnorm
  refine ⟨R, fun b s => (hp b s).trans ?_, hraw, hwords⟩
  exact P.generalizedLudersUpdate_trace hfr (a b) (ha b) s.val

end AlbertSequential.UnitalJordanProduct
