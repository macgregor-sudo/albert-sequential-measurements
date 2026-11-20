/- SPDX-License-Identifier: Apache-2.0 -/
module
public import CanonicalSupport
public import CompleteFrameQutritComparison
public import FieldDimensionTableEquivalence
public import GeneralEJAWordTransport

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential

open scoped Matrix ComplexOrder

/-- Coordinates for the defining Jordan product of a real spin factor. -/
structure SpinFactorCoordinates {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : UnitalJordanProduct E) (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W] where
  coordinates : E ≃ₗ[ℝ] ℝ × W
  unit : coordinates P.unit = (1, 0)
  product : ∀ x y, coordinates (P.product x y) =
    ((coordinates x).1 * (coordinates y).1 + inner ℝ (coordinates x).2 (coordinates y).2,
      (coordinates x).1 • (coordinates y).2 + (coordinates y).1 • (coordinates x).2)

namespace UnitalJordanProduct

/-- Tables of all words from an idempotent menu and one canonical density. -/
def canonicalProjectiveTables {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (P : UnitalJordanProduct E) (hfr : P.FormallyReal) (n : ℕ) : Set (Word (Fin n) → ℝ) :=
  {f | ∃ (p : Fin n → E) (ρ : E), (∀ i, P.product (p i) (p i) = p i) ∧
    P.IsCanonicalDensity hfr ρ ∧ ∀ w, P.canonicalPairingFunctional hfr ρ (P.sequentialWordEffect p w) = f w}

private theorem sequentialWordEffect_yes {E ι : Type*} [AddCommGroup E] [Module ℝ E]
    (P : UnitalJordanProduct E) (p : ι → E) (hp : ∀ i, P.product (p i) (p i) = p i) (i : ι) :
    P.sequentialWordEffect p [(i, true)] = p i :=
  (P.quadraticRepresentation_unit (p i)).trans (hp i)

end UnitalJordanProduct

namespace SpinFactorCoordinates

variable {E W : Type*} [AddCommGroup E] [Module ℝ E] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {P : UnitalJordanProduct E} (S : SpinFactorCoordinates P W)

theorem idempotent_cases (x : E) (hx : P.product x x = x) :
    x = 0 ∨ x = P.unit ∨ (S.coordinates x).1 = 1 / 2 := by
  have hxy := (S.product x x).symm.trans (congrArg S.coordinates hx)
  have hscalar := congrArg Prod.fst hxy
  have hvector := congrArg Prod.snd hxy
  change (S.coordinates x).1 * (S.coordinates x).1 +
    inner ℝ (S.coordinates x).2 (S.coordinates x).2 = (S.coordinates x).1 at hscalar
  change (S.coordinates x).1 • (S.coordinates x).2 +
    (S.coordinates x).1 • (S.coordinates x).2 = (S.coordinates x).2 at hvector
  by_cases hv : (S.coordinates x).2 = 0
  · rw [hv, inner_zero_left, add_zero] at hscalar
    have hf : (S.coordinates x).1 * ((S.coordinates x).1 - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hf with h0 | h1
    · left
      apply S.coordinates.injective
      rw [map_zero]
      exact Prod.ext h0 hv
    · right; left
      apply S.coordinates.injective
      rw [S.unit]
      exact Prod.ext (sub_eq_zero.mp h1) hv
  · right; right
    have hsmul : (2 * (S.coordinates x).1 - 1) • (S.coordinates x).2 = 0 := by
      rw [sub_smul, mul_smul, two_smul, one_smul, hvector, sub_self]
    have h := (smul_eq_zero.mp hsmul).resolve_right hv
    linarith

private theorem nonzero_idempotent_scalar_ge_half (x : E) (hx : P.product x x = x) (h0 : x ≠ 0) :
    1 / 2 ≤ (S.coordinates x).1 := by
  rcases S.idempotent_cases x hx with hz | hu | hh
  · exact (h0 hz).elim
  · rw [hu, S.unit]
    norm_num
  · exact hh.ge

include S in
theorem primitive_of_nontrivial_idempotent (x : E) (hx : P.product x x = x)
    (h0 : x ≠ 0) (h1 : x ≠ P.unit) : P.IsPrimitive x := by
  refine ⟨hx, h0, fun r s hr hs _ hsum => ?_⟩
  by_contra h
  push Not at h
  have hrhalf := S.nonzero_idempotent_scalar_ge_half r hr h.1
  have hshalf := S.nonzero_idempotent_scalar_ge_half s hs h.2
  have hxhalf := ((S.idempotent_cases x hx).resolve_left h0).resolve_left h1
  have heq := congrArg (fun y => (S.coordinates y).1) hsum
  simp only [map_add, Prod.fst_add] at heq
  linarith

include S in
/-- The qutrit's one-letter and two-letter yes statistics cannot occur in a spin factor. -/
theorem no_orthogonal_qutrit_statistics [FiniteDimensional ℝ E] (hfr : P.FormallyReal)
    (f : Word (Fin 3) → ℝ) (hyes : ∀ i, f [(i, true)] = 1 / 3)
    (hpair : ∀ i j, i ≠ j → f [(i, true), (j, true)] = 0) :
    f ∉ P.canonicalProjectiveTables hfr 3 := by
  rintro ⟨p, ρ, hp, hρ, hwords⟩
  let τ := P.canonicalTraceOfFormallyReal hfr
  let φ := P.canonicalPairingFunctional hfr ρ
  have hmass (i : Fin 3) : φ (p i) = 1 / 3 := by
    rw [← hyes i, ← hwords [(i, true)], P.sequentialWordEffect_yes p hp i]
  have hnonzero (i : Fin 3) : p i ≠ 0 := by
    intro hzero
    have h := hmass i
    rw [hzero, map_zero] at h
    norm_num at h
  have hnonunit (i : Fin 3) : p i ≠ P.unit := by
    intro hunit
    have h := hmass i
    rw [hunit] at h
    change P.canonicalTraceFormOfFormallyReal hfr ρ P.unit = 1 / 3 at h
    rw [P.canonicalTraceFormOfFormallyReal_unit, hρ.2] at h
    norm_num at h
  have hprimitive (i : Fin 3) : P.IsPrimitive (p i) :=
    S.primitive_of_nontrivial_idempotent (p i) (hp i) (hnonzero i) (hnonunit i)
  have hhalf (i : Fin 3) : (S.coordinates (p i)).1 = 1 / 2 := by
    exact ((S.idempotent_cases (p i) (hp i)).resolve_left (hnonzero i)).resolve_left (hnonunit i)
  have horth (i j : Fin 3) (hij : i ≠ j) : P.product (p i) (p j) = 0 := by
    have h := hwords [(i, true), (j, true)]
    change φ (P.quadraticRepresentation (p i) (P.sequentialWordEffect p [(j, true)])) = _ at h
    rw [P.sequentialWordEffect_yes p hp, hpair i j hij,
      P.canonicalTraceOfFormallyReal_primitive_compression hfr _ _ (hprimitive i),
      map_smul, smul_eq_mul, hmass] at h
    have hzero : τ (P.product (p i) (p j)) = 0 := by linarith
    have hpairswap : P.canonicalTraceFormOfFormallyReal hfr (p j) (p i) = 0 := by
      rw [P.canonicalTraceFormOfFormallyReal_apply, P.commutative]
      exact hzero
    have hfix := (P.quadraticSupport_of_canonicalTrace_pairing_zero hfr (p i) (p j)
      (hp i) ⟨p j, (hp j).symm⟩ hpairswap).2
    have hq : P.product (P.unit - p i) (P.unit - p i) = P.unit - p i := by
      have hunit (a : E) : P.product a P.unit = a := by rw [P.commutative, P.unit_left]
      simp only [map_sub, LinearMap.sub_apply, P.unit_left, hunit, hp i]
      abel
    have hpeirce := (P.mem_peirceOne _ _).mp (P.quadraticRepresentation_mem_peirceOne _ (p j) hq)
    rw [← hfix] at hpeirce
    simp only [map_sub, LinearMap.sub_apply, P.unit_left] at hpeirce
    exact sub_eq_self.mp hpeirce
  let r := p 0 + p 1 + p 2
  have hr : P.product r r = r := by
    simp only [r, map_add, LinearMap.add_apply, hp, horth 0 1 (by decide), horth 0 2 (by decide),
      horth 1 0 (by decide), horth 1 2 (by decide), horth 2 0 (by decide), horth 2 1 (by decide),
      add_zero, zero_add]
  have hrscalar : (S.coordinates r).1 = 3 / 2 := by
    simp only [r, map_add, Prod.fst_add, hhalf]
    norm_num
  rcases S.idempotent_cases r hr with h | h | h
  · rw [h, map_zero] at hrscalar
    norm_num at hrscalar
  · rw [h, S.unit] at hrscalar
    norm_num at hrscalar
  · rw [h] at hrscalar
    norm_num at hrscalar

end SpinFactorCoordinates

section QutritWitness

open AlbertChallenge.Bridge

def qutritCoordinateProjection (i : Fin 3) : ComplexMatrix3 :=
  qutritRankOneProjection (qutritStandardVector i)

theorem qutritCoordinateProjection_hermitian (i : Fin 3) :
    (qutritCoordinateProjection i).IsHermitian :=
  (qutritRankOneProjection_positive _).isHermitian

theorem qutritCoordinateProjection_idempotent (i : Fin 3) :
    qutritCoordinateProjection i * qutritCoordinateProjection i = qutritCoordinateProjection i :=
  qutritRankOneProjection_idempotent _ (by simp [qutritStandardVector_inner])

private theorem qutritCoordinateProjection_mul_zero (i j : Fin 3) (hij : i ≠ j) :
    qutritCoordinateProjection i * qutritCoordinateProjection j = 0 := by
  ext a b
  simp [qutritCoordinateProjection, qutritRankOneProjection_mul_apply, qutritStandardVector_inner, hij]

def qutritCoordinateModel : AlbertChallenge.ProjectiveRepresentation 3 ℂ (EuclideanSpace ℂ (Fin 3)) :=
  matrixRepresentation qutritCoordinateProjection qutritCoordinateProjection_hermitian
    qutritCoordinateProjection_idempotent qutritMixedState qutritMixedState_density.1 qutritMixedState_density.2

private def hilbertDataOfChallenge {n : ℕ} {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : AlbertChallenge.ProjectiveRepresentation n ℂ H) :
    HilbertProjectiveData (Fin n) ℂ H :=
  HilbertProjectiveData.ofBoundedProjections M.projection M.isStarProjection (restrictSelfAdjoint (reState M))
    (by change Complex.re (M.state (operatorValue ℂ H 1)) = 1; rw [map_one, M.state_one, Complex.one_re])
    (fun T hT => by
      obtain ⟨r, hr, he⟩ := M.state_nonneg (operatorValue ℂ H T.val) hT
      change 0 ≤ RCLike.re (M.state (operatorValue ℂ H T.val))
      rwa [he, RCLike.ofReal_re])

private theorem hilbertDataOfChallenge_probability {n : ℕ} {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : AlbertChallenge.ProjectiveRepresentation n ℂ H)
    (w : Word (Fin n)) : (hilbertDataOfChallenge M).toAlgebraic.probability w = M.probability w :=
  ofProjectiveRepresentation_probability M w

/-- The complete table from three coordinate projections on `ℂ³` and the state `I/3`. -/
def spinSeparationQutritTable : Word (Fin 3) → ℝ := qutritCoordinateModel.probability

theorem spinSeparationQutritTable_mem_finiteComplex :
    spinSeparationQutritTable ∈ finiteHilbertProjectiveTables.{0} ℂ 3 :=
  mem_finiteHilbertProjectiveTables_of_model (hilbertDataOfChallenge qutritCoordinateModel)
    (hilbertDataOfChallenge_probability qutritCoordinateModel)

private theorem coordinateWordOperator_yes (i : Fin 3) :
    wordOperator qutritCoordinateProjection [(i, true)] = qutritCoordinateProjection i := by
  rw [wordOperator_cons _ (fun j => (qutritCoordinateProjection_hermitian j).eq), wordOperator_nil]
  change qutritCoordinateProjection i * 1 * qutritCoordinateProjection i = _
  rw [mul_one, qutritCoordinateProjection_idempotent]

theorem spinSeparationQutritTable_yes (i : Fin 3) : spinSeparationQutritTable [(i, true)] = 1 / 3 := by
  rw [spinSeparationQutritTable, qutritCoordinateModel, matrixRepresentation_probability,
    coordinateWordOperator_yes, qutritMixedState, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul,
    qutritCoordinateProjection, qutritRankOneProjection_trace]
  norm_num [qutritStandardVector_inner, Complex.div_re]

theorem spinSeparationQutritTable_yes_yes (i j : Fin 3) (hij : i ≠ j) :
    spinSeparationQutritTable [(i, true), (j, true)] = 0 := by
  rw [spinSeparationQutritTable, qutritCoordinateModel, matrixRepresentation_probability,
    wordOperator_cons _ (fun k => (qutritCoordinateProjection_hermitian k).eq), coordinateWordOperator_yes]
  change (Matrix.trace (qutritMixedState *
    (qutritCoordinateProjection i * qutritCoordinateProjection j * qutritCoordinateProjection i))).re = 0
  simp [qutritCoordinateProjection_mul_zero i j hij]

theorem spinSeparationQutritTable_not_mem_spinFactor {E W : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup W] [InnerProductSpace ℝ W] {P : UnitalJordanProduct E}
    (S : SpinFactorCoordinates P W) (hfr : P.FormallyReal) :
    spinSeparationQutritTable ∉ P.canonicalProjectiveTables hfr 3 :=
  S.no_orthogonal_qutrit_statistics hfr spinSeparationQutritTable
    spinSeparationQutritTable_yes spinSeparationQutritTable_yes_yes

end QutritWitness

end AlbertSequential
