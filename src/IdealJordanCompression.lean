/- SPDX-License-Identifier: Apache-2.0 -/
module
public import IdealTestFoundations

/-! Exact compression from positivity, measured projection and ideality.
The cone-line argument retains all positive inputs, zero branches and every
idempotent rank; no complete positivity or continuity premise is used. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace AlbertSequential.PositiveInstruments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (P : UnitalJordanProduct E)
  (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
include hinner

omit [FiniteDimensional ℝ E] in
theorem trace_pos_of_nonzero (x : E) (hx : x∈P.squareCone) (hne : x≠0) :
    0<trace P x := by
  have hn : 0≤trace P x := P.squareCone_unitPairing_nonnegative hinner x hx
  have hz : trace P x≠0 := fun h => hne ((P.squareCone_unitPairing_zero_iff hinner x hx).mp h)
  exact lt_of_le_of_ne hn hz.symm

omit [FiniteDimensional ℝ E] in
theorem normalized_positive_isDensity (x : E) (hx : x∈P.squareCone) (hne : x≠0) :
    IsDensity P ((1/trace P x : ℝ) • x) := by
  have ht := trace_pos_of_nonzero P hinner x hx hne
  refine ⟨P.nonnegative_smul_mem_squareCone x hx _ (one_div_nonneg.mpr ht.le),?_⟩
  rw [trace_smul]
  exact one_div_mul_cancel (ne_of_gt ht)

omit [FiniteDimensional ℝ E] in
theorem fixes_positive_of_fixes_density (T : E→ₗ[ℝ]E) (p : E)
    (hfix : ∀ ρ, IsDensity P ρ → inner ℝ ρ p=1 → T ρ=ρ)
    (x : E) (hx : x∈P.squareCone) (hxp : inner ℝ x p=trace P x) : T x=x := by
  by_cases hzero : x=0
  · simp [hzero]
  have ht := trace_pos_of_nonzero P hinner x hx hzero
  have hn : inner ℝ ((1/trace P x : ℝ) • x) p=1 := by
    rw [real_inner_smul_left,hxp]
    exact one_div_mul_cancel (ne_of_gt ht)
  have hf := hfix _ (normalized_positive_isDensity P hinner x hx hzero) hn
  rw [map_smul] at hf
  have hs := congrArg (fun y : E => trace P x • y) hf
  have hc : trace P x * (1/trace P x)=1 := by field_simp [ne_of_gt ht]
  simpa only [smul_smul,hc,one_smul] using hs

omit [FiniteDimensional ℝ E] hinner in
theorem quadratic_opposite_idempotent_zero (p : E) (hp : P.product p p=p) :
    P.quadraticRepresentation (P.unit-p) p=0 := by
  have hqp : P.product (P.unit-p) p=0 := by
    rw [map_sub,LinearMap.sub_apply,P.unit_left,hp,sub_self]
  rw [P.quadraticRepresentation_apply,complementary_idempotent P p hp,hqp,map_zero,
    smul_zero,sub_zero]

theorem positiveMap_eq_quadraticRepresentation (T : E→ₗ[ℝ]E) (p : E)
    (hp : P.product p p=p)
    (hpos : ∀ x∈P.squareCone,T x∈P.squareCone)
    (htrace : ∀ x,trace P (T x)=inner ℝ x p)
    (hfix : ∀ ρ,IsDensity P ρ → inner ℝ ρ p=1 → T ρ=ρ) :
    T=P.quadraticRepresentation p := by
  have hon (x : E) (hx : x∈P.squareCone) : T x=P.quadraticRepresentation p x := by
    let b := P.quadraticRepresentation p x
    let d := P.quadraticRepresentation (P.unit-p) x
    let z := x-b-d
    have hb : b∈P.squareCone := P.quadraticRepresentation_preserves_squareCone hinner p x hx
    have hd : d∈P.squareCone := P.quadraticRepresentation_preserves_squareCone hinner _ x hx
    have hbp : inner ℝ b p=trace P b := by
      change inner ℝ (P.quadraticRepresentation p x) p=trace P (P.quadraticRepresentation p x)
      rw [P.quadraticRepresentation_inner hinner,P.quadraticRepresentation_idempotent_self p hp,
        trace_quadratic_idempotent P hinner p x hp]
    have hTb : T b=b := fixes_positive_of_fixes_density P hinner T p hfix b hb hbp
    have hTd : T d=0 := by
      apply (P.squareCone_unitPairing_zero_iff hinner (T d) (hpos d hd)).mp
      change trace P (T d)=0
      rw [htrace]
      change inner ℝ (P.quadraticRepresentation (P.unit-p) x) p=0
      rw [P.quadraticRepresentation_inner hinner,quadratic_opposite_idempotent_zero P p hp,
        inner_zero_right]
    have hline (t : ℝ) : b+t • T z∈P.squareCone := by
      have hu := P.quadraticRepresentation_preserves_squareCone hinner (p+t • (P.unit-p)) x hx
      rw [quadratic_filter_interpolation P p x hp t] at hu
      change b+t • z+(t*t) • d∈P.squareCone at hu
      have hi := hpos _ hu
      simpa only [map_add,map_smul,hTb,hTd,smul_zero,add_zero] using hi
    have hz : T z=0 := affine_line_in_squareCone_slope_zero P hinner b (T z) hline
    have heq : x=b+d+z := by dsimp only [z]; abel
    calc
      T x = T (b+d+z) := congrArg T heq
      _ = b := by rw [map_add,map_add,hTb,hTd,hz,add_zero,add_zero]
      _ = P.quadraticRepresentation p x := rfl
  have hs : Submodule.span ℝ P.squareCone≤(T-P.quadraticRepresentation p).ker := by
    apply Submodule.span_le.mpr
    intro x hx
    change T x-P.quadraticRepresentation p x=0
    exact sub_eq_zero.mpr (hon x hx)
  rw [P.span_squareCone] at hs
  ext x
  have hz := hs (Submodule.mem_top : x∈(⊤ : Submodule ℝ E))
  change T x-P.quadraticRepresentation p x=0 at hz
  exact sub_eq_zero.mp hz

theorem quadraticRepresentation_fixes_density (p : E) (hp : P.product p p=p)
    (ρ : E) (hρ : IsDensity P ρ) (hpair : inner ℝ ρ p=1) :
    P.quadraticRepresentation p ρ=ρ := by
  have hq := complementary_idempotent P p hp
  have hd : P.quadraticRepresentation (P.unit-p) ρ=0 := by
    apply (P.squareCone_unitPairing_zero_iff hinner _
      (P.quadraticRepresentation_preserves_squareCone hinner _ ρ hρ.1)).mp
    change trace P (P.quadraticRepresentation (P.unit-p) ρ)=0
    rw [trace_quadratic_idempotent P hinner _ ρ hq,inner_sub_right]
    change trace P ρ-inner ℝ ρ p=0
    rw [hρ.2,hpair,sub_self]
  have hline (t : ℝ) : P.quadraticRepresentation p ρ+
      t • (ρ-P.quadraticRepresentation p ρ)∈P.squareCone := by
    have hu := P.quadraticRepresentation_preserves_squareCone hinner (p+t • (P.unit-p)) ρ hρ.1
    rw [quadratic_filter_interpolation P p ρ hp t,hd,sub_zero,smul_zero,add_zero] at hu
    exact hu
  have hz := affine_line_in_squareCone_slope_zero P hinner _ _ hline
  exact (sub_eq_zero.mp hz).symm

theorem measuredEffect_eq_of_quadraticRepresentation (T : PositiveBinaryInstrument P)
    (p : E) (hp : P.product p p=p) (hyes : T.yes=P.quadraticRepresentation p) :
    measuredEffect P T=p := by
  have hall (x : E) : inner ℝ x (measuredEffect P T)=inner ℝ x p := by
    rw [measuredEffect_pairing,hyes,trace_quadratic_idempotent P hinner p x hp]
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  rw [inner_sub_right,hall,sub_self]

/-- The actual positive normalized instrument exists for EVERY idempotent,
including the zero and unit effects, without assuming an instrument contract. -/
def quadraticInstrument (p : E) (hp : P.product p p=p) : PositiveBinaryInstrument P where
  yes := P.quadraticRepresentation p
  no := P.quadraticRepresentation (P.unit-p)
  yes_positive := P.quadraticRepresentation_preserves_squareCone hinner p
  no_positive := P.quadraticRepresentation_preserves_squareCone hinner (P.unit-p)
  normalized := by
    intro x
    rw [trace_add,trace_quadratic_idempotent P hinner p x hp,
      trace_quadratic_idempotent P hinner _ x (complementary_idempotent P p hp),inner_sub_right]
    change inner ℝ x p+(trace P x-inner ℝ x p)=trace P x
    ring

theorem quadraticInstrument_isIdeal (p : E) (hp : P.product p p=p) :
    IsIdeal P (quadraticInstrument P hinner p hp) := by
  have hm : measuredEffect P (quadraticInstrument P hinner p hp)=p :=
    measuredEffect_eq_of_quadraticRepresentation P hinner _ p hp rfl
  constructor
  · intro ρ hρ hpair
    rw [hm] at hpair
    exact quadraticRepresentation_fixes_density P hinner p hp ρ hρ hpair
  · intro ρ hρ hpair
    rw [hm] at hpair
    apply quadraticRepresentation_fixes_density P hinner _ (complementary_idempotent P p hp) ρ hρ
    rw [inner_sub_right]
    change trace P ρ-inner ℝ ρ p=1
    rw [hρ.2,hpair,sub_zero]

end AlbertSequential.PositiveInstruments
