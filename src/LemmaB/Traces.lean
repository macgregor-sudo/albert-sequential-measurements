module

public import LemmaB.Gram
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Lemma B, part 7: the dictionary from the thirteen traces

Paper: core `sec:cer`, "The comparison form" (definitions of `m_x`, `ĉ_a`, `M̂_ab`,
`Ŝ`, `b̂`, `D̂`, eq:cer:Dhat), and core `sec:four` (def:traces, eq:fp:tracerel,
eq:A:Acal52). Proved here, with no trace relation:

* `D̂ = m³ 𝒜` (eq:cer:Dhat, first equality chain), as an identity of rational functions of the
  thirteen traces with `o_AB o_AC o_AD ≠ 0`;
* `τ = 2 m (RHS - LHS)` of eq:fp:tracerel, so the trace relation gives `τ = 0` (the one place it
  enters lem:cer:negative);
* the normalised determinant in the paper's form `-4 D̂³ / ∏_x (1 - o_Ax)`.

Conventions: `ω_r = t_1 + t_2 + t_3 - 2 t_r`; `ω_B = ω_1, ω_C = ω_2, ω_D = ω_3` (middle-letter
convention of lem:cer:short); `R_ADB` is stored as `RABD` (the shape invariants are symmetric).
-/

@[expose] public section

namespace LemmaB

noncomputable section

/-- The thirteen traces of def:traces. -/
structure Traces where
  oAB : ℝ
  oAC : ℝ
  oAD : ℝ
  oBC : ℝ
  oCD : ℝ
  oBD : ℝ
  RABC : ℝ
  RABD : ℝ
  RACD : ℝ
  RBCD : ℝ
  t1 : ℝ
  t2 : ℝ
  t3 : ℝ

namespace Traces

variable (τd : Traces)

/-- `ω_r = t_1 + t_2 + t_3 - 2 t_r`. -/
def ω1 : ℝ := τd.t1 + τd.t2 + τd.t3 - 2 * τd.t1
def ω2 : ℝ := τd.t1 + τd.t2 + τd.t3 - 2 * τd.t2
def ω3 : ℝ := τd.t1 + τd.t2 + τd.t3 - 2 * τd.t3

/-- The trace relation eq:fp:tracerel (it holds for any four atoms of `𝕁`,
prop:fp:tracerel; here it is a hypothesis). -/
def TraceRelation : Prop :=
  τd.t1 + τd.t2 + τd.t3 =
    1 / 2 - 1 / 2 * (τd.oAB + τd.oAC + τd.oAD + τd.oBC + τd.oCD + τd.oBD)
    + 1 / 2 * (τd.oAB * τd.oCD + τd.oAC * τd.oBD + τd.oAD * τd.oBC)
    + τd.RABC + τd.RABD + τd.RACD + τd.RBCD

/-- The four-point invariant `𝒜` (eq:A:Acal52, the sixteen-term form in `(o, R, ω)`). -/
def Acal : ℝ :=
  τd.oAB * τd.oAC * τd.oAD * τd.oBC * τd.oBD * τd.oCD
  - (τd.RABC ^ 2 * τd.oAD * τd.oBD * τd.oCD + τd.RABD ^ 2 * τd.oAC * τd.oBC * τd.oCD
    + τd.RACD ^ 2 * τd.oAB * τd.oBC * τd.oBD + τd.RBCD ^ 2 * τd.oAB * τd.oAC * τd.oAD)
  - 4 * τd.RABC * τd.RABD * τd.RACD * τd.RBCD
  - (τd.oAB * τd.oCD * τd.ω1 ^ 2 + τd.oAC * τd.oBD * τd.ω2 ^ 2 + τd.oAD * τd.oBC * τd.ω3 ^ 2)
  + 2 * τd.ω1 * (τd.RABC * τd.RABD * τd.oCD + τd.RACD * τd.RBCD * τd.oAB)
  + 2 * τd.ω2 * (τd.RABC * τd.RACD * τd.oBD + τd.RABD * τd.RBCD * τd.oAC)
  + 2 * τd.ω3 * (τd.RABC * τd.RBCD * τd.oAD + τd.RABD * τd.RACD * τd.oBC)
  - 2 * τd.ω1 * τd.ω2 * τd.ω3

/-- The parameters of the comparison form (paper, "The comparison form"):
`m_x = 1/o_Ax`, `ĉ_1 = R_ABC m_B m_C`, `ĉ_2 = R_ACD m_C m_D`, `ĉ_3 = R_ADB m_D m_B`,
`M̂_11 = o_BC m_B m_C - ĉ_1²` (cyclically), `M̂_12 = ĉ_1ĉ_2 - ω_C m`, `M̂_23 = ĉ_2ĉ_3 - ω_D m`,
`M̂_13 = ĉ_1ĉ_3 - ω_B m`, `Ŝ = ĉ_1ĉ_2ĉ_3 - ĉ_1M̂_23 - ĉ_2M̂_13 - ĉ_3M̂_12`, `b̂ = ĉ_4 - Ŝ` with
`ĉ_4 = R_BCD m`. -/
def toParams : Params ℝ :=
  let mB := τd.oAB⁻¹
  let mC := τd.oAC⁻¹
  let mD := τd.oAD⁻¹
  let m := mB * mC * mD
  let c1 := τd.RABC * mB * mC
  let c2 := τd.RACD * mC * mD
  let c3 := τd.RABD * mD * mB
  let M12 := c1 * c2 - τd.ω2 * m
  let M23 := c2 * c3 - τd.ω3 * m
  let M13 := c1 * c3 - τd.ω1 * m
  { mB := mB, mC := mC, mD := mD, c1 := c1, c2 := c2, c3 := c3,
    M11 := τd.oBC * mB * mC - c1 ^ 2, M22 := τd.oCD * mC * mD - c2 ^ 2,
    M33 := τd.oBD * mD * mB - c3 ^ 2, M12 := M12, M13 := M13, M23 := M23,
    b := τd.RBCD * m - (c1 * c2 * c3 - c1 * M23 - c2 * M13 - c3 * M12) }

/-- Where the trace relation enters: `τ = 2 m (RHS - LHS)` of eq:fp:tracerel. -/
theorem tau_toParams (hB : τd.oAB ≠ 0) (hC : τd.oAC ≠ 0) (hD : τd.oAD ≠ 0) :
    τd.toParams.tau = 2 * τd.toParams.m *
      ((1 / 2 - 1 / 2 * (τd.oAB + τd.oAC + τd.oAD + τd.oBC + τd.oCD + τd.oBD)
        + 1 / 2 * (τd.oAB * τd.oCD + τd.oAC * τd.oBD + τd.oAD * τd.oBC)
        + τd.RABC + τd.RABD + τd.RACD + τd.RBCD) - (τd.t1 + τd.t2 + τd.t3)) := by
  simp only [toParams, Params.tau, Params.μ, Params.μB, Params.μC, Params.μD, Params.d1,
    Params.d2, Params.d3, Params.Sprime, Params.m, ω1, ω2, ω3]
  field_simp
  ring

theorem tau_eq_zero (hB : τd.oAB ≠ 0) (hC : τd.oAC ≠ 0) (hD : τd.oAD ≠ 0)
    (hTR : τd.TraceRelation) : τd.toParams.tau = 0 := by
  rw [tau_toParams τd hB hC hD, TraceRelation] at *
  rw [hTR]; ring

/-- eq:cer:Dhat: `D̂ = m³ 𝒜` (no trace relation). -/
theorem Dhat_toParams (hB : τd.oAB ≠ 0) (hC : τd.oAC ≠ 0) (hD : τd.oAD ≠ 0) :
    τd.toParams.Dhat = τd.toParams.m ^ 3 * τd.Acal := by
  simp only [toParams, Params.Dhat, Params.detM, Params.m, Acal, ω1, ω2, ω3]
  field_simp
  ring

/-- The normalised determinant of lem:cer:negative in the paper's form:
for `E_x = Ξ_x / (2 α_x)`, `det Gram(E) = -4 D̂³ / ∏_x (1 - o_Ax)`. -/
theorem det_gram_normalised_traces (hTR : τd.TraceRelation)
    (hB : τd.oAB ≠ 0) (hC : τd.oAC ≠ 0) (hD : τd.oAD ≠ 0)
    (hB1 : τd.oAB ≠ 1) (hC1 : τd.oAC ≠ 1) (hD1 : τd.oAD ≠ 1) :
    (Matrix.of fun x y => Q τd.toParams ((2 * αv τd.toParams x)⁻¹ • Xi τd.toParams x)
        ((2 * αv τd.toParams y)⁻¹ • Xi τd.toParams y)).det =
      -4 * τd.toParams.Dhat ^ 3 / ((1 - τd.oAB) * (1 - τd.oAC) * (1 - τd.oAD)) := by
  have hμ : ∀ o : ℝ, o ≠ 0 → o ≠ 1 → o⁻¹ - 1 ≠ 0 := by
    intro o h0 h1 h
    apply h1
    have : o⁻¹ = 1 := by linarith
    simpa using congrArg (·⁻¹) this
  rw [det_gram_normalised τd.toParams (tau_eq_zero τd hB hC hD hTR) two_ne_zero
    (hμ _ hB hB1) (hμ _ hC hC1) (hμ _ hD hD1)]
  have e1 : (1 - τd.oAB) ≠ 0 := sub_ne_zero.mpr (Ne.symm hB1)
  have e2 : (1 - τd.oAC) ≠ 0 := sub_ne_zero.mpr (Ne.symm hC1)
  have e3 : (1 - τd.oAD) ≠ 0 := sub_ne_zero.mpr (Ne.symm hD1)
  simp only [toParams, Params.μB, Params.μC, Params.μD]
  have f1 : τd.oAB⁻¹ - 1 = (1 - τd.oAB) / τd.oAB := by field_simp
  have f2 : τd.oAC⁻¹ - 1 = (1 - τd.oAC) / τd.oAC := by field_simp
  have f3 : τd.oAD⁻¹ - 1 = (1 - τd.oAD) / τd.oAD := by field_simp
  rw [f1, f2, f3]
  field_simp

end Traces

end

end LemmaB
