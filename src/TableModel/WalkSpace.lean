/- SPDX-License-Identifier: Apache-2.0 -/
module

public import TableModel.Defs
public import LengthSeven.AlgebraicWalkSpace

@[expose] public section
noncomputable section

namespace AlbertSequential.LengthSeven.TableModel

open LemmaB

variable (τ : TraceData)

abbrev comparisonParams : Params ℝ := (toTraces τ).toParams

local notation "p" => comparisonParams τ

/-- The paper's projection onto a single comparison frame, as a linear map. -/
def comparisonProjection (x : Letter) : V ℝ →ₗ[ℝ] V ℝ where
  toFun := P p x
  map_add' F G := by simp [P, src_add, smul_add, Pi.single_add]
  map_smul' r F := by simp [P, src_smul, smul_smul, mul_comm, Pi.single_smul]

theorem comparisonProjection_apply (x : Letter) (F : V ℝ) : comparisonProjection τ x F = P p x F := rfl

theorem comparisonProjection_single (x y : Letter) (a : C8 ℝ) :
    comparisonProjection τ x (Pi.single y a) =
      Pi.single x ((mOf p x)⁻¹ • T p x y a) := by
  rw [comparisonProjection_apply, P, src_single]

theorem comparison_m_ne_zero (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)
    (x : Letter) : mOf p x ≠ 0 := by
  fin_cases x <;> simp [mOf, Traces.toParams, toTraces, hB, hC, hD]

theorem comparison_form_single (x y : Letter) (a b : C8 ℝ) :
    Q p (Pi.single x a) (Pi.single y b) = W p a (T p x y b) := by
  rw [Q_eq_src, Finset.sum_eq_single x]
  · rw [Pi.single_eq_same, src_single]
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi, W_symm]
    exact (Wl p _).map_zero
  · simp

/-- The literal comparison form and projections on four eight-coordinate frames. -/
def comparisonWalkSpace (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0) :
    AlgebraicWalkSpace (V ℝ) where
  form := Ql p
  symm := Q_symm p
  P := comparisonProjection τ
  idem x F := P_idem p x (comparison_m_ne_zero τ hB hC hD x) F
  selfAdj := P_selfadj p
  ξ := xi
  fixA := P_A_xi p
  unit := by
    change Q p (Pi.single 0 one8) (Pi.single 0 one8) = 1
    rw [comparison_form_single, T_diag, show mOf p 0 = 1 from rfl, one_smul, W_one]
    rfl

theorem comparison_pathVec (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)
    (w : List Letter) : (comparisonWalkSpace τ hB hC hD).pathVec w = uhat p w := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w x ih =>
    have hs : (comparisonWalkSpace τ hB hC hD).pathVec (w ++ [x]) =
        comparisonProjection τ x ((comparisonWalkSpace τ hB hC hD).pathVec w) := by
      simp [AlgebraicWalkSpace.pathVec, List.reverse_append, comparisonWalkSpace]
    rw [hs, ih]
    simp only [uhat, List.foldl_append]
    rfl

private theorem sig_invol (a : C8 ℝ) : sig (sig a) = a := by
  funext j
  fin_cases j <;> simp [sig]

private theorem holonomy_norm (e : C8 ℝ →ₗ[ℝ] C8 ℝ) (c s : ℝ)
    (he : ∀ a, e (e a) = (-s) • a) (a : C8 ℝ) :
    c • (c • a - e a) + e (c • a - e a) = (c ^ 2 + s) • a ∧
      c • (c • a + e a) - e (c • a + e a) = (c ^ 2 + s) • a := by
  simp only [map_sub, map_add, map_smul, he, smul_add, smul_sub]
  constructor <;> module

theorem h1_cancel (a : C8 ℝ) : h1 p (h1s p a) = ((comparisonParams τ).c1 ^ 2 + (comparisonParams τ).M11) • a ∧
    h1s p (h1 p a) = ((comparisonParams τ).c1 ^ 2 + (comparisonParams τ).M11) • a :=
  holonomy_norm ⟨⟨eps1 p, eps1_add p⟩, eps1_smul p⟩ _ _ (eps1_sq p) a

theorem h2_cancel (a : C8 ℝ) : h2 p (h2s p a) = ((comparisonParams τ).c2 ^ 2 + (comparisonParams τ).M22) • a ∧
    h2s p (h2 p a) = ((comparisonParams τ).c2 ^ 2 + (comparisonParams τ).M22) • a :=
  holonomy_norm ⟨⟨eps2 p, eps2_add p⟩, eps2_smul p⟩ _ _ (eps2_sq p) a

theorem h3_cancel (a : C8 ℝ) : h3 p (h3s p a) = ((comparisonParams τ).c3 ^ 2 + (comparisonParams τ).M33) • a ∧
    h3s p (h3 p a) = ((comparisonParams τ).c3 ^ 2 + (comparisonParams τ).M33) • a :=
  holonomy_norm ⟨⟨eps3 p, eps3_add p⟩, eps3_smul p⟩ _ _ (eps3_sq p) a

private theorem T_reverse_comp (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)
    (x y : Letter) (hxy : x ≠ y) (a : C8 ℝ) :
    T p x y (T p y x a) = (τ.o x y * mOf p x * mOf p y) • a := by
  have oB := τ.o_symm 1 0
  have oC := τ.o_symm 2 0
  have oD := τ.o_symm 3 0
  have oBC := τ.o_symm 2 1
  have oBD := τ.o_symm 3 1
  have oCD := τ.o_symm 3 2
  fin_cases x <;> fin_cases y <;> try contradiction
  all_goals
    simp [T, mOf, sig_invol, (h1_cancel τ _).1, (h1_cancel τ _).2,
      (h2_cancel τ _).1, (h2_cancel τ _).2, (h3_cancel τ _).1, (h3_cancel τ _).2,
      sig_smul]
  all_goals
    simp [Traces.toParams, toTraces, oB, oC, oD, oBC, oBD, oCD,
      mul_inv_cancel₀ hB, mul_inv_cancel₀ hC, mul_inv_cancel₀ hD]
  all_goals module

/-- The first short relation is an operator identity on the whole comparison space. -/
theorem comparison_R1 (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)
    (x y : Letter) (hxy : x ≠ y) (F : V ℝ) :
    P p x (P p y (P p x F)) = τ.o x y • P p x F := by
  let a := (mOf p x)⁻¹ • src p F x
  change comparisonProjection τ x (comparisonProjection τ y (Pi.single x a)) = τ.o x y • Pi.single x a
  simp only [comparisonProjection_single, T_smul, T_reverse_comp τ hB hC hD x y hxy, smul_smul]
  have hx := comparison_m_ne_zero τ hB hC hD x
  have hy := comparison_m_ne_zero τ hB hC hD y
  have he : (mOf p x)⁻¹ * ((mOf p y)⁻¹ * (τ.o x y * mOf p x * mOf p y)) = τ.o x y := by
    field_simp
  rw [he, Pi.single_smul]

end AlbertSequential.LengthSeven.TableModel
