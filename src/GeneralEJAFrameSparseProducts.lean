/- SPDX-License-Identifier: Apache-2.0 -/
module
public import GeneralEJACoefficientMatrixProduct

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : UnitalJordanProduct E) (hfr : P.FormallyReal) {n : ℕ} (c : Fin n → E)
    {r s t : Fin n} (C : P.PeirceTriangleCoordinates hfr c r s t)

local notation "A" => P.frameOffDiagonalSpace c r t
local notation "bar" => P.peirceCoefficientConjugate hfr c C
local notation "MJ" => P.peirceCoefficientMatrixJordan hfr c C
local notation "edge" => P.peirceCoefficientMatrixEdge hfr c C

theorem peirceCoefficientMatrixJordan_diagonal_pair (i j : Fin n) :
    MJ (Matrix.single i i C.unit) (Matrix.single j j C.unit) =
      if i = j then Matrix.single i i C.unit else 0 := by
  by_cases h : i = j
  · subst j
    simp only [P.peirceCoefficientMatrixJordan_apply, P.peirceCoefficientMatrixMul_single, C.unit_left]
    module
  · simp [P.peirceCoefficientMatrixJordan_apply, P.peirceCoefficientMatrixMul_single, h, Ne.symm h]

theorem peirceCoefficientMatrixJordan_diagonal_edge {i j : Fin n} (hij : i < j) (k : Fin n) (a : A) :
    MJ (Matrix.single k k C.unit) (edge i j a) =
      if k = i ∨ k = j then (1 / 2 : ℝ) • edge i j a else 0 := by
  by_cases hi : k = i
  · subst k
    simp [P.peirceCoefficientMatrixJordan_apply, peirceCoefficientMatrixEdge,
      map_add, LinearMap.add_apply, P.peirceCoefficientMatrixMul_single, ne_of_lt hij, ne_of_gt hij, C.unit_left,
      C.unit_right]
  by_cases hj : k = j
  · subst k
    simp [P.peirceCoefficientMatrixJordan_apply, peirceCoefficientMatrixEdge,
      map_add, LinearMap.add_apply, P.peirceCoefficientMatrixMul_single, ne_of_lt hij, ne_of_gt hij, C.unit_left,
      C.unit_right, add_comm]
  simp [P.peirceCoefficientMatrixJordan_apply, peirceCoefficientMatrixEdge,
    map_add, LinearMap.add_apply, P.peirceCoefficientMatrixMul_single, hi, hj, Ne.symm hi, Ne.symm hj]

theorem peirceCoefficientMatrixJordan_same_edge {i j : Fin n} (hij : i < j) (a b : A) :
    MJ (edge i j a) (edge i j b) =
      P.frameOffDiagonalTraceForm hfr c r t a b • (Matrix.single i i C.unit + Matrix.single j j C.unit) := by
  have heq :
      MJ (edge i j a) (edge i j b) =
        (1 / 2 : ℝ) • ((Matrix.single i i (C.product a (bar b)) + Matrix.single j j (C.product (bar a) b)) +
          (Matrix.single i i (C.product b (bar a)) + Matrix.single j j (C.product (bar b) a))) := by
    simp [P.peirceCoefficientMatrixJordan_apply, peirceCoefficientMatrixEdge,
      map_add, LinearMap.add_apply, P.peirceCoefficientMatrixMul_single, ne_of_lt hij, ne_of_gt hij]
    abel
  rw [heq]
  calc
    _ = (1 / 2 : ℝ) • (Matrix.single i i (C.product a (bar b) + C.product b (bar a)) +
        Matrix.single j j (C.product (bar a) b + C.product (bar b) a)) := by
      rw [Matrix.single_add, Matrix.single_add]
      congr 1
      abel
    _ = _ := by
      rw [P.peirceCoefficient_product_conjugate_polarized hfr c C,
        P.peirceCoefficient_conjugate_product_polarized hfr c C,
        ← Matrix.smul_single, ← Matrix.smul_single, ← smul_add, smul_smul]
      congr 1
      ring

theorem peirceCoefficientMatrixJordan_edge_chain {i j k : Fin n} (hij : i < j) (hjk : j < k) (a b : A) :
    MJ (edge i j a) (edge j k b) = (1 / 2 : ℝ) • edge i k (C.product a b) := by
  have hik := lt_trans hij hjk
  simp [P.peirceCoefficientMatrixJordan_apply, peirceCoefficientMatrixEdge,
    map_add, LinearMap.add_apply, P.peirceCoefficientMatrixMul_single,
    ne_of_lt hij, ne_of_gt hij, ne_of_lt hik, ne_of_gt hik, ne_of_lt hjk, ne_of_gt hjk,
    P.peirceCoefficientConjugate_product hfr c C]

theorem peirceCoefficientMatrixJordan_edges_same_first {i j k : Fin n}
    (hij : i < j) (hjk : j < k) (a b : A) :
    MJ (edge i j a) (edge i k b) = (1 / 2 : ℝ) • edge j k (C.product (bar a) b) := by
  have hik := lt_trans hij hjk
  have hbar (x : A) : bar (bar x) = x := P.peirceCoefficientConjugate_involutive hfr c C x
  simp [P.peirceCoefficientMatrixJordan_apply, peirceCoefficientMatrixEdge,
    map_add, LinearMap.add_apply, P.peirceCoefficientMatrixMul_single,
    ne_of_lt hij, ne_of_gt hij, ne_of_lt hik, ne_of_gt hik, ne_of_lt hjk, ne_of_gt hjk,
    P.peirceCoefficientConjugate_product hfr c C, hbar]

theorem peirceCoefficientMatrixJordan_edges_same_last {i j k : Fin n}
    (hij : i < j) (hjk : j < k) (a b : A) :
    MJ (edge i k a) (edge j k b) = (1 / 2 : ℝ) • edge i j (C.product a (bar b)) := by
  have hik := lt_trans hij hjk
  have hbar (x : A) : bar (bar x) = x := P.peirceCoefficientConjugate_involutive hfr c C x
  simp [P.peirceCoefficientMatrixJordan_apply, peirceCoefficientMatrixEdge,
    map_add, LinearMap.add_apply, P.peirceCoefficientMatrixMul_single,
    ne_of_lt hij, ne_of_gt hij, ne_of_lt hik, ne_of_gt hik, ne_of_lt hjk, ne_of_gt hjk,
    P.peirceCoefficientConjugate_product hfr c C, hbar, add_comm]

theorem peirceCoefficientMatrixJordan_edges_disjoint {i j k l : Fin n}
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (a b : A) :
    MJ (edge i j a) (edge k l b) = 0 := by
  simp [P.peirceCoefficientMatrixJordan_apply, peirceCoefficientMatrixEdge,
    map_add, LinearMap.add_apply, P.peirceCoefficientMatrixMul_single,
    hik, hil, hjk, hjl, hik.symm, hil.symm, hjk.symm, hjl.symm]

end AlbertSequential.UnitalJordanProduct
