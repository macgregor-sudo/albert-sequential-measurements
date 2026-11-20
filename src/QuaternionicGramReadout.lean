/- SPDX-License-Identifier: Apache-2.0 -/
module

public import QuaternionicSchurTrace

public section
noncomputable section

namespace AlbertSequential.MatchingModels

open scoped Matrix BigOperators

variable {m : Type*} [Fintype m]

def quatColumnInner (x y : m → Q) : Q := ∑ i, star (x i) * y i

private def quatWeightedDyad (x : m → Q) (q : Q) (y : m → Q) : Matrix m m Q :=
  Matrix.of fun i j => x i * q * star (y j)

def quatColumnDyad (x : m → Q) : Matrix m m Q := quatWeightedDyad x 1 x

def quatColumnGram (x : Fin 4 → m → Q) : Matrix (Fin 4) (Fin 4) Q :=
  Matrix.of fun i j => quatColumnInner (x i) (x j)

private theorem quatWeightedDyad_mul (x y z w : m → Q) (p q : Q) :
    quatWeightedDyad x p y * quatWeightedDyad z q w =
      quatWeightedDyad x (p * quatColumnInner y z * q) w := by
  apply Matrix.ext
  intro i j
  simp only [quatWeightedDyad, quatColumnInner, Matrix.mul_apply, Matrix.of_apply,
    Finset.mul_sum, Finset.sum_mul, mul_assoc]

private theorem quat_real_mul_comm (x y : Q) : (x * y).re = (y * x).re := by
  simp only [Quaternion.re_mul]
  ring

private theorem quatWeightedDyad_trace (x y : m → Q) (q : Q) :
    (quatWeightedDyad x q y).trace.re = (q * quatColumnInner y x).re := by
  have hre (f : m → Q) : (∑ i, f i).re = ∑ i, (f i).re := by
    exact map_sum (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)) _ _
  simp only [Matrix.trace, Matrix.diag_apply, quatWeightedDyad, Matrix.of_apply, quatColumnInner,
    Finset.mul_sum, hre]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc, quat_real_mul_comm (x i), mul_assoc]

private theorem quatColumnInner_star (u v : m → Q) :
    star (quatColumnInner u v) = quatColumnInner v u := by
  simp [quatColumnInner, star_mul]

theorem quatGramOverlap_eq_dyad_trace (x : Fin 4 → m → Q) (i j : Fin 4) :
    quatGramOverlap (quatColumnGram x) i j =
      (quatColumnDyad (x i) * quatColumnDyad (x j)).trace.re := by
  unfold quatGramOverlap quatColumnGram quatColumnDyad
  rw [Matrix.of_apply, quatWeightedDyad_mul, quatWeightedDyad_trace, one_mul, mul_one,
    ← quatColumnInner_star (x i) (x j), Quaternion.normSq_def]

theorem quatGramTriangle_eq_dyad_trace (x : Fin 4 → m → Q) (i j k : Fin 4) :
    quatGramTriangle (quatColumnGram x) i j k =
      (quatColumnDyad (x i) * quatColumnDyad (x j) * quatColumnDyad (x k)).trace.re := by
  unfold quatGramTriangle quatColumnGram quatColumnDyad
  rw [quatWeightedDyad_mul, quatWeightedDyad_mul, quatWeightedDyad_trace, one_mul, mul_one, mul_one]
  simp only [Matrix.of_apply]

theorem quatGramCycle_eq_dyad_trace (x : Fin 4 → m → Q) (i j k l : Fin 4) :
    quatGramCycle (quatColumnGram x) i j k l =
      (quatColumnDyad (x i) * quatColumnDyad (x j) * quatColumnDyad (x k) * quatColumnDyad (x l)).trace.re := by
  unfold quatGramCycle quatColumnGram quatColumnDyad
  rw [quatWeightedDyad_mul, quatWeightedDyad_mul, quatWeightedDyad_mul, quatWeightedDyad_trace,
    one_mul, mul_one, mul_one, mul_one]
  simp only [Matrix.of_apply]

private def quatMatrixRealTrace : Matrix m m Q →ₗ[ℝ] ℝ where
  toFun A := A.trace.re
  map_add' A B := by rw [Matrix.trace_add, Quaternion.re_add]
  map_smul' r A := by rw [Matrix.trace_smul, Quaternion.re_smul]; rfl

private theorem quatMatrixRealTrace_rotate (A B : Matrix m m Q) :
    quatMatrixRealTrace (A * B) = quatMatrixRealTrace (B * A) := by
  have hre (f : m → Q) : (∑ i, f i).re = ∑ i, (f i).re :=
    map_sum (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)) _ _
  simp only [quatMatrixRealTrace, LinearMap.coe_mk, AddHom.coe_mk, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, hre]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => quat_real_mul_comm _ _))

private theorem quatMatrixRealTrace_star (A : Matrix m m Q) :
    quatMatrixRealTrace (star A) = quatMatrixRealTrace A := by
  change (star A).trace.re = A.trace.re
  rw [Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose, Quaternion.re_star]

omit [Fintype m] in
private theorem quatColumnDyad_star (x : m → Q) : star (quatColumnDyad x) = quatColumnDyad x := by
  apply Matrix.ext
  intro i j
  simp [quatColumnDyad, quatWeightedDyad, Matrix.star_apply, star_mul]

private theorem quatTrace_four_reverse_first (A B C D : Matrix m m Q)
    (hA : star A = A) (hB : star B = B) (hC : star C = C) (hD : star D = D) :
    quatMatrixRealTrace (B * A * C * D) = quatMatrixRealTrace (A * B * D * C) := by
  calc
    _ = quatMatrixRealTrace (star (B * A * C * D)) := (quatMatrixRealTrace_star _).symm
    _ = quatMatrixRealTrace ((D * C) * (A * B)) := by
      rw [star_mul, star_mul, star_mul, hA, hB, hC, hD]
      simp only [Matrix.mul_assoc]
    _ = quatMatrixRealTrace ((A * B) * (D * C)) := quatMatrixRealTrace_rotate _ _
    _ = _ := by rw [← Matrix.mul_assoc]

theorem quatGramDoublePair_eq_jordan_trace (x : Fin 4 → m → Q) (i j k l : Fin 4) :
    let P := quatColumnDyad (x i)
    let Qj := quatColumnDyad (x j)
    let R := quatColumnDyad (x k)
    let S := quatColumnDyad (x l)
    (1/2 : ℝ) * (quatGramCycle (quatColumnGram x) i j k l +
      quatGramCycle (quatColumnGram x) i j l k) =
        (((1/2 : ℝ) • (P * Qj + Qj * P)) * ((1/2 : ℝ) • (R * S + S * R))).trace.re := by
  dsimp only
  rw [quatGramCycle_eq_dyad_trace, quatGramCycle_eq_dyad_trace]
  let A := quatColumnDyad (x i)
  let B := quatColumnDyad (x j)
  let C := quatColumnDyad (x k)
  let D := quatColumnDyad (x l)
  change (1/2 : ℝ) * (quatMatrixRealTrace (A*B*C*D) + quatMatrixRealTrace (A*B*D*C)) =
    quatMatrixRealTrace (((1/2 : ℝ) • (A*B+B*A)) * ((1/2 : ℝ) • (C*D+D*C)))
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  simp only [map_smul, map_add, smul_eq_mul]
  rw [quatTrace_four_reverse_first A B C D (quatColumnDyad_star _) (quatColumnDyad_star _)
      (quatColumnDyad_star _) (quatColumnDyad_star _),
    quatTrace_four_reverse_first A B D C (quatColumnDyad_star _) (quatColumnDyad_star _)
      (quatColumnDyad_star _) (quatColumnDyad_star _)]
  ring

end AlbertSequential.MatchingModels
