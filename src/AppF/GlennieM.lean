/- SPDX-License-Identifier: Apache-2.0 -/
module

public import AppF.GlennieS
public import ComplexWindowDeterminantAndMax
public import AppF.GlennieIngredients
-- build order only: keeps large modules from compiling concurrently (memory)
import AppF.GlennieSOrders

/-! # `thm:glennie` at the configuration `M` (exact instance)

`maximizerConfig = (p_A, p_B, p_C, p_D)` with `v_A = (1,0,0)`, `v_B = (1,√2,0)/√3`,
`v_C = (1,i,1)/√3`, `v_D = (1,j,ℓ)/√3`.  All entries lie in `ℚ(√2)`, so `F` is evaluated
exactly in the `ℚ(√2)` mirror (`Q2`) by kernel evaluation and transported:
`‖F(r_A,r_B,r_C,r_D)‖² = 2²⁴/3⁹ = 9·2²¹·N(p_A+p_B+p_C)·𝒜(M)` (`𝒜(M) = 4/3⁹`, `N = 2/9`). -/

@[expose] public section

namespace AlbertSequential.AppF

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

theorem toR_q2 (x : Q2) : ExactScalar.toR x = (x.a : ℝ) + (x.b : ℝ) * Real.sqrt 2 := rfl

def qq (a b : ℚ) : Q2 := ⟨a, b⟩
def eoq (a0 a1 a2 a3 b0 b1 b2 b3 : Q2) : EO Q2 := ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩⟩
def oq : Q2 := qq 0 0
def eoq0 : EO Q2 := eoq oq oq oq oq oq oq oq oq

def eaUnitQ2 : EA Q2 := ⟨qq 1 0, qq 1 0, qq 1 0, eoq0, eoq0, eoq0⟩
def symQ2 (x : EA Q2) : EA Q2 := (x.add x).sub eaUnitQ2

def MA : EA Q2 := ⟨qq 1 0, oq, oq, eoq0, eoq0, eoq0⟩
def MB : EA Q2 := ⟨qq (1/3) 0, qq (2/3) 0, oq, eoq (qq 0 (1/3)) oq oq oq oq oq oq oq, eoq0, eoq0⟩
def MC : EA Q2 := ⟨qq (1/3) 0, qq (1/3) 0, qq (1/3) 0, eoq oq (qq (-1/3) 0) oq oq oq oq oq oq,
  eoq (qq (1/3) 0) oq oq oq oq oq oq oq, eoq oq (qq (1/3) 0) oq oq oq oq oq oq⟩
def MD : EA Q2 := ⟨qq (1/3) 0, qq (1/3) 0, qq (1/3) 0, eoq oq oq (qq (-1/3) 0) oq oq oq oq oq,
  eoq oq oq oq oq (qq (-1/3) 0) oq oq oq, eoq oq oq oq oq oq oq (qq (-1/3) 0) oq⟩

set_option maxHeartbeats 400000000 in
theorem glM_dd : (eaOps Q2).mul (symQ2 MD) (symQ2 MD) =
    (⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg2 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MC) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg3 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MC) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg4 : Dop (eaOps Q2) (symQ2 MA) (symQ2 MA) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg5 : (eaOps Q2).mul (symQ2 MB) (symQ2 MC) =
    (⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (-2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-4/9) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (2/9)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg6 : Upol (eaOps Q2) ⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (-2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-4/9) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (2/9)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ ⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (-2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-4/9) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (2/9)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (11/27) (0)), (qq (7/27) (0)), (qq (5/9) (0)), eoq (qq (0) (-4/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-8/27) (0)) (qq (0) (4/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (4/27)) (qq (-4/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg7 : Upol (eaOps Q2) (symQ2 MC) (symQ2 MC) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg8 : Upol (eaOps Q2) (symQ2 MB) (symQ2 MB) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg9 : Ubr (eaOps Q2) (symQ2 MB) (symQ2 MB) (symQ2 MC) (symQ2 MC) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (-64/27) (0)), (qq (-80/27) (0)), (qq (-16/9) (0)), eoq (qq (0) (-16/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-32/27) (0)) (qq (0) (16/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (16/27)) (qq (-16/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  simp only [Ubr]
  rw [glM_stg5, glM_stg6, glM_stg7, glM_stg8]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg10 : Dop (eaOps Q2) (symQ2 MA) (symQ2 MA) ⟨(qq (-64/27) (0)), (qq (-80/27) (0)), (qq (-16/9) (0)), eoq (qq (0) (-16/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-32/27) (0)) (qq (0) (16/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (16/27)) (qq (-16/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg11 : Phi (eaOps Q2) (symQ2 MA) (symQ2 MB) (symQ2 MB) (symQ2 MA) (symQ2 MC) (symQ2 MC) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  simp only [Phi]
  rw [glM_stg2, glM_stg3, glM_stg4, glM_stg9, glM_stg10]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg12 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MC) (symQ2 MD) =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (-8/27)) (qq (-16/27) (0)) (qq (8/27) (0)) (qq (0) (-8/27)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (8/27)) (qq (-16/27) (0)) (qq (0) (0)) (qq (0) (-16/27)) (qq (0) (0)) (qq (8/27) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (-8/27) (0)) (qq (0) (8/27)) (qq (0) (0)) (qq (-8/27) (0)) (qq (0) (0)) (qq (0) (-16/27))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg13 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MC) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (-8/27)) (qq (-16/27) (0)) (qq (8/27) (0)) (qq (0) (-8/27)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (8/27)) (qq (-16/27) (0)) (qq (0) (0)) (qq (0) (-16/27)) (qq (0) (0)) (qq (8/27) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (-8/27) (0)) (qq (0) (8/27)) (qq (0) (0)) (qq (-8/27) (0)) (qq (0) (0)) (qq (0) (-16/27))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (32/27) (0)) (qq (0) (0)) (qq (0) (32/81)) (qq (-32/81) (0)) (qq (64/81) (0)) (qq (0) (32/81)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (32/81)) (qq (32/81) (0)) (qq (160/81) (0)) (qq (0) (0)) (qq (0) (-32/81)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (64/81) (0)) (qq (0) (32/81)) (qq (0) (-32/81)) (qq (0) (0)) (qq (128/81) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg14 : Dop (eaOps Q2) (symQ2 MA) (symQ2 MA) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (32/27) (0)) (qq (0) (0)) (qq (0) (32/81)) (qq (-32/81) (0)) (qq (64/81) (0)) (qq (0) (32/81)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (32/81)) (qq (32/81) (0)) (qq (160/81) (0)) (qq (0) (0)) (qq (0) (-32/81)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (64/81) (0)) (qq (0) (32/81)) (qq (0) (-32/81)) (qq (0) (0)) (qq (128/81) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg15 : (eaOps Q2).mul (symQ2 MB) (symQ2 MC) =
    (⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (-2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-4/9) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (2/9)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg16 : Upol (eaOps Q2) ⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (-2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-4/9) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (2/9)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ ⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (-2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-4/9) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (2/9)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ (symQ2 MD) =
    (⟨(qq (-11/81) (0)), (qq (-7/81) (0)), (qq (-5/27) (0)), eoq (qq (0) (4/81)) (qq (0) (0)) (qq (2/27) (0)) (qq (0) (0)) (qq (0) (4/81)) (qq (-4/81) (0)) (qq (8/81) (0)) (qq (0) (4/81)), eoq (qq (8/81) (0)) (qq (0) (-4/81)) (qq (0) (4/81)) (qq (4/81) (0)) (qq (14/81) (0)) (qq (0) (0)) (qq (0) (-4/81)) (qq (0) (0)), eoq (qq (0) (-4/81)) (qq (4/81) (0)) (qq (8/81) (0)) (qq (0) (4/81)) (qq (0) (-4/81)) (qq (0) (0)) (qq (10/81) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg17 : Upol (eaOps Q2) (symQ2 MC) (symQ2 MC) (symQ2 MD) =
    (⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (-1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (4/9) (0)) (qq (-4/9) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-4/9) (0)) (qq (2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (4/9) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (-4/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (4/9) (0)) (qq (2/9) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg18 : Upol (eaOps Q2) (symQ2 MB) (symQ2 MB) ⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (-1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (4/9) (0)) (qq (-4/9) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-4/9) (0)) (qq (2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (4/9) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (-4/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (4/9) (0)) (qq (2/9) (0)) (qq (0) (0))⟩ =
    (⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (-1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-4/9) (0)) (qq (4/9) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (8/27)) (qq (-4/27) (0)) (qq (2/27) (0)) (qq (0) (-8/27)) (qq (0) (-4/27)) (qq (4/27) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (4/27) (0)) (qq (0) (8/27)) (qq (0) (-4/27)) (qq (-4/27) (0)) (qq (-2/27) (0)) (qq (0) (-8/27))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg19 : Upol (eaOps Q2) (symQ2 MB) (symQ2 MB) (symQ2 MD) =
    (⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (-1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (2/3) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (4/9)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (4/9)) (qq (0) (0)) (qq (2/9) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg20 : Upol (eaOps Q2) (symQ2 MC) (symQ2 MC) ⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (-1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (2/3) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (4/9)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (4/9)) (qq (0) (0)) (qq (2/9) (0)) (qq (0) (0))⟩ =
    (⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (-1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (8/27)) (qq (4/27) (0)) (qq (4/27) (0)) (qq (0) (8/27)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (4/9) (0)) (qq (2/27) (0)) (qq (0) (8/27)) (qq (0) (-4/27)) (qq (-4/27) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (4/9) (0)) (qq (0) (0)) (qq (0) (-4/27)) (qq (4/27) (0)) (qq (-2/27) (0)) (qq (0) (8/27))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg21 : Ubr (eaOps Q2) (symQ2 MB) (symQ2 MB) (symQ2 MC) (symQ2 MC) (symQ2 MD) =
    (⟨(qq (64/81) (0)), (qq (80/81) (0)), (qq (16/27) (0)), eoq (qq (0) (16/81)) (qq (0) (0)) (qq (32/27) (0)) (qq (0) (0)) (qq (0) (-32/81)) (qq (32/81) (0)) (qq (-64/81) (0)) (qq (0) (-32/81)), eoq (qq (32/81) (0)) (qq (0) (-16/81)) (qq (0) (-32/81)) (qq (-32/81) (0)) (qq (32/81) (0)) (qq (0) (0)) (qq (0) (32/81)) (qq (0) (0)), eoq (qq (0) (-16/81)) (qq (16/81) (0)) (qq (-64/81) (0)) (qq (0) (-32/81)) (qq (0) (32/81)) (qq (0) (0)) (qq (64/81) (0)) (qq (0) (0))⟩ : EA Q2) := by
  simp only [Ubr]
  rw [glM_stg15, glM_stg16, glM_stg17, glM_stg18, glM_stg19, glM_stg20]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg22 : Dop (eaOps Q2) (symQ2 MA) (symQ2 MA) ⟨(qq (64/81) (0)), (qq (80/81) (0)), (qq (16/27) (0)), eoq (qq (0) (16/81)) (qq (0) (0)) (qq (32/27) (0)) (qq (0) (0)) (qq (0) (-32/81)) (qq (32/81) (0)) (qq (-64/81) (0)) (qq (0) (-32/81)), eoq (qq (32/81) (0)) (qq (0) (-16/81)) (qq (0) (-32/81)) (qq (-32/81) (0)) (qq (32/81) (0)) (qq (0) (0)) (qq (0) (32/81)) (qq (0) (0)), eoq (qq (0) (-16/81)) (qq (16/81) (0)) (qq (-64/81) (0)) (qq (0) (-32/81)) (qq (0) (32/81)) (qq (0) (0)) (qq (64/81) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg23 : Phi (eaOps Q2) (symQ2 MA) (symQ2 MB) (symQ2 MB) (symQ2 MA) (symQ2 MC) (symQ2 MC) (symQ2 MD) =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  simp only [Phi]
  rw [glM_stg12, glM_stg13, glM_stg14, glM_stg21, glM_stg22]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_term0 : glennieTerm (eaOps Q2) (symQ2 MD) (symQ2 MA) (symQ2 MB) (symQ2 MB) (symQ2 MA) (symQ2 MC) (symQ2 MC) =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  simp only [glennieTerm]
  rw [glM_dd, glM_stg11, glM_stg23]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg25 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MC) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg26 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MA) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg27 : Dop (eaOps Q2) (symQ2 MA) (symQ2 MC) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg28 : (eaOps Q2).mul (symQ2 MB) (symQ2 MA) =
    (⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg29 : (eaOps Q2).mul (symQ2 MB) (symQ2 MC) =
    (⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (-2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-4/9) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (2/9)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg30 : Upol (eaOps Q2) ⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ ⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (-2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-4/9) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (2/9)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (-1/27) (0)), (qq (1/27) (0)), (qq (1/3) (0)), eoq (qq (0) (2/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-4/27) (0)) (qq (0) (2/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (2/27)) (qq (-2/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg31 : Upol (eaOps Q2) (symQ2 MA) (symQ2 MC) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (-1/3) (0)), (qq (1/3) (0)), (qq (1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-2/3) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg32 : Upol (eaOps Q2) (symQ2 MB) (symQ2 MB) ⟨(qq (-1/3) (0)), (qq (1/3) (0)), (qq (1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-2/3) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (7/27) (0)), (qq (-7/27) (0)), (qq (1/3) (0)), eoq (qq (0) (4/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (4/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg33 : Upol (eaOps Q2) (symQ2 MB) (symQ2 MB) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg34 : Ubr (eaOps Q2) (symQ2 MB) (symQ2 MB) (symQ2 MA) (symQ2 MC) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-16/27) (0)) (qq (0) (-16/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (8/27)) (qq (16/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  simp only [Ubr]
  rw [glM_stg28, glM_stg29, glM_stg30, glM_stg31, glM_stg32, glM_stg33]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg35 : Dop (eaOps Q2) (symQ2 MA) (symQ2 MC) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-16/27) (0)) (qq (0) (-16/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (8/27)) (qq (16/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (-128/81) (0)), (qq (0) (0)), (qq (128/81) (0)), eoq (qq (0) (32/81)) (qq (-64/81) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (64/81) (0)) (qq (0) (-32/81)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (-64/81)) (qq (64/81) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg36 : Phi (eaOps Q2) (symQ2 MA) (symQ2 MB) (symQ2 MB) (symQ2 MC) (symQ2 MA) (symQ2 MC) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (-128/27) (0)), (qq (0) (0)), (qq (128/27) (0)), eoq (qq (0) (32/27)) (qq (-64/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (64/27) (0)) (qq (0) (-32/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (-64/27)) (qq (64/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  simp only [Phi]
  rw [glM_stg25, glM_stg26, glM_stg27, glM_stg34, glM_stg35]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg37 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MC) (symQ2 MD) =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (-8/27)) (qq (-16/27) (0)) (qq (8/27) (0)) (qq (0) (-8/27)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (8/27)) (qq (-16/27) (0)) (qq (0) (0)) (qq (0) (-16/27)) (qq (0) (0)) (qq (8/27) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (-8/27) (0)) (qq (0) (8/27)) (qq (0) (0)) (qq (-8/27) (0)) (qq (0) (0)) (qq (0) (-16/27))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg38 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MA) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (-8/27)) (qq (-16/27) (0)) (qq (8/27) (0)) (qq (0) (-8/27)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (8/27)) (qq (-16/27) (0)) (qq (0) (0)) (qq (0) (-16/27)) (qq (0) (0)) (qq (8/27) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (-8/27) (0)) (qq (0) (8/27)) (qq (0) (0)) (qq (-8/27) (0)) (qq (0) (0)) (qq (0) (-16/27))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (32/81)) (qq (-64/81) (0)) (qq (0) (0)) (qq (0) (32/81)) (qq (0) (0)) (qq (128/81) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (64/81) (0)) (qq (0) (-64/81)) (qq (0) (0)) (qq (-128/81) (0)) (qq (0) (0)) (qq (0) (32/81))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg39 : Dop (eaOps Q2) (symQ2 MA) (symQ2 MC) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (32/81)) (qq (-64/81) (0)) (qq (0) (0)) (qq (0) (32/81)) (qq (0) (0)) (qq (128/81) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (64/81) (0)) (qq (0) (-64/81)) (qq (0) (0)) (qq (-128/81) (0)) (qq (0) (0)) (qq (0) (32/81))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (-256/243) (0)) (qq (0) (256/243)) (qq (0) (0)) (qq (512/243) (0)) (qq (0) (0)) (qq (0) (-128/243)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (-256/243)) (qq (-256/243) (0)) (qq (-512/243) (0)) (qq (0) (0)) (qq (0) (-128/243)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (-256/243) (0)) (qq (0) (-128/243)) (qq (0) (128/243)) (qq (0) (0)) (qq (-512/243) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg40 : (eaOps Q2).mul (symQ2 MB) (symQ2 MA) =
    (⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg41 : (eaOps Q2).mul (symQ2 MB) (symQ2 MC) =
    (⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (-2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-4/9) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (2/9)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg42 : Upol (eaOps Q2) ⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ ⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (-2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-4/9) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (2/9)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ (symQ2 MD) =
    (⟨(qq (1/81) (0)), (qq (-1/81) (0)), (qq (-1/9) (0)), eoq (qq (0) (-2/81)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (2/81)) (qq (-2/81) (0)) (qq (4/81) (0)) (qq (0) (2/81)), eoq (qq (4/81) (0)) (qq (0) (-2/81)) (qq (0) (2/81)) (qq (2/81) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (2/27)) (qq (0) (0)), eoq (qq (0) (-2/81)) (qq (2/81) (0)) (qq (4/81) (0)) (qq (0) (2/81)) (qq (0) (2/27)) (qq (0) (0)) (qq (2/27) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg43 : Upol (eaOps Q2) (symQ2 MA) (symQ2 MC) (symQ2 MD) =
    (⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (-1/9) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-2/9) (0)) (qq (-2/9) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)), eoq (qq (0) (0)) (qq (2/9) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (-2/9) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg44 : Upol (eaOps Q2) (symQ2 MB) (symQ2 MB) ⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (-1/9) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-2/9) (0)) (qq (-2/9) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)), eoq (qq (0) (0)) (qq (2/9) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (-2/9) (0)) (qq (0) (0))⟩ =
    (⟨(qq (-7/81) (0)), (qq (7/81) (0)), (qq (-1/9) (0)), eoq (qq (0) (-4/81)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (2/9) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (-4/27)) (qq (0) (4/27)) (qq (2/27) (0)) (qq (0) (0)) (qq (0) (-4/27)) (qq (0) (4/27)) (qq (2/27) (0)), eoq (qq (0) (0)) (qq (-2/27) (0)) (qq (2/27) (0)) (qq (0) (-4/27)) (qq (0) (0)) (qq (-2/27) (0)) (qq (2/27) (0)) (qq (0) (-4/27))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg45 : Upol (eaOps Q2) (symQ2 MB) (symQ2 MB) (symQ2 MD) =
    (⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (-1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (2/3) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (4/9)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (4/9)) (qq (0) (0)) (qq (2/9) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg46 : Upol (eaOps Q2) (symQ2 MA) (symQ2 MC) ⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (-1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (2/3) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (4/9)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (4/9)) (qq (0) (0)) (qq (2/9) (0)) (qq (0) (0))⟩ =
    (⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (-1/9) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (4/27)) (qq (-2/27) (0)) (qq (2/27) (0)) (qq (0) (-4/27)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (4/27)) (qq (0) (0)) (qq (-2/27) (0)), eoq (qq (0) (0)) (qq (2/9) (0)) (qq (2/9) (0)) (qq (0) (0)) (qq (0) (4/27)) (qq (2/27) (0)) (qq (2/27) (0)) (qq (0) (4/27))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg47 : Ubr (eaOps Q2) (symQ2 MB) (symQ2 MB) (symQ2 MA) (symQ2 MC) (symQ2 MD) =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (-16/81)) (qq (-32/81) (0)) (qq (-32/81) (0)) (qq (0) (32/81)), eoq (qq (16/81) (0)) (qq (0) (16/81)) (qq (0) (-16/81)) (qq (32/81) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (-8/81)) (qq (-16/81) (0)) (qq (-32/81) (0)) (qq (0) (32/81)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  simp only [Ubr]
  rw [glM_stg40, glM_stg41, glM_stg42, glM_stg43, glM_stg44, glM_stg45, glM_stg46]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg48 : Dop (eaOps Q2) (symQ2 MA) (symQ2 MC) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (-16/81)) (qq (-32/81) (0)) (qq (-32/81) (0)) (qq (0) (32/81)), eoq (qq (16/81) (0)) (qq (0) (16/81)) (qq (0) (-16/81)) (qq (32/81) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (-8/81)) (qq (-16/81) (0)) (qq (-32/81) (0)) (qq (0) (32/81)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (128/243) (0)), (qq (0) (0)), (qq (-128/243) (0)), eoq (qq (0) (-32/243)) (qq (64/243) (0)) (qq (128/243) (0)) (qq (0) (-128/243)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-64/243) (0)) (qq (0) (32/243)) (qq (0) (128/243)) (qq (128/243) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (64/243)) (qq (-64/243) (0)) (qq (128/243) (0)) (qq (0) (64/243)) (qq (0) (-64/243)) (qq (-128/243) (0)) (qq (-128/243) (0)) (qq (0) (128/243))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg49 : Phi (eaOps Q2) (symQ2 MA) (symQ2 MB) (symQ2 MB) (symQ2 MC) (symQ2 MA) (symQ2 MC) (symQ2 MD) =
    (⟨(qq (128/81) (0)), (qq (0) (0)), (qq (-128/81) (0)), eoq (qq (0) (-32/81)) (qq (64/81) (0)) (qq (128/243) (0)) (qq (0) (-128/243)) (qq (0) (0)) (qq (512/243) (0)) (qq (0) (0)) (qq (0) (-128/243)), eoq (qq (-64/81) (0)) (qq (0) (32/81)) (qq (0) (128/243)) (qq (128/243) (0)) (qq (-512/243) (0)) (qq (0) (0)) (qq (0) (-128/243)) (qq (0) (0)), eoq (qq (0) (64/81)) (qq (-64/81) (0)) (qq (128/243) (0)) (qq (0) (64/243)) (qq (0) (-64/243)) (qq (-128/81) (0)) (qq (-896/243) (0)) (qq (0) (128/81))⟩ : EA Q2) := by
  simp only [Phi]
  rw [glM_stg37, glM_stg38, glM_stg39, glM_stg47, glM_stg48]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_term1 : glennieTerm (eaOps Q2) (symQ2 MD) (symQ2 MA) (symQ2 MB) (symQ2 MB) (symQ2 MC) (symQ2 MA) (symQ2 MC) =
    (⟨(qq (-1408/243) (0)), (qq (-1024/243) (0)), (qq (-2944/729) (0)), eoq (qq (0) (32/81)) (qq (-64/81) (0)) (qq (1280/243) (0)) (qq (0) (-1024/729)) (qq (0) (640/729)) (qq (128/243) (0)) (qq (640/729) (0)) (qq (0) (64/729)), eoq (qq (1088/729) (0)) (qq (0) (-800/729)) (qq (0) (640/729)) (qq (-128/243) (0)) (qq (512/729) (0)) (qq (0) (-1024/729)) (qq (0) (-64/81)) (qq (-128/81) (0)), eoq (qq (0) (-1088/729)) (qq (704/243) (0)) (qq (640/729) (0)) (qq (0) (64/729)) (qq (0) (-64/81)) (qq (-128/81) (0)) (qq (-1792/729) (0)) (qq (0) (1024/729))⟩ : EA Q2) := by
  simp only [glennieTerm]
  rw [glM_dd, glM_stg36, glM_stg49]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg51 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MA) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg52 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MC) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg53 : Dop (eaOps Q2) (symQ2 MA) (symQ2 MC) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg54 : (eaOps Q2).mul (symQ2 MB) (symQ2 MC) =
    (⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (-2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-4/9) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (2/9)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg55 : (eaOps Q2).mul (symQ2 MB) (symQ2 MA) =
    (⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg56 : Upol (eaOps Q2) ⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (-2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-4/9) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (2/9)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ ⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (-1/27) (0)), (qq (1/27) (0)), (qq (1/3) (0)), eoq (qq (0) (2/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-4/27) (0)) (qq (0) (2/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (2/27)) (qq (-2/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg57 : Upol (eaOps Q2) (symQ2 MC) (symQ2 MA) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (-1/3) (0)), (qq (1/3) (0)), (qq (1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-2/3) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg58 : Upol (eaOps Q2) (symQ2 MB) (symQ2 MB) ⟨(qq (-1/3) (0)), (qq (1/3) (0)), (qq (1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-2/3) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (7/27) (0)), (qq (-7/27) (0)), (qq (1/3) (0)), eoq (qq (0) (4/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (4/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg59 : Upol (eaOps Q2) (symQ2 MB) (symQ2 MB) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg60 : Ubr (eaOps Q2) (symQ2 MB) (symQ2 MB) (symQ2 MC) (symQ2 MA) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-16/27) (0)) (qq (0) (-16/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (8/27)) (qq (16/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  simp only [Ubr]
  rw [glM_stg54, glM_stg55, glM_stg56, glM_stg57, glM_stg58, glM_stg59]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg61 : Dop (eaOps Q2) (symQ2 MA) (symQ2 MC) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-16/27) (0)) (qq (0) (-16/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (8/27)) (qq (16/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (-128/81) (0)), (qq (0) (0)), (qq (128/81) (0)), eoq (qq (0) (32/81)) (qq (-64/81) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (64/81) (0)) (qq (0) (-32/81)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (-64/81)) (qq (64/81) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg62 : Phi (eaOps Q2) (symQ2 MA) (symQ2 MB) (symQ2 MB) (symQ2 MC) (symQ2 MC) (symQ2 MA) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (-128/27) (0)), (qq (0) (0)), (qq (128/27) (0)), eoq (qq (0) (32/27)) (qq (-64/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (64/27) (0)) (qq (0) (-32/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (-64/27)) (qq (64/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  simp only [Phi]
  rw [glM_stg51, glM_stg52, glM_stg53, glM_stg60, glM_stg61]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg63 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MA) (symQ2 MD) =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (8/9)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (-8/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg64 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MC) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (8/9)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (-8/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (32/81)) (qq (64/81) (0)) (qq (64/81) (0)) (qq (0) (-64/81)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (-32/81)) (qq (0) (0)) (qq (-128/81) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (128/81) (0)) (qq (0) (0)) (qq (0) (-32/81))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg65 : Dop (eaOps Q2) (symQ2 MA) (symQ2 MC) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (32/81)) (qq (64/81) (0)) (qq (64/81) (0)) (qq (0) (-64/81)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (-32/81)) (qq (0) (0)) (qq (-128/81) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (128/81) (0)) (qq (0) (0)) (qq (0) (-32/81))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-512/243) (0)) (qq (0) (0)) (qq (0) (128/243)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (512/243) (0)) (qq (0) (0)) (qq (0) (128/243)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (256/243) (0)) (qq (256/81) (0)) (qq (0) (-256/243))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg66 : (eaOps Q2).mul (symQ2 MB) (symQ2 MC) =
    (⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (-2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-4/9) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (2/9)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg67 : (eaOps Q2).mul (symQ2 MB) (symQ2 MA) =
    (⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg68 : Upol (eaOps Q2) ⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (-2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-4/9) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (2/9)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ ⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ (symQ2 MD) =
    (⟨(qq (1/81) (0)), (qq (-1/81) (0)), (qq (-1/9) (0)), eoq (qq (0) (-2/81)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (2/81)) (qq (-2/81) (0)) (qq (4/81) (0)) (qq (0) (2/81)), eoq (qq (4/81) (0)) (qq (0) (-2/81)) (qq (0) (2/81)) (qq (2/81) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (2/27)) (qq (0) (0)), eoq (qq (0) (-2/81)) (qq (2/81) (0)) (qq (4/81) (0)) (qq (0) (2/81)) (qq (0) (2/27)) (qq (0) (0)) (qq (2/27) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg69 : Upol (eaOps Q2) (symQ2 MC) (symQ2 MA) (symQ2 MD) =
    (⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (-1/9) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-2/9) (0)) (qq (-2/9) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)), eoq (qq (0) (0)) (qq (2/9) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (-2/9) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg70 : Upol (eaOps Q2) (symQ2 MB) (symQ2 MB) ⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (-1/9) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-2/9) (0)) (qq (-2/9) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)), eoq (qq (0) (0)) (qq (2/9) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (-2/9) (0)) (qq (0) (0))⟩ =
    (⟨(qq (-7/81) (0)), (qq (7/81) (0)), (qq (-1/9) (0)), eoq (qq (0) (-4/81)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (2/9) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (-4/27)) (qq (0) (4/27)) (qq (2/27) (0)) (qq (0) (0)) (qq (0) (-4/27)) (qq (0) (4/27)) (qq (2/27) (0)), eoq (qq (0) (0)) (qq (-2/27) (0)) (qq (2/27) (0)) (qq (0) (-4/27)) (qq (0) (0)) (qq (-2/27) (0)) (qq (2/27) (0)) (qq (0) (-4/27))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg71 : Upol (eaOps Q2) (symQ2 MB) (symQ2 MB) (symQ2 MD) =
    (⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (-1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (2/3) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (4/9)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (4/9)) (qq (0) (0)) (qq (2/9) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg72 : Upol (eaOps Q2) (symQ2 MC) (symQ2 MA) ⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (-1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (2/3) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (4/9)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (4/9)) (qq (0) (0)) (qq (2/9) (0)) (qq (0) (0))⟩ =
    (⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (-1/9) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (4/27)) (qq (-2/27) (0)) (qq (2/27) (0)) (qq (0) (-4/27)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (4/27)) (qq (0) (0)) (qq (-2/27) (0)), eoq (qq (0) (0)) (qq (2/9) (0)) (qq (2/9) (0)) (qq (0) (0)) (qq (0) (4/27)) (qq (2/27) (0)) (qq (2/27) (0)) (qq (0) (4/27))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg73 : Ubr (eaOps Q2) (symQ2 MB) (symQ2 MB) (symQ2 MC) (symQ2 MA) (symQ2 MD) =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (-16/81)) (qq (-32/81) (0)) (qq (-32/81) (0)) (qq (0) (32/81)), eoq (qq (16/81) (0)) (qq (0) (16/81)) (qq (0) (-16/81)) (qq (32/81) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (-8/81)) (qq (-16/81) (0)) (qq (-32/81) (0)) (qq (0) (32/81)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  simp only [Ubr]
  rw [glM_stg66, glM_stg67, glM_stg68, glM_stg69, glM_stg70, glM_stg71, glM_stg72]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg74 : Dop (eaOps Q2) (symQ2 MA) (symQ2 MC) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (-16/81)) (qq (-32/81) (0)) (qq (-32/81) (0)) (qq (0) (32/81)), eoq (qq (16/81) (0)) (qq (0) (16/81)) (qq (0) (-16/81)) (qq (32/81) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (-8/81)) (qq (-16/81) (0)) (qq (-32/81) (0)) (qq (0) (32/81)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (128/243) (0)), (qq (0) (0)), (qq (-128/243) (0)), eoq (qq (0) (-32/243)) (qq (64/243) (0)) (qq (128/243) (0)) (qq (0) (-128/243)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-64/243) (0)) (qq (0) (32/243)) (qq (0) (128/243)) (qq (128/243) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (64/243)) (qq (-64/243) (0)) (qq (128/243) (0)) (qq (0) (64/243)) (qq (0) (-64/243)) (qq (-128/243) (0)) (qq (-128/243) (0)) (qq (0) (128/243))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg75 : Phi (eaOps Q2) (symQ2 MA) (symQ2 MB) (symQ2 MB) (symQ2 MC) (symQ2 MC) (symQ2 MA) (symQ2 MD) =
    (⟨(qq (128/81) (0)), (qq (0) (0)), (qq (-128/81) (0)), eoq (qq (0) (-32/81)) (qq (64/81) (0)) (qq (128/81) (0)) (qq (0) (-128/81)) (qq (0) (0)) (qq (-512/243) (0)) (qq (0) (0)) (qq (0) (128/243)), eoq (qq (-64/81) (0)) (qq (0) (32/81)) (qq (0) (128/81)) (qq (128/81) (0)) (qq (512/243) (0)) (qq (0) (0)) (qq (0) (128/243)) (qq (0) (0)), eoq (qq (0) (64/81)) (qq (-64/81) (0)) (qq (128/81) (0)) (qq (0) (64/81)) (qq (0) (-64/81)) (qq (-128/243) (0)) (qq (128/81) (0)) (qq (0) (128/243))⟩ : EA Q2) := by
  simp only [Phi]
  rw [glM_stg63, glM_stg64, glM_stg65, glM_stg73, glM_stg74]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_term2 : glennieTerm (eaOps Q2) (symQ2 MD) (symQ2 MA) (symQ2 MB) (symQ2 MB) (symQ2 MC) (symQ2 MC) (symQ2 MA) =
    (⟨(qq (896/729) (0)), (qq (1024/243) (0)), (qq (6272/729) (0)), eoq (qq (0) (544/729)) (qq (-1088/729) (0)) (qq (-256/729) (0)) (qq (0) (-1024/729)) (qq (0) (128/81)) (qq (-2176/729) (0)) (qq (128/81) (0)) (qq (0) (832/729)), eoq (qq (64/81) (0)) (qq (0) (-32/729)) (qq (0) (128/81)) (qq (2176/729) (0)) (qq (-512/729) (0)) (qq (0) (-1024/729)) (qq (0) (-320/729)) (qq (-640/729) (0)), eoq (qq (0) (-64/81)) (qq (-448/729) (0)) (qq (128/81) (0)) (qq (0) (832/729)) (qq (0) (-320/729)) (qq (-640/729) (0)) (qq (-1792/729) (0)) (qq (0) (1024/729))⟩ : EA Q2) := by
  simp only [glennieTerm]
  rw [glM_dd, glM_stg62, glM_stg75]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg77 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MC) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg78 : Dop (eaOps Q2) (symQ2 MA) (symQ2 MC) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg79 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MA) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg80 : (eaOps Q2).mul (symQ2 MA) (symQ2 MC) =
    (⟨(qq (-1/3) (0)), (qq (1/3) (0)), (qq (1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-2/3) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg81 : (eaOps Q2).mul (symQ2 MB) (symQ2 MC) =
    (⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (-2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-4/9) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (2/9)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg82 : Upol (eaOps Q2) ⟨(qq (-1/3) (0)), (qq (1/3) (0)), (qq (1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-2/3) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ ⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (-2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-4/9) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (2/9)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (-1/27) (0)), (qq (1/9) (0)), (qq (7/27) (0)), eoq (qq (0) (-2/27)) (qq (-4/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (2/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (2/27)) (qq (-4/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg83 : Upol (eaOps Q2) (symQ2 MC) (symQ2 MC) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg84 : Upol (eaOps Q2) (symQ2 MA) (symQ2 MB) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg85 : Upol (eaOps Q2) (symQ2 MC) (symQ2 MC) ⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (7/27) (0)), (qq (7/27) (0)), (qq (-5/27) (0)), eoq (qq (0) (0)) (qq (-16/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-8/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-8/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg86 : Ubr (eaOps Q2) (symQ2 MA) (symQ2 MB) (symQ2 MC) (symQ2 MC) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (16/27) (0)), (qq (-16/27) (0)), eoq (qq (0) (-8/27)) (qq (16/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (16/27) (0)) (qq (0) (8/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (8/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  simp only [Ubr]
  rw [glM_stg80, glM_stg81, glM_stg82, glM_stg83, glM_stg84, glM_stg85]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg87 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MA) ⟨(qq (0) (0)), (qq (16/27) (0)), (qq (-16/27) (0)), eoq (qq (0) (-8/27)) (qq (16/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (16/27) (0)) (qq (0) (8/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (8/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (128/81) (0)), (qq (-128/81) (0)), (qq (0) (0)), eoq (qq (0) (-64/81)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-64/81) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (64/81)) (qq (64/81) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg88 : Phi (eaOps Q2) (symQ2 MB) (symQ2 MA) (symQ2 MB) (symQ2 MA) (symQ2 MC) (symQ2 MC) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (128/27) (0)), (qq (-128/27) (0)), (qq (0) (0)), eoq (qq (0) (-64/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-64/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (64/27)) (qq (64/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  simp only [Phi]
  rw [glM_stg77, glM_stg78, glM_stg79, glM_stg86, glM_stg87]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg89 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MC) (symQ2 MD) =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (-8/27)) (qq (-16/27) (0)) (qq (8/27) (0)) (qq (0) (-8/27)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (8/27)) (qq (-16/27) (0)) (qq (0) (0)) (qq (0) (-16/27)) (qq (0) (0)) (qq (8/27) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (-8/27) (0)) (qq (0) (8/27)) (qq (0) (0)) (qq (-8/27) (0)) (qq (0) (0)) (qq (0) (-16/27))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg90 : Dop (eaOps Q2) (symQ2 MA) (symQ2 MC) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (-8/27)) (qq (-16/27) (0)) (qq (8/27) (0)) (qq (0) (-8/27)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (8/27)) (qq (-16/27) (0)) (qq (0) (0)) (qq (0) (-16/27)) (qq (0) (0)) (qq (8/27) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (-8/27) (0)) (qq (0) (8/27)) (qq (0) (0)) (qq (-8/27) (0)) (qq (0) (0)) (qq (0) (-16/27))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (32/81) (0)) (qq (0) (-32/81)) (qq (0) (0)) (qq (32/81) (0)) (qq (0) (0)) (qq (0) (64/81)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (32/81)) (qq (32/81) (0)) (qq (-32/81) (0)) (qq (0) (0)) (qq (0) (64/81)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (-64/81) (0)) (qq (0) (-32/81)) (qq (0) (-32/27)) (qq (-64/81) (0)) (qq (0) (0)) (qq (0) (-32/81))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg91 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MA) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (32/81) (0)) (qq (0) (-32/81)) (qq (0) (0)) (qq (32/81) (0)) (qq (0) (0)) (qq (0) (64/81)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (32/81)) (qq (32/81) (0)) (qq (-32/81) (0)) (qq (0) (0)) (qq (0) (64/81)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (-64/81) (0)) (qq (0) (-32/81)) (qq (0) (-32/27)) (qq (-64/81) (0)) (qq (0) (0)) (qq (0) (-32/81))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (256/243)) (qq (256/243) (0)) (qq (256/81) (0)) (qq (0) (256/243)) (qq (0) (0)) (qq (256/243) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (256/243) (0)) (qq (0) (128/243)) (qq (0) (-128/243)) (qq (0) (0)) (qq (512/243) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg92 : (eaOps Q2).mul (symQ2 MA) (symQ2 MC) =
    (⟨(qq (-1/3) (0)), (qq (1/3) (0)), (qq (1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-2/3) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg93 : (eaOps Q2).mul (symQ2 MB) (symQ2 MC) =
    (⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (-2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-4/9) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (2/9)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg94 : Upol (eaOps Q2) ⟨(qq (-1/3) (0)), (qq (1/3) (0)), (qq (1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-2/3) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ ⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (-2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-4/9) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (2/9)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ (symQ2 MD) =
    (⟨(qq (1/81) (0)), (qq (-1/27) (0)), (qq (-7/81) (0)), eoq (qq (0) (2/81)) (qq (4/81) (0)) (qq (-2/81) (0)) (qq (0) (0)) (qq (0) (2/81)) (qq (0) (0)) (qq (-4/81) (0)) (qq (0) (2/81)), eoq (qq (0) (0)) (qq (0) (-2/81)) (qq (0) (2/81)) (qq (0) (0)) (qq (2/81) (0)) (qq (0) (0)) (qq (0) (-2/81)) (qq (8/81) (0)), eoq (qq (0) (-2/81)) (qq (4/81) (0)) (qq (-4/81) (0)) (qq (0) (2/81)) (qq (0) (-2/81)) (qq (8/81) (0)) (qq (2/27) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg95 : Upol (eaOps Q2) (symQ2 MC) (symQ2 MC) (symQ2 MD) =
    (⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (-1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (4/9) (0)) (qq (-4/9) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-4/9) (0)) (qq (2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (4/9) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (-4/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (4/9) (0)) (qq (2/9) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg96 : Upol (eaOps Q2) (symQ2 MA) (symQ2 MB) ⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (-1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (4/9) (0)) (qq (-4/9) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-4/9) (0)) (qq (2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (4/9) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (-4/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (4/9) (0)) (qq (2/9) (0)) (qq (0) (0))⟩ =
    (⟨(qq (1/9) (0)), (qq (1/9) (0)), (qq (-1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (2/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (4/27) (0)) (qq (-4/27) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (4/27)) (qq (4/27) (0)) (qq (-2/27) (0)) (qq (0) (-4/27)) (qq (0) (-2/27)) (qq (-4/27) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (-4/27) (0)) (qq (0) (4/27)) (qq (0) (-2/27)) (qq (4/27) (0)) (qq (2/27) (0)) (qq (0) (-4/27))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg97 : Upol (eaOps Q2) (symQ2 MA) (symQ2 MB) (symQ2 MD) =
    (⟨(qq (1/9) (0)), (qq (1/9) (0)), (qq (-1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (0) (0)) (qq (0) (2/9)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg98 : Upol (eaOps Q2) (symQ2 MC) (symQ2 MC) ⟨(qq (1/9) (0)), (qq (1/9) (0)), (qq (-1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (0) (0)) (qq (0) (2/9)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0))⟩ =
    (⟨(qq (-7/81) (0)), (qq (-7/81) (0)), (qq (5/81) (0)), eoq (qq (0) (0)) (qq (16/81) (0)) (qq (2/27) (0)) (qq (0) (0)) (qq (0) (4/27)) (qq (-4/27) (0)) (qq (-4/27) (0)) (qq (0) (4/27)), eoq (qq (8/81) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-4/27) (0)) (qq (-2/27) (0)) (qq (0) (4/27)) (qq (0) (-2/27)) (qq (4/27) (0)), eoq (qq (0) (0)) (qq (8/81) (0)) (qq (-4/27) (0)) (qq (0) (0)) (qq (0) (-2/27)) (qq (-4/27) (0)) (qq (2/27) (0)) (qq (0) (4/27))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg99 : Ubr (eaOps Q2) (symQ2 MA) (symQ2 MB) (symQ2 MC) (symQ2 MC) (symQ2 MD) =
    (⟨(qq (0) (0)), (qq (-16/81) (0)), (qq (16/81) (0)), eoq (qq (0) (8/81)) (qq (-16/81) (0)) (qq (-32/81) (0)) (qq (0) (0)) (qq (0) (-16/81)) (qq (0) (0)) (qq (32/81) (0)) (qq (0) (-16/81)), eoq (qq (-16/81) (0)) (qq (0) (-8/81)) (qq (0) (-16/81)) (qq (0) (0)) (qq (32/81) (0)) (qq (0) (0)) (qq (0) (16/81)) (qq (32/81) (0)), eoq (qq (0) (-8/81)) (qq (0) (0)) (qq (32/81) (0)) (qq (0) (-16/81)) (qq (0) (16/81)) (qq (32/81) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  simp only [Ubr]
  rw [glM_stg92, glM_stg93, glM_stg94, glM_stg95, glM_stg96, glM_stg97, glM_stg98]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg100 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MA) ⟨(qq (0) (0)), (qq (-16/81) (0)), (qq (16/81) (0)), eoq (qq (0) (8/81)) (qq (-16/81) (0)) (qq (-32/81) (0)) (qq (0) (0)) (qq (0) (-16/81)) (qq (0) (0)) (qq (32/81) (0)) (qq (0) (-16/81)), eoq (qq (-16/81) (0)) (qq (0) (-8/81)) (qq (0) (-16/81)) (qq (0) (0)) (qq (32/81) (0)) (qq (0) (0)) (qq (0) (16/81)) (qq (32/81) (0)), eoq (qq (0) (-8/81)) (qq (0) (0)) (qq (32/81) (0)) (qq (0) (-16/81)) (qq (0) (16/81)) (qq (32/81) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (-128/243) (0)), (qq (128/243) (0)), (qq (0) (0)), eoq (qq (0) (64/243)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (64/243) (0)) (qq (0) (0)) (qq (0) (-128/243)) (qq (128/243) (0)) (qq (-128/243) (0)) (qq (0) (-128/243)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (-64/243)) (qq (-64/243) (0)) (qq (-128/243) (0)) (qq (0) (0)) (qq (0) (128/243)) (qq (0) (0)) (qq (128/243) (0)) (qq (0) (128/243))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg101 : Phi (eaOps Q2) (symQ2 MB) (symQ2 MA) (symQ2 MB) (symQ2 MA) (symQ2 MC) (symQ2 MC) (symQ2 MD) =
    (⟨(qq (-128/81) (0)), (qq (128/81) (0)), (qq (0) (0)), eoq (qq (0) (64/81)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (64/81) (0)) (qq (0) (0)) (qq (0) (-128/243)) (qq (640/243) (0)) (qq (128/81) (0)) (qq (0) (-128/243)) (qq (0) (0)) (qq (256/243) (0)), eoq (qq (0) (-64/81)) (qq (-64/81) (0)) (qq (-128/243) (0)) (qq (0) (128/243)) (qq (0) (256/243)) (qq (0) (0)) (qq (896/243) (0)) (qq (0) (128/81))⟩ : EA Q2) := by
  simp only [Phi]
  rw [glM_stg89, glM_stg90, glM_stg91, glM_stg99, glM_stg100]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_term3 : glennieTerm (eaOps Q2) (symQ2 MD) (symQ2 MB) (symQ2 MA) (symQ2 MB) (symQ2 MA) (symQ2 MC) (symQ2 MC) =
    (⟨(qq (1408/243) (0)), (qq (896/729) (0)), (qq (5120/729) (0)), eoq (qq (0) (-832/729)) (qq (-512/729) (0)) (qq (-2560/729) (0)) (qq (0) (-1024/729)) (qq (0) (-640/729)) (qq (-1664/729) (0)) (qq (-640/729) (0)) (qq (0) (256/729)), eoq (qq (-1088/729) (0)) (qq (0) (256/729)) (qq (0) (-640/729)) (qq (1664/729) (0)) (qq (-1792/729) (0)) (qq (0) (-1024/729)) (qq (0) (896/729)) (qq (512/729) (0)), eoq (qq (0) (1088/729)) (qq (64/729) (0)) (qq (-640/729) (0)) (qq (0) (256/729)) (qq (0) (896/729)) (qq (512/729) (0)) (qq (1792/729) (0)) (qq (0) (1024/729))⟩ : EA Q2) := by
  simp only [glennieTerm]
  rw [glM_dd, glM_stg88, glM_stg101]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg103 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MC) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg104 : Dop (eaOps Q2) (symQ2 MA) (symQ2 MA) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg105 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MC) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg106 : (eaOps Q2).mul (symQ2 MA) (symQ2 MA) =
    (⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg107 : (eaOps Q2).mul (symQ2 MB) (symQ2 MC) =
    (⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (-2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-4/9) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (2/9)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg108 : Upol (eaOps Q2) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ ⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (-2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-4/9) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (2/9)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (-2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-4/9) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (2/9)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg109 : Upol (eaOps Q2) (symQ2 MA) (symQ2 MC) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (-1/3) (0)), (qq (1/3) (0)), (qq (1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-2/3) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg110 : Upol (eaOps Q2) (symQ2 MA) (symQ2 MB) ⟨(qq (-1/3) (0)), (qq (1/3) (0)), (qq (1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-2/3) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (-2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg111 : Upol (eaOps Q2) (symQ2 MA) (symQ2 MB) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg112 : Upol (eaOps Q2) (symQ2 MA) (symQ2 MC) ⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-4/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg113 : Ubr (eaOps Q2) (symQ2 MA) (symQ2 MB) (symQ2 MA) (symQ2 MC) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (-4/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-8/9) (0)) (qq (0) (4/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (8/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  simp only [Ubr]
  rw [glM_stg106, glM_stg107, glM_stg108, glM_stg109, glM_stg110, glM_stg111, glM_stg112]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg114 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MC) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (-4/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-8/9) (0)) (qq (0) (4/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (8/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (128/81) (0)), (qq (-128/81) (0)), eoq (qq (0) (32/81)) (qq (32/81) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-32/81) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-128/81) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg115 : Phi (eaOps Q2) (symQ2 MB) (symQ2 MA) (symQ2 MB) (symQ2 MC) (symQ2 MA) (symQ2 MC) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (128/27) (0)), (qq (-128/27) (0)), eoq (qq (0) (32/27)) (qq (32/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-32/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-128/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  simp only [Phi]
  rw [glM_stg103, glM_stg104, glM_stg105, glM_stg113, glM_stg114]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg116 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MC) (symQ2 MD) =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (-8/27)) (qq (-16/27) (0)) (qq (8/27) (0)) (qq (0) (-8/27)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (8/27)) (qq (-16/27) (0)) (qq (0) (0)) (qq (0) (-16/27)) (qq (0) (0)) (qq (8/27) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (-8/27) (0)) (qq (0) (8/27)) (qq (0) (0)) (qq (-8/27) (0)) (qq (0) (0)) (qq (0) (-16/27))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg117 : Dop (eaOps Q2) (symQ2 MA) (symQ2 MA) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (-8/27)) (qq (-16/27) (0)) (qq (8/27) (0)) (qq (0) (-8/27)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (8/27)) (qq (-16/27) (0)) (qq (0) (0)) (qq (0) (-16/27)) (qq (0) (0)) (qq (8/27) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (-8/27) (0)) (qq (0) (8/27)) (qq (0) (0)) (qq (-8/27) (0)) (qq (0) (0)) (qq (0) (-16/27))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg118 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MC) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg119 : (eaOps Q2).mul (symQ2 MA) (symQ2 MA) =
    (⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg120 : (eaOps Q2).mul (symQ2 MB) (symQ2 MC) =
    (⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (-2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-4/9) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (2/9)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg121 : Upol (eaOps Q2) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ ⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (-2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-4/9) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (2/9)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ (symQ2 MD) =
    (⟨(qq (-1/27) (0)), (qq (1/27) (0)), (qq (-1/9) (0)), eoq (qq (0) (2/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (-2/27)) (qq (2/27) (0)) (qq (-4/27) (0)) (qq (0) (-2/27)), eoq (qq (4/27) (0)) (qq (0) (-2/27)) (qq (0) (-2/27)) (qq (-2/27) (0)) (qq (-4/27) (0)) (qq (0) (0)) (qq (0) (2/27)) (qq (0) (0)), eoq (qq (0) (-2/27)) (qq (2/27) (0)) (qq (-4/27) (0)) (qq (0) (-2/27)) (qq (0) (2/27)) (qq (0) (0)) (qq (-2/27) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg122 : Upol (eaOps Q2) (symQ2 MA) (symQ2 MC) (symQ2 MD) =
    (⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (-1/9) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-2/9) (0)) (qq (-2/9) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)), eoq (qq (0) (0)) (qq (2/9) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (-2/9) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg123 : Upol (eaOps Q2) (symQ2 MA) (symQ2 MB) ⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (-1/9) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-2/9) (0)) (qq (-2/9) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)), eoq (qq (0) (0)) (qq (2/9) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (-2/9) (0)) (qq (0) (0))⟩ =
    (⟨(qq (-1/27) (0)), (qq (1/27) (0)), (qq (-1/9) (0)), eoq (qq (0) (2/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-2/27) (0)) (qq (-2/27) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (-2/27)) (qq (0) (2/27)) (qq (-2/27) (0)) (qq (0) (0)) (qq (0) (-2/27)) (qq (0) (2/27)) (qq (-2/27) (0)), eoq (qq (0) (0)) (qq (2/27) (0)) (qq (-2/27) (0)) (qq (0) (-2/27)) (qq (0) (0)) (qq (2/27) (0)) (qq (-2/27) (0)) (qq (0) (-2/27))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg124 : Upol (eaOps Q2) (symQ2 MA) (symQ2 MB) (symQ2 MD) =
    (⟨(qq (1/9) (0)), (qq (1/9) (0)), (qq (-1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (0) (0)) (qq (0) (2/9)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg125 : Upol (eaOps Q2) (symQ2 MA) (symQ2 MC) ⟨(qq (1/9) (0)), (qq (1/9) (0)), (qq (-1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (0) (0)) (qq (0) (2/9)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0))⟩ =
    (⟨(qq (-1/27) (0)), (qq (1/27) (0)), (qq (-1/9) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (2/27)) (qq (2/27) (0)) (qq (-2/27) (0)) (qq (0) (-2/27)), eoq (qq (4/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/27) (0)) (qq (0) (0)) (qq (0) (2/27)) (qq (0) (0)) (qq (2/27) (0)), eoq (qq (0) (0)) (qq (2/27) (0)) (qq (-2/27) (0)) (qq (0) (0)) (qq (0) (2/27)) (qq (-2/27) (0)) (qq (-2/27) (0)) (qq (0) (2/27))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg126 : Ubr (eaOps Q2) (symQ2 MA) (symQ2 MB) (symQ2 MA) (symQ2 MC) (symQ2 MD) =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (4/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (-4/9)) (qq (8/27) (0)) (qq (-8/27) (0)) (qq (0) (-4/27)), eoq (qq (8/27) (0)) (qq (0) (-4/27)) (qq (0) (-4/9)) (qq (-8/27) (0)) (qq (-16/27) (0)) (qq (0) (0)) (qq (0) (4/27)) (qq (0) (0)), eoq (qq (0) (-8/27)) (qq (0) (0)) (qq (-8/27) (0)) (qq (0) (-4/27)) (qq (0) (4/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  simp only [Ubr]
  rw [glM_stg119, glM_stg120, glM_stg121, glM_stg122, glM_stg123, glM_stg124, glM_stg125]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg127 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MC) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (4/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (-4/9)) (qq (8/27) (0)) (qq (-8/27) (0)) (qq (0) (-4/27)), eoq (qq (8/27) (0)) (qq (0) (-4/27)) (qq (0) (-4/9)) (qq (-8/27) (0)) (qq (-16/27) (0)) (qq (0) (0)) (qq (0) (4/27)) (qq (0) (0)), eoq (qq (0) (-8/27)) (qq (0) (0)) (qq (-8/27) (0)) (qq (0) (-4/27)) (qq (0) (4/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (-128/243) (0)), (qq (128/243) (0)), eoq (qq (0) (-32/243)) (qq (-32/243) (0)) (qq (-32/243) (0)) (qq (0) (-80/243)) (qq (0) (-80/243)) (qq (-160/243) (0)) (qq (32/243) (0)) (qq (0) (-32/243)), eoq (qq (32/243) (0)) (qq (0) (0)) (qq (0) (80/243)) (qq (-224/243) (0)) (qq (32/243) (0)) (qq (0) (-80/81)) (qq (0) (0)) (qq (32/243) (0)), eoq (qq (0) (0)) (qq (128/243) (0)) (qq (-32/243) (0)) (qq (0) (16/243)) (qq (0) (-16/243)) (qq (0) (0)) (qq (0) (0)) (qq (0) (-64/243))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg128 : Phi (eaOps Q2) (symQ2 MB) (symQ2 MA) (symQ2 MB) (symQ2 MC) (symQ2 MA) (symQ2 MC) (symQ2 MD) =
    (⟨(qq (0) (0)), (qq (-128/81) (0)), (qq (128/81) (0)), eoq (qq (0) (-32/81)) (qq (-32/81) (0)) (qq (-32/81) (0)) (qq (0) (-80/81)) (qq (0) (-80/81)) (qq (-160/81) (0)) (qq (32/81) (0)) (qq (0) (-32/81)), eoq (qq (32/81) (0)) (qq (0) (0)) (qq (0) (80/81)) (qq (-224/81) (0)) (qq (32/81) (0)) (qq (0) (-80/27)) (qq (0) (0)) (qq (32/81) (0)), eoq (qq (0) (0)) (qq (128/81) (0)) (qq (-32/81) (0)) (qq (0) (16/81)) (qq (0) (-16/81)) (qq (0) (0)) (qq (0) (0)) (qq (0) (-64/81))⟩ : EA Q2) := by
  simp only [Phi]
  rw [glM_stg116, glM_stg117, glM_stg118, glM_stg126, glM_stg127]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_term4 : glennieTerm (eaOps Q2) (symQ2 MD) (symQ2 MB) (symQ2 MA) (symQ2 MB) (symQ2 MC) (symQ2 MA) (symQ2 MC) =
    (⟨(qq (0) (0)), (qq (256/81) (0)), (qq (-256/81) (0)), eoq (qq (0) (64/81)) (qq (160/243) (0)) (qq (-128/81) (0)) (qq (0) (-512/243)) (qq (0) (0)) (qq (128/81) (0)) (qq (-64/243) (0)) (qq (0) (-32/243)), eoq (qq (-224/243) (0)) (qq (0) (-32/243)) (qq (0) (0)) (qq (-128/81) (0)) (qq (128/81) (0)) (qq (0) (-512/243)) (qq (0) (-32/81)) (qq (128/243) (0)), eoq (qq (0) (0)) (qq (-256/81) (0)) (qq (-64/243) (0)) (qq (0) (-32/243)) (qq (0) (-32/81)) (qq (128/243) (0)) (qq (0) (0)) (qq (0) (512/243))⟩ : EA Q2) := by
  simp only [glennieTerm]
  rw [glM_dd, glM_stg115, glM_stg128]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg130 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MA) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg131 : Dop (eaOps Q2) (symQ2 MA) (symQ2 MC) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg132 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MC) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg133 : (eaOps Q2).mul (symQ2 MA) (symQ2 MC) =
    (⟨(qq (-1/3) (0)), (qq (1/3) (0)), (qq (1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-2/3) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg134 : (eaOps Q2).mul (symQ2 MB) (symQ2 MA) =
    (⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg135 : Upol (eaOps Q2) ⟨(qq (-1/3) (0)), (qq (1/3) (0)), (qq (1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-2/3) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ ⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg136 : Upol (eaOps Q2) (symQ2 MC) (symQ2 MA) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (-1/3) (0)), (qq (1/3) (0)), (qq (1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-2/3) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg137 : Upol (eaOps Q2) (symQ2 MA) (symQ2 MB) ⟨(qq (-1/3) (0)), (qq (1/3) (0)), (qq (1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-2/3) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (-2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg138 : Upol (eaOps Q2) (symQ2 MA) (symQ2 MB) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg139 : Upol (eaOps Q2) (symQ2 MC) (symQ2 MA) ⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-4/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg140 : Ubr (eaOps Q2) (symQ2 MA) (symQ2 MB) (symQ2 MC) (symQ2 MA) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (4/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (8/9) (0)) (qq (0) (-4/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  simp only [Ubr]
  rw [glM_stg133, glM_stg134, glM_stg135, glM_stg136, glM_stg137, glM_stg138, glM_stg139]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg141 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MC) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (4/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (8/9) (0)) (qq (0) (-4/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (32/81) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (32/81) (0)) (qq (0) (32/81)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg142 : Phi (eaOps Q2) (symQ2 MB) (symQ2 MA) (symQ2 MB) (symQ2 MC) (symQ2 MC) (symQ2 MA) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (32/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (32/27) (0)) (qq (0) (32/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  simp only [Phi]
  rw [glM_stg130, glM_stg131, glM_stg132, glM_stg140, glM_stg141]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg143 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MA) (symQ2 MD) =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (8/9)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (-8/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg144 : Dop (eaOps Q2) (symQ2 MA) (symQ2 MC) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (8/9)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (-8/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (32/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (32/27)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (32/27))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg145 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MC) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (32/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (32/27)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (32/27))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (-256/243)) (qq (256/243) (0)) (qq (-256/243) (0)) (qq (0) (-128/243)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-256/81) (0)) (qq (0) (256/243)) (qq (0) (128/243)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-256/243) (0)) (qq (-512/243) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg146 : (eaOps Q2).mul (symQ2 MA) (symQ2 MC) =
    (⟨(qq (-1/3) (0)), (qq (1/3) (0)), (qq (1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-2/3) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg147 : (eaOps Q2).mul (symQ2 MB) (symQ2 MA) =
    (⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg148 : Upol (eaOps Q2) ⟨(qq (-1/3) (0)), (qq (1/3) (0)), (qq (1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-2/3) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ ⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ (symQ2 MD) =
    (⟨(qq (-1/27) (0)), (qq (1/27) (0)), (qq (-1/9) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-2/27) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/27) (0)) (qq (4/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (2/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-2/27) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg149 : Upol (eaOps Q2) (symQ2 MC) (symQ2 MA) (symQ2 MD) =
    (⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (-1/9) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-2/9) (0)) (qq (-2/9) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)), eoq (qq (0) (0)) (qq (2/9) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (-2/9) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg150 : Upol (eaOps Q2) (symQ2 MA) (symQ2 MB) ⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (-1/9) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-2/9) (0)) (qq (-2/9) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)), eoq (qq (0) (0)) (qq (2/9) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (-2/9) (0)) (qq (0) (0))⟩ =
    (⟨(qq (-1/27) (0)), (qq (1/27) (0)), (qq (-1/9) (0)), eoq (qq (0) (2/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-2/27) (0)) (qq (-2/27) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (-2/27)) (qq (0) (2/27)) (qq (-2/27) (0)) (qq (0) (0)) (qq (0) (-2/27)) (qq (0) (2/27)) (qq (-2/27) (0)), eoq (qq (0) (0)) (qq (2/27) (0)) (qq (-2/27) (0)) (qq (0) (-2/27)) (qq (0) (0)) (qq (2/27) (0)) (qq (-2/27) (0)) (qq (0) (-2/27))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg151 : Upol (eaOps Q2) (symQ2 MA) (symQ2 MB) (symQ2 MD) =
    (⟨(qq (1/9) (0)), (qq (1/9) (0)), (qq (-1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (0) (0)) (qq (0) (2/9)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg152 : Upol (eaOps Q2) (symQ2 MC) (symQ2 MA) ⟨(qq (1/9) (0)), (qq (1/9) (0)), (qq (-1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (0) (0)) (qq (0) (2/9)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0))⟩ =
    (⟨(qq (-1/27) (0)), (qq (1/27) (0)), (qq (-1/9) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (2/27)) (qq (2/27) (0)) (qq (-2/27) (0)) (qq (0) (-2/27)), eoq (qq (4/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/27) (0)) (qq (0) (0)) (qq (0) (2/27)) (qq (0) (0)) (qq (2/27) (0)), eoq (qq (0) (0)) (qq (2/27) (0)) (qq (-2/27) (0)) (qq (0) (0)) (qq (0) (2/27)) (qq (-2/27) (0)) (qq (-2/27) (0)) (qq (0) (2/27))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg153 : Ubr (eaOps Q2) (symQ2 MA) (symQ2 MB) (symQ2 MC) (symQ2 MA) (symQ2 MD) =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (-4/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (-4/27)) (qq (-8/27) (0)) (qq (8/27) (0)) (qq (0) (4/27)), eoq (qq (-8/27) (0)) (qq (0) (4/27)) (qq (0) (-4/27)) (qq (8/27) (0)) (qq (16/27) (0)) (qq (0) (0)) (qq (0) (-4/27)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (8/27) (0)) (qq (0) (4/27)) (qq (0) (-4/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  simp only [Ubr]
  rw [glM_stg146, glM_stg147, glM_stg148, glM_stg149, glM_stg150, glM_stg151, glM_stg152]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg154 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MC) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (-4/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (-4/27)) (qq (-8/27) (0)) (qq (8/27) (0)) (qq (0) (4/27)), eoq (qq (-8/27) (0)) (qq (0) (4/27)) (qq (0) (-4/27)) (qq (8/27) (0)) (qq (16/27) (0)) (qq (0) (0)) (qq (0) (-4/27)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (8/27) (0)) (qq (0) (4/27)) (qq (0) (-4/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (-32/243) (0)) (qq (-32/81) (0)) (qq (0) (-16/81)) (qq (0) (80/243)) (qq (160/243) (0)) (qq (-32/243) (0)) (qq (0) (32/243)), eoq (qq (-32/243) (0)) (qq (0) (-32/243)) (qq (0) (-80/243)) (qq (-32/243) (0)) (qq (32/81) (0)) (qq (0) (112/243)) (qq (0) (0)) (qq (-32/243) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (32/243) (0)) (qq (0) (-80/243)) (qq (0) (-16/81)) (qq (128/243) (0)) (qq (0) (0)) (qq (0) (64/243))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg155 : Phi (eaOps Q2) (symQ2 MB) (symQ2 MA) (symQ2 MB) (symQ2 MC) (symQ2 MC) (symQ2 MA) (symQ2 MD) =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (-32/81) (0)) (qq (-32/27) (0)) (qq (0) (-16/27)) (qq (0) (-16/243)) (qq (736/243) (0)) (qq (-352/243) (0)) (qq (0) (-32/243)), eoq (qq (-32/81) (0)) (qq (0) (-32/81)) (qq (0) (-80/81)) (qq (-32/81) (0)) (qq (-160/81) (0)) (qq (0) (592/243)) (qq (0) (128/243)) (qq (-32/81) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (32/81) (0)) (qq (0) (-80/81)) (qq (0) (-16/27)) (qq (128/243) (0)) (qq (-512/243) (0)) (qq (0) (64/81))⟩ : EA Q2) := by
  simp only [Phi]
  rw [glM_stg143, glM_stg144, glM_stg145, glM_stg153, glM_stg154]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_term5 : glennieTerm (eaOps Q2) (symQ2 MD) (symQ2 MB) (symQ2 MA) (symQ2 MB) (symQ2 MC) (symQ2 MC) (symQ2 MA) =
    (⟨(qq (-1024/243) (0)), (qq (-3200/729) (0)), (qq (-3968/729) (0)), eoq (qq (0) (-32/729)) (qq (608/729) (0)) (qq (1408/729) (0)) (qq (0) (512/729)) (qq (0) (-512/729)) (qq (1664/729) (0)) (qq (-320/729) (0)) (qq (0) (-736/729)), eoq (qq (1184/729) (0)) (qq (0) (128/729)) (qq (0) (-512/729)) (qq (-1664/729) (0)) (qq (640/729) (0)) (qq (0) (512/729)) (qq (0) (-32/729)) (qq (256/729) (0)), eoq (qq (0) (-512/729)) (qq (1664/729) (0)) (qq (-320/729) (0)) (qq (0) (-736/729)) (qq (0) (-32/729)) (qq (256/729) (0)) (qq (512/729) (0)) (qq (0) (-512/729))⟩ : EA Q2) := by
  simp only [glennieTerm]
  rw [glM_dd, glM_stg142, glM_stg155]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg157 : Dop (eaOps Q2) (symQ2 MA) (symQ2 MC) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg158 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MC) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg159 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MA) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg160 : (eaOps Q2).mul (symQ2 MB) (symQ2 MC) =
    (⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (-2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-4/9) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (2/9)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg161 : (eaOps Q2).mul (symQ2 MA) (symQ2 MC) =
    (⟨(qq (-1/3) (0)), (qq (1/3) (0)), (qq (1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-2/3) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg162 : Upol (eaOps Q2) ⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (-2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-4/9) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (2/9)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ ⟨(qq (-1/3) (0)), (qq (1/3) (0)), (qq (1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-2/3) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (-1/27) (0)), (qq (1/9) (0)), (qq (7/27) (0)), eoq (qq (0) (-2/27)) (qq (-4/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (2/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (2/27)) (qq (-4/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg163 : Upol (eaOps Q2) (symQ2 MC) (symQ2 MC) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg164 : Upol (eaOps Q2) (symQ2 MB) (symQ2 MA) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg165 : Upol (eaOps Q2) (symQ2 MC) (symQ2 MC) ⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (7/27) (0)), (qq (7/27) (0)), (qq (-5/27) (0)), eoq (qq (0) (0)) (qq (-16/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-8/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-8/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg166 : Ubr (eaOps Q2) (symQ2 MB) (symQ2 MA) (symQ2 MC) (symQ2 MC) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (16/27) (0)), (qq (-16/27) (0)), eoq (qq (0) (-8/27)) (qq (16/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (16/27) (0)) (qq (0) (8/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (8/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  simp only [Ubr]
  rw [glM_stg160, glM_stg161, glM_stg162, glM_stg163, glM_stg164, glM_stg165]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg167 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MA) ⟨(qq (0) (0)), (qq (16/27) (0)), (qq (-16/27) (0)), eoq (qq (0) (-8/27)) (qq (16/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (16/27) (0)) (qq (0) (8/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (8/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (128/81) (0)), (qq (-128/81) (0)), (qq (0) (0)), eoq (qq (0) (-64/81)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-64/81) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (64/81)) (qq (64/81) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg168 : Phi (eaOps Q2) (symQ2 MB) (symQ2 MB) (symQ2 MA) (symQ2 MA) (symQ2 MC) (symQ2 MC) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (128/27) (0)), (qq (-128/27) (0)), (qq (0) (0)), eoq (qq (0) (-64/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-64/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (64/27)) (qq (64/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  simp only [Phi]
  rw [glM_stg157, glM_stg158, glM_stg159, glM_stg166, glM_stg167]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg169 : Dop (eaOps Q2) (symQ2 MA) (symQ2 MC) (symQ2 MD) =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (8/9) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-8/9) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (-8/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (8/9) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg170 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MC) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (8/9) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-8/9) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (-8/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (8/9) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (32/81) (0)) (qq (0) (32/81)) (qq (0) (32/81)) (qq (-32/81) (0)) (qq (-64/81) (0)) (qq (0) (-32/81)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-32/81) (0)) (qq (-32/81) (0)) (qq (0) (0)) (qq (0) (-32/27)) (qq (-64/81) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (64/81)) (qq (0) (64/81)) (qq (0) (0)) (qq (0) (0)) (qq (0) (32/81))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg171 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MA) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (32/81) (0)) (qq (0) (32/81)) (qq (0) (32/81)) (qq (-32/81) (0)) (qq (-64/81) (0)) (qq (0) (-32/81)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-32/81) (0)) (qq (-32/81) (0)) (qq (0) (0)) (qq (0) (-32/27)) (qq (-64/81) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (64/81)) (qq (0) (64/81)) (qq (0) (0)) (qq (0) (0)) (qq (0) (32/81))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-512/243) (0)) (qq (-512/243) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-256/243) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (-128/243)) (qq (0) (-128/243)) (qq (0) (0)) (qq (-256/81) (0)) (qq (0) (-256/243))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg172 : (eaOps Q2).mul (symQ2 MB) (symQ2 MC) =
    (⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (-2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-4/9) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (2/9)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg173 : (eaOps Q2).mul (symQ2 MA) (symQ2 MC) =
    (⟨(qq (-1/3) (0)), (qq (1/3) (0)), (qq (1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-2/3) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg174 : Upol (eaOps Q2) ⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (-2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-4/9) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (2/9)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ ⟨(qq (-1/3) (0)), (qq (1/3) (0)), (qq (1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-2/3) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ (symQ2 MD) =
    (⟨(qq (1/81) (0)), (qq (-1/27) (0)), (qq (-7/81) (0)), eoq (qq (0) (2/81)) (qq (4/81) (0)) (qq (-2/81) (0)) (qq (0) (0)) (qq (0) (2/81)) (qq (0) (0)) (qq (-4/81) (0)) (qq (0) (2/81)), eoq (qq (0) (0)) (qq (0) (-2/81)) (qq (0) (2/81)) (qq (0) (0)) (qq (2/81) (0)) (qq (0) (0)) (qq (0) (-2/81)) (qq (8/81) (0)), eoq (qq (0) (-2/81)) (qq (4/81) (0)) (qq (-4/81) (0)) (qq (0) (2/81)) (qq (0) (-2/81)) (qq (8/81) (0)) (qq (2/27) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg175 : Upol (eaOps Q2) (symQ2 MC) (symQ2 MC) (symQ2 MD) =
    (⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (-1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (4/9) (0)) (qq (-4/9) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-4/9) (0)) (qq (2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (4/9) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (-4/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (4/9) (0)) (qq (2/9) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg176 : Upol (eaOps Q2) (symQ2 MB) (symQ2 MA) ⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (-1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (4/9) (0)) (qq (-4/9) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-4/9) (0)) (qq (2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (4/9) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (-4/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (4/9) (0)) (qq (2/9) (0)) (qq (0) (0))⟩ =
    (⟨(qq (1/9) (0)), (qq (1/9) (0)), (qq (-1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (2/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (4/27) (0)) (qq (-4/27) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (4/27)) (qq (4/27) (0)) (qq (-2/27) (0)) (qq (0) (-4/27)) (qq (0) (-2/27)) (qq (-4/27) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (-4/27) (0)) (qq (0) (4/27)) (qq (0) (-2/27)) (qq (4/27) (0)) (qq (2/27) (0)) (qq (0) (-4/27))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg177 : Upol (eaOps Q2) (symQ2 MB) (symQ2 MA) (symQ2 MD) =
    (⟨(qq (1/9) (0)), (qq (1/9) (0)), (qq (-1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (0) (0)) (qq (0) (2/9)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg178 : Upol (eaOps Q2) (symQ2 MC) (symQ2 MC) ⟨(qq (1/9) (0)), (qq (1/9) (0)), (qq (-1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (0) (0)) (qq (0) (2/9)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0))⟩ =
    (⟨(qq (-7/81) (0)), (qq (-7/81) (0)), (qq (5/81) (0)), eoq (qq (0) (0)) (qq (16/81) (0)) (qq (2/27) (0)) (qq (0) (0)) (qq (0) (4/27)) (qq (-4/27) (0)) (qq (-4/27) (0)) (qq (0) (4/27)), eoq (qq (8/81) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-4/27) (0)) (qq (-2/27) (0)) (qq (0) (4/27)) (qq (0) (-2/27)) (qq (4/27) (0)), eoq (qq (0) (0)) (qq (8/81) (0)) (qq (-4/27) (0)) (qq (0) (0)) (qq (0) (-2/27)) (qq (-4/27) (0)) (qq (2/27) (0)) (qq (0) (4/27))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg179 : Ubr (eaOps Q2) (symQ2 MB) (symQ2 MA) (symQ2 MC) (symQ2 MC) (symQ2 MD) =
    (⟨(qq (0) (0)), (qq (-16/81) (0)), (qq (16/81) (0)), eoq (qq (0) (8/81)) (qq (-16/81) (0)) (qq (-32/81) (0)) (qq (0) (0)) (qq (0) (-16/81)) (qq (0) (0)) (qq (32/81) (0)) (qq (0) (-16/81)), eoq (qq (-16/81) (0)) (qq (0) (-8/81)) (qq (0) (-16/81)) (qq (0) (0)) (qq (32/81) (0)) (qq (0) (0)) (qq (0) (16/81)) (qq (32/81) (0)), eoq (qq (0) (-8/81)) (qq (0) (0)) (qq (32/81) (0)) (qq (0) (-16/81)) (qq (0) (16/81)) (qq (32/81) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  simp only [Ubr]
  rw [glM_stg172, glM_stg173, glM_stg174, glM_stg175, glM_stg176, glM_stg177, glM_stg178]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg180 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MA) ⟨(qq (0) (0)), (qq (-16/81) (0)), (qq (16/81) (0)), eoq (qq (0) (8/81)) (qq (-16/81) (0)) (qq (-32/81) (0)) (qq (0) (0)) (qq (0) (-16/81)) (qq (0) (0)) (qq (32/81) (0)) (qq (0) (-16/81)), eoq (qq (-16/81) (0)) (qq (0) (-8/81)) (qq (0) (-16/81)) (qq (0) (0)) (qq (32/81) (0)) (qq (0) (0)) (qq (0) (16/81)) (qq (32/81) (0)), eoq (qq (0) (-8/81)) (qq (0) (0)) (qq (32/81) (0)) (qq (0) (-16/81)) (qq (0) (16/81)) (qq (32/81) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (-128/243) (0)), (qq (128/243) (0)), (qq (0) (0)), eoq (qq (0) (64/243)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (64/243) (0)) (qq (0) (0)) (qq (0) (-128/243)) (qq (128/243) (0)) (qq (-128/243) (0)) (qq (0) (-128/243)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (-64/243)) (qq (-64/243) (0)) (qq (-128/243) (0)) (qq (0) (0)) (qq (0) (128/243)) (qq (0) (0)) (qq (128/243) (0)) (qq (0) (128/243))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg181 : Phi (eaOps Q2) (symQ2 MB) (symQ2 MB) (symQ2 MA) (symQ2 MA) (symQ2 MC) (symQ2 MC) (symQ2 MD) =
    (⟨(qq (-128/81) (0)), (qq (128/81) (0)), (qq (0) (0)), eoq (qq (0) (64/81)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (64/81) (0)) (qq (0) (0)) (qq (0) (-128/81)) (qq (-128/243) (0)) (qq (-896/243) (0)) (qq (0) (-128/81)) (qq (0) (0)) (qq (-256/243) (0)), eoq (qq (0) (-64/81)) (qq (-64/81) (0)) (qq (-128/81) (0)) (qq (0) (-128/243)) (qq (0) (256/243)) (qq (0) (0)) (qq (-128/81) (0)) (qq (0) (128/243))⟩ : EA Q2) := by
  simp only [Phi]
  rw [glM_stg169, glM_stg170, glM_stg171, glM_stg179, glM_stg180]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_term6 : glennieTerm (eaOps Q2) (symQ2 MD) (symQ2 MB) (symQ2 MB) (symQ2 MA) (symQ2 MA) (symQ2 MC) (symQ2 MC) =
    (⟨(qq (-896/729) (0)), (qq (-1408/243) (0)), (qq (-5120/729) (0)), eoq (qq (0) (-832/729)) (qq (512/729) (0)) (qq (2560/729) (0)) (qq (0) (-1024/729)) (qq (0) (-128/81)) (qq (-128/729) (0)) (qq (-128/81) (0)) (qq (0) (-256/729)), eoq (qq (-64/81) (0)) (qq (0) (-256/729)) (qq (0) (-128/81)) (qq (128/729) (0)) (qq (-1792/729) (0)) (qq (0) (-1024/729)) (qq (0) (896/729)) (qq (-512/729) (0)), eoq (qq (0) (64/81)) (qq (1600/729) (0)) (qq (-128/81) (0)) (qq (0) (-256/729)) (qq (0) (896/729)) (qq (-512/729) (0)) (qq (1792/729) (0)) (qq (0) (1024/729))⟩ : EA Q2) := by
  simp only [glennieTerm]
  rw [glM_dd, glM_stg168, glM_stg181]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg183 : Dop (eaOps Q2) (symQ2 MA) (symQ2 MC) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg184 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MA) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg185 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MC) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg186 : (eaOps Q2).mul (symQ2 MB) (symQ2 MA) =
    (⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg187 : (eaOps Q2).mul (symQ2 MA) (symQ2 MC) =
    (⟨(qq (-1/3) (0)), (qq (1/3) (0)), (qq (1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-2/3) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg188 : Upol (eaOps Q2) ⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ ⟨(qq (-1/3) (0)), (qq (1/3) (0)), (qq (1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-2/3) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg189 : Upol (eaOps Q2) (symQ2 MA) (symQ2 MC) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (-1/3) (0)), (qq (1/3) (0)), (qq (1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-2/3) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg190 : Upol (eaOps Q2) (symQ2 MB) (symQ2 MA) ⟨(qq (-1/3) (0)), (qq (1/3) (0)), (qq (1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-2/3) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (-2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg191 : Upol (eaOps Q2) (symQ2 MB) (symQ2 MA) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg192 : Upol (eaOps Q2) (symQ2 MA) (symQ2 MC) ⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-4/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg193 : Ubr (eaOps Q2) (symQ2 MB) (symQ2 MA) (symQ2 MA) (symQ2 MC) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (4/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (8/9) (0)) (qq (0) (-4/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  simp only [Ubr]
  rw [glM_stg186, glM_stg187, glM_stg188, glM_stg189, glM_stg190, glM_stg191, glM_stg192]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg194 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MC) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (4/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (8/9) (0)) (qq (0) (-4/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (32/81) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (32/81) (0)) (qq (0) (32/81)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg195 : Phi (eaOps Q2) (symQ2 MB) (symQ2 MB) (symQ2 MA) (symQ2 MC) (symQ2 MA) (symQ2 MC) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (32/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (32/27) (0)) (qq (0) (32/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  simp only [Phi]
  rw [glM_stg183, glM_stg184, glM_stg185, glM_stg193, glM_stg194]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg196 : Dop (eaOps Q2) (symQ2 MA) (symQ2 MC) (symQ2 MD) =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (8/9) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-8/9) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (-8/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (8/9) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg197 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MA) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (8/9) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-8/9) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (-8/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (8/9) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (32/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (-32/27)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (-32/27))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg198 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MC) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (32/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (-32/27)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (-32/27))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (256/243) (0)) (qq (0) (256/243)) (qq (0) (256/243)) (qq (-256/243) (0)) (qq (256/243) (0)) (qq (0) (128/243)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (512/243) (0)) (qq (512/243) (0)) (qq (0) (0)) (qq (0) (-128/243)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (128/243)) (qq (0) (128/243)) (qq (0) (0)) (qq (512/243) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg199 : (eaOps Q2).mul (symQ2 MB) (symQ2 MA) =
    (⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg200 : (eaOps Q2).mul (symQ2 MA) (symQ2 MC) =
    (⟨(qq (-1/3) (0)), (qq (1/3) (0)), (qq (1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-2/3) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg201 : Upol (eaOps Q2) ⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ ⟨(qq (-1/3) (0)), (qq (1/3) (0)), (qq (1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-2/3) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ (symQ2 MD) =
    (⟨(qq (-1/27) (0)), (qq (1/27) (0)), (qq (-1/9) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-2/27) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/27) (0)) (qq (4/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (2/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-2/27) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg202 : Upol (eaOps Q2) (symQ2 MA) (symQ2 MC) (symQ2 MD) =
    (⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (-1/9) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-2/9) (0)) (qq (-2/9) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)), eoq (qq (0) (0)) (qq (2/9) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (-2/9) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg203 : Upol (eaOps Q2) (symQ2 MB) (symQ2 MA) ⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (-1/9) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-2/9) (0)) (qq (-2/9) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)), eoq (qq (0) (0)) (qq (2/9) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (-2/9) (0)) (qq (0) (0))⟩ =
    (⟨(qq (-1/27) (0)), (qq (1/27) (0)), (qq (-1/9) (0)), eoq (qq (0) (2/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-2/27) (0)) (qq (-2/27) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (-2/27)) (qq (0) (2/27)) (qq (-2/27) (0)) (qq (0) (0)) (qq (0) (-2/27)) (qq (0) (2/27)) (qq (-2/27) (0)), eoq (qq (0) (0)) (qq (2/27) (0)) (qq (-2/27) (0)) (qq (0) (-2/27)) (qq (0) (0)) (qq (2/27) (0)) (qq (-2/27) (0)) (qq (0) (-2/27))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg204 : Upol (eaOps Q2) (symQ2 MB) (symQ2 MA) (symQ2 MD) =
    (⟨(qq (1/9) (0)), (qq (1/9) (0)), (qq (-1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (0) (0)) (qq (0) (2/9)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg205 : Upol (eaOps Q2) (symQ2 MA) (symQ2 MC) ⟨(qq (1/9) (0)), (qq (1/9) (0)), (qq (-1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (0) (0)) (qq (0) (2/9)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0))⟩ =
    (⟨(qq (-1/27) (0)), (qq (1/27) (0)), (qq (-1/9) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (2/27)) (qq (2/27) (0)) (qq (-2/27) (0)) (qq (0) (-2/27)), eoq (qq (4/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/27) (0)) (qq (0) (0)) (qq (0) (2/27)) (qq (0) (0)) (qq (2/27) (0)), eoq (qq (0) (0)) (qq (2/27) (0)) (qq (-2/27) (0)) (qq (0) (0)) (qq (0) (2/27)) (qq (-2/27) (0)) (qq (-2/27) (0)) (qq (0) (2/27))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg206 : Ubr (eaOps Q2) (symQ2 MB) (symQ2 MA) (symQ2 MA) (symQ2 MC) (symQ2 MD) =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (-4/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (-4/27)) (qq (-8/27) (0)) (qq (8/27) (0)) (qq (0) (4/27)), eoq (qq (-8/27) (0)) (qq (0) (4/27)) (qq (0) (-4/27)) (qq (8/27) (0)) (qq (16/27) (0)) (qq (0) (0)) (qq (0) (-4/27)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (8/27) (0)) (qq (0) (4/27)) (qq (0) (-4/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  simp only [Ubr]
  rw [glM_stg199, glM_stg200, glM_stg201, glM_stg202, glM_stg203, glM_stg204, glM_stg205]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg207 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MC) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (-4/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (-4/27)) (qq (-8/27) (0)) (qq (8/27) (0)) (qq (0) (4/27)), eoq (qq (-8/27) (0)) (qq (0) (4/27)) (qq (0) (-4/27)) (qq (8/27) (0)) (qq (16/27) (0)) (qq (0) (0)) (qq (0) (-4/27)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (8/27) (0)) (qq (0) (4/27)) (qq (0) (-4/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (-32/243) (0)) (qq (-32/81) (0)) (qq (0) (-16/81)) (qq (0) (80/243)) (qq (160/243) (0)) (qq (-32/243) (0)) (qq (0) (32/243)), eoq (qq (-32/243) (0)) (qq (0) (-32/243)) (qq (0) (-80/243)) (qq (-32/243) (0)) (qq (32/81) (0)) (qq (0) (112/243)) (qq (0) (0)) (qq (-32/243) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (32/243) (0)) (qq (0) (-80/243)) (qq (0) (-16/81)) (qq (128/243) (0)) (qq (0) (0)) (qq (0) (64/243))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg208 : Phi (eaOps Q2) (symQ2 MB) (symQ2 MB) (symQ2 MA) (symQ2 MC) (symQ2 MA) (symQ2 MC) (symQ2 MD) =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (-32/81) (0)) (qq (-32/243) (0)) (qq (0) (112/243)) (qq (0) (496/243)) (qq (224/243) (0)) (qq (160/243) (0)) (qq (0) (224/243)), eoq (qq (-32/81) (0)) (qq (0) (-32/81)) (qq (0) (-80/81)) (qq (416/243) (0)) (qq (800/243) (0)) (qq (0) (112/81)) (qq (0) (-128/243)) (qq (-32/81) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (32/81) (0)) (qq (0) (-112/243)) (qq (0) (-16/243)) (qq (128/81) (0)) (qq (512/243) (0)) (qq (0) (64/81))⟩ : EA Q2) := by
  simp only [Phi]
  rw [glM_stg196, glM_stg197, glM_stg198, glM_stg206, glM_stg207]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_term7 : glennieTerm (eaOps Q2) (symQ2 MD) (symQ2 MB) (symQ2 MB) (symQ2 MA) (symQ2 MC) (symQ2 MA) (symQ2 MC) =
    (⟨(qq (1024/243) (0)), (qq (640/243) (0)), (qq (5248/729) (0)), eoq (qq (0) (-32/81)) (qq (32/243) (0)) (qq (-896/243) (0)) (qq (0) (512/729)) (qq (0) (512/729)) (qq (-128/243) (0)) (qq (704/729) (0)) (qq (0) (32/729)), eoq (qq (160/729) (0)) (qq (0) (896/729)) (qq (0) (512/729)) (qq (128/243) (0)) (qq (640/729) (0)) (qq (0) (512/729)) (qq (0) (-32/81)) (qq (256/243) (0)), eoq (qq (0) (512/729)) (qq (-128/243) (0)) (qq (704/729) (0)) (qq (0) (32/729)) (qq (0) (-32/81)) (qq (256/243) (0)) (qq (-512/729) (0)) (qq (0) (-512/729))⟩ : EA Q2) := by
  simp only [glennieTerm]
  rw [glM_dd, glM_stg195, glM_stg208]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg210 : Dop (eaOps Q2) (symQ2 MA) (symQ2 MA) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg211 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MC) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg212 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MC) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg213 : (eaOps Q2).mul (symQ2 MB) (symQ2 MC) =
    (⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (-2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-4/9) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (2/9)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg214 : (eaOps Q2).mul (symQ2 MA) (symQ2 MA) =
    (⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg215 : Upol (eaOps Q2) ⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (-2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-4/9) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (2/9)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (-2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-4/9) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (2/9)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg216 : Upol (eaOps Q2) (symQ2 MC) (symQ2 MA) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (-1/3) (0)), (qq (1/3) (0)), (qq (1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-2/3) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg217 : Upol (eaOps Q2) (symQ2 MB) (symQ2 MA) ⟨(qq (-1/3) (0)), (qq (1/3) (0)), (qq (1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-2/3) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (-2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg218 : Upol (eaOps Q2) (symQ2 MB) (symQ2 MA) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg219 : Upol (eaOps Q2) (symQ2 MC) (symQ2 MA) ⟨(qq (-1/3) (0)), (qq (-1/3) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-4/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg220 : Ubr (eaOps Q2) (symQ2 MB) (symQ2 MA) (symQ2 MC) (symQ2 MA) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (-4/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-8/9) (0)) (qq (0) (4/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (8/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  simp only [Ubr]
  rw [glM_stg213, glM_stg214, glM_stg215, glM_stg216, glM_stg217, glM_stg218, glM_stg219]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg221 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MC) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (-4/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-8/9) (0)) (qq (0) (4/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (8/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (128/81) (0)), (qq (-128/81) (0)), eoq (qq (0) (32/81)) (qq (32/81) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-32/81) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-128/81) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg222 : Phi (eaOps Q2) (symQ2 MB) (symQ2 MB) (symQ2 MA) (symQ2 MC) (symQ2 MC) (symQ2 MA) ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (128/27) (0)), (qq (-128/27) (0)), eoq (qq (0) (32/27)) (qq (32/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-32/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (-128/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  simp only [Phi]
  rw [glM_stg210, glM_stg211, glM_stg212, glM_stg220, glM_stg221]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg223 : Dop (eaOps Q2) (symQ2 MA) (symQ2 MA) (symQ2 MD) =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg224 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MC) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg225 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MC) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg226 : (eaOps Q2).mul (symQ2 MB) (symQ2 MC) =
    (⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (-2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-4/9) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (2/9)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg227 : (eaOps Q2).mul (symQ2 MA) (symQ2 MA) =
    (⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg228 : Upol (eaOps Q2) ⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (1/3) (0)), eoq (qq (0) (-2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (-4/9) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (2/9)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ ⟨(qq (1) (0)), (qq (1) (0)), (qq (1) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ (symQ2 MD) =
    (⟨(qq (-1/27) (0)), (qq (1/27) (0)), (qq (-1/9) (0)), eoq (qq (0) (2/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (-2/27)) (qq (2/27) (0)) (qq (-4/27) (0)) (qq (0) (-2/27)), eoq (qq (4/27) (0)) (qq (0) (-2/27)) (qq (0) (-2/27)) (qq (-2/27) (0)) (qq (-4/27) (0)) (qq (0) (0)) (qq (0) (2/27)) (qq (0) (0)), eoq (qq (0) (-2/27)) (qq (2/27) (0)) (qq (-4/27) (0)) (qq (0) (-2/27)) (qq (0) (2/27)) (qq (0) (0)) (qq (-2/27) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg229 : Upol (eaOps Q2) (symQ2 MC) (symQ2 MA) (symQ2 MD) =
    (⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (-1/9) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-2/9) (0)) (qq (-2/9) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)), eoq (qq (0) (0)) (qq (2/9) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (-2/9) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg230 : Upol (eaOps Q2) (symQ2 MB) (symQ2 MA) ⟨(qq (1/9) (0)), (qq (-1/9) (0)), (qq (-1/9) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-2/9) (0)) (qq (-2/9) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)), eoq (qq (0) (0)) (qq (2/9) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (-2/9) (0)) (qq (0) (0))⟩ =
    (⟨(qq (-1/27) (0)), (qq (1/27) (0)), (qq (-1/9) (0)), eoq (qq (0) (2/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (-2/27) (0)) (qq (-2/27) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (-2/27)) (qq (0) (2/27)) (qq (-2/27) (0)) (qq (0) (0)) (qq (0) (-2/27)) (qq (0) (2/27)) (qq (-2/27) (0)), eoq (qq (0) (0)) (qq (2/27) (0)) (qq (-2/27) (0)) (qq (0) (-2/27)) (qq (0) (0)) (qq (2/27) (0)) (qq (-2/27) (0)) (qq (0) (-2/27))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg231 : Upol (eaOps Q2) (symQ2 MB) (symQ2 MA) (symQ2 MD) =
    (⟨(qq (1/9) (0)), (qq (1/9) (0)), (qq (-1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (0) (0)) (qq (0) (2/9)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg232 : Upol (eaOps Q2) (symQ2 MC) (symQ2 MA) ⟨(qq (1/9) (0)), (qq (1/9) (0)), (qq (-1/3) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/9) (0)) (qq (0) (0)) (qq (0) (2/9)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (2/9)) (qq (0) (0)) (qq (-2/9) (0)) (qq (0) (0))⟩ =
    (⟨(qq (-1/27) (0)), (qq (1/27) (0)), (qq (-1/9) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (2/27)) (qq (2/27) (0)) (qq (-2/27) (0)) (qq (0) (-2/27)), eoq (qq (4/27) (0)) (qq (0) (0)) (qq (0) (0)) (qq (2/27) (0)) (qq (0) (0)) (qq (0) (2/27)) (qq (0) (0)) (qq (2/27) (0)), eoq (qq (0) (0)) (qq (2/27) (0)) (qq (-2/27) (0)) (qq (0) (0)) (qq (0) (2/27)) (qq (-2/27) (0)) (qq (-2/27) (0)) (qq (0) (2/27))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg233 : Ubr (eaOps Q2) (symQ2 MB) (symQ2 MA) (symQ2 MC) (symQ2 MA) (symQ2 MD) =
    (⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (4/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (-4/9)) (qq (8/27) (0)) (qq (-8/27) (0)) (qq (0) (-4/27)), eoq (qq (8/27) (0)) (qq (0) (-4/27)) (qq (0) (-4/9)) (qq (-8/27) (0)) (qq (-16/27) (0)) (qq (0) (0)) (qq (0) (4/27)) (qq (0) (0)), eoq (qq (0) (-8/27)) (qq (0) (0)) (qq (-8/27) (0)) (qq (0) (-4/27)) (qq (0) (4/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ : EA Q2) := by
  simp only [Ubr]
  rw [glM_stg226, glM_stg227, glM_stg228, glM_stg229, glM_stg230, glM_stg231, glM_stg232]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg234 : Dop (eaOps Q2) (symQ2 MB) (symQ2 MC) ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (4/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (-4/9)) (qq (8/27) (0)) (qq (-8/27) (0)) (qq (0) (-4/27)), eoq (qq (8/27) (0)) (qq (0) (-4/27)) (qq (0) (-4/9)) (qq (-8/27) (0)) (qq (-16/27) (0)) (qq (0) (0)) (qq (0) (4/27)) (qq (0) (0)), eoq (qq (0) (-8/27)) (qq (0) (0)) (qq (-8/27) (0)) (qq (0) (-4/27)) (qq (0) (4/27)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0))⟩ =
    (⟨(qq (0) (0)), (qq (-128/243) (0)), (qq (128/243) (0)), eoq (qq (0) (-32/243)) (qq (-32/243) (0)) (qq (-32/243) (0)) (qq (0) (-80/243)) (qq (0) (-80/243)) (qq (-160/243) (0)) (qq (32/243) (0)) (qq (0) (-32/243)), eoq (qq (32/243) (0)) (qq (0) (0)) (qq (0) (80/243)) (qq (-224/243) (0)) (qq (32/243) (0)) (qq (0) (-80/81)) (qq (0) (0)) (qq (32/243) (0)), eoq (qq (0) (0)) (qq (128/243) (0)) (qq (-32/243) (0)) (qq (0) (16/243)) (qq (0) (-16/243)) (qq (0) (0)) (qq (0) (0)) (qq (0) (-64/243))⟩ : EA Q2) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_stg235 : Phi (eaOps Q2) (symQ2 MB) (symQ2 MB) (symQ2 MA) (symQ2 MC) (symQ2 MC) (symQ2 MA) (symQ2 MD) =
    (⟨(qq (0) (0)), (qq (-128/81) (0)), (qq (128/81) (0)), eoq (qq (0) (-32/81)) (qq (-32/81) (0)) (qq (-32/81) (0)) (qq (0) (-80/81)) (qq (0) (-80/81)) (qq (-160/81) (0)) (qq (32/81) (0)) (qq (0) (-32/81)), eoq (qq (32/81) (0)) (qq (0) (0)) (qq (0) (80/81)) (qq (-224/81) (0)) (qq (32/81) (0)) (qq (0) (-80/27)) (qq (0) (0)) (qq (32/81) (0)), eoq (qq (0) (0)) (qq (128/81) (0)) (qq (-32/81) (0)) (qq (0) (16/81)) (qq (0) (-16/81)) (qq (0) (0)) (qq (0) (0)) (qq (0) (-64/81))⟩ : EA Q2) := by
  simp only [Phi]
  rw [glM_stg223, glM_stg224, glM_stg225, glM_stg233, glM_stg234]
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glM_term8 : glennieTerm (eaOps Q2) (symQ2 MD) (symQ2 MB) (symQ2 MB) (symQ2 MA) (symQ2 MC) (symQ2 MC) (symQ2 MA) =
    (⟨(qq (0) (0)), (qq (256/81) (0)), (qq (-256/81) (0)), eoq (qq (0) (64/81)) (qq (160/243) (0)) (qq (-128/81) (0)) (qq (0) (-512/243)) (qq (0) (0)) (qq (128/81) (0)) (qq (-64/243) (0)) (qq (0) (-32/243)), eoq (qq (-224/243) (0)) (qq (0) (-32/243)) (qq (0) (0)) (qq (-128/81) (0)) (qq (128/81) (0)) (qq (0) (-512/243)) (qq (0) (-32/81)) (qq (128/243) (0)), eoq (qq (0) (0)) (qq (-256/81) (0)) (qq (-64/243) (0)) (qq (0) (-32/243)) (qq (0) (-32/81)) (qq (128/243) (0)) (qq (0) (0)) (qq (0) (512/243))⟩ : EA Q2) := by
  simp only [glennieTerm]
  rw [glM_dd, glM_stg222, glM_stg235]
  decide +kernel
def glM_val : EA Q2 := ⟨(qq (0) (0)), (qq (0) (0)), (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (-2048/243)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (-2048/243)) (qq (0) (0)) (qq (0) (0)), eoq (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (0)) (qq (0) (2048/243))⟩
set_option maxHeartbeats 400000000 in
theorem glM_eq : glennieF (eaOps Q2) (symQ2 MA) (symQ2 MB) (symQ2 MC) (symQ2 MD) = glM_val := by
  simp only [glennieF]
  rw [glM_term0, glM_term1, glM_term2, glM_term3, glM_term4, glM_term5, glM_term6, glM_term7, glM_term8]
  decide +kernel

theorem glM_normSq : glM_val.tp glM_val = qq (16777216 / 19683) 0 := by
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem cubicNorm_M_ABC : ((MA.add MB).add MC).cubicNorm = qq (2 / 9) 0 := by
  decide +kernel

end AlbertSequential.AppF
