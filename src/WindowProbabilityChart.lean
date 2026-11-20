/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ThirteenTracesAndAform

/-! Coordinate identities for integrating the rank-one Albert chart. The
octonion product is never reassociated as an octonion-valued product. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

/-- The eight ordinary real coordinates of the pinned octonion model. -/
def octonionChartCoordinates : (Fin 8 → ℝ) ≃ₗ[ℝ] Octonion where
  toFun u := (⟨u 0, u 1, u 2, u 3⟩, ⟨u 4, u 5, u 6, u 7⟩)
  invFun z := ![z.1.re, z.1.imI, z.1.imJ, z.1.imK, z.2.re, z.2.imI, z.2.imJ, z.2.imK]
  left_inv := by intro u; funext i; fin_cases i <;> rfl
  right_inv := by rintro ⟨⟨a, b, c, d⟩, ⟨e, f, g, h⟩⟩; rfl
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem octNormSq_octonionChartCoordinates (u : Fin 8 → ℝ) :
    octNormSq (octonionChartCoordinates u) = ∑ i, (u i)^2 := by
  rw [octNormSq_eq_coords]
  change (u 0)^2 + (u 1)^2 + (u 2)^2 + (u 3)^2 +
    (u 4)^2 + (u 5)^2 + (u 6)^2 + (u 7)^2 = _
  simp [Fin.sum_univ_succ, add_assoc]

/-- First affine chart of the rank-one cone, before multiplication by its ray parameter. -/
def chartDyad (u w : Octonion) : Albert := octDyad ![octOne, u, w]

theorem chartDyad_trace (u w : Octonion) :
    albertTrace (chartDyad u w) = 1 + octNormSq u + octNormSq w := by
  unfold albertTrace
  rw [Fin.sum_univ_three]
  change octNormSq octOne + octNormSq u + octNormSq w = _
  rw [octNormSq_one]

theorem chartDyad_trace_pos (u w : Octonion) : 0 < albertTrace (chartDyad u w) := by
  rw [chartDyad_trace]
  exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg zero_lt_one (octNormSq_nonneg u))
    (octNormSq_nonneg w)

private theorem octDyad_scale (r : ℝ) (v : Fin 3 → Octonion) :
    octDyad (fun i => r • v i) = r^2 • octDyad v := by
  have hsnd (A : Albert) : (r ^ 2 • A).2 = r ^ 2 • A.2 := rfl
  apply Prod.ext <;> funext i
  · change octNormSq (r • v i) = r ^ 2 * octNormSq (v i)
    exact octNormSq_smul r (v i)
  · rw [hsnd]
    fin_cases i <;>
      simp [octDyad, Pi.smul_apply, octonionConj_smul, octonionMul_smul_left,
        octonionMul_smul_right, smul_smul, pow_two]

/-- Each point of the affine chart, normalized by its own trace, is an
atom of the native Albert algebra. -/
theorem chartDyad_normalize_isAtom (u w : Octonion) :
    IsAtom ((albertTrace (chartDyad u w))⁻¹ • chartDyad u w) := by
  let d := albertTrace (chartDyad u w)
  let r := (Real.sqrt d)⁻¹
  have hd : 0 < d := chartDyad_trace_pos u w
  have hr : r^2 = d⁻¹ := by
    dsimp [r]
    rw [inv_pow, Real.sq_sqrt hd.le]
  have hnorm : r^2 + octNormSq (r • u) + octNormSq (r • w) = 1 := by
    rw [octNormSq_smul, octNormSq_smul, hr]
    have heq : d = 1 + octNormSq u + octNormSq w := chartDyad_trace u w
    calc
      _ = d⁻¹ * (1 + octNormSq u + octNormSq w) := by ring
      _ = 1 := by rw [← heq, inv_mul_cancel₀ hd.ne']
  have ha := octDyad_real0_isAtom r (r • u) (r • w) hnorm
  have hcol : (![octonionScalar r, r • u, r • w] : Fin 3 → Octonion) =
      fun i => r • (![octOne, u, w] : Fin 3 → Octonion) i := by
    funext i
    fin_cases i
    · exact octonionScalar_eq_smul r
    · rfl
    · rfl
  change IsAtom (d⁻¹ • chartDyad u w)
  rw [hcol, octDyad_scale, hr] at ha
  exact ha

/-- Hermitian coefficient in the trace kernel, with first column `(a, x, y)`. -/
def schurMatrix (a b c : ℝ) (x y z : Octonion) : Albert :=
  (![a, b, c], ![octonionConj x, octonionConj y, z])

private theorem octDot_conj_both (x y : Octonion) :
    octDot (octonionConj x) (octonionConj y) = octDot x y := by
  have h := octNormSq_add (octonionConj x) (octonionConj y)
  rw [← octonionConj_add, octNormSq_conj, octNormSq_add, octNormSq_conj, octNormSq_conj] at h
  linarith

theorem tracePairing_chartDyad (a b c : ℝ) (x y z u w : Octonion) :
    tracePairing (schurMatrix a b c x y z) (chartDyad u w) =
      a + b * octNormSq u + c * octNormSq w +
        2 * (octDot x u + octDot y w + octDot u (octonionMul z w)) := by
  rw [tracePairing_eq_coords]
  change a * octNormSq octOne + b * octNormSq u + c * octNormSq w +
    2 * (octDot (octonionConj x) (octonionMul octOne (octonionConj u)) +
      octDot (octonionConj y) (octonionMul octOne (octonionConj w)) +
      octDot z (octonionMul u (octonionConj w))) = _
  rw [octNormSq_one, mul_one, octonionMul_one_left, octonionMul_one_left,
    octDot_conj_both, octDot_conj_both, octDot_comm z, octDot_mul_right, octonionConj_conj]

/-- The remaining scalar after completing the two octonionic squares. -/
def schurScalar (a b c : ℝ) (x y z : Octonion) : ℝ :=
  a - octNormSq x / b -
    octNormSq (y - b⁻¹ • octonionMul (octonionConj z) x) / (c - octNormSq z / b)

private theorem completeSquare (b : ℝ) (hb : b ≠ 0) (u q : Octonion) :
    b * octNormSq (u + b⁻¹ • q) - octNormSq q / b =
      b * octNormSq u + 2 * octDot u q := by
  rw [octNormSq_add, octNormSq_smul, octDot_smul_right]
  field_simp [hb]
  ring

/-- Complete the two real Gaussian squares using the adjoint of left
multiplication by `z` and the norm identity on native octonions. -/
theorem chartDyad_completeSquares (a b c : ℝ) (x y z u w : Octonion)
    (hb : b ≠ 0) (hr : c - octNormSq z / b ≠ 0) :
    tracePairing (schurMatrix a b c x y z) (chartDyad u w) =
      b * octNormSq (u + b⁻¹ • (x + octonionMul z w)) +
      (c - octNormSq z / b) * octNormSq
        (w + (c - octNormSq z / b)⁻¹ • (y - b⁻¹ • octonionMul (octonionConj z) x)) +
      schurScalar a b c x y z := by
  have h1 := completeSquare b hb u (x + octonionMul z w)
  have h2 := completeSquare (c - octNormSq z / b) hr w
    (y - b⁻¹ • octonionMul (octonionConj z) x)
  have hzx : octDot x (octonionMul z w) = octDot w (octonionMul (octonionConj z) x) := by
    rw [octDot_comm x, octDot_mul_left]
  rw [octNormSq_add x (octonionMul z w), octNormSq_mul, hzx,
    octDot_add_right, octDot_comm u x] at h1
  rw [octDot_sub_right, octDot_smul_right, octDot_comm w y] at h2
  rw [tracePairing_chartDyad]
  unfold schurScalar
  simp only [div_eq_mul_inv] at h1 h2 ⊢
  linear_combination -h1 - h2

/-- The product of the Gaussian and radial scale coefficients equals the
native cubic norm in the deposited normalization. -/
theorem schurScalar_cubicNorm (a b c : ℝ) (x y z : Octonion)
    (hb : b ≠ 0) (hr : c - octNormSq z / b ≠ 0) :
    b * (c - octNormSq z / b) * schurScalar a b c x y z =
      albertCubicNorm (schurMatrix a b c x y z) := by
  have hcross : octDot (octonionMul (octonionConj x) z) (octonionConj y) =
      octDot y (octonionMul (octonionConj z) x) := by
    rw [octDot_mul_right, ← octonionConj_mul, octDot_conj_both, octDot_comm x, octDot_mul_left]
  unfold schurScalar albertCubicNorm
  change b * (c - octNormSq z / b) *
    (a - octNormSq x / b - octNormSq (y - b⁻¹ • octonionMul (octonionConj z) x) /
      (c - octNormSq z / b)) =
    a * b * c - a * octNormSq z - b * octNormSq (octonionConj y) -
      c * octNormSq (octonionConj x) + 2 * octDot (octonionMul (octonionConj x) z) (octonionConj y)
  rw [hcross, octNormSq_sub, octNormSq_smul, octNormSq_mul, octDot_smul_right,
    octNormSq_conj, octNormSq_conj, octNormSq_conj]
  have hdet : b * c - octNormSq z ≠ 0 := by
    intro h
    apply hr
    field_simp [hb]
    linarith
  field_simp [hb, hdet]
  ring

end AlbertSequential.WindowProbability
