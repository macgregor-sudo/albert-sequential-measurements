/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilityChart
public import WindowProbabilityIntegrals

/-! Evaluation of the octonionic rank-one chart kernel in ordinary real
Lebesgue coordinates. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open MeasureTheory Real Set

/-- Native Albert trace and determinant in the exact iterated octonionic
chart integral. The Schur scales describe the domain on which this
calculation applies. -/
theorem integral_albertChart_trace_kernel (a b c : ℝ) (x y z : Octonion)
    (hb : 0 < b) (hr : 0 < c - octNormSq z / b) (hs : 0 < schurScalar a b c x y z) :
    (∫ t in Ioi (0 : ℝ), t ^ (11 : ℝ) *
      (∫ w : Fin 8 → ℝ, ∫ u : Fin 8 → ℝ,
        Real.exp (-tracePairing (schurMatrix a b c x y z)
          (t • chartDyad (octonionChartCoordinates u) (octonionChartCoordinates w))))) =
      π^8 * Gamma 4 / (albertCubicNorm (schurMatrix a b c x y z))^4 := by
  let e := octonionChartCoordinates
  let r := c - octNormSq z / b
  let s := schurScalar a b c x y z
  let uCenter := fun w : Fin 8 → ℝ => e.symm (b⁻¹ • (x + octonionMul z (e w)))
  let wCenter := e.symm (r⁻¹ • (y - b⁻¹ • octonionMul (octonionConj z) x))
  have hu (w u : Fin 8 → ℝ) : e u + b⁻¹ • (x + octonionMul z (e w)) = e (u + uCenter w) := by
    rw [map_add]
    simp [uCenter]
  have hw (w : Fin 8 → ℝ) :
      e w + r⁻¹ • (y - b⁻¹ • octonionMul (octonionConj z) x) = e (w + wCenter) := by
    rw [map_add]
    simp [wCenter]
  have hk (t : ℝ) (w u : Fin 8 → ℝ) :
      -tracePairing (schurMatrix a b c x y z) (t • chartDyad (e u) (e w)) =
        -t * (b * ∑ i, (u i + uCenter w i)^2) +
          -(t * r) * (∑ i, (w i + wCenter i)^2) + -(t * s) := by
    rw [tracePairing_smul_right, chartDyad_completeSquares a b c x y z (e u) (e w) hb.ne' hr.ne']
    change -(t * (b * octNormSq (e u + b⁻¹ • (x + octonionMul z (e w))) +
      r * octNormSq (e w + r⁻¹ • (y - b⁻¹ • octonionMul (octonionConj z) x)) + s)) = _
    rw [hu w u, hw w]
    dsimp only [e]
    rw [octNormSq_octonionChartCoordinates, octNormSq_octonionChartCoordinates]
    simp only [Pi.add_apply]
    ring
  change (∫ t in Ioi (0 : ℝ), t ^ (11 : ℝ) *
    (∫ w : Fin 8 → ℝ, ∫ u : Fin 8 → ℝ,
      Real.exp (-tracePairing (schurMatrix a b c x y z) (t • chartDyad (e u) (e w))))) = _
  simp_rw [hk]
  have h := integral_rankOne_chart_kernel 4 (by decide) b r s hb hr hs uCenter wCenter
  norm_num only [Nat.cast_ofNat, show (3 : ℝ) * 4 - 1 = 11 by norm_num] at h
  rw [h, ← schurScalar_cubicNorm a b c x y z hb.ne' hr.ne', Real.rpow_neg hs.le]
  change (π / b)^4 * (π / r)^4 * ((s ^ (4 : ℝ))⁻¹ * Gamma 4) = _
  rw [Real.rpow_ofNat]
  change (π / b)^4 * (π / r)^4 * ((s^4)⁻¹ * Gamma 4) = π^8 * Gamma 4 / (b * r * s)^4
  have hR : 0 < r := hr
  have hS : 0 < s := hs
  field_simp [hb.ne', hR.ne', hS.ne']

end AlbertSequential.WindowProbability
