/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CompanionSignedInvariant
public import SubalgebraCoordsAndLine
public import SuppliedEmbeddingStateTransport
public import Mathlib.Tactic.NoncommRing

@[expose] public section
noncomputable section

namespace AlbertSequential.NativeAnalysis

/-- Cyclicity cancels the signed trace polynomial in any associative real algebra. -/
theorem cyclicTrace_signedThree_zero {A : Type*} [Ring A] [Algebra ℝ A]
    (τ : A →ₗ[ℝ] ℝ) (hτ : ∀ a b, τ (a * b) = τ (b * a)) (X Y Z : A) :
    τ ((X * (Y * Z * Y) * X - Y * (X * Z * X) * Y) *
      (Z * ((1 / 2 : ℝ) • (X * Y + Y * X)) * Z)) = 0 := by
  let P := X * Y * Z
  let Q := Y * X * Z
  have hpoly :
      (X * (Y * Z * Y) * X - Y * (X * Z * X) * Y) * (Z * (X * Y + Y * X) * Z) =
        P * Q * P + P * Q * Q - Q * P * P - Q * P * Q := by
    dsimp only [P, Q]
    noncomm_ring
  have hp : τ (P * Q * P) = τ (Q * P * P) := by
    rw [mul_assoc, hτ P (Q * P)]
  have hq : τ (P * Q * Q) = τ (Q * P * Q) := by
    exact (hτ (P * Q) Q).trans (congrArg τ (mul_assoc Q P Q).symm)
  simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, map_smul, smul_eq_mul, hpoly, map_sub, map_add, hp, hq]
  ring

/-- A trace-compatible special embedding kills the invariant on its entire domain. -/
theorem signedThreeInvariant_zero_of_scaledEmbedding {B : NativeJordanSubalgebra} {d : ℕ}
    (ι : SuppliedHermitianEmbedding B d) (c : ℝ) (hc : 0 < c)
    (htr : ∀ a b : B.carrier, (Matrix.trace (ι.map a * ι.map b)).re =
      c * tracePairing a.1 b.1) (x y z : B.carrier) :
    signedThreeInvariant x.1 y.1 z.1 = 0 := by
  let U := B.restrictedQuadratic
  let V := U x (U y z) - U y (U x z)
  let W := U z (B.restrictedProduct.product x y)
  have hτ : (Matrix.trace (ι.map V * ι.map W)).re = 0 := by
    dsimp only [V, W, U]
    rw [map_sub, ι.map_quadratic, ι.map_quadratic, ι.map_quadratic,
      ι.map_quadratic, ι.map_quadratic]
    have hj : ι.map (B.restrictedProduct.product x y) =
        (1 / 2 : ℝ) • (ι.map x * ι.map y + ι.map y * ι.map x) := ι.jordan x y
    rw [hj]
    let τ := Complex.reCLM.toLinearMap.comp (Matrix.traceLinearMap (Fin d) ℝ ℂ)
    have hcyc : ∀ a b, τ (a * b) = τ (b * a) := by
      intro a b
      change (Matrix.trace (a * b)).re = (Matrix.trace (b * a)).re
      rw [Matrix.trace_mul_comm]
    exact cyclicTrace_signedThree_zero τ hcyc (ι.map x) (ι.map y) (ι.map z)
  have hz := (htr V W).symm.trans hτ
  change c * signedThreeInvariant x.1 y.1 z.1 = 0 at hz
  exact (mul_eq_zero.mp hz).resolve_left hc.ne'

theorem signedThreeInvariant_zero_of_proper_subalgebra (B : NativeJordanSubalgebra) (hB : B ≠ ⊤)
    (x y z : B.carrier) : signedThreeInvariant x.1 y.1 z.1 = 0 := by
  have hlt : B.carrier < (H3Subalgebra .O).carrier := by
    rw [H3Subalgebra_O_eq_top]
    refine lt_of_le_of_ne le_top fun heq => hB ?_
    cases B
    congr
  rcases lem_five_sub .O B hlt with ⟨q, hq, _, hline⟩ | ⟨Q, hQ⟩
  · exact signedThreeInvariant_zero_of_scaledEmbedding (lineCliffordEmbed q hq) 8 (by norm_num)
      (lineCliffordEmbed_tracePairing q hq) ⟨x.1, hline x.2⟩ ⟨y.1, hline y.2⟩ ⟨z.1, hline z.2⟩
  · exact signedThreeInvariant_zero_of_scaledEmbedding (symplecticQuatEmbed Q) 2 (by norm_num)
      (symplecticQuatEmbed_tracePairing Q) ⟨x.1, hQ x.2⟩ ⟨y.1, hQ y.2⟩ ⟨z.1, hQ z.2⟩

/-- A nonzero signed invariant forces the three elements and the unit to generate the Albert algebra. -/
theorem signedThreeInvariant_generates_of_ne_zero (x y z : Albert)
    (h : signedThreeInvariant x y z ≠ 0) : GeneratesAlbert ![x, y, z] := by
  intro a B hB
  by_contra ha
  have hproper : B ≠ ⊤ := fun ht => ha (by rw [ht]; trivial)
  exact h (signedThreeInvariant_zero_of_proper_subalgebra B hproper
    ⟨x, hB 0⟩ ⟨y, hB 1⟩ ⟨z, hB 2⟩)

end AlbertSequential.NativeAnalysis
