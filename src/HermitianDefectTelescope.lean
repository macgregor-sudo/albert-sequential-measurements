/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CornerHolonomyDefects
public import Mathlib.Tactic.NoncommRing

/-! Six-term Hermitian defect telescope with literal normalized scalar data.
Every error is retained, and the local unit remains an explicit projection J.
Paper h1,h2,h3 correspond to h 0,h 1,h 2. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
namespace CornerHolonomy

def cornerScalarPart (c : Fin 3 → ℝ) (K12 K13 K23 : ℝ) : ℝ :=
  c 0 * c 1 * c 2 - c 0 * (c 1 * c 2 - K23) -
    c 1 * (c 0 * c 2 - K13) - c 2 * (c 0 * c 1 - K12)

def cornerCliffordParameters (c : Fin 3 → ℝ) (K12 K13 K23 c4 : ℝ) : CliffordScalarParameters where
  m1 := 1 - c 0 ^ 2
  m2 := 1 - c 1 ^ 2
  m3 := 1 - c 2 ^ 2
  u := c 0 * c 1 - K12
  v := c 0 * c 2 - K13
  w := c 1 * c 2 - K23
  d0 := c4 - cornerScalarPart c K12 K13 K23

section Cubic
variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]

def cornerCubicDefect (J : A) (h : Fin 3 → A) (c4 : ℝ) : A :=
  (1 / 2 : ℝ) • (h 0 * h 1 * h 2 + star (h 0 * h 1 * h 2)) - c4 • J

def hermitianProductTelescope (J : A) (h : Fin 3 → A) (c : Fin 3 → ℝ) : A :=
  let a := fun i => hermitianDefect J (h i) (c i)
  let b := fun i => centeredApproximation J (h i) (c i)
  (1 / 2 : ℝ) • (a 0 * h 1 * h 2 + b 0 * a 1 * h 2 + b 0 * b 1 * a 2 +
    a 2 * star (h 1) * star (h 0) + star (b 2) * a 1 * star (h 0) +
      star (b 2) * star (b 1) * a 0)

omit [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A] in
theorem symmetricProduct_telescopingIdentity (h a b : Fin 3 → A)
    (hdecomp : ∀ i, h i = a i + b i) (hastar : ∀ i, star (a i) = a i) :
    a 0 * h 1 * h 2 + b 0 * a 1 * h 2 + b 0 * b 1 * a 2 +
      a 2 * star (h 1) * star (h 0) + star (b 2) * a 1 * star (h 0) +
      star (b 2) * star (b 1) * a 0 =
    h 0 * h 1 * h 2 + star (h 0 * h 1 * h 2) -
      b 0 * b 1 * b 2 - star (b 0 * b 1 * b 2) := by
  simp only [hdecomp, star_add, star_mul, hastar]
  noncomm_ring

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem hermitianProductTelescope_identity (J : A) (h : Fin 3 → A)
    (hJ : star J = J) (c : Fin 3 → ℝ) :
    hermitianProductTelescope J h c =
      (1 / 2 : ℝ) • (h 0 * h 1 * h 2 + star (h 0 * h 1 * h 2)) -
        (1 / 2 : ℝ) •
          (centeredApproximation J (h 0) (c 0) * centeredApproximation J (h 1) (c 1) *
              centeredApproximation J (h 2) (c 2) +
            star (centeredApproximation J (h 0) (c 0) * centeredApproximation J (h 1) (c 1) *
              centeredApproximation J (h 2) (c 2))) := by
  dsimp only [hermitianProductTelescope]
  rw [symmetricProduct_telescopingIdentity h
    (fun i => hermitianDefect J (h i) (c i)) (fun i => centeredApproximation J (h i) (c i))
    (fun i => decomposition J (h i) (c i)) (fun i => hermitianDefect_selfAdjoint J (h i) hJ (c i))]
  module

omit [StarRing A] [StarModule ℝ A] in
theorem centeredProduct_expansion (J : A) (hJJ : J * J = J)
    (N : Fin 3 → A) (hN : ∀ i, CornerSupported J (N i))
    (c : Fin 3 → ℝ) (K12 K13 K23 : ℝ) :
    (1 / 2 : ℝ) •
      ((c 0 • J + N 0) * (c 1 • J + N 1) * (c 2 • J + N 2) +
        (c 2 • J - N 2) * (c 1 • J - N 1) * (c 0 • J - N 0)) =
      cliffordVolume N + cornerScalarPart c K12 K13 K23 • J +
        (1 / 2 : ℝ) •
          (c 0 • (N 1 * N 2 + N 2 * N 1 + (2 * (c 1 * c 2 - K23)) • J) +
            c 1 • (N 0 * N 2 + N 2 * N 0 + (2 * (c 0 * c 2 - K13)) • J) +
            c 2 • (N 0 * N 1 + N 1 * N 0 + (2 * (c 0 * c 1 - K12)) • J)) := by
  have hl (i : Fin 3) : J * N i = N i := (hN i).1
  have hr (i : Fin 3) : N i * J = N i := (hN i).2
  simp only [cliffordVolume, cornerScalarPart, add_mul, sub_mul, mul_add, mul_sub,
    smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul,
    hJJ, hl, hr, mul_assoc]
  module

theorem cornerDataError_element (J : A) (hJJ : J * J = J) (hJ : star J = J)
    (h : Fin 3 → A) (hsupport : ∀ i, CornerSupported J (h i))
    (c : Fin 3 → ℝ) (K12 K13 K23 c4 : ℝ) :
    cliffordVolume (fun i => skewHermitianPart (h i)) -
        (c4 - cornerScalarPart c K12 K13 K23) • J =
      cornerCubicDefect J h c4 - hermitianProductTelescope J h c -
        (1 / 2 : ℝ) •
          (c 0 • pairCliffordDefect J (h 1) (h 2) (c 1) (c 2) K23 +
            c 1 • pairCliffordDefect J (h 0) (h 2) (c 0) (c 2) K13 +
            c 2 • pairCliffordDefect J (h 0) (h 1) (c 0) (c 1) K12) := by
  have hparts (i : Fin 3) : CornerSupported J (skewHermitianPart (h i)) :=
    skewHermitianPart_supported J (h i) hJ (hsupport i)
  have hc := centeredProduct_expansion J hJJ (fun i => skewHermitianPart (h i)) hparts c K12 K13 K23
  have hb : (1 / 2 : ℝ) •
      (centeredApproximation J (h 0) (c 0) * centeredApproximation J (h 1) (c 1) *
          centeredApproximation J (h 2) (c 2) +
        star (centeredApproximation J (h 0) (c 0) * centeredApproximation J (h 1) (c 1) *
          centeredApproximation J (h 2) (c 2))) =
      cliffordVolume (fun i => skewHermitianPart (h i)) + cornerScalarPart c K12 K13 K23 • J +
        (1 / 2 : ℝ) •
          (c 0 • pairCliffordDefect J (h 1) (h 2) (c 1) (c 2) K23 +
            c 1 • pairCliffordDefect J (h 0) (h 2) (c 0) (c 2) K13 +
            c 2 • pairCliffordDefect J (h 0) (h 1) (c 0) (c 1) K12) := by
    rw [star_mul, star_mul, centeredApproximation_star J (h 2) hJ,
      centeredApproximation_star J (h 1) hJ, centeredApproximation_star J (h 0) hJ]
    simpa only [centeredApproximation, pairCliffordDefect, mul_assoc] using hc
  rw [cornerCubicDefect, hermitianProductTelescope_identity J h hJ c, hb]
  module

end Cubic
end CornerHolonomy
end AlbertSequential
