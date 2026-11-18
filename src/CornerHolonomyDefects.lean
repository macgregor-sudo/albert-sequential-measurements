/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CliffordDefectData

/-! Hermitian and skew-Hermitian defects in a supported proper corner.
The corner unit J need not be the ambient unit and h need not be unitary.
Paper indices 1,2,3 become Fin-3 indices 0,1,2 in the later cubic binder. -/
@[expose] public section
noncomputable section
namespace AlbertSequential

def CornerSupported {A : Type*} [Ring A] (J x : A) : Prop := J * x = x ∧ x * J = x

namespace CornerHolonomy
section Parts
variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]

def hermitianPart (h : A) : A := (1 / 2 : ℝ) • (h + star h)
def skewHermitianPart (h : A) : A := (1 / 2 : ℝ) • (h - star h)
def hermitianDefect (J h : A) (c : ℝ) : A := hermitianPart h - c • J
def centeredApproximation (J h : A) (c : ℝ) : A := c • J + skewHermitianPart h
def leftUnitarityDefect (J h : A) : A := star h * h - J
def rightUnitarityDefect (J h : A) : A := h * star h - J
def pairProductDefect (J h k : A) (K : ℝ) : A :=
  (1 / 2 : ℝ) • (h * k + star k * star h) - K • J
def squareCliffordDefect (J h : A) (c : ℝ) : A :=
  skewHermitianPart h * skewHermitianPart h + (1 - c ^ 2) • J
def pairCliffordDefect (J h k : A) (c d K : ℝ) : A :=
  skewHermitianPart h * skewHermitianPart k + skewHermitianPart k * skewHermitianPart h +
    (2 * (c * d - K)) • J

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem hermitianPart_selfAdjoint (h : A) : star (hermitianPart h) = hermitianPart h := by
  simp only [hermitianPart, star_smul, star_trivial, star_add, star_star]
  congr 1
  abel

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem skewHermitianPart_skew (h : A) : star (skewHermitianPart h) = -skewHermitianPart h := by
  simp only [skewHermitianPart, star_smul, star_trivial, star_sub, star_star]
  module

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A] in
theorem hermitian_add_skew (h : A) : hermitianPart h + skewHermitianPart h = h := by
  simp only [hermitianPart, skewHermitianPart]
  module

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem hermitianDefect_selfAdjoint (J h : A) (hJ : star J = J) (c : ℝ) :
    star (hermitianDefect J h c) = hermitianDefect J h c := by
  simp only [hermitianDefect, star_sub, hermitianPart_selfAdjoint, star_smul, star_trivial, hJ]

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem centeredApproximation_star (J h : A) (hJ : star J = J) (c : ℝ) :
    star (centeredApproximation J h c) = c • J - skewHermitianPart h := by
  simp only [centeredApproximation, star_add, star_smul, star_trivial, hJ,
    skewHermitianPart_skew, sub_eq_add_neg]

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A] in
theorem decomposition (J h : A) (c : ℝ) :
    h = hermitianDefect J h c + centeredApproximation J h c := by
  calc
    h = hermitianPart h + skewHermitianPart h := (hermitian_add_skew h).symm
    _ = _ := by unfold hermitianDefect centeredApproximation; module

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem adjoint_decomposition (J h : A) (hJ : star J = J) (c : ℝ) :
    star h = hermitianDefect J h c + star (centeredApproximation J h c) := by
  have hh := congrArg star (decomposition J h c)
  simpa only [star_add, hermitianDefect_selfAdjoint J h hJ c] using hh

omit [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A] in
theorem supported_star (J h : A) (hJ : star J = J) (hh : CornerSupported J h) :
    CornerSupported J (star h) := by
  constructor
  · have hs := congrArg star hh.2
    simpa only [star_mul, hJ] using hs
  · have hs := congrArg star hh.1
    simpa only [star_mul, hJ] using hs

omit [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A] in
theorem supported_add (J x y : A) (hx : CornerSupported J x) (hy : CornerSupported J y) :
    CornerSupported J (x + y) := by
  constructor
  · rw [mul_add, hx.1, hy.1]
  · rw [add_mul, hx.2, hy.2]

omit [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A] in
theorem supported_sub (J x y : A) (hx : CornerSupported J x) (hy : CornerSupported J y) :
    CornerSupported J (x - y) := by
  constructor
  · rw [mul_sub, hx.1, hy.1]
  · rw [sub_mul, hx.2, hy.2]

omit [StarRing A] [StarModule ℝ A] in
theorem supported_smul (J x : A) (hx : CornerSupported J x) (r : ℝ) :
    CornerSupported J (r • x) := by
  constructor
  · rw [mul_smul_comm, hx.1]
  · rw [smul_mul_assoc, hx.2]

omit [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A] in
theorem supported_mul (J x y : A) (hx : CornerSupported J x) (hy : CornerSupported J y) :
    CornerSupported J (x * y) := by
  constructor
  · rw [← mul_assoc, hx.1]
  · rw [mul_assoc, hy.2]

omit [StarModule ℝ A] in
theorem hermitianPart_supported (J h : A) (hJ : star J = J) (hh : CornerSupported J h) :
    CornerSupported J (hermitianPart h) :=
  supported_smul J _ (supported_add J _ _ hh (supported_star J h hJ hh)) _

omit [StarModule ℝ A] in
theorem skewHermitianPart_supported (J h : A) (hJ : star J = J) (hh : CornerSupported J h) :
    CornerSupported J (skewHermitianPart h) :=
  supported_smul J _ (supported_sub J _ _ hh (supported_star J h hJ hh)) _

omit [StarModule ℝ A] in
theorem hermitian_square_difference (h : A) :
    hermitianPart h * hermitianPart h - skewHermitianPart h * skewHermitianPart h =
      (1 / 2 : ℝ) • (h * star h + star h * h) := by
  simp only [hermitianPart, skewHermitianPart, add_mul, sub_mul, mul_add, mul_sub,
    smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul]
  module

omit [StarModule ℝ A] in
theorem squareDefect_reduction (J h : A) (hJJ : J * J = J) (hJ : star J = J)
    (hh : CornerSupported J h) (c : ℝ) :
    squareCliffordDefect J h c =
      (hermitianPart h + c • J) * hermitianDefect J h c -
        (1 / 2 : ℝ) • (rightUnitarityDefect J h + leftUnitarityDefect J h) := by
  have hs := supported_star J h hJ hh
  simp only [squareCliffordDefect, hermitianDefect, hermitianPart, skewHermitianPart,
    rightUnitarityDefect, leftUnitarityDefect, add_mul, sub_mul, mul_add, mul_sub,
    smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul,
    hh.1, hh.2, hs.1, hs.2, hJJ]
  module

theorem pairDefect_reduction (J h k : A) (hJJ : J * J = J) (hJ : star J = J)
    (hh : CornerSupported J h) (hk : CornerSupported J k) (c d K : ℝ) :
    pairCliffordDefect J h k c d K =
      (2 : ℝ) • pairProductDefect J h k K -
        (hermitianDefect J h c * k + centeredApproximation J h c * hermitianDefect J k d +
          hermitianDefect J k d * star h + star (centeredApproximation J k d) * hermitianDefect J h c) := by
  have hhs := supported_star J h hJ hh
  have hks := supported_star J k hJ hk
  rw [centeredApproximation_star J k hJ]
  simp only [pairCliffordDefect, pairProductDefect, hermitianDefect, centeredApproximation,
    hermitianPart, skewHermitianPart, add_mul, sub_mul, mul_add, mul_sub,
    smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul,
    hh.1, hh.2, hk.1, hk.2, hhs.1, hhs.2, hks.1, hks.2, hJJ]
  module

end Parts
end CornerHolonomy
end AlbertSequential
