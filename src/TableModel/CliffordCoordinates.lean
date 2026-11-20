/- SPDX-License-Identifier: Apache-2.0 -/
module

public import LemmaB.Model
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.Tactic.Module

public section
noncomputable section

namespace LemmaB

open scoped BigOperators

variable (p : Params ℝ)

@[expose] def comparisonMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![p.M11, p.M12, p.M13; p.M12, p.M22, p.M23; p.M13, p.M23, p.M33]

@[expose] def comparisonQuadratic : QuadraticForm ℝ (Fin 3 → ℝ) :=
  -LinearMap.BilinMap.toQuadraticMap
    (Matrix.toLinearMap₂' ℝ (S₁ := ℝ) (S₂ := ℝ) (comparisonMatrix p))

abbrev ComparisonClifford := CliffordAlgebra (comparisonQuadratic p)

private def epsilon1 : Module.End ℝ (C8 ℝ) := ⟨⟨eps1 p, eps1_add p⟩, eps1_smul p⟩
private def epsilon2 : Module.End ℝ (C8 ℝ) := ⟨⟨eps2 p, eps2_add p⟩, eps2_smul p⟩
private def epsilon3 : Module.End ℝ (C8 ℝ) := ⟨⟨eps3 p, eps3_add p⟩, eps3_smul p⟩

def epsilonAction (i : Fin 3) : Module.End ℝ (C8 ℝ) :=
  ![epsilon1 p, epsilon2 p, epsilon3 p] i

@[simp] theorem epsilonAction_zero (v : C8 ℝ) : epsilonAction p 0 v = eps1 p v := by
  unfold epsilonAction epsilon1
  rfl

@[simp] theorem epsilonAction_one (v : C8 ℝ) : epsilonAction p 1 v = eps2 p v := by
  unfold epsilonAction epsilon2
  rfl

@[simp] theorem epsilonAction_two (v : C8 ℝ) : epsilonAction p 2 v = eps3 p v := by
  unfold epsilonAction epsilon3
  rfl

private def epsLinear : (Fin 3 → ℝ) →ₗ[ℝ] Module.End ℝ (C8 ℝ) where
  toFun x := x 0 • epsilon1 p + x 1 • epsilon2 p + x 2 • epsilon3 p
  map_add' x y := by simp only [Pi.add_apply, add_smul]; abel
  map_smul' c x := by simp only [Pi.smul_apply, smul_eq_mul, mul_smul, smul_add, RingHom.id_apply]

private theorem epsLinear_square (x : Fin 3 → ℝ) :
    epsLinear p x * epsLinear p x = algebraMap ℝ _ (comparisonQuadratic p x) := by
  apply LinearMap.ext
  intro v
  change epsLinear p x (epsLinear p x v) = comparisonQuadratic p x • v
  calc
    _ = (x 0)^2 • eps1 p (eps1 p v) + (x 1)^2 • eps2 p (eps2 p v) +
        (x 2)^2 • eps3 p (eps3 p v) +
        (x 0 * x 1) • (eps1 p (eps2 p v) + eps2 p (eps1 p v)) +
        (x 0 * x 2) • (eps1 p (eps3 p v) + eps3 p (eps1 p v)) +
        (x 1 * x 2) • (eps2 p (eps3 p v) + eps3 p (eps2 p v)) := by
      simp only [epsLinear, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
        LinearMap.smul_apply, epsilon1, epsilon2, epsilon3, eps1_add, eps2_add, eps3_add,
        eps1_smul, eps2_smul, eps3_smul]
      module
    _ = _ := by
      rw [eps1_sq, eps2_sq, eps3_sq, eps12_anti, eps13_anti, eps23_anti]
      simp only [comparisonQuadratic, neg_apply,
        LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply, Fin.sum_univ_three,
        comparisonMatrix, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, smul_eq_mul]
      module

def cliffordAction : ComparisonClifford p →ₐ[ℝ] Module.End ℝ (C8 ℝ) :=
  CliffordAlgebra.lift (comparisonQuadratic p) ⟨epsLinear p, epsLinear_square p⟩

@[expose] def cliffordGenerator (i : Fin 3) : ComparisonClifford p :=
  CliffordAlgebra.ι (comparisonQuadratic p) (Pi.single i 1)

@[simp] theorem cliffordAction_generator (i : Fin 3) :
    cliffordAction p (cliffordGenerator p i) = epsilonAction p i := by
  unfold cliffordAction cliffordGenerator
  rw [CliffordAlgebra.lift_ι_apply]
  fin_cases i <;> simp [epsLinear, epsilonAction]

def cliffordCoordinates : ComparisonClifford p →ₗ[ℝ] C8 ℝ :=
  (LinearMap.applyₗ (R := ℝ) (one8 : C8 ℝ)).comp (cliffordAction p).toLinearMap

@[simp] theorem cliffordCoordinates_one : cliffordCoordinates p 1 = one8 := by
  change cliffordAction p 1 one8 = one8
  simp

theorem cliffordCoordinates_generator_mul (i : Fin 3) (a : ComparisonClifford p) :
    cliffordCoordinates p (cliffordGenerator p i * a) =
      epsilonAction p i (cliffordCoordinates p a) := by
  change cliffordAction p (cliffordGenerator p i * a) one8 =
    epsilonAction p i (cliffordAction p a one8)
  rw [map_mul, cliffordAction_generator]
  rfl

@[expose] def cliffordVolume : ComparisonClifford p :=
  cliffordGenerator p 0 * (cliffordGenerator p 1 * cliffordGenerator p 2) +
    p.M23 • cliffordGenerator p 0 - p.M13 • cliffordGenerator p 1 + p.M12 • cliffordGenerator p 2

@[expose] def cliffordGhost : ComparisonClifford p := cliffordVolume p - p.b • 1

def cliffordBasisWords : Fin 8 → ComparisonClifford p :=
  ![1, cliffordGenerator p 0, cliffordGenerator p 1, cliffordGenerator p 2,
    cliffordGenerator p 1 * cliffordGenerator p 2 + p.M23 • 1,
    cliffordGenerator p 2 * cliffordGenerator p 0 + p.M13 • 1,
    cliffordGenerator p 0 * cliffordGenerator p 1 + p.M12 • 1, cliffordGhost p]

theorem cliffordCoordinates_basisWords (i : Fin 8) :
    cliffordCoordinates p (cliffordBasisWords p i) = Pi.single i 1 := by
  have he0 := (eps_one p).1
  have he1 := (eps_one p).2.1
  have he2 := (eps_one p).2.2
  obtain ⟨hc0, hc1, hc2, hg⟩ := chi_basis p
  have hword (j : Fin 3) : cliffordCoordinates p (cliffordGenerator p j) =
      epsilonAction p j one8 := by
    simpa only [mul_one, cliffordCoordinates_one] using cliffordCoordinates_generator_mul p j 1
  fin_cases i
  · change cliffordCoordinates p 1 = _
    rw [cliffordCoordinates_one]
    funext j; fin_cases j <;> simp [one8]
  · change cliffordCoordinates p (cliffordGenerator p 0) = _
    rw [hword]
    change eps1 p one8 = _
    rw [he0]
    funext j; fin_cases j <;> simp [e1v]
  · change cliffordCoordinates p (cliffordGenerator p 1) = _
    rw [hword]
    change eps2 p one8 = _
    rw [he1]
    funext j; fin_cases j <;> simp [e2v]
  · change cliffordCoordinates p (cliffordGenerator p 2) = _
    rw [hword]
    change eps3 p one8 = _
    rw [he2]
    funext j; fin_cases j <;> simp [e3v]
  · change cliffordCoordinates p (cliffordGenerator p 1 * cliffordGenerator p 2 + p.M23 • 1) = _
    simp only [map_add, map_smul, cliffordCoordinates_generator_mul, hword, cliffordCoordinates_one]
    change eps2 p (eps3 p one8) + p.M23 • one8 = _
    rw [hc0]
    funext j; fin_cases j <;> simp
  · change cliffordCoordinates p (cliffordGenerator p 2 * cliffordGenerator p 0 + p.M13 • 1) = _
    simp only [map_add, map_smul, cliffordCoordinates_generator_mul, hword, cliffordCoordinates_one]
    change eps3 p (eps1 p one8) + p.M13 • one8 = _
    rw [hc1]
    funext j; fin_cases j <;> simp
  · change cliffordCoordinates p (cliffordGenerator p 0 * cliffordGenerator p 1 + p.M12 • 1) = _
    simp only [map_add, map_smul, cliffordCoordinates_generator_mul, hword, cliffordCoordinates_one]
    change eps1 p (eps2 p one8) + p.M12 • one8 = _
    rw [hc2]
    funext j; fin_cases j <;> simp
  · change cliffordCoordinates p (cliffordGhost p) = _
    simp only [cliffordGhost, cliffordVolume, map_add, map_sub, map_smul,
      cliffordCoordinates_generator_mul, hword, cliffordCoordinates_one]
    change Gam p one8 - p.b • one8 = _
    rw [hg]
    funext j; fin_cases j <;> simp [gee]

private theorem cliffordCoordinates_surj : Function.Surjective (cliffordCoordinates p) := by
  intro v
  refine ⟨∑ i, v i • cliffordBasisWords p i, ?_⟩
  rw [map_sum]
  simp only [map_smul, cliffordCoordinates_basisWords]
  funext i
  simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul]

theorem cliffordCoordinates_ghost :
    cliffordCoordinates p (cliffordGhost p) = Pi.single 7 1 := by
  change cliffordCoordinates p (cliffordBasisWords p 7) = _
  exact cliffordCoordinates_basisWords p 7

private def exteriorComparison : ComparisonClifford p ≃ₗ[ℝ] ExteriorAlgebra ℝ (Fin 3 → ℝ) := by
  letI : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  exact CliffordAlgebra.equivExterior (comparisonQuadratic p)

private def comparisonCliffordBasis : Module.Basis (Finset (Fin 3)) ℝ (ComparisonClifford p) :=
  (Pi.basisFun ℝ (Fin 3)).ExteriorAlgebra.map (exteriorComparison p).symm

theorem comparisonClifford_finrank : Module.finrank ℝ (ComparisonClifford p) = 8 := by
  rw [Module.finrank_eq_card_basis (comparisonCliffordBasis p)]
  decide

def cliffordCoordinateEquiv : ComparisonClifford p ≃ₗ[ℝ] C8 ℝ := by
  letI : FiniteDimensional ℝ (ComparisonClifford p) :=
    Module.Finite.of_basis (comparisonCliffordBasis p)
  have hdim : Module.finrank ℝ (ComparisonClifford p) = Module.finrank ℝ (C8 ℝ) := by
    rw [comparisonClifford_finrank, Module.finrank_eq_card_basis (Pi.basisFun ℝ (Fin 8))]
    decide
  exact LinearEquiv.ofBijective (cliffordCoordinates p)
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2
      (cliffordCoordinates_surj p), cliffordCoordinates_surj p⟩

@[simp] theorem cliffordCoordinateEquiv_apply (a : ComparisonClifford p) :
    cliffordCoordinateEquiv p a = cliffordCoordinates p a := by
  unfold cliffordCoordinateEquiv
  rfl

def cliffordConjugate : ComparisonClifford p →ₗ[ℝ] ComparisonClifford p :=
  CliffordAlgebra.reverse.comp CliffordAlgebra.involute.toLinearMap

@[simp] theorem cliffordConjugate_one : cliffordConjugate p 1 = 1 := by
  simp [cliffordConjugate]

@[simp] theorem cliffordConjugate_generator (i : Fin 3) :
    cliffordConjugate p (cliffordGenerator p i) = -cliffordGenerator p i := by
  simp [cliffordConjugate, cliffordGenerator]

theorem cliffordConjugate_mul (a b : ComparisonClifford p) :
    cliffordConjugate p (a * b) = cliffordConjugate p b * cliffordConjugate p a := by
  simp [cliffordConjugate, CliffordAlgebra.reverse.map_mul]

def cliffordScalar : ComparisonClifford p →ₗ[ℝ] ℝ :=
  (LinearMap.proj 0).comp (cliffordCoordinates p)

def cliffordPairing : ComparisonClifford p →ₗ[ℝ] ComparisonClifford p →ₗ[ℝ] ℝ where
  toFun a := (cliffordScalar p).comp (LinearMap.mul ℝ (ComparisonClifford p) (cliffordConjugate p a))
  map_add' a b := by
    ext z
    simp
  map_smul' c a := by
    ext z
    simp

theorem cliffordPairing_apply (a b : ComparisonClifford p) :
    cliffordPairing p a b = cliffordScalar p (cliffordConjugate p a * b) := by
  unfold cliffordPairing
  rfl

private theorem cliffordPairing_skew (i : Fin 3) (a b : ComparisonClifford p) :
    cliffordPairing p a (cliffordGenerator p i * b) =
      -cliffordPairing p (cliffordGenerator p i * a) b := by
  simp [cliffordPairing_apply, cliffordConjugate_mul, mul_assoc]

theorem cliffordPairing_eq_W (a b : ComparisonClifford p) :
    cliffordPairing p a b = W p (cliffordCoordinates p a) (cliffordCoordinates p b) := by
  let e := cliffordCoordinateEquiv p
  let B := LinearMap.compl₁₂ (cliffordPairing p) e.symm.toLinearMap e.symm.toLinearMap
  have hgen (i : Fin 3) (v : C8 ℝ) :
      e.symm (epsilonAction p i v) = cliffordGenerator p i * e.symm v := by
    apply e.injective
    rw [LinearEquiv.apply_symm_apply]
    change _ = cliffordCoordinates p (cliffordGenerator p i * e.symm v)
    rw [cliffordCoordinates_generator_mul, ← cliffordCoordinateEquiv_apply]
    rw [show cliffordCoordinateEquiv p (e.symm v) = v from e.apply_symm_apply v]
  have hskew (i : Fin 3) (v w : C8 ℝ) :
      B v (epsilonAction p i w) = -B (epsilonAction p i v) w := by
    change cliffordPairing p (e.symm v) (e.symm (epsilonAction p i w)) =
      -cliffordPairing p (e.symm (epsilonAction p i v)) (e.symm w)
    rw [hgen, hgen, cliffordPairing_skew]
  have hone : e.symm one8 = 1 := by
    apply e.injective
    rw [LinearEquiv.apply_symm_apply]
    exact (cliffordCoordinates_one p).symm
  have hbase (w : C8 ℝ) : B one8 w = w 0 := by
    change cliffordPairing p (e.symm one8) (e.symm w) = w 0
    rw [hone, cliffordPairing_apply, cliffordConjugate_one, one_mul]
    exact congrFun (e.apply_symm_apply w) 0
  have hW := W_unique p B (hskew 0) (hskew 1) (hskew 2) hbase (e a) (e b)
  change cliffordPairing p (e.symm (e a)) (e.symm (e b)) = W p (e a) (e b) at hW
  rw [e.symm_apply_apply, e.symm_apply_apply] at hW
  simpa only [e, cliffordCoordinateEquiv_apply] using hW

theorem cliffordPairing_symm (a b : ComparisonClifford p) :
    cliffordPairing p a b = cliffordPairing p b a := by
  rw [cliffordPairing_eq_W, cliffordPairing_eq_W, W_symm]

theorem cliffordScalar_conjugate (a : ComparisonClifford p) :
    cliffordScalar p (cliffordConjugate p a) = cliffordScalar p a := by
  simpa only [cliffordPairing_apply, cliffordConjugate_one, mul_one, one_mul] using
    cliffordPairing_symm p a 1

end LemmaB
