/- SPDX-License-Identifier: Apache-2.0 -/
module
public import AppF.Shestakov
public import NativeTraceRiesz
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.LinearAlgebra.Multilinear.Basic

set_option autoImplicit false
set_option maxRecDepth 4000
@[expose] public section
noncomputable section

namespace AlbertSequential.AppF

open scoped BigOperators
open MvPolynomial

/-- The exponent vector of the coefficient in the printed formula for F. -/
def glennieCoefficientExponent : Fin 3 →₀ ℕ :=
  ∑ j : Fin 3, Finsupp.single j 2

@[simp] theorem glennieCoefficientExponent_apply (j : Fin 3) :
    glennieCoefficientExponent j = 2 := by
  fin_cases j <;> simp [glennieCoefficientExponent,Fin.sum_univ_three,Finsupp.add_apply]

private theorem Dop_add_first (y z : Albert) (u v : Albert) :
    Dop nativeOps (u + v) y z = Dop nativeOps u y z + Dop nativeOps v y z := by
  simp only [Dop,four,nativeOps,jordanMul_add_left,jordanMul_add_right]
  abel

private theorem Dop_smul_first (y z : Albert) (r : ℝ) (u : Albert) :
    Dop nativeOps (r • u) y z = r • Dop nativeOps u y z := by
  simp only [Dop,four,nativeOps,jordanMul_smul_left,jordanMul_smul_right,← smul_add,← smul_sub]

private theorem Dop_add_second (x z : Albert) (u v : Albert) :
    Dop nativeOps x (u + v) z = Dop nativeOps x u z + Dop nativeOps x v z := by
  simp only [Dop,four,nativeOps,jordanMul_add_left,jordanMul_add_right]
  abel

private theorem Dop_smul_second (x z : Albert) (r : ℝ) (u : Albert) :
    Dop nativeOps x (r • u) z = r • Dop nativeOps x u z := by
  simp only [Dop,four,nativeOps,jordanMul_smul_left,jordanMul_smul_right,← smul_add,← smul_sub]

private theorem Dop_add_last (x y : Albert) (u v : Albert) :
    Dop nativeOps x y (u + v) = Dop nativeOps x y u + Dop nativeOps x y v := by
  simp only [Dop,four,nativeOps,jordanMul_add_right]
  abel

private theorem Dop_smul_last (x y : Albert) (r : ℝ) (u : Albert) :
    Dop nativeOps x y (r • u) = r • Dop nativeOps x y u := by
  simp only [Dop,four,nativeOps,jordanMul_smul_right,← smul_add,← smul_sub]

private theorem Dop_sub_last (x y : Albert) (u v : Albert) :
    Dop nativeOps x y (u - v) = Dop nativeOps x y u - Dop nativeOps x y v := by
  simp only [Dop,four,nativeOps,jordanMul_sub_right]
  abel

private theorem Upol_add_first (y z : Albert) (u v : Albert) :
    Upol nativeOps (u + v) y z = Upol nativeOps u y z + Upol nativeOps v y z := by
  simp only [Upol,nativeOps,jordanMul_add_left,jordanMul_add_right]
  abel

private theorem Upol_smul_first (y z : Albert) (r : ℝ) (u : Albert) :
    Upol nativeOps (r • u) y z = r • Upol nativeOps u y z := by
  simp only [Upol,nativeOps,jordanMul_smul_left,jordanMul_smul_right,← smul_add,← smul_sub]

private theorem Upol_add_second (x z : Albert) (u v : Albert) :
    Upol nativeOps x (u + v) z = Upol nativeOps x u z + Upol nativeOps x v z := by
  simp only [Upol,nativeOps,jordanMul_add_left,jordanMul_add_right]
  abel

private theorem Upol_smul_second (x z : Albert) (r : ℝ) (u : Albert) :
    Upol nativeOps x (r • u) z = r • Upol nativeOps x u z := by
  simp only [Upol,nativeOps,jordanMul_smul_left,jordanMul_smul_right,← smul_add,← smul_sub]

private theorem Upol_add_last (x y : Albert) (u v : Albert) :
    Upol nativeOps x y (u + v) = Upol nativeOps x y u + Upol nativeOps x y v := by
  simp only [Upol,nativeOps,jordanMul_add_right]
  abel

private theorem Upol_smul_last (x y : Albert) (r : ℝ) (u : Albert) :
    Upol nativeOps x y (r • u) = r • Upol nativeOps x y u := by
  simp only [Upol,nativeOps,jordanMul_smul_right,← smul_add,← smul_sub]

private theorem nativePhi_decomp (x₁ x₂ x₃ y₁ y₂ y₃ z : Albert) :
    Phi nativeOps x₁ x₂ x₃ y₁ y₂ y₃ z =
      Dop nativeOps x₁ y₁ (Dop nativeOps x₂ y₂ (Dop nativeOps x₃ y₃ z)) +
        (3 : ℝ) • Dop nativeOps x₁ y₁ (Ubr nativeOps x₂ x₃ y₂ y₃ z) := by
  simp only [Phi,three,nativeOps]
  module

private theorem nativeUbr_decomp (a b c d z : Albert) :
    Ubr nativeOps a b c d z =
      (4 : ℝ) • Upol nativeOps (jordanMul a c) (jordanMul b d) z -
        (2 : ℝ) • (Upol nativeOps a b (Upol nativeOps c d z) +
          Upol nativeOps c d (Upol nativeOps a b z)) := by
  simp only [Ubr,four,two,nativeOps]
  module

private theorem nativeGlennieTerm_decomp (d a b c x y z : Albert) :
    glennieTerm nativeOps d a b c x y z =
      Phi nativeOps a b c x y z (jordanMul d d) -
        (2 : ℝ) • jordanMul d (Phi nativeOps a b c x y z d) := by
  simp only [glennieTerm,two,nativeOps]
  module

set_option maxHeartbeats 1500000 in
set_option linter.unusedSimpArgs false in
/-- The three x slots precede the three y slots. The last input d is fixed. -/
def glennieMultilinear (d : Albert) : MultilinearMap (RingHom.id ℝ) (fun _ : Fin 6 => Albert) Albert :=
  MultilinearMap.mk'
    (fun m => glennieTerm nativeOps d (m 0) (m 1) (m 2) (m 3) (m 4) (m 5))
    (by
      intro m i u v
      fin_cases i <;> simp (disch := decide) only [Function.update_apply,ite_eq_left,ite_eq_right]
      all_goals
        simp only [nativeGlennieTerm_decomp,nativePhi_decomp,nativeUbr_decomp,
          Dop_add_first,Dop_add_second,Dop_add_last,Dop_sub_last,Upol_add_first,Upol_add_second,Upol_add_last,
          jordanMul_add_left,jordanMul_add_right,jordanMul_sub_right,smul_add,smul_sub]
        module)
    (by
      intro m i r u
      fin_cases i <;> simp (disch := decide) only [Function.update_apply,ite_eq_left,ite_eq_right,RingHom.id_apply]
      all_goals
        simp only [nativeGlennieTerm_decomp,nativePhi_decomp,nativeUbr_decomp,
          Dop_smul_first,Dop_smul_second,Dop_smul_last,Upol_smul_first,Upol_smul_second,Upol_smul_last,
          jordanMul_smul_left,jordanMul_smul_right,
          ← smul_comm r (2 : ℝ),← smul_comm r (3 : ℝ),← smul_comm r (4 : ℝ),← smul_add,← smul_sub])

/-- Variable 0 is s, variable 1 is t, and variable 2 is u. A true
placement selects s and a in either set of slots. -/
def glennieSlotVariable (k : Fin 6) (same : Bool) : Fin 3 :=
  if same then 0 else if k.val < 3 then 1 else 2

def glennieSlotArgument (a b c : Albert) (k : Fin 6) (same : Bool) : Albert :=
  if same then a else if k.val < 3 then b else c

def glenniePlacementExponent (placement : Fin 6 → Bool) : Fin 3 →₀ ℕ :=
  ∑ k : Fin 6, Finsupp.single (glennieSlotVariable k (placement k)) 1

/-- Scalar polynomial obtained from the literal native Shestakov expression
by an arbitrary real-linear readout. -/
def nativePsiPolynomial (f : Albert →ₗ[ℝ] ℝ) (a b c d : Albert) : MvPolynomial (Fin 3) ℝ :=
  ∑ placement : Fin 6 → Bool,
    monomial (glenniePlacementExponent placement)
      (f (glennieMultilinear d (fun k => glennieSlotArgument a b c k (placement k))))

theorem eval_nativePsiPolynomial (f : Albert →ₗ[ℝ] ℝ) (a b c d : Albert) (v : Fin 3 → ℝ) :
    eval v (nativePsiPolynomial f a b c d) =
      f (nativePsi (v 0 • a + v 1 • b) (v 0 • a + v 2 • c) d) := by
  let m (k : Fin 6) (choice : Bool) := v (glennieSlotVariable k choice) • glennieSlotArgument a b c k choice
  have hdiag : nativePsi (v 0 • a + v 1 • b) (v 0 • a + v 2 • c) d =
      glennieMultilinear d (fun k => ∑ b : Bool, m k b) := by
    simp [nativePsi,psi,glennieMultilinear,glennieTerm,Phi_diag,m,glennieSlotVariable,
      glennieSlotArgument]
  rw [hdiag,(glennieMultilinear d).map_sum m,map_sum,nativePsiPolynomial,map_sum]
  apply Finset.sum_congr rfl
  intro placement _
  change eval v (monomial (glenniePlacementExponent placement)
      (f (glennieMultilinear d (fun k => glennieSlotArgument a b c k (placement k))))) =
    f (glennieMultilinear d (fun k => v (glennieSlotVariable k (placement k)) •
      glennieSlotArgument a b c k (placement k)))
  rw [(glennieMultilinear d).map_smul_univ,map_smul,glenniePlacementExponent,monomial_sum_index]
  simp [map_prod,← X_pow_eq_monomial,mul_comm]

/-- There is exactly one polynomial realizing the native expression after
each linear readout. -/
theorem nativePsiPolynomial_unique (f : Albert →ₗ[ℝ] ℝ) (a b c d : Albert)
    (g : MvPolynomial (Fin 3) ℝ)
    (h : ∀ v : Fin 3 → ℝ,
      eval v g = f (nativePsi (v 0 • a + v 1 • b) (v 0 • a + v 2 • c) d)) :
    g = nativePsiPolynomial f a b c d := by
  apply MvPolynomial.funext
  intro v
  exact (h v).trans (eval_nativePsiPolynomial f a b c d v).symm

private def survivingPlacements : Finset (Fin 6 → Bool) := {
  ![true,false,false,true,false,false], ![true,false,false,false,true,false],
  ![true,false,false,false,false,true], ![false,true,false,true,false,false],
  ![false,true,false,false,true,false], ![false,true,false,false,false,true],
  ![false,false,true,true,false,false], ![false,false,true,false,true,false],
  ![false,false,true,false,false,true] }

private def countSelections (placement : Fin 6 → Bool) (j : Fin 3) : ℕ :=
  ∑ k : Fin 6, if glennieSlotVariable k (placement k) = j then 1 else 0

private theorem placementExponent_apply (placement : Fin 6 → Bool) (j : Fin 3) :
    glenniePlacementExponent placement j = countSelections placement j := by
  simp only [glenniePlacementExponent,countSelections,Fin.sum_univ_six,Finsupp.add_apply,Finsupp.single_apply]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem filter_placements :
    (Finset.univ.filter fun placement : Fin 6 → Bool => glenniePlacementExponent placement = glennieCoefficientExponent)
      = survivingPlacements := by
  have he (placement : Fin 6 → Bool) :
      glenniePlacementExponent placement = glennieCoefficientExponent ↔
        countSelections placement 0 = 2 ∧ countSelections placement 1 = 2 ∧ countSelections placement 2 = 2 := by
    rw [DFunLike.ext_iff]
    simp only [placementExponent_apply,glennieCoefficientExponent_apply]
    constructor
    · exact fun h => ⟨h 0,h 1,h 2⟩
    · rintro ⟨h₀,h₁,h₂⟩ j
      fin_cases j <;> assumption
  simp_rw [he]
  decide +kernel

/-- The literal multivariate coefficient is the readout of the native
nine-placement Glennie value, for all four Albert inputs. -/
theorem coeff_nativePsiPolynomial (f : Albert →ₗ[ℝ] ℝ) (a b c d : Albert) :
    (nativePsiPolynomial f a b c d).coeff glennieCoefficientExponent =
      f (nativeGlennieF a b c d) := by
  rw [nativePsiPolynomial,coeff_sum]
  simp only [coeff_monomial]
  rw [← Finset.sum_filter,filter_placements,← map_sum]
  congr 1
  simp [survivingPlacements,glennieMultilinear,glennieSlotArgument,nativeGlennieF,glennieF,nativeOps]
  abel

/-- The scalar coefficient statement is independent of the chosen polynomial
presentation of the literal substitution. -/
theorem coeff_eq_nativeGlennieF_of_eval (f : Albert →ₗ[ℝ] ℝ) (a b c d : Albert)
    (g : MvPolynomial (Fin 3) ℝ)
    (h : ∀ v : Fin 3 → ℝ,
      eval v g = f (nativePsi (v 0 • a + v 1 • b) (v 0 • a + v 2 • c) d)) :
    g.coeff glennieCoefficientExponent = f (nativeGlennieF a b c d) := by
  rw [nativePsiPolynomial_unique f a b c d g h,coeff_nativePsiPolynomial]

/-- All real-linear coefficient tests determine one literal Albert vector. -/
theorem existsUnique_nativePsiCoefficient (a b c d : Albert) :
    ∃! F : Albert, ∀ f : Albert →ₗ[ℝ] ℝ,
      (nativePsiPolynomial f a b c d).coeff glennieCoefficientExponent = f F := by
  refine ⟨nativeGlennieF a b c d,fun f => coeff_nativePsiPolynomial f a b c d,?_⟩
  intro F hF
  let q := F - nativeGlennieF a b c d
  let f := NativeAnalysis.tracePairingFunctional q
  have heq := (hF f).symm.trans (coeff_nativePsiPolynomial f a b c d)
  have hq : tracePairing q q = 0 := by
    change f q = 0
    change f (F - nativeGlennieF a b c d) = 0
    rw [map_sub,heq,sub_self]
  exact sub_eq_zero.mp ((NativeAnalysis.tracePairing_self_eq_zero q).mp hq)

end AlbertSequential.AppF
