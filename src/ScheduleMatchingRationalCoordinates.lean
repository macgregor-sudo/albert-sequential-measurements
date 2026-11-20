/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ScheduleMatchingRationalForm
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! The coordinate basis of the 15/12 eigenspaces and the 27-dimensional
rational form of Appendix C.5. -/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace AlbertSequential.MatchingModels

open FiveTest
open scoped Quaternion

/-- Diagonal coordinates, then upper slot, Cayley–Dickson component, and quaternion coordinate. -/
abbrev HorizonCoordinateIndex := Fin 3 ⊕ (Fin 3 × Fin 2 × Fin 4)

def horizonQuatCoordinate (q : Quaternion ℝ) (c : Fin 4) : ℝ :=
  ![q.re,q.imI,q.imJ,q.imK] c

def horizonOctCoordinate (o : Octonion) (h : Fin 2) (c : Fin 4) : ℝ :=
  ![horizonQuatCoordinate o.1 c, horizonQuatCoordinate o.2 c] h

def horizonAlbertCoordinate (x : Albert) : HorizonCoordinateIndex → ℝ
  | .inl i => x.1 i
  | .inr (i,h,c) => horizonOctCoordinate (x.2 i) h c

def horizonAlbertOfCoordinates (v : HorizonCoordinateIndex → ℝ) : Albert :=
  (fun i => v (.inl i), fun i =>
    (⟨v (.inr (i,0,0)), v (.inr (i,0,1)), v (.inr (i,0,2)), v (.inr (i,0,3))⟩,
     ⟨v (.inr (i,1,0)), v (.inr (i,1,1)), v (.inr (i,1,2)), v (.inr (i,1,3))⟩))

/-- The explicit real coordinate system used to count and scale the basis. -/
def horizonAlbertCoordinates : Albert ≃ₗ[ℝ] (HorizonCoordinateIndex → ℝ) where
  toFun := horizonAlbertCoordinate
  invFun := horizonAlbertOfCoordinates
  left_inv x := by
    apply Prod.ext
    · rfl
    · funext i
      apply Prod.ext <;> apply Quaternion.ext <;> rfl
  right_inv v := by
    funext i
    rcases i with i | ⟨i,h,c⟩
    · rfl
    · fin_cases h <;> fin_cases c <;> rfl
  map_add' x y := by
    funext i
    rcases i with i | ⟨i,h,c⟩
    · rfl
    · fin_cases h <;> fin_cases c <;> rfl
  map_smul' r x := by
    funext i
    rcases i with i | ⟨i,h,c⟩
    · rfl
    · fin_cases h <;> fin_cases c <;> rfl

/-- Odd entries are those where the quaternion conjugation sign and the D sign disagree. -/
def horizonOddCoordinate : HorizonCoordinateIndex → Bool
  | .inl _ => false
  | .inr (i,_,c) => Bool.xor (decide (i ≠ 1)) (decide (c = 1 ∨ c = 2))

/-- Beta is the diagonal sign map in these coordinates. -/
theorem horizonAlbertCoordinates_beta (x : Albert) (i : HorizonCoordinateIndex) :
    horizonAlbertCoordinates (horizonRationalBeta.linearEquiv x) i =
      if horizonOddCoordinate i then -horizonAlbertCoordinates x i else horizonAlbertCoordinates x i := by
  rw [horizonRationalBeta_apply]
  rcases i with i | ⟨s,h,c⟩
  · rfl
  · fin_cases s <;> fin_cases h <;> fin_cases c <;>
      simp [horizonAlbertCoordinates, horizonAlbertCoordinate, horizonOctCoordinate, horizonQuatCoordinate,
        horizonOddCoordinate, horizonGammaOct, horizonGammaOctEquiv, horizonGammaQuat] <;> try rfl
    all_goals
      change -(-(_ : ℝ)) = _
      simp

def horizonRatQuatCoordinate (q : QQ) (c : Fin 4) : ℚ :=
  ![q.re,q.i,q.j,q.k] c

def horizonRatOctCoordinate (o : QO) (h : Fin 2) (c : Fin 4) : ℚ :=
  ![horizonRatQuatCoordinate o.fst c, horizonRatQuatCoordinate o.snd c] h

def horizonRatAlbertCoordinate (x : QA) : HorizonCoordinateIndex → ℚ
  | .inl i => ![x.d0,x.d1,x.d2] i
  | .inr (i,h,c) => horizonRatOctCoordinate (![x.o0,x.o1,x.o2] i) h c

def horizonRatAlbertOfCoordinates (v : HorizonCoordinateIndex → ℚ) : QA :=
  let o (i : Fin 3) : QO :=
    ⟨⟨v (.inr (i,0,0)), v (.inr (i,0,1)), v (.inr (i,0,2)), v (.inr (i,0,3))⟩,
     ⟨v (.inr (i,1,0)), v (.inr (i,1,1)), v (.inr (i,1,2)), v (.inr (i,1,3))⟩⟩
  ⟨v (.inl 0), v (.inl 1), v (.inl 2), o 0, o 1, o 2⟩

theorem horizonAlbertCoordinates_castA (x : QA) (i : HorizonCoordinateIndex) :
    horizonAlbertCoordinates (castA x) i = (horizonRatAlbertCoordinate x i : ℝ) := by
  rcases i with i | ⟨s,h,c⟩
  · fin_cases i <;> rfl
  · fin_cases s <;> fin_cases h <;> fin_cases c <;> rfl

theorem horizonRatAlbertCoordinate_ofCoordinates (v : HorizonCoordinateIndex → ℚ)
    (i : HorizonCoordinateIndex) :
    horizonRatAlbertCoordinate (horizonRatAlbertOfCoordinates v) i = v i := by
  rcases i with i | ⟨s,h,c⟩
  · fin_cases i <;> rfl
  · fin_cases s <;> fin_cases h <;> fin_cases c <;> rfl

/-- The rational-coordinate subspace supported on one beta parity. -/
def horizonParityCoordinates (odd : Bool) : Submodule ℚ (HorizonCoordinateIndex → ℚ) where
  carrier := {v | ∀ i, horizonOddCoordinate i ≠ odd → v i = 0}
  zero_mem' := by intro i _; rfl
  add_mem' := by
    intro v w hv hw i hi
    change v i + w i = 0
    rw [hv i hi, hw i hi, add_zero]
  smul_mem' := by
    intro a v hv i hi
    change a * v i = 0
    rw [hv i hi, mul_zero]

def horizonParityCoordinateEquiv (odd : Bool) :
    horizonParityCoordinates odd ≃ₗ[ℚ] ({i // horizonOddCoordinate i = odd} → ℚ) where
  toFun v i := v.1 i.1
  invFun v := ⟨fun i => if h : horizonOddCoordinate i = odd then v ⟨i,h⟩ else 0,
    by intro i hi; simp [hi]⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    by_cases h : horizonOddCoordinate i = odd
    · simp [h]
    · simp [h, v.2 i h]
  right_inv v := by
    funext i
    simp [i.2]
  map_add' v w := rfl
  map_smul' a v := rfl

private theorem horizonParity_coordinate_zero {odd : Bool} {x : Albert}
    (h : horizonRationalBeta.linearEquiv x = if odd then -x else x)
    (i : HorizonCoordinateIndex) (hi : horizonOddCoordinate i ≠ odd) :
    horizonAlbertCoordinates x i = 0 := by
  have hb := congrArg (fun y => horizonAlbertCoordinates y i) h
  change horizonAlbertCoordinates (horizonRationalBeta.linearEquiv x) i =
    horizonAlbertCoordinates (if odd then -x else x) i at hb
  rw [horizonAlbertCoordinates_beta] at hb
  cases odd <;> cases ho : horizonOddCoordinate i <;> simp [ho] at hi hb <;> linarith

/-- These coordinate subspaces are exactly the paper's rational-coordinate eigenspaces. -/
theorem horizonRationalParity_iff_coordinates (odd : Bool) (x : Albert) :
    horizonRationalParity odd x ↔ ∃ v : horizonParityCoordinates odd,
      ∀ i, horizonAlbertCoordinates x i = (v.1 i : ℝ) := by
  constructor
  · intro hx
    obtain ⟨q,hq⟩ := hx.1
    refine ⟨⟨horizonRatAlbertCoordinate q, ?_⟩, ?_⟩
    · intro i hi
      have hz := horizonParity_coordinate_zero hx.2 i hi
      rw [← hq, horizonAlbertCoordinates_castA] at hz
      exact_mod_cast hz
    · intro i
      change horizonAlbertCoordinates x i = (horizonRatAlbertCoordinate q i : ℝ)
      rw [← hq]
      exact horizonAlbertCoordinates_castA q i
  · rintro ⟨v,hv⟩
    constructor
    · refine ⟨horizonRatAlbertOfCoordinates v.1, horizonAlbertCoordinates.injective ?_⟩
      funext i
      rw [horizonAlbertCoordinates_castA, horizonRatAlbertCoordinate_ofCoordinates, hv]
    · apply horizonAlbertCoordinates.injective
      funext i
      rw [horizonAlbertCoordinates_beta]
      by_cases hi : horizonOddCoordinate i = odd
      · rw [hi]
        cases odd <;> simp
      · have hz : horizonAlbertCoordinates x i = 0 := by rw [hv, v.2 i hi]; simp
        cases odd <;> cases h : horizonOddCoordinate i <;> simp [hz]

/-- The exact rational dimensions of the beta fixed and anti-fixed coordinate spaces. -/
theorem horizonRationalParity_dimensions :
    Module.finrank ℚ (horizonParityCoordinates false) = 15 ∧
      Module.finrank ℚ (horizonParityCoordinates true) = 12 := by
  constructor
  · rw [(horizonParityCoordinateEquiv false).finrank_eq, Module.finrank_pi_fintype]
    simp only [CommSemiring.finrank_self, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    decide +kernel
  · rw [(horizonParityCoordinateEquiv true).finrank_eq, Module.finrank_pi_fintype]
    simp only [CommSemiring.finrank_self, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    decide +kernel

def horizonTwistScale (i : HorizonCoordinateIndex) : ℝ :=
  if horizonOddCoordinate i then Real.sqrt 2 else 1

theorem horizonTwistScale_ne_zero (i : HorizonCoordinateIndex) : horizonTwistScale i ≠ 0 := by
  cases h : horizonOddCoordinate i <;> simp [horizonTwistScale, h]

/-- The coordinate embedding of the rational form multiplies odd coordinates by √2. -/
def horizonTwistedCoordinates : (HorizonCoordinateIndex → ℚ) →ₗ[ℚ] (HorizonCoordinateIndex → ℝ) where
  toFun v i := horizonTwistScale i * (v i : ℝ)
  map_add' v w := by
    funext i
    change horizonTwistScale i * ((v i + w i : ℚ) : ℝ) =
      horizonTwistScale i * (v i : ℝ) + horizonTwistScale i * (w i : ℝ)
    rw [Rat.cast_add, mul_add]
  map_smul' a v := by
    funext i
    change horizonTwistScale i * ((a * v i : ℚ) : ℝ) =
      (a : ℝ) * (horizonTwistScale i * (v i : ℝ))
    rw [Rat.cast_mul]
    ring

theorem horizonTwistedCoordinates_injective : Function.Injective horizonTwistedCoordinates := by
  intro v w h
  funext i
  have h' := congrFun h i
  change horizonTwistScale i * (v i : ℝ) = horizonTwistScale i * (w i : ℝ) at h'
  have he := mul_left_cancel₀ (horizonTwistScale_ne_zero i) h'
  exact_mod_cast he

theorem horizonRationalForm_iff_coordinates (x : Albert) :
    horizonRationalForm x ↔ horizonAlbertCoordinates x ∈ horizonTwistedCoordinates.range := by
  constructor
  · rintro ⟨u,v,hu,hv,rfl⟩
    obtain ⟨a,ha⟩ := (horizonRationalParity_iff_coordinates false u).mp hu
    obtain ⟨b,hb⟩ := (horizonRationalParity_iff_coordinates true v).mp hv
    refine ⟨fun i => if horizonOddCoordinate i then b.1 i else a.1 i, ?_⟩
    funext i
    rw [map_add, map_smul, Pi.add_apply, Pi.smul_apply, ha, hb]
    cases ho : horizonOddCoordinate i
    · have hz := b.2 i (by simp [ho])
      change horizonTwistScale i * ((if horizonOddCoordinate i then b.1 i else a.1 i : ℚ) : ℝ) = _
      simp [horizonTwistScale, ho, hz]
    · have hz := a.2 i (by simp [ho])
      change horizonTwistScale i * ((if horizonOddCoordinate i then b.1 i else a.1 i : ℚ) : ℝ) = _
      simp [horizonTwistScale, ho, hz]
  · rintro ⟨v,hv⟩
    let a : horizonParityCoordinates false :=
      ⟨fun i => if horizonOddCoordinate i then 0 else v i, by
        intro i hi
        change (if horizonOddCoordinate i then 0 else v i) = 0
        cases ho : horizonOddCoordinate i <;> simp [ho] at hi ⊢⟩
    let b : horizonParityCoordinates true :=
      ⟨fun i => if horizonOddCoordinate i then v i else 0, by
        intro i hi
        change (if horizonOddCoordinate i then v i else 0) = 0
        cases ho : horizonOddCoordinate i <;> simp [ho] at hi ⊢⟩
    let u := castA (horizonRatAlbertOfCoordinates a.1)
    let y := castA (horizonRatAlbertOfCoordinates b.1)
    have hu (i : HorizonCoordinateIndex) : horizonAlbertCoordinates u i = (a.1 i : ℝ) := by
      dsimp only [u]
      rw [horizonAlbertCoordinates_castA, horizonRatAlbertCoordinate_ofCoordinates]
    have hy (i : HorizonCoordinateIndex) : horizonAlbertCoordinates y i = (b.1 i : ℝ) := by
      dsimp only [y]
      rw [horizonAlbertCoordinates_castA, horizonRatAlbertCoordinate_ofCoordinates]
    refine ⟨u,y,(horizonRationalParity_iff_coordinates false u).2 ⟨a,hu⟩,
      (horizonRationalParity_iff_coordinates true y).2 ⟨b,hy⟩, ?_⟩
    apply horizonAlbertCoordinates.injective
    funext i
    rw [← hv, map_add, map_smul, Pi.add_apply, Pi.smul_apply, hu, hy]
    change ((a.1 i : ℚ) : ℝ) + Real.sqrt 2 • ((b.1 i : ℚ) : ℝ) =
      horizonTwistScale i * (v i : ℝ)
    cases ho : horizonOddCoordinate i <;> simp [a,b,horizonTwistScale,ho]

/-- The exact dimension of the twisted rational form in native coordinates. -/
theorem horizonRationalForm_dimension : Module.finrank ℚ horizonTwistedCoordinates.range = 27 := by
  rw [← (LinearEquiv.ofInjective horizonTwistedCoordinates horizonTwistedCoordinates_injective).finrank_eq,
    Module.finrank_pi_fintype]
  simp only [CommSemiring.finrank_self, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  decide +kernel

/-- The real extension of the twisted coordinate basis is invertible. -/
def horizonRealTwist : (HorizonCoordinateIndex → ℝ) ≃ₗ[ℝ] (HorizonCoordinateIndex → ℝ) where
  toFun v i := horizonTwistScale i * v i
  invFun v i := (horizonTwistScale i)⁻¹ * v i
  left_inv v := by
    funext i
    simp only [← mul_assoc, inv_mul_cancel₀ (horizonTwistScale_ne_zero i), one_mul]
  right_inv v := by
    funext i
    simp only [← mul_assoc, mul_inv_cancel₀ (horizonTwistScale_ne_zero i), one_mul]
  map_add' v w := by funext i; exact mul_add _ _ _
  map_smul' r v := by funext i; change _ * (r * _) = r * (_ * _); ring

/-- Every element of the rational form has rational coordinates in the basis
obtained by scaling the odd native coordinate axes by √2. -/
theorem horizonRationalForm_twisted_coordinate_values {x : Albert} (hx : horizonRationalForm x) :
    ∃ v : HorizonCoordinateIndex → ℚ,
      horizonRealTwist.symm (horizonAlbertCoordinates x) = fun i => (v i : ℝ) := by
  obtain ⟨v,hv⟩ := (horizonRationalForm_iff_coordinates x).mp hx
  refine ⟨v, ?_⟩
  apply horizonRealTwist.injective
  rw [LinearEquiv.apply_symm_apply]
  exact hv.symm

/-- The even-plus-scaled-odd representation has a unique pair of rational parts. -/
theorem horizonRationalForm_decomposition_unique {u v x y : Albert}
    (hu : horizonRationalParity false u) (hv : horizonRationalParity true v)
    (hx : horizonRationalParity false x) (hy : horizonRationalParity true y)
    (h : u + Real.sqrt 2 • v = x + Real.sqrt 2 • y) :
    u = x ∧ v = y := by
  constructor
  · apply horizonAlbertCoordinates.injective
    funext i
    cases hi : horizonOddCoordinate i
    · have hv0 := horizonParity_coordinate_zero hv.2 i (by simp [hi])
      have hy0 := horizonParity_coordinate_zero hy.2 i (by simp [hi])
      have he := congrArg (fun z => horizonAlbertCoordinates z i) h
      simpa [hv0, hy0] using he
    · rw [horizonParity_coordinate_zero hu.2 i (by simp [hi]),
        horizonParity_coordinate_zero hx.2 i (by simp [hi])]
  · apply horizonAlbertCoordinates.injective
    funext i
    cases hi : horizonOddCoordinate i
    · rw [horizonParity_coordinate_zero hv.2 i (by simp [hi]),
        horizonParity_coordinate_zero hy.2 i (by simp [hi])]
    · have hu0 := horizonParity_coordinate_zero hu.2 i (by simp [hi])
      have hx0 := horizonParity_coordinate_zero hx.2 i (by simp [hi])
      have he := congrArg (fun z => horizonAlbertCoordinates z i) h
      apply mul_left_cancel₀ (show Real.sqrt 2 ≠ 0 by positivity)
      simpa [hu0, hx0] using he

/-- A real basis whose rational span is the prescribed twist. -/
def horizonRationalBasis : Module.Basis HorizonCoordinateIndex ℝ Albert :=
  (Pi.basisFun ℝ HorizonCoordinateIndex).map (horizonRealTwist.trans horizonAlbertCoordinates.symm)

theorem horizonRationalBasis_mem (i : HorizonCoordinateIndex) :
    horizonRationalForm (horizonRationalBasis i) := by
  apply (horizonRationalForm_iff_coordinates _).2
  refine ⟨Pi.single i 1, ?_⟩
  rw [horizonRationalBasis, Module.Basis.map_apply, LinearEquiv.trans_apply,
    horizonAlbertCoordinates.apply_symm_apply, Pi.basisFun_apply]
  funext j
  change horizonTwistScale j * (((Pi.single i (1 : ℚ) : HorizonCoordinateIndex → ℚ) j : ℚ) : ℝ) =
    horizonTwistScale j * (Pi.single i (1 : ℝ) : HorizonCoordinateIndex → ℝ) j
  by_cases hij : j = i <;> simp [hij]

theorem horizonRationalBasis_multiplication_coefficients (i j : HorizonCoordinateIndex) :
    ∃ v : HorizonCoordinateIndex → ℚ, horizonRealTwist.symm (horizonAlbertCoordinates
      (jordanMul (horizonRationalBasis i) (horizonRationalBasis j))) = fun k => (v k : ℝ) :=
  horizonRationalForm_twisted_coordinate_values
    (horizonRationalForm_jordan (horizonRationalBasis_mem i) (horizonRationalBasis_mem j))

theorem horizonRationalBasis_quadratic_coefficients {x : Albert} (hx : horizonRationalForm x)
    (j : HorizonCoordinateIndex) :
    ∃ v : HorizonCoordinateIndex → ℚ, horizonRealTwist.symm (horizonAlbertCoordinates
      (quadraticMap x (horizonRationalBasis j))) = fun k => (v k : ℝ) :=
  horizonRationalForm_twisted_coordinate_values (horizonRationalForm_quadratic hx (horizonRationalBasis_mem j))

/-- The standard coordinates of M lie in the real quadratic extension Q(√2). -/
def horizonMOriginalEntryField : IntermediateField ℚ ℝ :=
  IntermediateField.adjoin ℚ {Real.sqrt 2}

theorem horizon_M_original_coordinate_field (i : Fin 4) (j : HorizonCoordinateIndex) :
    horizonAlbertCoordinates (maximizerConfig i) j ∈ horizonMOriginalEntryField := by
  obtain ⟨v,hv⟩ := (horizonRationalForm_iff_coordinates _).mp (horizonMRational_atoms i)
  rw [← congrFun hv j]
  change horizonTwistScale j * (v j : ℝ) ∈ horizonMOriginalEntryField
  apply horizonMOriginalEntryField.mul_mem
  · cases ho : horizonOddCoordinate j
    · simp [horizonTwistScale, ho]
    · unfold horizonTwistScale
      rw [ho]
      exact IntermediateField.mem_adjoin_of_mem ℚ (S := {Real.sqrt 2}) (by simp)
  · exact SubfieldClass.ratCast_mem horizonMOriginalEntryField (v j)

/-- In the standard basis the B upper-slot real coordinate is irrational. -/
theorem horizon_M_B_not_original_rational : ¬ horizonRationalCoordinates (maximizerConfig 1) := by
  rintro ⟨q,hq⟩
  let j : HorizonCoordinateIndex := .inr (0,0,0)
  have ha : horizonAlbertCoordinates (maximizerConfig 1) j = Real.sqrt 2 / 3 := by
    rw [horizonMRational_coordinate_binding, map_add, map_smul, Pi.add_apply, Pi.smul_apply,
      horizonAlbertCoordinates_castA, horizonAlbertCoordinates_castA]
    change (((0 : ℚ) : ℝ) + Real.sqrt 2 • (((1/3 : ℚ)) : ℝ)) = _
    norm_num [smul_eq_mul, div_eq_mul_inv]
  have hi := irrational_sqrt_two.div_ratCast (show (3 : ℚ) ≠ 0 by norm_num)
  apply hi
  refine ⟨horizonRatAlbertCoordinate q j, ?_⟩
  rw [← horizonAlbertCoordinates_castA, hq, ha]
  norm_num

end AlbertSequential.MatchingModels
