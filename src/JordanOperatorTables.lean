/- SPDX-License-Identifier: Apache-2.0 -/
module
public import JordanTableMixtures

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace AlbertSequential
open scoped InnerProductSpace BigOperators

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "A" => HilbertOperatorAlgebra ℂ H

def selfAdjointJordanMul (x y : selfAdjoint A) : selfAdjoint A :=
  ⟨(1/2 : ℝ) • (x.val*y.val+y.val*x.val), by
    change star ((1/2 : ℝ) • (x.val*y.val+y.val*x.val)) = _
    rw [star_smul,star_add,star_mul,star_mul,x.property,y.property,add_comm]
    rfl⟩

/-- The real Jordan product of the actual complex self-adjoint operators. -/
def selfAdjointOperatorJordanProduct : UnitalJordanProduct (selfAdjoint A) where
  product := LinearMap.mk₂ ℝ selfAdjointJordanMul
    (by intros; apply Subtype.ext; dsimp [selfAdjointJordanMul]; simp only [add_mul,mul_add]; module)
    (by intros; apply Subtype.ext; dsimp [selfAdjointJordanMul]; simp only [smul_mul_assoc,mul_smul_comm,smul_add,smul_smul]; module)
    (by intros; apply Subtype.ext; dsimp [selfAdjointJordanMul]; simp only [add_mul,mul_add]; module)
    (by intros; apply Subtype.ext; dsimp [selfAdjointJordanMul]; simp only [smul_mul_assoc,mul_smul_comm,smul_add,smul_smul]; module)
  unit := 1
  commutative x y := Subtype.ext (by change (1/2 : ℝ) • (_+_) = (1/2 : ℝ) • (_+_); rw [add_comm])
  unit_left x := Subtype.ext (by change (1/2 : ℝ) • (1*x.val+x.val*1) = x.val; rw [one_mul,mul_one]; module)
  jordan_identity x y := by
    apply Subtype.ext
    change (selfAdjointJordanMul (selfAdjointJordanMul x y) (selfAdjointJordanMul x x)).val =
      (selfAdjointJordanMul x (selfAdjointJordanMul y (selfAdjointJordanMul x x))).val
    dsimp only [selfAdjointJordanMul]
    simp only [smul_mul_assoc,mul_smul_comm,add_mul,mul_add,smul_add,smul_smul,mul_assoc]
    abel

private theorem selfAdjointOperatorJordan_square (T : selfAdjoint A) :
    ((selfAdjointOperatorJordanProduct (H := H)).product T T).val = star T.val*T.val := by
  change (1/2 : ℝ) • (T.val*T.val+T.val*T.val) = star T.val*T.val
  rw [T.property]
  module

def selfAdjointOperatorInclusion : selfAdjoint A →ₗ[ℝ] A where
  toFun T := T.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem selfAdjointOperatorInclusion_apply (T : selfAdjoint A) :
    selfAdjointOperatorInclusion T = T.val := rfl

theorem selfAdjointOperatorJordan_formallyReal :
    (selfAdjointOperatorJordanProduct (H := H)).FormallyReal := by
  intro n X h i
  apply Subtype.ext
  apply (operatorValue ℂ H).injective
  ext v
  have hs : ∑ k, star (X k).val * (X k).val = 0 := by
    have h' := congrArg (selfAdjointOperatorInclusion (H := H)) h
    rw [map_sum,map_zero] at h'
    simpa only [selfAdjointOperatorInclusion_apply,selfAdjointOperatorJordan_square] using h'
  let T (k : Fin n) := operatorValue ℂ H (X k).val
  have hzero : ∑ k, inner ℂ (T k v) (T k v) = 0 := by
    rw [← inner_zero_right (𝕜 := ℂ) (x := v)]
    have he := congrArg (fun S : A => inner ℂ v ((operatorValue ℂ H S) v)) hs
    simpa only [map_sum,map_zero,sum_apply,zero_apply,
      inner_sum,operatorValue_mul_apply,operatorValue_star,T,
      ContinuousLinearMap.adjoint_inner_right] using he
  have hr : ∑ k, ‖T k v‖ ^ 2 = 0 := by
    have h := congrArg Complex.re hzero
    rw [Complex.re_sum,Complex.zero_re] at h
    convert h using 1
    apply Finset.sum_congr rfl
    intro k _
    rw [inner_self_eq_norm_sq_to_K]
    change ‖T k v‖ ^ 2 = (Complex.ofReal ‖T k v‖ ^ 2).re
    rw [← Complex.ofReal_pow,Complex.ofReal_re]
  have hi := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => sq_nonneg ‖T k v‖).mp hr i (Finset.mem_univ i)
  change T i v = 0
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hi)

private theorem selfAdjointOperatorJordan_quadratic (q x : selfAdjoint A) :
    ((selfAdjointOperatorJordanProduct (H := H)).quadraticRepresentation q x).val =
      q.val*x.val*q.val := by
  simp only [UnitalJordanProduct.quadraticRepresentation_apply]
  change (2 : ℝ) • (selfAdjointJordanMul q (selfAdjointJordanMul q x)).val -
    (selfAdjointJordanMul (selfAdjointJordanMul q q) x).val = _
  apply sub_eq_iff_eq_add.mpr
  dsimp only [selfAdjointJordanMul]
  simp only [smul_mul_assoc,mul_smul_comm,add_mul,mul_add,smul_add,smul_smul,mul_assoc]
  module

private theorem hilbert_effect_value {n : ℕ} (M : HilbertProjectiveData (Fin n) ℂ H)
    (p : Fin n → selfAdjoint A) (hp : ∀ i, (p i).val = M.projection i) (w : Word (Fin n)) :
    ((selfAdjointOperatorJordanProduct (H := H)).sequentialWordEffect p w).val =
      wordOperator M.projection w := by
  induction w with
  | nil => simp [UnitalJordanProduct.sequentialWordEffect,wordOperator_nil,selfAdjointOperatorJordanProduct]
  | cons a v ih =>
    rw [UnitalJordanProduct.sequentialWordEffect,selfAdjointOperatorJordan_quadratic,ih,
      wordOperator_cons M.projection (fun i => (M.isStarProjection i).isSelfAdjoint)]
    have hout :
        ((selfAdjointOperatorJordanProduct (H := H)).sequentialOutcome p a).val =
          algebraicOutcome M.projection a := by
      rcases a with ⟨i,b⟩
      cases b <;> simp [UnitalJordanProduct.sequentialOutcome, algebraicOutcome, hp, selfAdjointOperatorJordanProduct]
    rw [hout]

/-- A complex finite-dimensional class-(I) table is a Jordan table through
the actual self-adjoint operator Jordan algebra and the given state. -/
theorem finiteComplexTables_subset_finiteJordan (n : ℕ) :
    finiteHilbertProjectiveTables.{u} ℂ n ⊆ finiteJordanTables.{u} n := by
  intro f hf
  rcases hf with ⟨K,hN,hI,hC,hD,M,hM⟩
  let := hN
  let := hI
  let := hC
  let := hD
  let hA := hilbertOperatorAlgebra_finiteReal (𝕜 := ℂ) (H := K)
  let : FiniteDimensional ℝ (selfAdjoint (HilbertOperatorAlgebra ℂ K)) :=
    @FiniteDimensional.of_injective ℝ _ _ _ _ _ _ _
      (selfAdjointOperatorInclusion (H := K)) Subtype.val_injective hA
  let J := selfAdjointOperatorJordanProduct (H := K)
  refine ⟨selfAdjoint (HilbertOperatorAlgebra ℂ K),inferInstance,inferInstance,inferInstance,
    J,selfAdjointOperatorJordan_formallyReal,?_⟩
  apply (J.mem_canonicalProjectiveTables_iff_functional _).mpr
  let p : Fin n → selfAdjoint (HilbertOperatorAlgebra ℂ K) :=
    fun i => ⟨M.projection i,(M.isStarProjection i).isSelfAdjoint⟩
  refine ⟨p,M.state,?_,?_,M.normalized,?_⟩
  · intro i
    apply Subtype.ext
    rw [selfAdjointOperatorJordan_square,(M.isStarProjection i).isSelfAdjoint]
    exact (M.isStarProjection i).isIdempotentElem
  · intro x
    apply M.positive
    rw [selfAdjointOperatorJordan_square]
    exact operatorValue_star_mul_positive ℂ K x.val
  · intro w
    have he := M.toAlgebraic_state_selfAdjoint (J.sequentialWordEffect p w)
    rw [hilbert_effect_value M p (fun _ => rfl)] at he
    exact he.symm.trans (hM w)

end AlbertSequential
