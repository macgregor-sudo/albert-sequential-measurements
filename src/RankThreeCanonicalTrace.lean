/- SPDX-License-Identifier: Apache-2.0 -/
module
public import GeneralEJALowRankClassification
public import ThirteenTracesAndAform

@[expose] public section
noncomputable section
namespace AlbertSequential.UnitalJordanProduct
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
variable (P : UnitalJordanProduct E) (hfr : P.FormallyReal)
local notation "τ" => P.canonicalTraceOfFormallyReal hfr

omit [FiniteDimensional ℝ E] in
/-- Coordinatewise multiplication in the primitive spectral frame. -/
private theorem product_in_frame {n : ℕ} (c : Fin n → E)
    (hi : ∀ i, P.IsPrimitive (c i)) (ho : ∀ i j, i ≠ j → P.product (c i) (c j) = 0)
    (f g : Fin n → ℝ) :
    P.product (∑ i, f i • c i) (∑ i, g i • c i) = ∑ i, (f i * g i) • c i := by
  classical
  simp only [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · rw [(hi i).1,mul_comm]
  · intro j _ hj; simp [ho _ _ hj]
  · simp

theorem rankThree_cubic_identity (hr : τ P.unit = 3) (x : E) : ∃ N : ℝ,
    P.product x (P.product x x) - τ x • P.product x x +
      ((1/2 : ℝ) * ((τ x)^2 - τ (P.product x x))) • x = N • P.unit := by
  obtain ⟨n,a,c,hi,ho,hu,hx⟩ := P.primitive_spectral_resolution_of_formallyReal hfr x
  have hn : n = 3 := by exact_mod_cast (P.canonicalTrace_unit_eq_primitive_frame_length hfr c hi hu).symm.trans hr
  subst n
  refine ⟨a 0 * a 1 * a 2,?_⟩
  rw [hx,P.product_in_frame c hi ho a a,P.product_in_frame c hi ho]
  simp only [map_sum,map_smul,smul_eq_mul,fun i => P.canonicalTraceOfFormallyReal_primitive hfr _ (hi i),mul_one]
  rw [← hu]
  simp only [Finset.smul_sum,smul_smul,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← sub_smul,← add_smul]
  congr 1
  fin_cases i <;> simp [Fin.sum_univ_three] <;> ring

def rankThreeCanonicalModel (hr : τ P.unit = 3) : RankThreeCubicModel E where
  mul x y := P.product x y
  one := P.unit
  tr := τ
  mul_comm := P.commutative
  mul_add_left x y z := by simp only [map_add,LinearMap.add_apply]
  mul_smul_left r x y := by simp only [map_smul,LinearMap.smul_apply]
  mul_one_left := P.unit_left
  tr_one := hr
  tr_assoc := P.canonicalTraceOfFormallyReal_associative hfr
  cubic_identity := P.rankThree_cubic_identity hfr hr

/-- The trace relation for arbitrary rank-three Euclidean Jordan algebras,
with the canonical normalization on primitive idempotents. -/
theorem canonical_fourPrimitive_trace_relation (hr : τ P.unit = 3) (p : Fin 4 → E)
    (hp : ∀ i, P.IsPrimitive (p i)) :
    let o := fun i j => τ (P.product (p i) (p j))
    let R := fun i j k => τ (P.product (P.product (p i) (p j)) (p k))
    let t := fun i j k l => τ (P.product (P.product (p i) (p j)) (P.product (p k) (p l)))
    t 0 1 2 3 + t 0 2 1 3 + t 0 3 1 2 =
      1/2 - 1/2 * (o 0 1 + o 0 2 + o 0 3 + o 1 2 + o 1 3 + o 2 3) +
      1/2 * (o 0 1 * o 2 3 + o 0 2 * o 1 3 + o 0 3 * o 1 2) +
      R 0 1 2 + R 0 1 3 + R 0 2 3 + R 1 2 3 :=
  rankThree_fourIdempotent_trace_relation (P.rankThreeCanonicalModel hfr hr) p
    (fun i => (hp i).1) (fun i => P.canonicalTraceOfFormallyReal_primitive hfr _ (hp i))

end AlbertSequential.UnitalJordanProduct
