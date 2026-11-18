/- SPDX-License-Identifier: Apache-2.0 -/
module
public import FormalRealitySpectral
public import JordanRegularTrace

/-! The paper's algebraic finite-sum formal reality implies a positive
associative form: the actual regular operator-trace form. This trace need not
give value1 to primitives and is not the canonical normalized Jordan trace. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.UnitalJordanProduct
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  (P : UnitalJordanProduct E)

theorem regularTraceForm_positive_of_formallyReal
    (hfr : P.FormallyReal) (x : E) (hx : x≠0) :
    0<P.regularTraceForm x x := by
  classical
  obtain ⟨n,lam,c,hlam,hc,ho,hs,hxspec⟩ := P.spectral_resolution_of_formallyReal hfr x
  have hsquare : P.product x x=∑ i,(lam i)^2 • c i := by
    rw [hxspec]
    simp only [map_sum,LinearMap.sum_apply,map_smul,
      LinearMap.smul_apply,Finset.smul_sum,smul_smul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · rw [(hc i).2,pow_two]
    · intro j _ hji
      rw [P.commutative (c j) (c i),ho i j hji.symm,smul_zero]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  have hex : ∃ i,lam i≠0 := by
    by_contra h
    push Not at h
    apply hx
    rw [hxspec]
    simp only [h,zero_smul,Finset.sum_const_zero]
  obtain ⟨i,hi⟩ := hex
  rw [P.regularTraceForm_apply,hsquare,map_sum]
  simp only [map_smul,smul_eq_mul]
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (sq_nonneg _) (P.regularTrace_idempotent_positive _ (hc j).2 (hc j).1).le
  · exact ⟨i,Finset.mem_univ _,mul_pos (sq_pos_of_ne_zero hi)
      (P.regularTrace_idempotent_positive _ (hc i).2 (hc i).1)⟩

theorem regularTraceForm_nonnegative_of_formallyReal
    (hfr : P.FormallyReal) (x : E) : 0≤P.regularTraceForm x x := by
  by_cases hx : x=0
  · simp [hx]
  · exact (P.regularTraceForm_positive_of_formallyReal hfr x hx).le

theorem regularTraceForm_definite_of_formallyReal
    (hfr : P.FormallyReal) (x : E) : P.regularTraceForm x x=0 ↔ x=0 := by
  constructor
  · intro hz
    by_contra hx
    exact (ne_of_gt (P.regularTraceForm_positive_of_formallyReal hfr x hx)) hz
  · intro hx
    simp [hx]

theorem exists_positive_associative_form_of_formallyReal (hfr : P.FormallyReal) :
    ∃ B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ,
      (∀ x y, B x y=B y x) ∧
      (∀ x, x≠0 → 0<B x x) ∧
      (∀ x y z, B (P.product x y) z=B x (P.product y z)) :=
  ⟨P.regularTraceForm,P.regularTraceForm_symmetric,
    P.regularTraceForm_positive_of_formallyReal hfr,P.regularTraceForm_associative⟩

end AlbertSequential.UnitalJordanProduct
