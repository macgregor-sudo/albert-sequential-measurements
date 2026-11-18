module

public import LemmaB.Gram
public import LemmaB.Access

/-!
# Lemma B, part 6: assembly of lem:cer:negative (model side, over any field)

`Ξ_B, Ξ_C, Ξ_D` lie in the span of the path vectors `û(w)`, `w ∈ 𝒲₂₈` (existence of the
coefficients only), their `𝒬`-Gram matrix is `gramXi`, with determinant `-256 D̂³ μ³ m`; the
trace relation enters only as `τ = 0`.
-/

@[expose] public section

namespace LemmaB

variable {K : Type*} [Field K] (p : Params K)

/-- The defining condition of the frame subspace `S_f`. -/
def frameCond (f : Fin 4) (β : C8 K) : Prop :=
  ![β 7 = 0, β 5 = -p.c2 * β 7, β 6 = -p.c3 * β 7, β 4 = -p.c1 * β 7] f

/-- Back-substitution coefficients by frame. -/
def coefFrame (f : Fin 4) : C8 K → Fin 7 → K := ![coefA p, coefB p, coefC p, coefD p] f

theorem span_frame (f : Fin 4) (β : C8 K) (h : frameCond p f β) :
    ∑ j, coefFrame p f β j • amp p (wordFI f j) = β := by
  fin_cases f
  · exact spanA p β h
  · exact spanB p β h
  · exact spanC p β h
  · exact spanD p β h

/-- The frame components of the `Ξ_x` lie in the frame subspaces (from the ghost data). -/
theorem Xi_frameCond (x : Fin 3) (f : Fin 4) : frameCond p f (Xi p x f) := by
  obtain ⟨b0, b1, b1', b2, b2', b3, b3'⟩ := ghost_XiB p
  obtain ⟨c0, c1, c1', c2, c2', c3, c3'⟩ := ghost_XiC p
  obtain ⟨d0, d1, d1', d2, d2', d3, d3'⟩ := ghost_XiD p
  fin_cases x <;> fin_cases f <;>
    simp [frameCond, Xi, b0, b1, b1', b2, b2', b3, b3', c0, c1, c1', c2, c2', c3, c3', d0, d1,
      d1', d2, d2', d3, d3'] <;> ring

theorem single_sum_smul (f : Fin 4) (c : Fin 7 → K) (a : Fin 7 → C8 K) :
    (Pi.single f (∑ i, c i • a i) : V K) = ∑ i, c i • (Pi.single f (a i) : V K) := by
  funext z
  by_cases h : z = f
  · subst h; simp [Finset.sum_apply]
  · simp [Finset.sum_apply, Pi.single_eq_of_ne h]

/-- Accessibility in terms of the unnormalised path vectors `ũ(w)`. -/
theorem Xi_mem_span_utilde (x : Fin 3) :
    Xi p x = ∑ f, ∑ i, coefFrame p f (Xi p x f) i • utilde p (wordFI f i) := by
  conv_lhs => rw [← Finset.univ_sum_single (Xi p x)]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp only [utilde_eq, frameOf_wordFI]
  rw [← single_sum_smul, span_frame p f _ (Xi_frameCond p x f)]

theorem prod_mOf_ne_zero (hm : ∀ x, mOf p x ≠ 0) (w : List (Fin 4)) :
    (w.map (mOf p)).prod ≠ 0 := by
  induction w with
  | nil => simp
  | cons x w ih => simp only [List.map_cons, List.prod_cons]; exact mul_ne_zero (hm x) ih

/-- Accessibility in terms of the paper's path vectors `û(w)` (needs `m_x ≠ 0`). -/
theorem Xi_mem_span_uhat (hm : ∀ x, mOf p x ≠ 0) (x : Fin 3) :
    Xi p x = ∑ f, ∑ i, (coefFrame p f (Xi p x f) i * ((wordFI f i).map (mOf p)).prod) •
      uhat p (wordFI f i) := by
  refine (Xi_mem_span_utilde p x).trans ?_
  refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun i _ => ?_
  rw [uhat_eq, smul_smul, mul_assoc, mul_inv_cancel₀ (prod_mOf_ne_zero p hm _), mul_one]

/-- The twenty-eight words flattened: `word28 (7 f + i) = wordFI f i`
(frames `A, B, C, D` in the order of eq:cer:W28). -/
def word28 (k : Fin 28) : List (Fin 4) :=
  wordFI ((finProdFinEquiv (m := 4) (n := 7)).symm k).1 ((finProdFinEquiv (m := 4) (n := 7)).symm k).2

theorem sum_fin28 {M : Type*} [AddCommMonoid M] (g : Fin 28 → M) :
    ∑ k, g k = ∑ f : Fin 4, ∑ i : Fin 7, g (finProdFinEquiv (m := 4) (n := 7) (f, i)) := by
  rw [← Fintype.sum_prod_type']
  exact (Equiv.sum_comp (finProdFinEquiv (m := 4) (n := 7)) g).symm

/-- **lem:cer:negative, model side.** Over any field, assume the trace relation in the form
`τ = 0` and `m_B, m_C, m_D ≠ 0`. Then there are coefficients `c` with
`Ξ_x = Σ_{w ∈ 𝒲₂₈} c_{x,w} û(w)` for `x = B, C, D`; the `𝒬`-Gram matrix of the `Ξ_x` is
`gramXi` (diagonal `4 D̂ α_x (α_x + μ_x)`, off-diagonal `-4 D̂ μ m_z`), and its determinant is
`-256 D̂³ μ³ m`. -/
theorem lemmaB_model (hτ : p.tau = 0) (hm : p.mB ≠ 0 ∧ p.mC ≠ 0 ∧ p.mD ≠ 0) :
    ∃ c : Fin 3 → Fin 28 → K,
      (∀ x, Xi p x = ∑ k, c x k • uhat p (word28 k)) ∧
      (∀ x y, Q p (Xi p x) (Xi p y) = gramXi p x y) ∧
      (gramXi p).det = -256 * p.Dhat ^ 3 * p.μ ^ 3 * p.m := by
  have hm' : ∀ x, mOf p x ≠ 0 := by
    intro x; fin_cases x
    · simp [mOf]
    · simpa [mOf] using hm.1
    · simpa [mOf] using hm.2.1
    · simpa [mOf] using hm.2.2
  refine ⟨fun x k => coefFrame p ((finProdFinEquiv (m := 4) (n := 7)).symm k).1
      (Xi p x ((finProdFinEquiv (m := 4) (n := 7)).symm k).1)
      ((finProdFinEquiv (m := 4) (n := 7)).symm k).2 *
      ((word28 k).map (mOf p)).prod, fun x => ?_, gram_Xi p hτ, det_gramXi p⟩
  rw [sum_fin28, Xi_mem_span_uhat p hm' x]
  simp [word28]

end LemmaB
