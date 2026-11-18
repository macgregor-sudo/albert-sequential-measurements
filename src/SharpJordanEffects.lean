/- SPDX-License-Identifier: Apache-2.0 -/
module
public import IdealJordanCompression

/-! The literal full-state sharpness condition characterizes idempotent effects.
A single intermediate spectral component supplies the forbidden state/effect;
no classification, primitive normalization or matrix embedding is used. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace AlbertSequential.PositiveInstruments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (P : UnitalJordanProduct E)
  (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
include hinner

omit [FiniteDimensional ℝ E] in
theorem trace_idempotent_self (p : E) (hp : P.product p p=p) :
    trace P p=inner ℝ p p := by
  simpa only [trace,hp] using P.square_inner_unit hinner p

omit [FiniteDimensional ℝ E] in
theorem normalized_idempotent_pairing (p : E) (hp : P.product p p=p) (hne : p≠0) :
    inner ℝ ((1/trace P p : ℝ) • p) p=1 := by
  rw [real_inner_smul_left,← trace_idempotent_self P hinner p hp]
  exact one_div_mul_cancel (ne_of_gt (trace_pos_of_nonzero P hinner p ⟨p,hp.symm⟩ hne))

omit [FiniteDimensional ℝ E] in
theorem idempotent_isSharpEffect (p : E) (hp : P.product p p=p) : IsSharpEffect P p := by
  rintro ⟨σ,f,hσ,hf,hσf,hfaces⟩
  have hpf : inner ℝ p f=0 := by
    by_cases hz : p=0
    · simp [hz]
    have hd := normalized_positive_isDensity P hinner p ⟨p,hp.symm⟩ hz
    have hn := normalized_idempotent_pairing P hinner p hp hz
    have hv := hfaces _ hd (Or.inr hn)
    rw [real_inner_smul_left] at hv
    exact (mul_eq_zero.mp hv).resolve_left
      (one_div_ne_zero (ne_of_gt (trace_pos_of_nonzero P hinner p ⟨p,hp.symm⟩ hz)))
  let q := P.unit-p
  have hq : P.product q q=q := complementary_idempotent P p hp
  have hqf : inner ℝ q f=0 := by
    by_cases hz : q=0
    · simp [hz]
    have hd := normalized_positive_isDensity P hinner q ⟨q,hq.symm⟩ hz
    have hqp : P.product q p=0 := by
      dsimp only [q]
      rw [map_sub,LinearMap.sub_apply,P.unit_left,hp,sub_self]
    have horth : inner ℝ q p=0 := P.orthogonal_idempotents_inner_zero hinner q p hqp
    have hn : inner ℝ ((1/trace P q : ℝ) • q) p=0 := by
      rw [real_inner_smul_left,horth,mul_zero]
    have hv := hfaces _ hd (Or.inl hn)
    rw [real_inner_smul_left] at hv
    exact (mul_eq_zero.mp hv).resolve_left
      (one_div_ne_zero (ne_of_gt (trace_pos_of_nonzero P hinner q ⟨q,hq.symm⟩ hz)))
  have hpfr : inner ℝ f p=0 := by rw [real_inner_comm]; exact hpf
  have hqfr : inner ℝ f q=0 := by rw [real_inner_comm]; exact hqf
  have ht : trace P f=0 := by
    change inner ℝ f P.unit=0
    have he : P.unit=p+q := by dsimp only [q]; abel
    rw [he,inner_add_right,hpfr,hqfr,add_zero]
  have hz : f=0 := (P.squareCone_unitPairing_zero_iff hinner f hf.1).mp ht
  rw [hz,inner_zero_right] at hσf
  exact zero_ne_one hσf

theorem weighted_pairing_component_zero {n : ℕ} (c : Fin n→E) (μ : Fin n→ℝ)
    (hc : ∀ j,c j∈P.squareCone) (hμ : ∀ j,0≤μ j)
    (ρ : E) (hρ : ρ∈P.squareCone)
    (hs : inner ℝ (∑ j,μ j • c j) ρ=0) (i : Fin n) (hi : 0<μ i) :
    inner ℝ ρ (c i)=0 := by
  have hsum : (∑ j,μ j * inner ℝ (c j) ρ)=0 := by
    simpa only [sum_inner,real_inner_smul_left] using hs
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
    mul_nonneg (hμ j) (P.squareCone_inner_nonnegative hinner _ _ (hc j) hρ))).mp
      hsum i (Finset.mem_univ i)
  have hz : inner ℝ (c i) ρ=0 :=
    (mul_eq_zero.mp hterm).resolve_left (ne_of_gt hi)
  rw [real_inner_comm]
  exact hz

theorem sharpEffect_isIdempotent (a : E) (ha : IsEffect P a)
    (hsharp : IsSharpEffect P a) : P.product a a=a := by
  classical
  obtain ⟨n,lam,c,_,hc,horth,hsum,hres⟩ := P.spectral_resolution hinner a
  have hcone (i : Fin n) : c i∈P.squareCone := ⟨c i,(hc i).2.symm⟩
  have hN (i : Fin n) : 0 < inner ℝ (c i) (c i) := real_inner_self_pos.mpr (hc i).1
  have hlo (i : Fin n) : 0≤lam i := by
    have h := P.squareCone_inner_nonnegative hinner a (c i) ha.1 (hcone i)
    rw [hres,P.orthogonal_expansion_inner_component hinner c lam horth i] at h
    exact nonneg_of_mul_nonneg_left h (hN i)
  have hhi (i : Fin n) : lam i≤1 := by
    have h := P.squareCone_inner_nonnegative hinner (P.unit-a) (c i) ha.2 (hcone i)
    have he : inner ℝ P.unit (c i)=inner ℝ (c i) (c i) :=
      (real_inner_comm _ _).trans (trace_idempotent_self P hinner (c i) (hc i).2)
    rw [inner_sub_left,he,hres,P.orthogonal_expansion_inner_component hinner c lam horth i] at h
    nlinarith [hN i]
  have hcomp : P.unit-a=∑ j,(1-lam j) • c j := by
    rw [← hsum,hres,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    module
  have hbinary (i : Fin n) : lam i=0 ∨ lam i=1 := by
    by_cases hz : lam i=0
    · exact Or.inl hz
    by_cases ho : lam i=1
    · exact Or.inr ho
    have hi0 : 0<lam i := lt_of_le_of_ne (hlo i) (Ne.symm hz)
    have hi1 : 0<1-lam i := sub_pos.mpr (lt_of_le_of_ne (hhi i) ho)
    have hd := normalized_positive_isDensity P hinner (c i) (hcone i) (hc i).1
    have hp := normalized_idempotent_pairing P hinner (c i) (hc i).2 (hc i).1
    apply False.elim
    apply hsharp
    refine ⟨(1/trace P (c i) : ℝ) • c i,c i,hd,idempotent_isEffect P _ (hc i).2,hp,?_⟩
    intro ρ hρ hface
    rcases hface with hf0 | hf1
    · have hz : inner ℝ a ρ=0 := by rw [real_inner_comm]; exact hf0
      rw [hres] at hz
      exact weighted_pairing_component_zero P hinner c lam hcone hlo ρ hρ.1 hz i hi0
    · have hz : inner ℝ (P.unit-a) ρ=0 := by
        rw [inner_sub_left]
        have he : inner ℝ P.unit ρ=1 := (real_inner_comm _ _).trans hρ.2
        have heA : inner ℝ a ρ=1 := by rw [real_inner_comm]; exact hf1
        rw [he,heA,sub_self]
      rw [hcomp] at hz
      exact weighted_pairing_component_zero P hinner c (fun j => 1-lam j) hcone
        (fun j => sub_nonneg.mpr (hhi j)) ρ hρ.1 hz i hi1
  rw [hres,P.square_of_orthogonal_expansion c lam (fun i => (hc i).2) horth]
  apply Finset.sum_congr rfl
  intro i _
  rcases hbinary i with h0 | h1
  · simp [h0]
  · simp [h1]

end AlbertSequential.PositiveInstruments
