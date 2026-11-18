/- SPDX-License-Identifier: Apache-2.0 -/
module
public import JordanPeircePositiveMultiplication
public import JordanSpectralResolution
public import Mathlib.Analysis.Convex.Basic

/-! The literal square cone is self-dual, closed and convex in the finite
positive-associative-inner-form setting. No canonical trace, formal-reality
converse, U positivity or classification theorem is assumed or claimed. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.UnitalJordanProduct
variable {E : Type*} [AddCommGroup E] [Module ℝ E] (P : UnitalJordanProduct E)

/-- Actual squares, before proving closure or convexity. -/
def squareCone : Set E := {x | ∃ y : E, x=P.product y y}

theorem zero_mem_squareCone : (0 : E)∈P.squareCone := by
  exact ⟨0, by simp⟩

theorem unit_mem_squareCone : P.unit∈P.squareCone :=
  ⟨P.unit,(P.unit_left P.unit).symm⟩

theorem nonnegative_smul_mem_squareCone (x : E) (hx : x∈P.squareCone)
    (t : ℝ) (ht : 0≤t) : t • x∈P.squareCone := by
  obtain ⟨y,rfl⟩ := hx
  refine ⟨Real.sqrt t • y,?_⟩
  simp only [map_smul,LinearMap.smul_apply,smul_smul]
  rw [Real.mul_self_sqrt ht]

/-- Finite orthogonal idempotent expansion, with zero/repeated coefficients allowed. -/
theorem square_of_orthogonal_expansion {ι : Type*} [Fintype ι]
    (c : ι→E) (lam : ι→ℝ) (hc : ∀ i, P.product (c i) (c i)=c i)
    (horth : ∀ i j, i≠j → P.product (c i) (c j)=0) :
    P.product (∑ i,lam i • c i) (∑ i,lam i • c i)=∑ i,(lam i)^2 • c i := by
  classical
  calc
    P.product (∑ i,lam i • c i) (∑ i,lam i • c i)=
        ∑ i,∑ j,(lam i*lam j) • P.product (c i) (c j) := by
      simp only [map_sum,LinearMap.sum_apply,map_smul,
        LinearMap.smul_apply,Finset.smul_sum,smul_smul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [P.commutative (c j) (c i)]
    _=∑ i,(lam i)^2 • c i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · rw [hc i,pow_two]
      · intro j _ hji
        rw [horth i j hji.symm,smul_zero]
      · intro hi
        exact (hi (Finset.mem_univ i)).elim

/-- The literal square cone spans the whole unital bilinear algebra. -/
theorem span_squareCone : Submodule.span ℝ P.squareCone=⊤ := by
  apply top_unique
  intro x _
  have hplus : P.product (P.unit+x) (P.unit+x)∈Submodule.span ℝ P.squareCone :=
    Submodule.subset_span ⟨P.unit+x,rfl⟩
  have hminus : P.product (P.unit-x) (P.unit-x)∈Submodule.span ℝ P.squareCone :=
    Submodule.subset_span ⟨P.unit-x,rfl⟩
  have h := (Submodule.span ℝ P.squareCone).sub_mem hplus hminus
  have hid : P.product (P.unit+x) (P.unit+x)-P.product (P.unit-x) (P.unit-x)=
      (4 : ℝ) • x := by
    have hright : P.product x P.unit=x := by rw [P.commutative,P.unit_left]
    simp only [map_add,map_sub,LinearMap.add_apply,LinearMap.sub_apply,
      P.unit_left,hright]
    module
  have hs := (Submodule.span ℝ P.squareCone).smul_mem (1/4 : ℝ) h
  rw [hid,smul_smul] at hs
  norm_num at hs
  exact hs

end AlbertSequential.UnitalJordanProduct

namespace AlbertSequential.UnitalJordanProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (P : UnitalJordanProduct E)

theorem orthogonal_idempotents_inner_zero
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (a b : E) (hab : P.product a b=0) : inner ℝ a b=0 := by
  calc
    inner ℝ a b=inner ℝ P.unit (P.product a b) := by
      simpa only [P.unit_left] using hinner P.unit a b
    _=0 := by rw [hab,inner_zero_right]

theorem orthogonal_expansion_inner_component {ι : Type*} [Fintype ι]
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (c : ι→E) (lam : ι→ℝ)
    (horth : ∀ i j, i≠j → P.product (c i) (c j)=0) (i : ι) :
    inner ℝ (∑ j,lam j • c j) (c i)=lam i*inner ℝ (c i) (c i) := by
  classical
  rw [sum_inner]
  simp only [real_inner_smul_left]
  rw [Finset.sum_eq_single i]
  · intro j _ hji
    rw [P.orthogonal_idempotents_inner_zero hinner _ _ (horth j i hji),mul_zero]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- Supplied unit pairing is faithful, without claiming canonical trace normalization. -/
theorem squareCone_unitPairing_nonnegative
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (x : E) (hx : x∈P.squareCone) : 0 ≤ inner ℝ x P.unit := by
  obtain ⟨y,rfl⟩ := hx
  rw [P.square_inner_unit hinner]
  exact real_inner_self_nonneg

theorem squareCone_unitPairing_zero_iff
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (x : E) (hx : x∈P.squareCone) : inner ℝ x P.unit=0 ↔ x=0 := by
  constructor
  · intro h
    obtain ⟨y,rfl⟩ := hx
    rw [P.square_inner_unit hinner] at h
    have hy : y=0 := inner_self_eq_zero.mp h
    simp only [hy,map_zero]
  · intro h
    rw [h,inner_zero_left]

theorem squareCone_pointed
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (x : E) (hx : x∈P.squareCone) (hneg : -x∈P.squareCone) : x=0 := by
  have hp := P.squareCone_unitPairing_nonnegative hinner x hx
  have hn := P.squareCone_unitPairing_nonnegative hinner (-x) hneg
  rw [inner_neg_left] at hn
  apply (P.squareCone_unitPairing_zero_iff hinner x hx).mp
  linarith

end AlbertSequential.UnitalJordanProduct

namespace AlbertSequential.UnitalJordanProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (P : UnitalJordanProduct E)

theorem squareCone_inner_nonnegative
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (x y : E) (hx : x∈P.squareCone) (hy : y∈P.squareCone) : 0 ≤ inner ℝ x y := by
  obtain ⟨z,rfl⟩ := hx
  obtain ⟨w,rfl⟩ := hy
  obtain ⟨n,lam,c,_,hc,horth,_,hz⟩ := P.spectral_resolution hinner z
  rw [hz,P.square_of_orthogonal_expansion c lam (fun i => (hc i).2) horth,sum_inner]
  apply Finset.sum_nonneg
  intro i _
  rw [real_inner_smul_left]
  exact mul_nonneg (sq_nonneg _) (P.idempotent_inner_square_nonneg hinner _ _ (hc i).2)

/-- Exact self-duality of actual squares; no cone-closure premise. -/
theorem squareCone_self_dual
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z)) (x : E) :
    x∈P.squareCone ↔ ∀ y∈P.squareCone,0 ≤ inner ℝ x y := by
  constructor
  · intro hx y hy
    exact P.squareCone_inner_nonnegative hinner x y hx hy
  · intro hx
    obtain ⟨n,lam,c,_,hc,horth,_,hres⟩ := P.spectral_resolution hinner x
    have hnonneg (i : Fin n) : 0≤lam i := by
      have h := hx (c i) ⟨c i,(hc i).2.symm⟩
      rw [hres,P.orthogonal_expansion_inner_component hinner c lam horth i] at h
      exact nonneg_of_mul_nonneg_left h (real_inner_self_pos.mpr (hc i).1)
    refine ⟨∑ i,Real.sqrt (lam i) • c i,?_⟩
    rw [P.square_of_orthogonal_expansion c (fun i => Real.sqrt (lam i))
      (fun i => (hc i).2) horth]
    have hsqrt : ∀ i, (Real.sqrt (lam i))^2=lam i := fun i => Real.sq_sqrt (hnonneg i)
    simpa only [hsqrt] using hres

theorem squareCone_isClosed
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z)) :
    IsClosed P.squareCone := by
  have hset : P.squareCone=⋂ y:E,{x:E | 0 ≤ inner ℝ x (P.product y y)} := by
    ext x
    simp only [Set.mem_iInter,Set.mem_ofPred_eq]
    constructor
    · intro hx y
      exact (P.squareCone_self_dual hinner x).mp hx _ ⟨y,rfl⟩
    · intro hx
      apply (P.squareCone_self_dual hinner x).mpr
      rintro y ⟨z,rfl⟩
      exact hx z
  rw [hset]
  exact isClosed_iInter (fun y => isClosed_le continuous_const
    (continuous_id.inner continuous_const))

theorem add_mem_squareCone
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (x y : E) (hx : x∈P.squareCone) (hy : y∈P.squareCone) : x+y∈P.squareCone := by
  apply (P.squareCone_self_dual hinner _).mpr
  intro z hz
  rw [inner_add_left]
  exact add_nonneg (P.squareCone_inner_nonnegative hinner x z hx hz)
    (P.squareCone_inner_nonnegative hinner y z hy hz)

theorem squareCone_convex
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z)) :
    Convex ℝ P.squareCone := by
  intro x hx y hy a b ha hb _
  exact P.add_mem_squareCone hinner _ _
    (P.nonnegative_smul_mem_squareCone x hx a ha)
    (P.nonnegative_smul_mem_squareCone y hy b hb)

/-- The separating element is itself an actual square; no cone axiom is used. -/
theorem squareCone_separates_nonsquare
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (x : E) (hx : x∉P.squareCone) : ∃ y∈P.squareCone,inner ℝ x y<0 := by
  classical
  by_contra hn
  apply hx
  apply (P.squareCone_self_dual hinner x).mpr
  intro y hy
  exact le_of_not_gt (fun hlt => hn ⟨y,hy,hlt⟩)

end AlbertSequential.UnitalJordanProduct
