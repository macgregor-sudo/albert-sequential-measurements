/- SPDX-License-Identifier: Apache-2.0 -/
module
public import GeneralEJAFrameTraceNormalization

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

abbrev IncreasingFramePairs (n : ℕ) := {ij : Fin n × Fin n // ij.1 < ij.2}

section LinearProjections

variable {E : Type*} [AddCommGroup E] [Module ℝ E] (P : UnitalJordanProduct E)
    {n : ℕ} (c : Fin n → E)

local notation "W" => P.frameOffDiagonalSpace c

def frameEdgeProjection (i j : Fin n) : E →ₗ[ℝ] E :=
  (P.peirceHalfProjection (c i)).comp (P.peirceHalfProjection (c j))

theorem peirceHalfProjection_on_frameEdge {i j : Fin n} (k : Fin n) {x : E} (hx : x ∈ W i j) :
    P.peirceHalfProjection (c k) x = if k = i ∨ k = j then x else 0 := by
  have he := (P.mem_frameJointSpace c _).mp hx k
  by_cases hk : k = i ∨ k = j
  · rw [frameOffDiagonalPattern, ite_eq_left hk] at he
    rw [ite_eq_left hk, P.peirceHalfProjection_apply, he, map_smul, he]
    module
  · rw [frameOffDiagonalPattern, ite_eq_right hk, zero_smul] at he
    rw [ite_eq_right hk]
    simp [he]

theorem frameEdgeProjection_on_frameEdge {i j k l : Fin n} (hij : i < j) (hkl : k < l)
    {x : E} (hx : x ∈ W k l) :
    P.frameEdgeProjection c i j x = if i = k ∧ j = l then x else 0 := by
  have hpair : ((i = k ∨ i = l) ∧ (j = k ∨ j = l)) ↔ i = k ∧ j = l := by
    constructor
    · rintro ⟨hi, hj⟩
      rcases hi with hi | hi <;> rcases hj with hj | hj <;> omega
    · rintro ⟨hi, hj⟩
      exact ⟨Or.inl hi, Or.inr hj⟩
  rw [frameEdgeProjection, LinearMap.comp_apply, P.peirceHalfProjection_on_frameEdge c j hx]
  by_cases hj : j = k ∨ j = l
  · rw [ite_eq_left hj, P.peirceHalfProjection_on_frameEdge c i hx]
    by_cases hi : i = k ∨ i = l
    · rw [ite_eq_left hi, ite_eq_left (hpair.mp ⟨hi, hj⟩)]
    · rw [ite_eq_right hi, ite_eq_right (fun h => hi ((hpair.mpr h).1))]
  · rw [ite_eq_right hj, map_zero, ite_eq_right (fun h => hj ((hpair.mpr h).2))]

theorem peirceHalfProjection_on_framePrimitive
    (hc : ∀ j, P.IsPrimitive (c j)) (hor : ∀ i j, i ≠ j → P.product (c i) (c j) = 0)
    (i j : Fin n) : P.peirceHalfProjection (c i) (c j) = 0 := by
  by_cases hij : i = j
  · subst j
    simp [(hc i).1]
  · simp [hor i j hij]

theorem frameEdgeProjection_on_framePrimitive
    (hc : ∀ j, P.IsPrimitive (c j)) (hor : ∀ i j, i ≠ j → P.product (c i) (c j) = 0)
    (i j k : Fin n) : P.frameEdgeProjection c i j (c k) = 0 := by
  rw [frameEdgeProjection, LinearMap.comp_apply, P.peirceHalfProjection_on_framePrimitive c hc hor, map_zero]

theorem frameDiagonalProjection_on_framePrimitive
    (hc : ∀ j, P.IsPrimitive (c j)) (hor : ∀ i j, i ≠ j → P.product (c i) (c j) = 0)
    (i j : Fin n) : P.quadraticRepresentation (c i) (c j) = if i = j then c j else 0 := by
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl, P.quadraticRepresentation_idempotent_self (c i) (hc i).1]
  · simp [hij, (hc i).1, hor i j hij]

theorem frameDiagonalProjection_on_frameEdge
    (hc : ∀ j, P.IsPrimitive (c j)) {i j : Fin n} (k : Fin n) {x : E} (hx : x ∈ W i j) :
    P.quadraticRepresentation (c k) x = 0 := by
  have he := (P.mem_frameJointSpace c _).mp hx k
  by_cases hk : k = i ∨ k = j
  · rw [frameOffDiagonalPattern, ite_eq_left hk] at he
    rw [P.quadraticRepresentation_apply, (hc k).1, he, map_smul, he]
    module
  · rw [frameOffDiagonalPattern, ite_eq_right hk, zero_smul] at he
    simp [(hc k).1, he]

variable [FiniteDimensional ℝ E] (hfr : P.FormallyReal)

def frameDiagonalCoefficient (i : Fin n) : E →ₗ[ℝ] ℝ :=
  (P.canonicalTraceOfFormallyReal hfr).comp (P.product (c i))

theorem frameDiagonalCoefficient_on_framePrimitive
    (hc : ∀ j, P.IsPrimitive (c j)) (hor : ∀ i j, i ≠ j → P.product (c i) (c j) = 0)
    (i j : Fin n) : P.frameDiagonalCoefficient c hfr i (c j) = if i = j then 1 else 0 := by
  change P.canonicalTraceOfFormallyReal hfr (P.product (c i) (c j)) = _
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl, (hc i).1, P.canonicalTraceOfFormallyReal_primitive hfr (c i) (hc i)]
  · rw [ite_eq_right hij, hor i j hij, map_zero]

theorem frameDiagonalCoefficient_on_frameEdge
    (hc : ∀ j, P.IsPrimitive (c j)) {i j : Fin n} (k : Fin n) {x : E} (hx : x ∈ W i j) :
    P.frameDiagonalCoefficient c hfr k x = 0 := by
  have h := P.canonicalTraceOfFormallyReal_primitive_compression hfr (c k) x (hc k)
  rw [P.frameDiagonalProjection_on_frameEdge c hc k hx] at h
  exact (smul_eq_zero.mp h.symm).resolve_right (hc k).2.1

end LinearProjections

section Reconstruct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : UnitalJordanProduct E) {n : ℕ} (c : Fin n → E)
    (hc : ∀ j, P.IsPrimitive (c j)) (hor : ∀ i j, i ≠ j → P.product (c i) (c j) = 0)
    (hunit : ∑ j, c j = P.unit)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))

local notation "W" => P.frameOffDiagonalSpace c

include hc hor hunit hinner

theorem framePeirce_linear_ext {M : Type*} [AddCommGroup M] [Module ℝ M]
    {f g : E →ₗ[ℝ] M} (hd : ∀ i, f (c i) = g (c i))
    (he : ∀ (i j : Fin n), i < j → ∀ x ∈ W i j, f x = g x) : f = g := by
  let T := (f - g).ker
  have hspan : (⊤ : Submodule ℝ E) ≤ T := by
    rw [← P.framePeirce_spanning c hc hor hunit hinner]
    refine sup_le (iSup_le fun i => ?_) (iSup_le fun ij => ?_)
    · apply Submodule.span_le.mpr
      rintro _ rfl
      exact LinearMap.mem_ker.mpr (sub_eq_zero.mpr (hd i))
    · intro x hx
      exact LinearMap.mem_ker.mpr (sub_eq_zero.mpr (he ij.val.1 ij.val.2 ij.property x hx))
  ext x
  exact sub_eq_zero.mp (LinearMap.mem_ker.mp (hspan (show x ∈ (⊤ : Submodule ℝ E) from trivial)))

theorem frameEdgeProjection_mem (i j : Fin n) (hij : i < j) (x : E) :
    P.frameEdgeProjection c i j x ∈ W i j := by
  let T := (W i j).comap (P.frameEdgeProjection c i j)
  have hspan : (⊤ : Submodule ℝ E) ≤ T := by
    rw [← P.framePeirce_spanning c hc hor hunit hinner]
    refine sup_le (iSup_le fun k => ?_) (iSup_le fun kl => ?_)
    · apply Submodule.span_le.mpr
      rintro _ rfl
      change P.frameEdgeProjection c i j (c k) ∈ W i j
      rw [P.frameEdgeProjection_on_framePrimitive c hc hor]
      exact Submodule.zero_mem _
    · intro y hy
      change P.frameEdgeProjection c i j y ∈ W i j
      rw [P.frameEdgeProjection_on_frameEdge c hij kl.property hy]
      split
      · rename_i h
        simpa only [h.1, h.2] using hy
      · exact Submodule.zero_mem _
  exact hspan (show x ∈ (⊤ : Submodule ℝ E) from trivial)

theorem framePeirce_reconstruct (x : E) :
    x = (∑ i, P.quadraticRepresentation (c i) x) +
      ∑ ij : IncreasingFramePairs n, P.frameEdgeProjection c ij.val.1 ij.val.2 x := by
  classical
  let S : E →ₗ[ℝ] E := (∑ i, P.quadraticRepresentation (c i)) +
    ∑ ij : IncreasingFramePairs n, P.frameEdgeProjection c ij.val.1 ij.val.2
  have hS : S = LinearMap.id := by
    apply P.framePeirce_linear_ext c hc hor hunit hinner
    · intro i
      simp only [S, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.id_apply,
        P.frameDiagonalProjection_on_framePrimitive c hc hor, P.frameEdgeProjection_on_framePrimitive c hc hor,
        Finset.sum_const_zero, add_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    · intro i j hij y hy
      simp only [S, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.id_apply,
        P.frameDiagonalProjection_on_frameEdge c hc _ hy, Finset.sum_const_zero, zero_add]
      let ij : IncreasingFramePairs n := ⟨(i, j), hij⟩
      have hsum :
          (∑ kl : IncreasingFramePairs n, P.frameEdgeProjection c kl.val.1 kl.val.2 y) =
            P.frameEdgeProjection c i j y :=
        Finset.sum_eq_single ij (fun kl _ he => by
          have hh : ¬ (kl.val.1 = i ∧ kl.val.2 = j) := fun h => he (Subtype.ext (Prod.ext h.1 h.2))
          rw [P.frameEdgeProjection_on_frameEdge c kl.property hij hy, ite_eq_right hh])
          (fun hn => (hn (Finset.mem_univ ij)).elim)
      rw [hsum, P.frameEdgeProjection_on_frameEdge c hij hij hy, ite_eq_left ⟨rfl, rfl⟩]
  have hy := LinearMap.congr_fun hS x
  simpa only [S, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.id_apply] using hy.symm

end Reconstruct

end AlbertSequential.UnitalJordanProduct
