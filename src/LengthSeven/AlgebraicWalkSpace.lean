/- SPDX-License-Identifier: Apache-2.0 -/
module

public import LengthSeven.Basic

/-! The walk-space carrier for core Lemma 6.6. Only symmetry and bilinearity
are assumed of the form. The short vector relations are inputs. -/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace AlbertSequential.LengthSeven

/-- The paper's normalized walk space, including indefinite and degenerate forms. -/
structure AlgebraicWalkSpace (V : Type*) [AddCommGroup V] [Module ℝ V] where
  form : V →ₗ[ℝ] V →ₗ[ℝ] ℝ
  symm : ∀ x y, form x y = form y x
  P : Letter → V →ₗ[ℝ] V
  idem : ∀ i x, P i (P i x) = P i x
  selfAdj : ∀ i x y, form (P i x) y = form x (P i y)
  ξ : V
  fixA : P 0 ξ = ξ
  unit : form ξ ξ = 1

namespace AlgebraicWalkSpace

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (W : AlgebraicWalkSpace V)

def prodL : List Letter → V →ₗ[ℝ] V
  | [] => LinearMap.id
  | i :: w => (W.P i).comp (prodL w)

@[simp] theorem prodL_nil_apply (x : V) : W.prodL [] x = x := rfl

@[simp] theorem prodL_cons_apply (i : Letter) (w : List Letter) (x : V) :
    W.prodL (i :: w) x = W.P i (W.prodL w x) := rfl

theorem prodL_append (u v : List Letter) (x : V) :
    W.prodL (u ++ v) x = W.prodL u (W.prodL v x) := by
  induction u with
  | nil => rfl
  | cons i u ih => simp only [List.cons_append, prodL_cons_apply, ih]

theorem adjoint_prodL (w : List Letter) (x y : V) :
    W.form (W.prodL w x) y = W.form x (W.prodL w.reverse y) := by
  induction w generalizing y with
  | nil => rfl
  | cons i w ih =>
    rw [prodL_cons_apply, W.selfAdj, ih, List.reverse_cons, W.prodL_append]
    rfl

/-- Chronological history vector. -/
def pathVec (w : List Letter) : V := W.prodL w.reverse W.ξ

def L (w : List Letter) : ℝ := W.form W.ξ (W.prodL w W.ξ)

theorem form_pathVec (u v : List Letter) :
    W.form (W.pathVec u) (W.pathVec v) = W.L (u ++ v.reverse) := by
  rw [L, W.prodL_append, pathVec, pathVec, W.adjoint_prodL, List.reverse_reverse]

theorem L_reverse (w : List Letter) : W.L w.reverse = W.L w := by
  unfold L
  rw [← W.adjoint_prodL, W.symm (W.prodL w W.ξ)]

theorem L_drop_leftA (w : List Letter) : W.L (0 :: w) = W.L w := by
  simp only [L, prodL_cons_apply, ← W.selfAdj, W.fixA]

theorem L_drop_rightA (w : List Letter) : W.L (w ++ [0]) = W.L w := by
  simp only [L, W.prodL_append, prodL_cons_apply, prodL_nil_apply, W.fixA]

theorem L_merge (u : List Letter) (i : Letter) (v : List Letter) :
    W.L (u ++ i :: i :: v) = W.L (u ++ i :: v) := by
  simp only [L, W.prodL_append, prodL_cons_apply, W.idem]

end AlgebraicWalkSpace

/-- Only the singleton and six-letter values and the three short vector rules
printed in the reduction lemma. Each history is a word of yes labels. -/
structure AlgebraicWalkHypotheses {V : Type*} [AddCommGroup V] [Module ℝ V]
    (W : AlgebraicWalkSpace V) (τ : TraceData) : Prop where
  singleton : ∀ x : Letter, x ≠ 0 → W.L [x] = τ.o 0 x
  six : ∀ x y z : Letter, IsOrderingBCD x y z →
    W.L [x, y, 0, z, y, x] = τ.o 0 x * τ.o x y * τ.R 0 y z
  r1 : ∀ (t : List Letter) (q v : Letter), q ≠ v → t.length ≤ 2 →
    let η := W.P q (W.pathVec t)
    W.P q (W.P v (W.P q η)) = τ.o q v • η
  r2 : ∀ (t : List Letter) (q v w : Letter), q ≠ v → v ≠ w → q ≠ w → t.length ≤ 1 →
    let η := W.P q (W.pathVec t)
    W.P q (W.P v (W.P w (W.P q η))) + W.P q (W.P w (W.P v (W.P q η))) =
      (2 * τ.R q v w) • η
  r3 : ∀ x y z : Letter, IsOrderingBCD x y z →
    W.P 0 (W.P x (W.P y (W.P z (W.P 0 W.ξ)))) +
      W.P 0 (W.P z (W.P y (W.P x (W.P 0 W.ξ)))) = (2 * τ.om y) • W.ξ

namespace AlgebraicWalkHypotheses

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
  {W : AlgebraicWalkSpace V} {τ : TraceData} (h : AlgebraicWalkHypotheses W τ)

open AlgebraicWalkSpace
include h

theorem L_r1 (u v : List Letter) (i j : Letter) (hij : i ≠ j) (hv : v.length ≤ 2) :
    W.L (u ++ [i, j, i] ++ v) = τ.o i j * W.L (u ++ [i] ++ v) := by
  have hh := h.r1 v.reverse i j hij (by simpa only [List.length_reverse] using hv)
  simp only [pathVec, List.reverse_reverse, W.idem] at hh
  have hp := congrArg (fun x => W.form W.ξ (W.prodL u x)) hh
  simpa only [List.append_assoc, L, W.prodL_append, List.cons_append, List.nil_append,
    prodL_cons_apply, map_smul, smul_eq_mul] using hp

theorem L_r2 (u v : List Letter) (i j k : Letter) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hv : v.length ≤ 1) :
    W.L (u ++ [i, j, k, i] ++ v) + W.L (u ++ [i, k, j, i] ++ v) =
      (2 * τ.R i j k) * W.L (u ++ [i] ++ v) := by
  have hh := h.r2 v.reverse i j k hij hjk hik (by simpa only [List.length_reverse] using hv)
  simp only [pathVec, List.reverse_reverse, W.idem] at hh
  have hp := congrArg (fun x => W.form W.ξ (W.prodL u x)) hh
  simpa only [List.append_assoc, L, W.prodL_append, List.cons_append, List.nil_append,
    prodL_cons_apply, map_add, map_smul, smul_eq_mul] using hp

theorem L_r3_afterA (u : List Letter) (i j k : Letter) (hijk : IsOrderingBCD i j k) :
    W.L (u ++ [0, i, j, k]) + W.L (u ++ [0, k, j, i]) = (2 * τ.om j) * W.L (u ++ [0]) := by
  have hh := h.r3 i j k hijk
  simp only [W.fixA] at hh
  have hp := congrArg (fun x => W.form W.ξ (W.prodL u x)) hh
  simpa only [L, W.prodL_append, prodL_cons_apply, prodL_nil_apply, W.fixA,
    map_add, map_smul, smul_eq_mul] using hp

theorem L_r3_base (i j k : Letter) (hijk : IsOrderingBCD i j k) :
    W.L [i, j, k] + W.L [k, j, i] = 2 * τ.om j := by
  have hs := h.L_r3_afterA [] i j k hijk
  simp only [List.nil_append, W.L_drop_leftA] at hs
  rw [show W.L [] = 1 from W.unit, mul_one] at hs
  exact hs

theorem L_second_A (i : Letter) (hi : i ≠ 0) (w : List Letter) :
    W.L (i :: 0 :: w) = τ.o 0 i * W.L w := by
  have hs := h.L_r1 w.reverse [] 0 i hi.symm (by simp)
  simp only [List.append_nil, ← W.L_reverse (w.reverse ++ [0, i, 0]),
    List.reverse_append, List.reverse_reverse, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, W.L_drop_leftA] at hs
  rwa [W.L_drop_rightA, W.L_reverse] at hs

theorem L_pair (i j : Letter) (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) :
    W.L [i, j] = τ.R 0 i j := by
  have hh := h.L_r2 [] [] 0 i j hi.symm hij hj.symm (by simp)
  have hc (i j : Letter) : W.L [0, i, j, 0] = W.L [i, j] := by
    rw [W.L_drop_leftA]
    exact W.L_drop_rightA [i, j]
  have hre : W.L [j, i] = W.L [i, j] := W.L_reverse [i, j]
  simp only [List.nil_append, List.append_nil] at hh
  rw [hc, hc, W.L_drop_leftA, show W.L [] = 1 from W.unit, mul_one, hre] at hh
  linarith only [hh]

end AlgebraicWalkHypotheses

/-- Scalar identities induced by the paper's walk and vector hypotheses. -/
structure AlgebraicWalkRules (τ : TraceData) (L : List Letter → ℝ) : Prop where
  empty : L [] = 1
  reverse : ∀ w, L w.reverse = L w
  dropLeftA : ∀ w, L (0 :: w) = L w
  dropRightA : ∀ w, L (w ++ [0]) = L w
  merge : ∀ u i v, L (u ++ i :: i :: v) = L (u ++ i :: v)
  singleton : ∀ i, i ≠ 0 → L [i] = τ.o 0 i
  secondA : ∀ i, i ≠ 0 → ∀ w, L (i :: 0 :: w) = τ.o 0 i * L w
  pair : ∀ i j, i ≠ 0 → j ≠ 0 → i ≠ j → L [i, j] = τ.R 0 i j
  six : ∀ i j k, IsOrderingBCD i j k → L [i, j, 0, k, j, i] = τ.o 0 i * τ.o i j * τ.R 0 j k
  r1 : ∀ u v i j, i ≠ j → v.length ≤ 2 → L (u ++ [i, j, i] ++ v) = τ.o i j * L (u ++ [i] ++ v)
  r2 : ∀ u v i j k, i ≠ j → j ≠ k → i ≠ k → v.length ≤ 1 →
    L (u ++ [i, j, k, i] ++ v) + L (u ++ [i, k, j, i] ++ v) = (2 * τ.R i j k) * L (u ++ [i] ++ v)
  r3Base : ∀ i j k, IsOrderingBCD i j k → L [i, j, k] + L [k, j, i] = 2 * τ.om j
  r3AfterA : ∀ u i j k, IsOrderingBCD i j k →
    L (u ++ [0, i, j, k]) + L (u ++ [0, k, j, i]) = (2 * τ.om j) * L (u ++ [0])

theorem AlgebraicWalkHypotheses.scalarRules {V : Type*} [AddCommGroup V] [Module ℝ V]
    {W : AlgebraicWalkSpace V} {τ : TraceData} (h : AlgebraicWalkHypotheses W τ) : AlgebraicWalkRules τ W.L where
  empty := W.unit
  reverse := W.L_reverse
  dropLeftA := W.L_drop_leftA
  dropRightA := W.L_drop_rightA
  merge := W.L_merge
  singleton := h.singleton
  secondA := h.L_second_A
  pair := h.L_pair
  six := h.six
  r1 := h.L_r1
  r2 := h.L_r2
  r3Base := h.L_r3_base
  r3AfterA := h.L_r3_afterA

end AlbertSequential.LengthSeven
