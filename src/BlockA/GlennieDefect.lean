/- SPDX-License-Identifier: Apache-2.0 -/
module

public import AppF.GlennieIngredients
public import ComplexWindowDeterminantAndMax
public import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # `thm:glennie` Step 3: Total Defect Norm Identity

Coordinate-free Second-Tits proof (valid for every `p_D : Albert` with `IsAtom p_D`, with no
Zariski-density patch or diagonal-entry exclusion) of:
* `defectVec p_D = (3 : ℝ) • defectAdI (projPerpAlbert (jordanMul M M))`, where
  `M = projPerpAlbert p_D = p_D - standardComplexWindow.embedding (windowProj standardComplexWindow p_D)`,
* `tracePairing (defectVec p_D) (defectVec p_D) = 72 * (windowProj standardComplexWindow p_D : ComplexMatrix3).det.re`.
-/

@[expose] public section

namespace AlbertSequential.AppF

set_option autoImplicit false
set_option linter.unusedSimpArgs false

noncomputable section

/-! ## Section 1: Private Coordinate Helpers -/

private theorem albert_ext' {x y : Albert}
    (hd0 : x.1 0 = y.1 0) (hd1 : x.1 1 = y.1 1) (hd2 : x.1 2 = y.1 2)
    (ho0 : x.2 0 = y.2 0) (ho1 : x.2 1 = y.2 1) (ho2 : x.2 2 = y.2 2) : x = y := by
  apply Prod.ext <;> funext k <;> fin_cases k <;> assumption

private theorem albert_zero_fst (j : Fin 3) : (0 : Albert).1 j = 0 := rfl
private theorem albert_zero_snd (k : Fin 3) : (0 : Albert).2 k = 0 := rfl
private theorem albert_add_fst (x y : Albert) (j : Fin 3) : (x + y).1 j = x.1 j + y.1 j := rfl
private theorem albert_add_snd (x y : Albert) (k : Fin 3) : (x + y).2 k = x.2 k + y.2 k := rfl
private theorem albert_sub_fst (x y : Albert) (j : Fin 3) : (x - y).1 j = x.1 j - y.1 j := rfl
private theorem albert_sub_snd (x y : Albert) (k : Fin 3) : (x - y).2 k = x.2 k - y.2 k := rfl
private theorem albert_neg_fst (x : Albert) (j : Fin 3) : (-x).1 j = -x.1 j := rfl
private theorem albert_neg_snd (x : Albert) (k : Fin 3) : (-x).2 k = -x.2 k := rfl
private theorem albert_smul_fst (r : ℝ) (x : Albert) (j : Fin 3) : (r • x).1 j = r * x.1 j := rfl
private theorem albert_smul_snd (r : ℝ) (x : Albert) (k : Fin 3) : (r • x).2 k = r • x.2 k := rfl

private theorem q_re_add (p q : Quaternion ℝ) : (p + q).re = p.re + q.re := rfl
private theorem q_imI_add (p q : Quaternion ℝ) : (p + q).imI = p.imI + q.imI := rfl
private theorem q_imJ_add (p q : Quaternion ℝ) : (p + q).imJ = p.imJ + q.imJ := rfl
private theorem q_imK_add (p q : Quaternion ℝ) : (p + q).imK = p.imK + q.imK := rfl
private theorem q_re_sub (p q : Quaternion ℝ) : (p - q).re = p.re - q.re := rfl
private theorem q_imI_sub (p q : Quaternion ℝ) : (p - q).imI = p.imI - q.imI := rfl
private theorem q_imJ_sub (p q : Quaternion ℝ) : (p - q).imJ = p.imJ - q.imJ := rfl
private theorem q_imK_sub (p q : Quaternion ℝ) : (p - q).imK = p.imK - q.imK := rfl
private theorem q_re_neg (p : Quaternion ℝ) : (-p).re = -p.re := rfl
private theorem q_imI_neg (p : Quaternion ℝ) : (-p).imI = -p.imI := rfl
private theorem q_imJ_neg (p : Quaternion ℝ) : (-p).imJ = -p.imJ := rfl
private theorem q_imK_neg (p : Quaternion ℝ) : (-p).imK = -p.imK := rfl
private theorem q_re_smul (r : ℝ) (p : Quaternion ℝ) : (r • p).re = r * p.re := rfl
private theorem q_imI_smul (r : ℝ) (p : Quaternion ℝ) : (r • p).imI = r * p.imI := rfl
private theorem q_imJ_smul (r : ℝ) (p : Quaternion ℝ) : (r • p).imJ = r * p.imJ := rfl
private theorem q_imK_smul (r : ℝ) (p : Quaternion ℝ) : (r • p).imK = r * p.imK := rfl
private theorem q_re_zero : (0 : Quaternion ℝ).re = 0 := rfl
private theorem q_imI_zero : (0 : Quaternion ℝ).imI = 0 := rfl
private theorem q_imJ_zero : (0 : Quaternion ℝ).imJ = 0 := rfl
private theorem q_imK_zero : (0 : Quaternion ℝ).imK = 0 := rfl
private theorem q_re_star (p : Quaternion ℝ) : (star p).re = p.re := by simp
private theorem q_imI_star (p : Quaternion ℝ) : (star p).imI = -p.imI := by simp
private theorem q_imJ_star (p : Quaternion ℝ) : (star p).imJ = -p.imJ := by simp
private theorem q_imK_star (p : Quaternion ℝ) : (star p).imK = -p.imK := by simp

private theorem hermE_apply' (k i j : Fin 3) :
    (hermE k : ComplexMatrix3) i j = if i = k ∧ j = k then 1 else 0 := by
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [hermE, hermitian3Equiv, mkHerm3Matrix] <;>
    (apply Complex.ext <;> simp)

private theorem hermRe_apply' (k i j : Fin 3) :
    (hermRe k : ComplexMatrix3) i j =
      if (k = 0 ∧ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0))) ∨
         (k = 1 ∧ ((i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0))) ∨
         (k = 2 ∧ ((i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1))) then 1 else 0 := by
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [hermRe, hermitian3Equiv, mkHerm3Matrix] <;>
    (apply Complex.ext <;> simp)

private theorem hermIm_apply' (k i j : Fin 3) :
    (hermIm k : ComplexMatrix3) i j =
      if (k = 0 ∧ i = 0 ∧ j = 1) ∨ (k = 1 ∧ i = 0 ∧ j = 2) ∨ (k = 2 ∧ i = 1 ∧ j = 2) then Complex.I
      else if (k = 0 ∧ i = 1 ∧ j = 0) ∨ (k = 1 ∧ i = 2 ∧ j = 0) ∨ (k = 2 ∧ i = 2 ∧ j = 1) then -Complex.I
      else 0 := by
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [hermIm, hermitian3Equiv, mkHerm3Matrix] <;>
    (apply Complex.ext <;> simp)

/-! ## Section 2: Octonion `ℂ_i ⊕ ℂ_i^⊥` and `octAdI` Identities -/

/-- Membership in the distinguished complex subalgebra `ℂ_i = span(1, i) ⊂ Octonion`. -/
def InC (u : Octonion) : Prop := u.1.imJ = 0 ∧ u.1.imK = 0 ∧ u.2 = 0

theorem octAdI_add (u v : Octonion) : octAdI (u + v) = octAdI u + octAdI v := by
  unfold octAdI
  rw [octonionMul_add_right, octonionMul_add_left]
  abel

theorem octAdI_sub (u v : Octonion) : octAdI (u - v) = octAdI u - octAdI v := by
  unfold octAdI
  rw [octonionMul_sub_right, octonionMul_sub_left]
  abel

theorem octAdI_smul (r : ℝ) (u : Octonion) : octAdI (r • u) = r • octAdI u := by
  unfold octAdI
  rw [octonionMul_smul_right, octonionMul_smul_left, smul_sub]

theorem octAdI_zero : octAdI 0 = 0 := by
  unfold octAdI
  rw [octonionMul_zero_right, octonionMul_zero_left, sub_zero]

theorem octAdI_neg (u : Octonion) : octAdI (-u) = -octAdI u := by
  rw [← neg_one_smul ℝ u, octAdI_smul, neg_one_smul]

theorem octAdI_conj (u : Octonion) : octAdI (octonionConj u) = octonionConj (octAdI u) := by
  apply oct_ext' <;>
    simp [octAdI, q_re_sub, q_imI_sub, q_imJ_sub, q_imK_sub,
      q_re_neg, q_imI_neg, q_imJ_neg, q_imK_neg,
      q_re_star, q_imI_star, q_imJ_star, q_imK_star,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;>
    ring

theorem octAdI_of_inC {a : Octonion} (ha : InC a) : octAdI a = 0 := by
  rcases ha with ⟨hj, hk, hs⟩
  apply oct_ext' <;>
    (simp [octAdI, hj, hk, hs, q_re_sub, q_imI_sub, q_imJ_sub, q_imK_sub,
      q_re_zero, q_imI_zero, q_imJ_zero, q_imK_zero,
      q_re_star, q_imI_star, q_imJ_star, q_imK_star,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul];
      try ring)

theorem inC_projC (u : Octonion) : InC (projC u) := ⟨rfl, rfl, rfl⟩

theorem inC_complexToOctonion (z : ℂ) : InC (complexToOctonion z) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [complexToOctonion_apply]

theorem inC_conj {a : Octonion} (ha : InC a) : InC (octonionConj a) := by
  rcases ha with ⟨hj, hk, hs⟩
  refine ⟨?_, ?_, ?_⟩
  · simp [oct_conj_fst, hj]
  · simp [oct_conj_fst, hk]
  · simp [oct_conj_snd, hs]

theorem octAdI_projC (u : Octonion) : octAdI (projC u) = 0 :=
  octAdI_of_inC (inC_projC u)

theorem octAdI_complexToOctonion (z : ℂ) : octAdI (complexToOctonion z) = 0 :=
  octAdI_of_inC (inC_complexToOctonion z)

theorem inCperp_projPerp (u : Octonion) : InCperp (projPerp u) := by
  refine ⟨?_, ?_⟩
  · change (u - projC u).1.re = 0
    rw [oct_sub_fst, q_re_sub, projC_fst]
    ring
  · change (u - projC u).1.imI = 0
    rw [oct_sub_fst, q_imI_sub, projC_fst]
    ring

theorem inCperp_conj {u : Octonion} (hu : InCperp u) : InCperp (octonionConj u) := by
  refine ⟨?_, ?_⟩ <;> simp [oct_conj_fst, hu.1, hu.2]

theorem octonionConj_of_inCperp {u : Octonion} (hu : InCperp u) : octonionConj u = -u := by
  apply oct_ext' <;> simp [hu.1, hu.2, q_re_star, q_imI_star, q_imJ_star, q_imK_star,
    q_re_neg, q_imI_neg, q_imJ_neg, q_imK_neg]

theorem inCperp_octAdI (u : Octonion) : InCperp (octAdI u) := by
  refine ⟨?_, ?_⟩ <;>
    simp [octAdI, q_re_sub, q_imI_sub, q_re_star, q_imI_star, q_imJ_star, q_imK_star,
      Quaternion.re_mul, Quaternion.imI_mul]

theorem octAdI_of_inCperp {u : Octonion} (hu : InCperp u) :
    octAdI u = (2 : ℝ) • octonionMul octI u := by
  apply oct_ext' <;>
    (simp [octAdI, hu.1, hu.2, q_re_sub, q_imI_sub, q_imJ_sub, q_imK_sub,
      q_re_smul, q_imI_smul, q_imJ_smul, q_imK_smul,
      q_re_star, q_imI_star, q_imJ_star, q_imK_star,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul];
      try ring)

theorem octDot_inC_inCperp {a u : Octonion} (ha : InC a) (hu : InCperp u) : octDot a u = 0 := by
  rw [octDot_coords, ha.1, ha.2.1, ha.2.2, hu.1, hu.2]
  simp

theorem octDot_self_octAdI (u : Octonion) : octDot u (octAdI u) = 0 := by
  rw [octDot_coords]
  simp [octAdI, q_re_sub, q_imI_sub, q_imJ_sub, q_imK_sub,
    q_re_star, q_imI_star, q_imJ_star, q_imK_star,
    Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
  ring

theorem octNormSq_octAdI_of_perp {u : Octonion} (hu : InCperp u) :
    octNormSq (octAdI u) = 4 * octNormSq u := by
  rw [octNormSq_coords, octNormSq_coords]
  simp [octAdI, hu.1, hu.2, q_re_sub, q_imI_sub, q_imJ_sub, q_imK_sub,
    q_re_star, q_imI_star, q_imJ_star, q_imK_star,
    Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
  ring

theorem octAdI_mul_inC_left {a : Octonion} (ha : InC a) (u : Octonion) :
    octAdI (octonionMul a u) = octonionMul a (octAdI u) := by
  rcases ha with ⟨hj, hk, hs⟩
  apply oct_ext' <;>
    simp [octAdI, hj, hk, hs, q_re_sub, q_imI_sub, q_imJ_sub, q_imK_sub,
      q_re_zero, q_imI_zero, q_imJ_zero, q_imK_zero,
      q_re_star, q_imI_star, q_imJ_star, q_imK_star,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;>
    ring

theorem octAdI_mul_inC_right {a : Octonion} (ha : InC a) (u : Octonion) :
    octAdI (octonionMul u a) = octonionMul (octAdI u) a := by
  rcases ha with ⟨hj, hk, hs⟩
  apply oct_ext' <;>
    simp [octAdI, hj, hk, hs, q_re_sub, q_imI_sub, q_imJ_sub, q_imK_sub,
      q_re_zero, q_imI_zero, q_imJ_zero, q_imK_zero,
      q_re_star, q_imI_star, q_imJ_star, q_imK_star,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;>
    ring

theorem inCperp_mul_inC_left {a u : Octonion} (ha : InC a) (hu : InCperp u) :
    InCperp (octonionMul a u) := by
  rcases ha with ⟨hj, hk, hs⟩
  refine ⟨?_, ?_⟩ <;>
    simp [hj, hk, hs, hu.1, hu.2, q_re_zero, q_imI_zero, q_imJ_zero, q_imK_zero,
      Quaternion.re_mul, Quaternion.imI_mul]

theorem inCperp_mul_inC_right {u a : Octonion} (hu : InCperp u) (ha : InC a) :
    InCperp (octonionMul u a) := by
  rcases ha with ⟨hj, hk, hs⟩
  refine ⟨?_, ?_⟩ <;>
    simp [hj, hk, hs, hu.1, hu.2, q_re_zero, q_imI_zero, q_imJ_zero, q_imK_zero,
      q_re_star, q_imI_star, q_imJ_star, q_imK_star,
      Quaternion.re_mul, Quaternion.imI_mul]

theorem projC_add (u v : Octonion) : projC (u + v) = projC u + projC v := by
  apply oct_ext' <;> first | rfl | (change (0 : ℝ) = 0 + 0; ring)

theorem projC_add_projPerp (u : Octonion) : projC u + projPerp u = u := by
  unfold projPerp
  abel

theorem projPerp_eq_self_of_inCperp {u : Octonion} (hu : InCperp u) : projPerp u = u := by
  apply oct_ext'
  · change (u - projC u).1.re = u.1.re
    rw [oct_sub_fst, q_re_sub, projC_fst]; simp [hu.1]
  · change (u - projC u).1.imI = u.1.imI
    rw [oct_sub_fst, q_imI_sub, projC_fst]; simp [hu.2]
  · change (u - projC u).1.imJ = u.1.imJ
    rw [oct_sub_fst, q_imJ_sub, projC_fst]; simp
  · change (u - projC u).1.imK = u.1.imK
    rw [oct_sub_fst, q_imK_sub, projC_fst]; simp
  · change (u - projC u).2.re = u.2.re
    rw [oct_sub_snd, q_re_sub, projC_snd]; simp
  · change (u - projC u).2.imI = u.2.imI
    rw [oct_sub_snd, q_imI_sub, projC_snd]; simp
  · change (u - projC u).2.imJ = u.2.imJ
    rw [oct_sub_snd, q_imJ_sub, projC_snd]; simp
  · change (u - projC u).2.imK = u.2.imK
    rw [oct_sub_snd, q_imK_sub, projC_snd]; simp

theorem octNormSq_projC_add_projPerp (u : Octonion) :
    octNormSq u = octNormSq (projC u) + octNormSq (projPerp u) := by
  rw [octNormSq_coords, octNormSq_coords, octNormSq_coords]
  unfold projPerp
  simp only [oct_sub_fst, oct_sub_snd, q_re_sub, q_imI_sub, q_imJ_sub, q_imK_sub,
    projC_fst, projC_snd, q_re_zero, q_imI_zero, q_imJ_zero, q_imK_zero]
  ring

/-- On `C_i^⊥ × C_i^⊥`: `u B(v) + B(u) v = -2 B(π⊥(uv))`. -/
theorem octonionMul_perp_octAdI_symm {u v : Octonion} (hu : InCperp u) (hv : InCperp v) :
    octonionMul u (octAdI v) + octonionMul (octAdI u) v =
      (-2 : ℝ) • octAdI (projPerp (octonionMul u v)) := by
  have hleib := octAdI_leibniz_defect u v
  have hassoc := assoc_i_of_perp u v hu hv
  have had_w : octAdI (projPerp (octonionMul u v)) =
      (2 : ℝ) • octonionMul octI (projPerp (octonionMul u v)) :=
    octAdI_of_inCperp (inCperp_projPerp _)
  have had_uv : octAdI (octonionMul u v) = octAdI (projPerp (octonionMul u v)) := by
    conv_lhs => rw [← projC_add_projPerp (octonionMul u v)]
    rw [octAdI_add, octAdI_projC, zero_add]
  have hassoc' : octAssoc octI u v = -octAdI (projPerp (octonionMul u v)) := by
    rw [hassoc, had_w]
    module
  rw [hassoc', had_uv] at hleib
  calc
    octonionMul u (octAdI v) + octonionMul (octAdI u) v
      = octAdI (projPerp (octonionMul u v)) -
          (octAdI (projPerp (octonionMul u v)) - octonionMul (octAdI u) v -
            octonionMul u (octAdI v)) := by abel
    _ = octAdI (projPerp (octonionMul u v)) -
          (-3 : ℝ) • (-octAdI (projPerp (octonionMul u v))) := by rw [hleib]
    _ = (-2 : ℝ) • octAdI (projPerp (octonionMul u v)) := by module

/-! ## Section 3: `defectAdI`, `defectVec`, `projPerpAlbert`, and the 4-Line Formula -/

/-- Entrywise commutator `[i I₃, -]` on `Albert`, vanishing on diagonals and applying `octAdI`
to off-diagonals. -/
def defectAdI : Albert →ₗ[ℝ] Albert where
  toFun z := (0, fun k => octAdI (z.2 k))
  map_add' x y := by
    apply Prod.ext
    · funext i; exact (add_zero (0 : ℝ)).symm
    · funext k; exact octAdI_add (x.2 k) (y.2 k)
  map_smul' r x := by
    apply Prod.ext
    · funext i; exact (smul_zero r).symm
    · funext k; exact octAdI_smul r (x.2 k)

@[simp] theorem defectAdI_apply (z : Albert) :
    defectAdI z = (0, fun k => octAdI (z.2 k)) := rfl

@[simp] theorem defectAdI_fst (z : Albert) (i : Fin 3) : (defectAdI z).1 i = 0 := rfl

@[simp] theorem defectAdI_snd (z : Albert) (k : Fin 3) : (defectAdI z).2 k = octAdI (z.2 k) := rfl

/-- The Glennie defect vector `Def(z) = B(z) - 2 z ∘ B(z)`. -/
def defectVec (z : Albert) : Albert :=
  defectAdI z - (2 : ℝ) • jordanMul z (defectAdI z)

/-- Orthogonal projection onto `W^⊥ = (H₃(ℂ_i))^⊥ ⊂ Albert`. -/
def projPerpAlbert (z : Albert) : Albert :=
  z - standardComplexWindow.embedding (windowProj standardComplexWindow z)

/-- Predicate `m ∈ W^⊥`: zero diagonal and off-diagonal entries in `ℂ_i^⊥`. -/
def InWPerp (m : Albert) : Prop :=
  (∀ i : Fin 3, m.1 i = 0) ∧ (∀ k : Fin 3, InCperp (m.2 k))

theorem standardComplexWindow_embedding_windowProj (z : Albert) :
    standardComplexWindow.embedding (windowProj standardComplexWindow z) =
      (z.1, fun k => projC (z.2 k)) := by
  have hdiag : ∀ i : Fin 3, tracePairing z (standardComplexWindow.embedding (hermE i)) = z.1 i := by
    intro i
    rw [tracePairing_eq_coords]
    have hs : ∀ j : Fin 3, (standardComplexWindow.embedding (hermE i)).2 j = 0 := by
      intro j
      fin_cases i <;> fin_cases j <;>
        (apply oct_ext' <;>
          simp [standardComplexWindow_apply, complexHermToAlbert, hermE_apply',
            complexToOctonion_apply])
    have hd : ∀ j : Fin 3, (standardComplexWindow.embedding (hermE i)).1 j =
        if j = i then 1 else 0 := by
      intro j
      fin_cases i <;> fin_cases j <;>
        simp [standardComplexWindow_apply, complexHermToAlbert, hermE_apply']
    simp only [hs 0, hs 1, hs 2, octDot_zero_right, hd 0, hd 1, hd 2]
    fin_cases i <;> simp
  have hre : ∀ k : Fin 3,
      tracePairing z (standardComplexWindow.embedding (hermRe k)) = 2 * (z.2 k).1.re := by
    intro k
    rw [tracePairing_eq_coords]
    have hd : ∀ j : Fin 3, (standardComplexWindow.embedding (hermRe k)).1 j = 0 := by
      intro j
      fin_cases k <;> fin_cases j <;>
        simp [standardComplexWindow_apply, complexHermToAlbert, hermRe_apply']
    have hs : ∀ j : Fin 3, (standardComplexWindow.embedding (hermRe k)).2 j =
        if j = k then octonionScalar 1 else 0 := by
      intro j
      fin_cases k <;> fin_cases j <;>
        (apply oct_ext' <;>
          simp [standardComplexWindow_apply, complexHermToAlbert, hermRe_apply',
            complexToOctonion_apply])
    rw [hd 0, hd 1, hd 2, hs 0, hs 1, hs 2]
    fin_cases k <;>
      simp [octDot_zero_right, octDot_coords, oct_scalar_fst, oct_scalar_snd]
  have him : ∀ k : Fin 3,
      tracePairing z (standardComplexWindow.embedding (hermIm k)) = 2 * (z.2 k).1.imI := by
    intro k
    rw [tracePairing_eq_coords]
    have hd : ∀ j : Fin 3, (standardComplexWindow.embedding (hermIm k)).1 j = 0 := by
      intro j
      fin_cases k <;> fin_cases j <;>
        simp [standardComplexWindow_apply, complexHermToAlbert, hermIm_apply']
    have hs : ∀ j : Fin 3, (standardComplexWindow.embedding (hermIm k)).2 j =
        if j = k then octI else 0 := by
      intro j
      fin_cases k <;> fin_cases j <;>
        (apply oct_ext' <;>
          simp [standardComplexWindow_apply, complexHermToAlbert, hermIm_apply',
            complexToOctonion_apply])
    rw [hd 0, hd 1, hd 2, hs 0, hs 1, hs 2]
    fin_cases k <;>
      simp [octDot_zero_right, octDot_coords]
  have hwp : windowProj standardComplexWindow z =
      hermitian3Equiv.symm (z.1, fun k => ⟨(z.2 k).1.re, (z.2 k).1.imI⟩) := by
    dsimp only [windowProj, LinearMap.coe_mk, AddHom.coe_mk]
    congr 1
    apply Prod.ext
    · funext i; exact hdiag i
    · funext k
      apply Complex.ext <;>
        simp only [← standardComplexWindow_apply, hre k, him k] <;> ring
  rw [hwp, standardComplexWindow_apply]
  apply albert_ext'
  · simp [complexHermToAlbert, hermitian3Equiv, mkHerm3Matrix]
  · simp [complexHermToAlbert, hermitian3Equiv, mkHerm3Matrix]
  · simp [complexHermToAlbert, hermitian3Equiv, mkHerm3Matrix]
  · apply oct_ext' <;> simp [complexHermToAlbert, hermitian3Equiv, mkHerm3Matrix,
      complexToOctonion_apply]
  · apply oct_ext' <;> simp [complexHermToAlbert, hermitian3Equiv, mkHerm3Matrix,
      complexToOctonion_apply]
  · apply oct_ext' <;> simp [complexHermToAlbert, hermitian3Equiv, mkHerm3Matrix,
      complexToOctonion_apply]

theorem projPerpAlbert_eq (z : Albert) :
    projPerpAlbert z = (0, fun k => projPerp (z.2 k)) := by
  unfold projPerpAlbert
  rw [standardComplexWindow_embedding_windowProj]
  apply Prod.ext
  · funext i; exact sub_self (z.1 i)
  · funext k; rfl

theorem projPerpAlbert_inWPerp (z : Albert) : InWPerp (projPerpAlbert z) := by
  rw [projPerpAlbert_eq]
  exact ⟨fun _ => rfl, fun k => inCperp_projPerp (z.2 k)⟩

theorem projPerpAlbert_of_inWPerp {m : Albert} (hm : InWPerp m) : projPerpAlbert m = m := by
  rw [projPerpAlbert_eq]
  apply albert_ext'
  · exact (hm.1 0).symm
  · exact (hm.1 1).symm
  · exact (hm.1 2).symm
  · exact projPerp_eq_self_of_inCperp (hm.2 0)
  · exact projPerp_eq_self_of_inCperp (hm.2 1)
  · exact projPerp_eq_self_of_inCperp (hm.2 2)

theorem projPerpAlbert_embedding (A : Hermitian3) :
    projPerpAlbert (standardComplexWindow.embedding A) = 0 := by
  unfold projPerpAlbert
  rw [windowProj_embedding, sub_self]

theorem projPerpAlbert_add (x y : Albert) :
    projPerpAlbert (x + y) = projPerpAlbert x + projPerpAlbert y := by
  unfold projPerpAlbert
  rw [map_add, map_add]
  abel

theorem projPerpAlbert_smul (r : ℝ) (x : Albert) :
    projPerpAlbert (r • x) = r • projPerpAlbert x := by
  unfold projPerpAlbert
  rw [map_smul, map_smul, smul_sub]

theorem projPerpAlbert_add_window (z : Albert) :
    standardComplexWindow.embedding (windowProj standardComplexWindow z) + projPerpAlbert z = z := by
  unfold projPerpAlbert
  abel

theorem defectAdI_embedding (A : Hermitian3) :
    defectAdI (standardComplexWindow.embedding A) = 0 := by
  apply albert_ext'
  · rfl
  · rfl
  · rfl
  · exact octAdI_complexToOctonion _
  · exact octAdI_complexToOctonion _
  · exact octAdI_complexToOctonion _

private theorem embedding_off_inC (A : Hermitian3) (k : Fin 3) :
    InC ((standardComplexWindow.embedding A).2 k) := by
  fin_cases k <;> exact inC_complexToOctonion _

theorem jordanMul_embedding_inWPerp (A : Hermitian3) {m : Albert} (hm : InWPerp m) :
    InWPerp (jordanMul (standardComplexWindow.embedding A) m) := by
  let x := standardComplexWindow.embedding A
  have hx0 : InC (x.2 0) := embedding_off_inC A 0
  have hx1 : InC (x.2 1) := embedding_off_inC A 1
  have hx2 : InC (x.2 2) := embedding_off_inC A 2
  have hd0 : (jordanMul x m).1 0 = 0 := by
    rw [jordanMul_diag_0, hm.1 0, mul_zero, zero_add,
      octDot_inC_inCperp hx0 (hm.2 0), octDot_inC_inCperp hx1 (hm.2 1), zero_add]
  have hd1 : (jordanMul x m).1 1 = 0 := by
    rw [jordanMul_diag_1, hm.1 1, mul_zero, zero_add,
      octDot_inC_inCperp hx0 (hm.2 0), octDot_inC_inCperp hx2 (hm.2 2), zero_add]
  have hd2 : (jordanMul x m).1 2 = 0 := by
    rw [jordanMul_diag_2, hm.1 2, mul_zero, zero_add,
      octDot_inC_inCperp hx1 (hm.2 1), octDot_inC_inCperp hx2 (hm.2 2), zero_add]
  have hsm : ∀ (r : ℝ) (u : Octonion), InCperp u → InCperp (r • u) := fun r u hu =>
    ⟨by simp [oct_smul_fst, hu.1], by simp [oct_smul_fst, hu.2]⟩
  have hadd : ∀ (u v : Octonion), InCperp u → InCperp v → InCperp (u + v) := fun u v hu hv =>
    ⟨by simp [oct_add_fst, hu.1, hv.1], by simp [oct_add_fst, hu.2, hv.2]⟩
  have ho0 : InCperp ((jordanMul x m).2 0) := by
    rw [jordanMul_off_0, hm.1 0, hm.1 1, add_zero, zero_smul, add_zero]
    exact hsm _ _ (hadd _ _
      (hadd _ _ (hsm _ _ (hm.2 0)) (inCperp_mul_inC_left hx1 (inCperp_conj (hm.2 2))))
      (inCperp_mul_inC_right (hm.2 1) (inC_conj hx2)))
  have ho1 : InCperp ((jordanMul x m).2 1) := by
    rw [jordanMul_off_1, hm.1 0, hm.1 2, add_zero, zero_smul, add_zero]
    exact hsm _ _ (hadd _ _
      (hadd _ _ (hsm _ _ (hm.2 1)) (inCperp_mul_inC_left hx0 (hm.2 2)))
      (inCperp_mul_inC_right (hm.2 0) hx2))
  have ho2 : InCperp ((jordanMul x m).2 2) := by
    rw [jordanMul_off_2, hm.1 1, hm.1 2, add_zero, zero_smul, add_zero]
    exact hsm _ _ (hadd _ _
      (hadd _ _ (hsm _ _ (hm.2 2)) (inCperp_mul_inC_left (inC_conj hx0) (hm.2 1)))
      (inCperp_mul_inC_right (inCperp_conj (hm.2 0)) hx1))
  refine ⟨fun i => ?_, fun k => ?_⟩
  · fin_cases i <;> assumption
  · fin_cases k <;> assumption

theorem defectAdI_jordanMul_embedding (A : Hermitian3) {m : Albert} (hm : InWPerp m) :
    defectAdI (jordanMul (standardComplexWindow.embedding A) m) =
      jordanMul (standardComplexWindow.embedding A) (defectAdI m) := by
  have hx0 : InC ((standardComplexWindow.embedding A).2 0) := embedding_off_inC A 0
  have hx1 : InC ((standardComplexWindow.embedding A).2 1) := embedding_off_inC A 1
  have hx2 : InC ((standardComplexWindow.embedding A).2 2) := embedding_off_inC A 2
  have hdm : InWPerp (defectAdI m) := ⟨fun _ => rfl, fun k => inCperp_octAdI (m.2 k)⟩
  have hR : InWPerp (jordanMul (standardComplexWindow.embedding A) (defectAdI m)) :=
    jordanMul_embedding_inWPerp A hdm
  apply albert_ext'
  · exact (hR.1 0).symm
  · exact (hR.1 1).symm
  · exact (hR.1 2).symm
  · dsimp only [defectAdI_snd]
    rw [jordanMul_off_0, jordanMul_off_0]
    simp only [hm.1 0, hm.1 1, defectAdI_fst, defectAdI_snd, add_zero, zero_smul,
      octAdI_smul, octAdI_add, octAdI_mul_inC_left hx1 _, octAdI_mul_inC_right (inC_conj hx2) _,
      octAdI_conj]
  · dsimp only [defectAdI_snd]
    rw [jordanMul_off_1, jordanMul_off_1]
    simp only [hm.1 0, hm.1 2, defectAdI_fst, defectAdI_snd, add_zero, zero_smul,
      octAdI_smul, octAdI_add, octAdI_mul_inC_left hx0 _, octAdI_mul_inC_right hx2 _]
  · dsimp only [defectAdI_snd]
    rw [jordanMul_off_2, jordanMul_off_2]
    simp only [hm.1 1, hm.1 2, defectAdI_fst, defectAdI_snd, add_zero, zero_smul,
      octAdI_smul, octAdI_add, octAdI_mul_inC_left (inC_conj hx0) _, octAdI_mul_inC_right hx1 _,
      octAdI_conj]

theorem jordanMul_defectAdI_inWPerp {m : Albert} (hm : InWPerp m) :
    jordanMul m (defectAdI m) = -defectAdI (projPerpAlbert (jordanMul m m)) := by
  have hm0 : m.1 0 = 0 := hm.1 0
  have hm1 : m.1 1 = 0 := hm.1 1
  have hm2 : m.1 2 = 0 := hm.1 2
  have h12 : (1 / 2 : ℝ) * (-2 : ℝ) = -1 := by norm_num
  apply albert_ext'
  · rw [jordanMul_diag_0, hm0, defectAdI_fst, mul_zero, zero_add,
      defectAdI_snd, defectAdI_snd, octDot_self_octAdI, octDot_self_octAdI, add_zero,
      albert_neg_fst, defectAdI_fst, neg_zero]
  · rw [jordanMul_diag_1, hm1, defectAdI_fst, mul_zero, zero_add,
      defectAdI_snd, defectAdI_snd, octDot_self_octAdI, octDot_self_octAdI, add_zero,
      albert_neg_fst, defectAdI_fst, neg_zero]
  · rw [jordanMul_diag_2, hm2, defectAdI_fst, mul_zero, zero_add,
      defectAdI_snd, defectAdI_snd, octDot_self_octAdI, octDot_self_octAdI, add_zero,
      albert_neg_fst, defectAdI_fst, neg_zero]
  · rw [albert_neg_snd, defectAdI_snd, projPerpAlbert_eq]
    dsimp only
    rw [jordanMul_off_0, jordanMul_off_0]
    simp only [hm0, hm1, defectAdI_fst, add_zero, zero_smul, zero_add]
    have hdup : (1 / 2 : ℝ) •
        (octonionMul (m.2 1) (octonionConj (m.2 2)) +
          octonionMul (m.2 1) (octonionConj (m.2 2))) =
        octonionMul (m.2 1) (octonionConj (m.2 2)) := by
      rw [← two_smul ℝ, smul_smul]; norm_num
    rw [hdup, defectAdI_snd, defectAdI_snd, ← octAdI_conj,
      octonionMul_perp_octAdI_symm (hm.2 1) (inCperp_conj (hm.2 2)),
      smul_smul, h12, neg_one_smul]
  · rw [albert_neg_snd, defectAdI_snd, projPerpAlbert_eq]
    dsimp only
    rw [jordanMul_off_1, jordanMul_off_1]
    simp only [hm0, hm2, defectAdI_fst, add_zero, zero_smul, zero_add]
    have hdup : (1 / 2 : ℝ) •
        (octonionMul (m.2 0) (m.2 2) + octonionMul (m.2 0) (m.2 2)) =
        octonionMul (m.2 0) (m.2 2) := by
      rw [← two_smul ℝ, smul_smul]; norm_num
    rw [hdup, defectAdI_snd, defectAdI_snd,
      octonionMul_perp_octAdI_symm (hm.2 0) (hm.2 2),
      smul_smul, h12, neg_one_smul]
  · rw [albert_neg_snd, defectAdI_snd, projPerpAlbert_eq]
    dsimp only
    rw [jordanMul_off_2, jordanMul_off_2]
    simp only [hm1, hm2, defectAdI_fst, add_zero, zero_smul, zero_add]
    have hdup : (1 / 2 : ℝ) •
        (octonionMul (octonionConj (m.2 0)) (m.2 1) +
          octonionMul (octonionConj (m.2 0)) (m.2 1)) =
        octonionMul (octonionConj (m.2 0)) (m.2 1) := by
      rw [← two_smul ℝ, smul_smul]; norm_num
    rw [hdup, defectAdI_snd, defectAdI_snd, ← octAdI_conj,
      octonionMul_perp_octAdI_symm (inCperp_conj (hm.2 0)) (hm.2 1),
      smul_smul, h12, neg_one_smul]

theorem projPerpAlbert_idempotent {p : Albert} (hp : jordanMul p p = p) :
    let X_W := standardComplexWindow.embedding (windowProj standardComplexWindow p)
    let M := projPerpAlbert p
    M = (2 : ℝ) • jordanMul X_W M + projPerpAlbert (jordanMul M M) := by
  intro X_W M
  have hp_dec : p = X_W + M := (projPerpAlbert_add_window p).symm
  have hsq : p = jordanMul X_W X_W + (2 : ℝ) • jordanMul X_W M + jordanMul M M := by
    conv_lhs => rw [← hp, hp_dec]
    rw [jordanMul_add_left, jordanMul_add_right, jordanMul_add_right,
      jordanMul_comm M X_W, two_smul]
    abel
  have hXX_perp : projPerpAlbert (jordanMul X_W X_W) = 0 := by
    obtain ⟨z, hz⟩ := standardComplexWindow.product_closed
      (windowProj standardComplexWindow p) (windowProj standardComplexWindow p)
    rw [← standardComplexWindow.preserves_product _ _ z hz]
    exact projPerpAlbert_embedding z
  have hXM_perp : projPerpAlbert (jordanMul X_W M) = jordanMul X_W M :=
    projPerpAlbert_of_inWPerp (jordanMul_embedding_inWPerp _ (projPerpAlbert_inWPerp p))
  calc
    M = projPerpAlbert p := rfl
    _ = projPerpAlbert (jordanMul X_W X_W + (2 : ℝ) • jordanMul X_W M + jordanMul M M) := by
          conv_lhs => rw [hsq]
    _ = projPerpAlbert (jordanMul X_W X_W) +
          (2 : ℝ) • projPerpAlbert (jordanMul X_W M) + projPerpAlbert (jordanMul M M) := by
          rw [projPerpAlbert_add, projPerpAlbert_add, projPerpAlbert_smul]
    _ = (2 : ℝ) • jordanMul X_W M + projPerpAlbert (jordanMul M M) := by
          rw [hXX_perp, zero_add, hXM_perp]

theorem defectVec_eq_three_defectAdI_sq {p : Albert} (hp : jordanMul p p = p) :
    defectVec p =
      (3 : ℝ) • defectAdI (projPerpAlbert (jordanMul (projPerpAlbert p) (projPerpAlbert p))) := by
  let X := windowProj standardComplexWindow p
  let X_W := standardComplexWindow.embedding X
  let M := projPerpAlbert p
  have hm_perp : InWPerp M := projPerpAlbert_inWPerp p
  have hp_dec : p = X_W + M := (projPerpAlbert_add_window p).symm
  have had_p : defectAdI p = defectAdI M := by
    rw [hp_dec, map_add, defectAdI_embedding, zero_add]
  have hidem : M - (2 : ℝ) • jordanMul X_W M = projPerpAlbert (jordanMul M M) := by
    have h := projPerpAlbert_idempotent hp
    change M = (2 : ℝ) • jordanMul X_W M + projPerpAlbert (jordanMul M M) at h
    exact sub_eq_iff_eq_add'.mpr h
  unfold defectVec
  rw [had_p]
  conv_lhs =>
    rw [hp_dec, jordanMul_add_left, smul_add,
      ← defectAdI_jordanMul_embedding X hm_perp,
      jordanMul_defectAdI_inWPerp hm_perp]
  calc
    defectAdI M - ((2 : ℝ) • defectAdI (jordanMul X_W M) +
        (2 : ℝ) • (-defectAdI (projPerpAlbert (jordanMul M M))))
      = defectAdI (M - (2 : ℝ) • jordanMul X_W M) +
          (2 : ℝ) • defectAdI (projPerpAlbert (jordanMul M M)) := by
            rw [map_sub, map_smul]; module
    _ = defectAdI (projPerpAlbert (jordanMul M M)) +
          (2 : ℝ) • defectAdI (projPerpAlbert (jordanMul M M)) := by rw [hidem]
    _ = (3 : ℝ) • defectAdI (projPerpAlbert (jordanMul M M)) := by module

/-! ## Section 4: Norm Calculation via `normSq_projPerp` and `3 × 3` Matrix Adjugate -/

theorem tracePairing_defectAdI_self {z : Albert} (hz : InWPerp z) :
    tracePairing (defectAdI z) (defectAdI z) = 4 * tracePairing z z := by
  rw [tracePairing_eq_coords, tracePairing_eq_coords,
    hz.1 0, hz.1 1, hz.1 2, defectAdI_fst, defectAdI_fst, defectAdI_fst]
  simp only [defectAdI_snd, octDot_self, octNormSq_octAdI_of_perp (hz.2 0),
    octNormSq_octAdI_of_perp (hz.2 1), octNormSq_octAdI_of_perp (hz.2 2)]
  ring

/-- Canonical `ℂ³` coordinates of an octonion (projecting onto `ℂ_i^⊥`). -/
def octToC3 (u : Octonion) : Fin 3 → ℂ :=
  ![⟨u.1.imJ, u.1.imK⟩, ⟨u.2.re, u.2.imI⟩, ⟨u.2.imJ, -u.2.imK⟩]

theorem octNormSq_eq_sum_octToC3 {u : Octonion} (hu : InCperp u) :
    octNormSq u = ∑ r : Fin 3, Complex.normSq (octToC3 u r) := by
  rw [octNormSq_coords, Fin.sum_univ_three]
  simp [octToC3, Complex.normSq_apply, hu.1, hu.2]
  ring

theorem octonionMul_projC_complex {u v : Octonion} (hu : InCperp u) (hv : InCperp v) :
    (⟨(octonionMul u v).1.re, (octonionMul u v).1.imI⟩ : ℂ) =
      -∑ r : Fin 3, octToC3 u r * star (octToC3 v r) := by
  apply Complex.ext <;>
    simp [octToC3, Fin.sum_univ_three, hu.1, hu.2, hv.1, hv.2,
      q_re_star, q_imI_star, q_imJ_star, q_imK_star,
      Quaternion.re_mul, Quaternion.imI_mul] <;>
    ring

theorem hNormSq_eq_normSq_dot {u v : Octonion} (hu : InCperp u) (hv : InCperp v) :
    hNormSq u v = Complex.normSq (∑ r : Fin 3, star (octToC3 u r) * octToC3 v r) := by
  have h := congrArg Complex.normSq (octonionMul_projC_complex hu hv)
  have hL : Complex.normSq ⟨(octonionMul u v).1.re, (octonionMul u v).1.imI⟩ = hNormSq u v := by
    simp [hNormSq, Complex.normSq_apply, sq]
  have hR : Complex.normSq (-∑ r : Fin 3, octToC3 u r * star (octToC3 v r)) =
      Complex.normSq (∑ r : Fin 3, star (octToC3 u r) * octToC3 v r) := by
    rw [Complex.normSq_neg, ← Complex.normSq_conj]
    congr 1
    apply Complex.ext <;>
      simp [Fin.sum_univ_three, Complex.mul_re, Complex.mul_im]
  rw [hL, hR] at h
  exact h

theorem octToC3_neg (u : Octonion) : octToC3 (-u) = -octToC3 u := by
  funext r
  fin_cases r <;> apply Complex.ext <;> simp [octToC3, q_imJ_neg, q_imK_neg, q_re_neg, q_imI_neg]

theorem octToC3_conj {u : Octonion} (hu : InCperp u) :
    octToC3 (octonionConj u) = -octToC3 u := by
  rw [octonionConj_of_inCperp hu, octToC3_neg]

/-- The `3 × 3` complex matrix representing the `W^⊥` component `m ∈ W^⊥` in Second-Tits
coordinates (`(M)_{col 0} = m₁₂`, `(M)_{col 1} = \bar{m}₀₂ = -m₀₂`, `(M)_{col 2} = m₀₁`). -/
def perpMatrix (m : Albert) : ComplexMatrix3 :=
  fun r j =>
    if j = 0 then octToC3 (m.2 2) r
    else if j = 1 then -octToC3 (m.2 1) r
    else octToC3 (m.2 0) r

private theorem complex_normSq_eq_mul_conj (z : ℂ) :
    (Complex.normSq z : ℂ) = z * star z := by
  apply Complex.ext
  · simp [Complex.normSq_apply, Complex.mul_re]
  · simp [Complex.mul_im]; ring

private theorem complex_mul_star_re (z : ℂ) : (z * star z).re = Complex.normSq z := by
  rw [← complex_normSq_eq_mul_conj, Complex.ofReal_re]

private theorem normSq_sum_conj_dot_symm (a b : Fin 3 → ℂ) :
    Complex.normSq (∑ r : Fin 3, star (a r) * b r) =
      Complex.normSq (∑ r : Fin 3, star (b r) * a r) := by
  rw [← Complex.normSq_conj (∑ r : Fin 3, star (a r) * b r)]
  congr 1
  apply Complex.ext
  · simp [Fin.sum_univ_three, Complex.mul_re]; ring
  · simp [Fin.sum_univ_three, Complex.mul_im]; ring

private theorem adjugate_fin3_diag_0 (A : ComplexMatrix3) :
    A.adjugate 0 0 = A 1 1 * A 2 2 - A 1 2 * A 2 1 := by
  rw [Matrix.adjugate_fin_three]; rfl

private theorem adjugate_fin3_diag_1 (A : ComplexMatrix3) :
    A.adjugate 1 1 = A 0 0 * A 2 2 - A 0 2 * A 2 0 := by
  rw [Matrix.adjugate_fin_three]; rfl

private theorem adjugate_fin3_diag_2 (A : ComplexMatrix3) :
    A.adjugate 2 2 = A 0 0 * A 1 1 - A 0 1 * A 1 0 := by
  rw [Matrix.adjugate_fin_three]; rfl

private theorem adjugate_fin3_01 (A : ComplexMatrix3) :
    A.adjugate 0 1 = -(A 0 1 * A 2 2 - A 0 2 * A 2 1) := by
  rw [Matrix.adjugate_fin_three]
  dsimp
  ring

private theorem adjugate_fin3_02 (A : ComplexMatrix3) :
    A.adjugate 0 2 = A 0 1 * A 1 2 - A 0 2 * A 1 1 := by
  rw [Matrix.adjugate_fin_three]; rfl

private theorem adjugate_fin3_12 (A : ComplexMatrix3) :
    A.adjugate 1 2 = -(A 0 0 * A 1 2 - A 0 2 * A 1 0) := by
  rw [Matrix.adjugate_fin_three]
  dsimp
  ring

theorem tracePairing_projPerp_jordanMul_self {m : Albert} (hm : InWPerp m) :
    tracePairing (projPerpAlbert (jordanMul m m)) (projPerpAlbert (jordanMul m m)) =
      2 * (((perpMatrix m).conjTranspose * (perpMatrix m)).adjugate).trace.re := by
  let Z := projPerpAlbert (jordanMul m m)
  let H : ComplexMatrix3 := (perpMatrix m).conjTranspose * (perpMatrix m)
  have hH_herm : H.IsHermitian := by
    dsimp [H]
    rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hH_sym : ∀ i j : Fin 3, H j i = star (H i j) := fun i j => by
    have h := congrFun (congrFun hH_herm.eq j) i
    simpa [Matrix.conjTranspose_apply] using h.symm
  have hH00 : H 0 0 = (octNormSq (m.2 2) : ℂ) := by
    simp only [H, Matrix.mul_apply, Matrix.conjTranspose_apply, perpMatrix, Fin.sum_univ_three]
    rw [octNormSq_eq_sum_octToC3 (hm.2 2), Fin.sum_univ_three]
    push_cast
    simp [complex_normSq_eq_mul_conj, mul_comm]
  have hH11 : H 1 1 = (octNormSq (m.2 1) : ℂ) := by
    simp only [H, Matrix.mul_apply, Matrix.conjTranspose_apply, perpMatrix, Fin.sum_univ_three]
    rw [octNormSq_eq_sum_octToC3 (hm.2 1), Fin.sum_univ_three]
    push_cast
    simp [complex_normSq_eq_mul_conj, mul_comm]
  have hH22 : H 2 2 = (octNormSq (m.2 0) : ℂ) := by
    simp only [H, Matrix.mul_apply, Matrix.conjTranspose_apply, perpMatrix, Fin.sum_univ_three]
    rw [octNormSq_eq_sum_octToC3 (hm.2 0), Fin.sum_univ_three]
    push_cast
    simp [complex_normSq_eq_mul_conj, mul_comm]
  have hH01 : H 0 1 = -∑ r : Fin 3, star (octToC3 (m.2 2) r) * octToC3 (m.2 1) r := by
    simp [H, Matrix.mul_apply, Matrix.conjTranspose_apply, perpMatrix, Fin.sum_univ_three]
  have hH02 : H 0 2 = ∑ r : Fin 3, star (octToC3 (m.2 2) r) * octToC3 (m.2 0) r := by
    simp [H, Matrix.mul_apply, Matrix.conjTranspose_apply, perpMatrix, Fin.sum_univ_three]
  have hH12 : H 1 2 = -∑ r : Fin 3, star (octToC3 (m.2 1) r) * octToC3 (m.2 0) r := by
    simp [H, Matrix.mul_apply, Matrix.conjTranspose_apply, perpMatrix, Fin.sum_univ_three]
  have hZ0 : Z.2 0 = projPerp (octonionMul (m.2 1) (octonionConj (m.2 2))) := by
    dsimp only [Z]
    rw [projPerpAlbert_eq]
    dsimp only
    rw [jordanMul_off_0, hm.1 0, hm.1 1, add_zero, zero_smul, zero_add, zero_add,
      ← two_smul ℝ, smul_smul]
    norm_num
  have hZ1 : Z.2 1 = projPerp (octonionMul (m.2 0) (m.2 2)) := by
    dsimp only [Z]
    rw [projPerpAlbert_eq]
    dsimp only
    rw [jordanMul_off_1, hm.1 0, hm.1 2, add_zero, zero_smul, zero_add, zero_add,
      ← two_smul ℝ, smul_smul]
    norm_num
  have hZ2 : Z.2 2 = projPerp (octonionMul (octonionConj (m.2 0)) (m.2 1)) := by
    dsimp only [Z]
    rw [projPerpAlbert_eq]
    dsimp only
    rw [jordanMul_off_2, hm.1 1, hm.1 2, add_zero, zero_smul, zero_add, zero_add,
      ← two_smul ℝ, smul_smul]
    norm_num
  have hnorm0 : octNormSq (Z.2 0) = (H.adjugate 2 2).re := by
    rw [hZ0, normSq_projPerp (m.2 1) (octonionConj (m.2 2)) (hm.2 1) (inCperp_conj (hm.2 2)),
      octNormSq_conj, hNormSq_eq_normSq_dot (hm.2 1) (inCperp_conj (hm.2 2))]
    have hh01 : Complex.normSq (∑ r : Fin 3, star (octToC3 (m.2 1) r) *
        octToC3 (octonionConj (m.2 2)) r) = Complex.normSq (H 0 1) := by
      rw [hH01, Complex.normSq_neg, normSq_sum_conj_dot_symm]
      simp only [octToC3_conj (hm.2 2), Pi.neg_apply, star_neg, neg_mul, Finset.sum_neg_distrib,
        Complex.normSq_neg]
    rw [hh01, adjugate_fin3_diag_2, hH_sym 0 1, hH00, hH11, Complex.sub_re,
      ← Complex.ofReal_mul, Complex.ofReal_re, complex_mul_star_re]
    ring
  have hnorm1 : octNormSq (Z.2 1) = (H.adjugate 1 1).re := by
    rw [hZ1, normSq_projPerp (m.2 0) (m.2 2) (hm.2 0) (hm.2 2),
      hNormSq_eq_normSq_dot (hm.2 0) (hm.2 2)]
    have hh02 : Complex.normSq (∑ r : Fin 3, star (octToC3 (m.2 0) r) * octToC3 (m.2 2) r) =
        Complex.normSq (H 0 2) := by
      rw [hH02, normSq_sum_conj_dot_symm]
    rw [hh02, adjugate_fin3_diag_1, hH_sym 0 2, hH00, hH22, Complex.sub_re,
      ← Complex.ofReal_mul, Complex.ofReal_re, complex_mul_star_re]
    ring
  have hnorm2 : octNormSq (Z.2 2) = (H.adjugate 0 0).re := by
    rw [hZ2, normSq_projPerp (octonionConj (m.2 0)) (m.2 1) (inCperp_conj (hm.2 0)) (hm.2 1),
      octNormSq_conj, hNormSq_eq_normSq_dot (inCperp_conj (hm.2 0)) (hm.2 1)]
    have hh12 : Complex.normSq (∑ r : Fin 3, star (octToC3 (octonionConj (m.2 0)) r) *
          octToC3 (m.2 1) r) = Complex.normSq (H 1 2) := by
      rw [hH12, Complex.normSq_neg, normSq_sum_conj_dot_symm]
      simp only [octToC3_conj (hm.2 0), Pi.neg_apply, mul_neg, Finset.sum_neg_distrib,
        Complex.normSq_neg]
    rw [hh12, adjugate_fin3_diag_0, hH_sym 1 2, hH11, hH22, Complex.sub_re,
      ← Complex.ofReal_mul, Complex.ofReal_re, complex_mul_star_re]
    ring
  have hZperp : InWPerp Z := projPerpAlbert_inWPerp _
  change tracePairing Z Z = 2 * (H.adjugate).trace.re
  rw [tracePairing_eq_coords, hZperp.1 0, hZperp.1 1, hZperp.1 2]
  simp only [octDot_self, hnorm0, hnorm1, hnorm2]
  have htr : (H.adjugate).trace.re =
      (H.adjugate 0 0).re + (H.adjugate 1 1).re + (H.adjugate 2 2).re := by
    simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_three, Complex.add_re]
  rw [htr]
  ring

theorem adjugate_mul_conjTranspose_adjugate (M : ComplexMatrix3) :
    M.adjugate * M.adjugate.conjTranspose = (M.conjTranspose * M).adjugate := by
  rw [Matrix.adjugate_conjTranspose, ← Matrix.adjugate_mul_distrib]

theorem adjugate_conjTranspose_mul_adjugate (M : ComplexMatrix3) :
    M.adjugate.conjTranspose * M.adjugate = (M * M.conjTranspose).adjugate := by
  rw [Matrix.adjugate_conjTranspose, ← Matrix.adjugate_mul_distrib]

private def octToC (o : Octonion) : ℂ := ⟨o.1.re, o.1.imI⟩

private theorem octToC_add (x y : Octonion) : octToC (x + y) = octToC x + octToC y := by
  apply Complex.ext <;> simp [octToC, oct_add_fst, q_re_add, q_imI_add]

private theorem octToC_sub (x y : Octonion) : octToC (x - y) = octToC x - octToC y := by
  apply Complex.ext <;> simp [octToC, oct_sub_fst, q_re_sub, q_imI_sub]

private theorem octToC_smul (r : ℝ) (x : Octonion) : octToC (r • x) = (r : ℂ) * octToC x := by
  apply Complex.ext <;> simp [octToC, oct_smul_fst, q_re_smul, q_imI_smul, Complex.ofReal_mul]

private theorem octToC_zero : octToC 0 = 0 := by
  apply Complex.ext <;> simp [octToC, oct_zero_fst, q_re_zero, q_imI_zero]

private theorem octToC_of_inCperp {u : Octonion} (hu : InCperp u) : octToC u = 0 := by
  apply Complex.ext <;> simp [octToC, hu.1, hu.2]

theorem perpMatrix_gram_eq_adjugate {p : Albert} (hp : IsAtom p) :
    (perpMatrix (projPerpAlbert p)).conjTranspose * (perpMatrix (projPerpAlbert p)) =
      (windowProj standardComplexWindow p : ComplexMatrix3).adjugate := by
  let X := windowProj standardComplexWindow p
  let m := projPerpAlbert p
  let H : ComplexMatrix3 := (perpMatrix m).conjTranspose * (perpMatrix m)
  let A : ComplexMatrix3 := (X : ComplexMatrix3).adjugate
  have hm_perp : InWPerp m := projPerpAlbert_inWPerp p
  have hX_herm : (X : ComplexMatrix3).IsHermitian := X.prop
  have hX_sym : ∀ i j : Fin 3, (X : ComplexMatrix3) j i = star ((X : ComplexMatrix3) i j) :=
    fun i j => by
      have h := congrFun (congrFun hX_herm.eq j) i
      simpa [Matrix.conjTranspose_apply] using h.symm
  have hH_herm : H.IsHermitian := by
    dsimp [H]
    rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hA_herm : A.IsHermitian := by
    dsimp [A]
    rw [Matrix.IsHermitian, Matrix.adjugate_conjTranspose, hX_herm.eq]
  have hH_sym : ∀ i j : Fin 3, H j i = star (H i j) := fun i j => by
    have h := congrFun (congrFun hH_herm.eq j) i
    simpa [Matrix.conjTranspose_apply] using h.symm
  have hA_sym : ∀ i j : Fin 3, A j i = star (A i j) := fun i j => by
    have h := congrFun (congrFun hA_herm.eq j) i
    simpa [Matrix.conjTranspose_apply] using h.symm
  have hX_eq := standardComplexWindow_embedding_windowProj p
  have hXd : ∀ i : Fin 3, (X : ComplexMatrix3) i i = (p.1 i : ℂ) := fun i => by
    have him : ((X : ComplexMatrix3) i i).im = 0 := by
      have h := congrArg Complex.im (hX_sym i i)
      simp at h; linarith
    have hre : ((X : ComplexMatrix3) i i).re = p.1 i := by
      have h := congrArg (fun a : Albert => a.1 i) hX_eq
      simpa [standardComplexWindow_apply, complexHermToAlbert] using h
    exact Complex.ext hre him
  have hX01 : (X : ComplexMatrix3) 0 1 = octToC (p.2 0) := by
    have h := congrArg (fun a : Albert => a.2 0) hX_eq
    apply Complex.ext
    · have := congrArg (fun o : Octonion => o.1.re) h
      simpa [standardComplexWindow_apply, complexHermToAlbert, complexToOctonion_apply, projC,
        octToC] using this
    · have := congrArg (fun o : Octonion => o.1.imI) h
      simpa [standardComplexWindow_apply, complexHermToAlbert, complexToOctonion_apply, projC,
        octToC] using this
  have hX02 : (X : ComplexMatrix3) 0 2 = octToC (p.2 1) := by
    have h := congrArg (fun a : Albert => a.2 1) hX_eq
    apply Complex.ext
    · have := congrArg (fun o : Octonion => o.1.re) h
      simpa [standardComplexWindow_apply, complexHermToAlbert, complexToOctonion_apply, projC,
        octToC] using this
    · have := congrArg (fun o : Octonion => o.1.imI) h
      simpa [standardComplexWindow_apply, complexHermToAlbert, complexToOctonion_apply, projC,
        octToC] using this
  have hX12 : (X : ComplexMatrix3) 1 2 = octToC (p.2 2) := by
    have h := congrArg (fun a : Albert => a.2 2) hX_eq
    apply Complex.ext
    · have := congrArg (fun o : Octonion => o.1.re) h
      simpa [standardComplexWindow_apply, complexHermToAlbert, complexToOctonion_apply, projC,
        octToC] using this
    · have := congrArg (fun o : Octonion => o.1.imI) h
      simpa [standardComplexWindow_apply, complexHermToAlbert, complexToOctonion_apply, projC,
        octToC] using this
  have hm_eq : ∀ k : Fin 3, m.2 k = projPerp (p.2 k) := fun k => by
    dsimp only [m]; rw [projPerpAlbert_eq]
  have hp_split : ∀ k : Fin 3, p.2 k = projC (p.2 k) + m.2 k := fun k => by
    rw [hm_eq k, projC_add_projPerp]
  have hnorm_split : ∀ k : Fin 3,
      octNormSq (p.2 k) = octNormSq (projC (p.2 k)) + octNormSq (m.2 k) := fun k => by
    rw [hm_eq k, octNormSq_projC_add_projPerp]
  have hc_norm : ∀ k : Fin 3,
      octNormSq (projC (p.2 k)) = (p.2 k).1.re ^ 2 + (p.2 k).1.imI ^ 2 := fun k => by
    rw [octNormSq_coords]
    simp [projC]
  have hsharp := albertSharp_of_isAtom hp
  have hs_d0 : p.1 1 * p.1 2 - octNormSq (p.2 2) = 0 := by
    simpa [albertSharp, albert_zero_fst] using congrArg (fun a : Albert => a.1 0) hsharp
  have hs_d1 : p.1 0 * p.1 2 - octNormSq (p.2 1) = 0 := by
    simpa [albertSharp, albert_zero_fst] using congrArg (fun a : Albert => a.1 1) hsharp
  have hs_d2 : p.1 0 * p.1 1 - octNormSq (p.2 0) = 0 := by
    simpa [albertSharp, albert_zero_fst] using congrArg (fun a : Albert => a.1 2) hsharp
  have hH00 : H 0 0 = (octNormSq (m.2 2) : ℂ) := by
    simp only [H, Matrix.mul_apply, Matrix.conjTranspose_apply, perpMatrix, Fin.sum_univ_three]
    rw [octNormSq_eq_sum_octToC3 (hm_perp.2 2), Fin.sum_univ_three]
    push_cast; simp [complex_normSq_eq_mul_conj, mul_comm]
  have hH11 : H 1 1 = (octNormSq (m.2 1) : ℂ) := by
    simp only [H, Matrix.mul_apply, Matrix.conjTranspose_apply, perpMatrix, Fin.sum_univ_three]
    rw [octNormSq_eq_sum_octToC3 (hm_perp.2 1), Fin.sum_univ_three]
    push_cast; simp [complex_normSq_eq_mul_conj, mul_comm]
  have hH22 : H 2 2 = (octNormSq (m.2 0) : ℂ) := by
    simp only [H, Matrix.mul_apply, Matrix.conjTranspose_apply, perpMatrix, Fin.sum_univ_three]
    rw [octNormSq_eq_sum_octToC3 (hm_perp.2 0), Fin.sum_univ_three]
    push_cast; simp [complex_normSq_eq_mul_conj, mul_comm]
  have hH01 : H 0 1 = -∑ r : Fin 3, star (octToC3 (m.2 2) r) * octToC3 (m.2 1) r := by
    simp [H, Matrix.mul_apply, Matrix.conjTranspose_apply, perpMatrix, Fin.sum_univ_three]
  have hH02 : H 0 2 = ∑ r : Fin 3, star (octToC3 (m.2 2) r) * octToC3 (m.2 0) r := by
    simp [H, Matrix.mul_apply, Matrix.conjTranspose_apply, perpMatrix, Fin.sum_univ_three]
  have hH12 : H 1 2 = -∑ r : Fin 3, star (octToC3 (m.2 1) r) * octToC3 (m.2 0) r := by
    simp [H, Matrix.mul_apply, Matrix.conjTranspose_apply, perpMatrix, Fin.sum_univ_three]
  have h00 : H 0 0 = A 0 0 := by
    rw [hH00]
    dsimp [A]
    rw [adjugate_fin3_diag_0, hX_sym 1 2, hXd 1, hXd 2, hX12]
    have hns2 := hnorm_split 2
    rw [hc_norm 2] at hns2
    apply Complex.ext <;> simp [octToC, Complex.mul_re, Complex.mul_im] <;> linarith
  have h11 : H 1 1 = A 1 1 := by
    rw [hH11]
    dsimp [A]
    rw [adjugate_fin3_diag_1, hX_sym 0 2, hXd 0, hXd 2, hX02]
    have hns1 := hnorm_split 1
    rw [hc_norm 1] at hns1
    apply Complex.ext <;> simp [octToC, Complex.mul_re, Complex.mul_im] <;> linarith
  have h22 : H 2 2 = A 2 2 := by
    rw [hH22]
    dsimp [A]
    rw [adjugate_fin3_diag_2, hX_sym 0 1, hXd 0, hXd 1, hX01]
    have hns0 := hnorm_split 0
    rw [hc_norm 0] at hns0
    apply Complex.ext <;> simp [octToC, Complex.mul_re, Complex.mul_im] <;> linarith
  have h01 : H 0 1 = A 0 1 := by
    dsimp [A]
    rw [adjugate_fin3_01, hX_sym 1 2, hXd 2, hX01, hX02, hX12]
    have hexp : octonionMul (p.2 1) (octonionConj (p.2 2)) - p.1 2 • p.2 0 =
        (octonionMul (projC (p.2 1)) (octonionConj (projC (p.2 2))) - p.1 2 • projC (p.2 0)) +
        octonionMul (projC (p.2 1)) (octonionConj (m.2 2)) +
        octonionMul (m.2 1) (octonionConj (projC (p.2 2))) +
        octonionMul (m.2 1) (octonionConj (m.2 2)) - p.1 2 • m.2 0 := by
      conv_lhs => rw [hp_split 1, hp_split 2, hp_split 0]
      rw [octonionConj_add, octonionMul_add_left, octonionMul_add_right, octonionMul_add_right,
        smul_add]
      abel
    have hs0' : octonionMul (p.2 1) (octonionConj (p.2 2)) - p.1 2 • p.2 0 = 0 := by
      simpa [albertSharp, albert_zero_snd] using congrArg (fun a : Albert => a.2 0) hsharp
    rw [hexp] at hs0'
    have htoc := congrArg octToC hs0'
    rw [octToC_sub, octToC_add, octToC_add, octToC_add, octToC_smul, octToC_zero,
      octToC_of_inCperp (inCperp_mul_inC_left (inC_projC _) (inCperp_conj (hm_perp.2 2))),
      octToC_of_inCperp (inCperp_mul_inC_right (hm_perp.2 1) (inC_conj (inC_projC _))),
      octToC_of_inCperp (hm_perp.2 0),
      add_zero, add_zero, mul_zero, sub_zero] at htoc
    have hpart_m : octToC (octonionMul (m.2 1) (octonionConj (m.2 2))) = -H 0 1 := by
      change (⟨(octonionMul (m.2 1) (octonionConj (m.2 2))).1.re,
        (octonionMul (m.2 1) (octonionConj (m.2 2))).1.imI⟩ : ℂ) = -H 0 1
      rw [octonionMul_projC_complex (hm_perp.2 1) (inCperp_conj (hm_perp.2 2)), hH01, neg_neg]
      simp only [octToC3_conj (hm_perp.2 2), Pi.neg_apply, star_neg, mul_neg,
        Finset.sum_neg_distrib, neg_neg, Fin.sum_univ_three]
      ring
    have hpart_c : octToC (octonionMul (projC (p.2 1)) (octonionConj (projC (p.2 2))) -
        p.1 2 • projC (p.2 0)) =
        -(octToC (p.2 0) * (p.1 2 : ℂ) - octToC (p.2 1) * star (octToC (p.2 2))) := by
      apply Complex.ext <;>
        simp [octToC, oct_sub_fst, oct_mul_fst, oct_conj_fst, oct_conj_snd, oct_smul_fst,
          projC_fst, projC_snd, q_re_sub, q_imI_sub, q_re_smul, q_imI_smul,
          q_re_star, q_imI_star, q_imJ_star, q_imK_star,
          Quaternion.re_mul, Quaternion.imI_mul] <;>
        ring
    rw [hpart_c, hpart_m] at htoc
    linear_combination -htoc
  have h02 : H 0 2 = A 0 2 := by
    dsimp [A]
    rw [adjugate_fin3_02, hXd 1, hX01, hX02, hX12]
    have hexp : octonionMul (p.2 0) (p.2 2) - p.1 1 • p.2 1 =
        (octonionMul (projC (p.2 0)) (projC (p.2 2)) - p.1 1 • projC (p.2 1)) +
        octonionMul (projC (p.2 0)) (m.2 2) +
        octonionMul (m.2 0) (projC (p.2 2)) +
        octonionMul (m.2 0) (m.2 2) - p.1 1 • m.2 1 := by
      conv_lhs => rw [hp_split 0, hp_split 2, hp_split 1]
      rw [octonionMul_add_left, octonionMul_add_right, octonionMul_add_right, smul_add]
      abel
    have hs1' : octonionMul (p.2 0) (p.2 2) - p.1 1 • p.2 1 = 0 := by
      simpa [albertSharp, albert_zero_snd] using congrArg (fun a : Albert => a.2 1) hsharp
    rw [hexp] at hs1'
    have htoc := congrArg octToC hs1'
    rw [octToC_sub, octToC_add, octToC_add, octToC_add, octToC_smul, octToC_zero,
      octToC_of_inCperp (inCperp_mul_inC_left (inC_projC _) (hm_perp.2 2)),
      octToC_of_inCperp (inCperp_mul_inC_right (hm_perp.2 0) (inC_projC _)),
      octToC_of_inCperp (hm_perp.2 1),
      add_zero, add_zero, mul_zero, sub_zero] at htoc
    have hpart_m : octToC (octonionMul (m.2 0) (m.2 2)) = -H 0 2 := by
      change (⟨(octonionMul (m.2 0) (m.2 2)).1.re,
        (octonionMul (m.2 0) (m.2 2)).1.imI⟩ : ℂ) = -H 0 2
      rw [octonionMul_projC_complex (hm_perp.2 0) (hm_perp.2 2), hH02]
      simp only [Fin.sum_univ_three]
      ring
    have hpart_c : octToC (octonionMul (projC (p.2 0)) (projC (p.2 2)) -
        p.1 1 • projC (p.2 1)) =
        octToC (p.2 0) * octToC (p.2 2) - octToC (p.2 1) * (p.1 1 : ℂ) := by
      apply Complex.ext <;>
        simp [octToC, oct_sub_fst, oct_mul_fst, oct_smul_fst,
          projC_fst, projC_snd, q_re_sub, q_imI_sub, q_re_smul, q_imI_smul,
          Quaternion.re_mul, Quaternion.imI_mul] <;>
        ring
    rw [hpart_c, hpart_m] at htoc
    linear_combination -htoc
  have h12 : H 1 2 = A 1 2 := by
    dsimp [A]
    rw [adjugate_fin3_12, hX_sym 0 1, hXd 0, hX01, hX02, hX12]
    have hexp : octonionMul (octonionConj (p.2 0)) (p.2 1) - p.1 0 • p.2 2 =
        (octonionMul (octonionConj (projC (p.2 0))) (projC (p.2 1)) - p.1 0 • projC (p.2 2)) +
        octonionMul (octonionConj (projC (p.2 0))) (m.2 1) +
        octonionMul (octonionConj (m.2 0)) (projC (p.2 1)) +
        octonionMul (octonionConj (m.2 0)) (m.2 1) - p.1 0 • m.2 2 := by
      conv_lhs => rw [hp_split 0, hp_split 1, hp_split 2]
      rw [octonionConj_add, octonionMul_add_left, octonionMul_add_right, octonionMul_add_right,
        smul_add]
      abel
    have hs2' : octonionMul (octonionConj (p.2 0)) (p.2 1) - p.1 0 • p.2 2 = 0 := by
      simpa [albertSharp, albert_zero_snd] using congrArg (fun a : Albert => a.2 2) hsharp
    rw [hexp] at hs2'
    have htoc := congrArg octToC hs2'
    rw [octToC_sub, octToC_add, octToC_add, octToC_add, octToC_smul, octToC_zero,
      octToC_of_inCperp (inCperp_mul_inC_left (inC_conj (inC_projC _)) (hm_perp.2 1)),
      octToC_of_inCperp (inCperp_mul_inC_right (inCperp_conj (hm_perp.2 0)) (inC_projC _)),
      octToC_of_inCperp (hm_perp.2 2),
      add_zero, add_zero, mul_zero, sub_zero] at htoc
    have hpart_m : octToC (octonionMul (octonionConj (m.2 0)) (m.2 1)) = -H 1 2 := by
      change (⟨(octonionMul (octonionConj (m.2 0)) (m.2 1)).1.re,
        (octonionMul (octonionConj (m.2 0)) (m.2 1)).1.imI⟩ : ℂ) = -H 1 2
      rw [octonionMul_projC_complex (inCperp_conj (hm_perp.2 0)) (hm_perp.2 1), hH12]
      simp only [octToC3_conj (hm_perp.2 0), Pi.neg_apply, neg_mul,
        Finset.sum_neg_distrib, neg_neg, Fin.sum_univ_three]
      ring
    have hpart_c : octToC (octonionMul (octonionConj (projC (p.2 0))) (projC (p.2 1)) -
        p.1 0 • projC (p.2 2)) =
        -((p.1 0 : ℂ) * octToC (p.2 2) - octToC (p.2 1) * star (octToC (p.2 0))) := by
      apply Complex.ext <;>
        simp [octToC, oct_sub_fst, oct_mul_fst, oct_conj_fst, oct_conj_snd, oct_smul_fst,
          projC_fst, projC_snd, q_re_sub, q_imI_sub, q_re_smul, q_imI_smul,
          q_re_star, q_imI_star, q_imJ_star, q_imK_star,
          Quaternion.re_mul, Quaternion.imI_mul] <;>
        ring
    rw [hpart_c, hpart_m] at htoc
    linear_combination -htoc
  change H = A
  ext i j
  fin_cases i <;> fin_cases j <;> dsimp
  · exact h00
  · exact h01
  · exact h02
  · rw [hH_sym 0 1, hA_sym 0 1, h01]
  · exact h11
  · exact h12
  · rw [hH_sym 0 2, hA_sym 0 2, h02]
  · rw [hH_sym 1 2, hA_sym 1 2, h12]
  · exact h22

theorem double_adjugate_trace_re (X : Hermitian3) :
    ((X : ComplexMatrix3).adjugate.adjugate).trace.re =
      (X : ComplexMatrix3).det.re * (Matrix.trace (X : ComplexMatrix3)).re := by
  have hadj : (X : ComplexMatrix3).adjugate.adjugate =
      (X : ComplexMatrix3).det • (X : ComplexMatrix3) := by
    simpa using Matrix.adjugate_adjugate (X : ComplexMatrix3)
  have hdet_im : (X : ComplexMatrix3).det.im = 0 :=
    (standardComplexWindow_albertCubicNorm_eq_det X).2
  have htr_im : (Matrix.trace (X : ComplexMatrix3)).im = 0 := by
    have hs := congrArg (fun M : ComplexMatrix3 => (Matrix.trace M).im) X.prop
    simp only [Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose, Complex.star_def,
      Complex.conj_im] at hs
    linarith
  rw [hadj, Matrix.trace_smul, smul_eq_mul, Complex.mul_re, hdet_im, htr_im]
  ring

theorem tracePairing_projPerp_sq_eq_two_det_mul_trace {p : Albert} (hp : IsAtom p) :
    tracePairing (projPerpAlbert (jordanMul (projPerpAlbert p) (projPerpAlbert p)))
        (projPerpAlbert (jordanMul (projPerpAlbert p) (projPerpAlbert p))) =
      2 * (windowProj standardComplexWindow p : ComplexMatrix3).det.re *
        albertTrace (standardComplexWindow.embedding (windowProj standardComplexWindow p)) := by
  rw [tracePairing_projPerp_jordanMul_self (projPerpAlbert_inWPerp p),
    perpMatrix_gram_eq_adjugate hp, double_adjugate_trace_re,
    ← standardComplexWindow.preserves_trace (windowProj standardComplexWindow p)]
  ring

theorem tracePairing_projPerp_sq_eq_two_det {p : Albert} (hp : IsAtom p) :
    tracePairing (projPerpAlbert (jordanMul (projPerpAlbert p) (projPerpAlbert p)))
        (projPerpAlbert (jordanMul (projPerpAlbert p) (projPerpAlbert p))) =
      2 * (windowProj standardComplexWindow p : ComplexMatrix3).det.re := by
  rw [tracePairing_projPerp_sq_eq_two_det_mul_trace hp]
  have htr : albertTrace (standardComplexWindow.embedding (windowProj standardComplexWindow p)) = 1 := by
    rw [standardComplexWindow_embedding_windowProj]
    exact hp.2
  rw [htr, mul_one]

/-- Total coordinate-free defect norm identity (valid for every atom
`p_D : Albert` with no coordinate exclusion):
`‖Def(p_D)‖² = 72 · Re(det(P_W p_D))`. -/
theorem tracePairing_defectVec_eq_72_det (p_D : Albert) (hp_D : IsAtom p_D) :
    tracePairing (defectVec p_D) (defectVec p_D) =
      72 * (windowProj standardComplexWindow p_D : ComplexMatrix3).det.re := by
  rw [defectVec_eq_three_defectAdI_sq hp_D.1, tracePairing_smul_left, tracePairing_smul_right,
    tracePairing_defectAdI_self (projPerpAlbert_inWPerp _),
    tracePairing_projPerp_sq_eq_two_det hp_D]
  ring

/-! ## Section 5: Automorphism & General-Window Transport -/

theorem tracePairing_defect_transport (g : NativeAlbertAutomorphism)
    (p_D : Albert) (hp_D : IsAtom p_D) :
    tracePairing (defectVec (g.linearEquiv p_D)) (defectVec (g.linearEquiv p_D)) =
      72 * (windowProj (standardComplexWindow.transport g.symm) p_D : ComplexMatrix3).det.re := by
  rw [tracePairing_defectVec_eq_72_det (g.linearEquiv p_D) (g.map_isAtom hp_D)]
  have hwp : windowProj (standardComplexWindow.transport g.symm) p_D =
      windowProj standardComplexWindow (g.linearEquiv p_D) := by
    have h := windowProj_transport standardComplexWindow g.symm (g.linearEquiv p_D)
    simpa [NativeAlbertAutomorphism.symm] using h
  rw [hwp]

theorem tracePairing_defect_window (W : ComplexWindow) (g : NativeAlbertAutomorphism)
    (hg : ∀ M : Hermitian3, g.linearEquiv (W.embedding M) = standardComplexWindow.embedding M)
    (p_D : Albert) (hp_D : IsAtom p_D) :
    tracePairing (defectVec (g.linearEquiv p_D)) (defectVec (g.linearEquiv p_D)) =
      72 * (windowProj W p_D : ComplexMatrix3).det.re := by
  rw [tracePairing_defect_transport g p_D hp_D]
  have hsub : W.toSubalgebra.carrier =
      (standardComplexWindow.transport g.symm).toSubalgebra.carrier := by
    ext x
    constructor
    · rintro ⟨M, rfl⟩
      refine ⟨M, ?_⟩
      apply g.linearEquiv.injective
      simpa [ComplexWindow.transport, NativeAlbertAutomorphism.symm] using (hg M).symm
    · rintro ⟨M, rfl⟩
      refine ⟨M, ?_⟩
      apply g.linearEquiv.injective
      simpa [ComplexWindow.transport, NativeAlbertAutomorphism.symm] using hg M
  rw [windowProj_det_eq_of_subalgebra_eq W (standardComplexWindow.transport g.symm) hsub p_D]

end

end AlbertSequential.AppF
