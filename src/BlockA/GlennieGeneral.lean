/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Pending.GlennieGeneral
public import ComplexWindowDeterminantAndMax
public import SubalgebraCoordsAndLine
public import BlockA.GlennieWindowTrace
public import BlockA.GlennieDefect
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Appendix F (`thm:glennie`): General Four-Atom Polarised Glennie Identity

Proves `AlbertSequential.AppF.Pending.GlennieViolationStatement`,
`AlbertSequential.AppF.Pending.GlennieViolationAnyOrder`, and clean headline statements
matching `thm:glennie`:
- `F₄`-equivariance of `nativeGlennieF` and `symmetryOf`.
- Degenerate case (`tripleDelta (p 0) (p 1) (p 2) = 0`): quaternionic subalgebra embedding
  via `symplecticQuatEmbed` kills `nativeGlennieF`.
- Nondegenerate case (`tripleDelta (p 0) (p 1) (p 2) ≠ 0`): `lemma_A_window_generated` +
  `native_complexWindow_conjugate_standard` + `BlockA.GlennieBimodule` +
  `BlockA.GlennieWindowTrace` + `BlockA.GlennieDefect`.
- Exported headlines: `glennieViolationStatement_holds`, `glennieViolationAnyOrder_holds`,
  `thm_glennie_normSq`, `thm_glennie_perm`, `thm_glennie_eq_zero_iff`, `thm_glennie`.
-/

@[expose] public section

namespace AlbertSequential.AppF

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

noncomputable section

/-! ## Part 1: `F₄`-equivariance of `nativeGlennieF` and `symmetryOf` -/

theorem nativeGlennieF_aut (g : NativeAlbertAutomorphism) (a b c d : Albert) :
    nativeGlennieF (g.linearEquiv a) (g.linearEquiv b) (g.linearEquiv c) (g.linearEquiv d) =
      g.linearEquiv (nativeGlennieF a b c d) := by
  symm
  exact map_glennieF (o := nativeOps) (o' := nativeOps) g.linearEquiv
    (fun x y => map_add g.linearEquiv x y)
    (fun x y => map_sub g.linearEquiv x y)
    g.preserves_product a b c d

theorem symmetryOf_aut (g : NativeAlbertAutomorphism) (p : Albert) :
    symmetryOf (g.linearEquiv p) = g.linearEquiv (symmetryOf p) := by
  unfold symmetryOf
  rw [map_sub, map_smul, g.preserves_unit]

theorem tracePairing_nativeGlennieF_aut (g : NativeAlbertAutomorphism) (a b c d : Albert) :
    tracePairing
        (nativeGlennieF (symmetryOf (g.linearEquiv a)) (symmetryOf (g.linearEquiv b))
          (symmetryOf (g.linearEquiv c)) (symmetryOf (g.linearEquiv d)))
        (nativeGlennieF (symmetryOf (g.linearEquiv a)) (symmetryOf (g.linearEquiv b))
          (symmetryOf (g.linearEquiv c)) (symmetryOf (g.linearEquiv d))) =
      tracePairing
        (nativeGlennieF (symmetryOf a) (symmetryOf b) (symmetryOf c) (symmetryOf d))
        (nativeGlennieF (symmetryOf a) (symmetryOf b) (symmetryOf c) (symmetryOf d)) := by
  rw [symmetryOf_aut, symmetryOf_aut, symmetryOf_aut, symmetryOf_aut, nativeGlennieF_aut,
    g.map_tracePairing]

/-! ## Part 2: Special Jordan algebras kill `glennieF`, and the quaternionic/degenerate case -/

section SpecialGlennieF

variable {A : Type*} [NonUnitalRing A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]

private lemma special_add_def (x y : A) : (specialOps A).add x y = x + y := rfl
private lemma special_sub_def (x y : A) : (specialOps A).sub x y = x - y := rfl

private lemma special_mul_add_left (x₁ x₂ y : A) :
    (specialOps A).mul (x₁ + x₂) y = (specialOps A).mul x₁ y + (specialOps A).mul x₂ y := by
  simp only [specialOps, add_mul, mul_add, smul_add]
  abel

private lemma special_mul_add_right (x y₁ y₂ : A) :
    (specialOps A).mul x (y₁ + y₂) = (specialOps A).mul x y₁ + (specialOps A).mul x y₂ := by
  simp only [specialOps, add_mul, mul_add, smul_add]
  abel

private lemma special_mul_neg_left (x y : A) :
    (specialOps A).mul (-x) y = -(specialOps A).mul x y := by
  simp only [specialOps, neg_mul, mul_neg]
  module

private lemma special_mul_neg_right (x y : A) :
    (specialOps A).mul x (-y) = -(specialOps A).mul x y := by
  simp only [specialOps, neg_mul, mul_neg]
  module

private lemma special_Dop_add_x (x₁ x₂ y z : A) :
    Dop (specialOps A) (x₁ + x₂) y z = Dop (specialOps A) x₁ y z + Dop (specialOps A) x₂ y z := by
  simp only [Dop, four, special_add_def, special_sub_def, special_mul_add_left,
    special_mul_add_right]
  abel

private lemma special_Dop_neg_x (x y z : A) :
    Dop (specialOps A) (-x) y z = -Dop (specialOps A) x y z := by
  simp only [Dop, four, special_add_def, special_sub_def, special_mul_neg_left,
    special_mul_neg_right]
  abel

private lemma special_Dop_add_y (x y₁ y₂ z : A) :
    Dop (specialOps A) x (y₁ + y₂) z = Dop (specialOps A) x y₁ z + Dop (specialOps A) x y₂ z := by
  simp only [Dop, four, special_add_def, special_sub_def, special_mul_add_left,
    special_mul_add_right]
  abel

private lemma special_Dop_neg_y (x y z : A) :
    Dop (specialOps A) x (-y) z = -Dop (specialOps A) x y z := by
  simp only [Dop, four, special_add_def, special_sub_def, special_mul_neg_left,
    special_mul_neg_right]
  abel

private lemma special_Dop_add_z (x y z₁ z₂ : A) :
    Dop (specialOps A) x y (z₁ + z₂) = Dop (specialOps A) x y z₁ + Dop (specialOps A) x y z₂ := by
  simp only [Dop, four, special_add_def, special_sub_def, special_mul_add_right]
  abel

private lemma special_Dop_neg_z (x y z : A) :
    Dop (specialOps A) x y (-z) = -Dop (specialOps A) x y z := by
  simp only [Dop, four, special_add_def, special_sub_def, special_mul_neg_right]
  abel

private lemma special_Upol_add_1 (w₁ w₂ w' z : A) :
    Upol (specialOps A) (w₁ + w₂) w' z =
      Upol (specialOps A) w₁ w' z + Upol (specialOps A) w₂ w' z := by
  simp only [Upol, special_add_def, special_sub_def, special_mul_add_left, special_mul_add_right]
  abel

private lemma special_Upol_neg_1 (w w' z : A) :
    Upol (specialOps A) (-w) w' z = -Upol (specialOps A) w w' z := by
  simp only [Upol, special_add_def, special_sub_def, special_mul_neg_left, special_mul_neg_right]
  abel

private lemma special_Upol_add_2 (w w₁' w₂' z : A) :
    Upol (specialOps A) w (w₁' + w₂') z =
      Upol (specialOps A) w w₁' z + Upol (specialOps A) w w₂' z := by
  simp only [Upol, special_add_def, special_sub_def, special_mul_add_left, special_mul_add_right]
  abel

private lemma special_Upol_neg_2 (w w' z : A) :
    Upol (specialOps A) w (-w') z = -Upol (specialOps A) w w' z := by
  simp only [Upol, special_add_def, special_sub_def, special_mul_neg_left, special_mul_neg_right]
  abel

private lemma special_Upol_add_3 (w w' z₁ z₂ : A) :
    Upol (specialOps A) w w' (z₁ + z₂) =
      Upol (specialOps A) w w' z₁ + Upol (specialOps A) w w' z₂ := by
  simp only [Upol, special_add_def, special_sub_def, special_mul_add_right]
  abel

private lemma special_Upol_neg_3 (w w' z : A) :
    Upol (specialOps A) w w' (-z) = -Upol (specialOps A) w w' z := by
  simp only [Upol, special_add_def, special_sub_def, special_mul_neg_right]
  abel

private lemma special_Ubr_add_1 (x₁ x₁' x₂ y₁ y₂ z : A) :
    Ubr (specialOps A) (x₁ + x₁') x₂ y₁ y₂ z =
      Ubr (specialOps A) x₁ x₂ y₁ y₂ z + Ubr (specialOps A) x₁' x₂ y₁ y₂ z := by
  simp only [Ubr, four, two, special_add_def, special_sub_def, special_mul_add_left,
    special_Upol_add_1, special_Upol_add_3]
  abel

private lemma special_Ubr_neg_1 (x₁ x₂ y₁ y₂ z : A) :
    Ubr (specialOps A) (-x₁) x₂ y₁ y₂ z = -Ubr (specialOps A) x₁ x₂ y₁ y₂ z := by
  simp only [Ubr, four, two, special_add_def, special_sub_def, special_mul_neg_left,
    special_Upol_neg_1, special_Upol_neg_3]
  abel

private lemma special_Ubr_add_2 (x₁ x₂ x₂' y₁ y₂ z : A) :
    Ubr (specialOps A) x₁ (x₂ + x₂') y₁ y₂ z =
      Ubr (specialOps A) x₁ x₂ y₁ y₂ z + Ubr (specialOps A) x₁ x₂' y₁ y₂ z := by
  simp only [Ubr, four, two, special_add_def, special_sub_def, special_mul_add_left,
    special_Upol_add_2, special_Upol_add_3]
  abel

private lemma special_Ubr_neg_2 (x₁ x₂ y₁ y₂ z : A) :
    Ubr (specialOps A) x₁ (-x₂) y₁ y₂ z = -Ubr (specialOps A) x₁ x₂ y₁ y₂ z := by
  simp only [Ubr, four, two, special_add_def, special_sub_def, special_mul_neg_left,
    special_Upol_neg_2, special_Upol_neg_3]
  abel

private lemma special_Ubr_add_3 (x₁ x₂ y₁ y₁' y₂ z : A) :
    Ubr (specialOps A) x₁ x₂ (y₁ + y₁') y₂ z =
      Ubr (specialOps A) x₁ x₂ y₁ y₂ z + Ubr (specialOps A) x₁ x₂ y₁' y₂ z := by
  simp only [Ubr, four, two, special_add_def, special_sub_def, special_mul_add_right,
    special_Upol_add_1, special_Upol_add_3]
  abel

private lemma special_Ubr_neg_3 (x₁ x₂ y₁ y₂ z : A) :
    Ubr (specialOps A) x₁ x₂ (-y₁) y₂ z = -Ubr (specialOps A) x₁ x₂ y₁ y₂ z := by
  simp only [Ubr, four, two, special_add_def, special_sub_def, special_mul_neg_right,
    special_Upol_neg_1, special_Upol_neg_3]
  abel

private lemma special_Ubr_add_4 (x₁ x₂ y₁ y₂ y₂' z : A) :
    Ubr (specialOps A) x₁ x₂ y₁ (y₂ + y₂') z =
      Ubr (specialOps A) x₁ x₂ y₁ y₂ z + Ubr (specialOps A) x₁ x₂ y₁ y₂' z := by
  simp only [Ubr, four, two, special_add_def, special_sub_def, special_mul_add_right,
    special_Upol_add_2, special_Upol_add_3]
  abel

private lemma special_Ubr_neg_4 (x₁ x₂ y₁ y₂ z : A) :
    Ubr (specialOps A) x₁ x₂ y₁ (-y₂) z = -Ubr (specialOps A) x₁ x₂ y₁ y₂ z := by
  simp only [Ubr, four, two, special_add_def, special_sub_def, special_mul_neg_right,
    special_Upol_neg_2, special_Upol_neg_3]
  abel

private lemma special_term_add_x1 (d x₁ x₁' x₂ x₃ y₁ y₂ y₃ : A) :
    glennieTerm (specialOps A) d (x₁ + x₁') x₂ x₃ y₁ y₂ y₃ =
      glennieTerm (specialOps A) d x₁ x₂ x₃ y₁ y₂ y₃ +
        glennieTerm (specialOps A) d x₁' x₂ x₃ y₁ y₂ y₃ := by
  simp only [glennieTerm, Phi, three, two, special_add_def, special_sub_def, special_Dop_add_x,
    special_mul_add_right]
  abel

private lemma special_term_neg_x1 (d x₁ x₂ x₃ y₁ y₂ y₃ : A) :
    glennieTerm (specialOps A) d (-x₁) x₂ x₃ y₁ y₂ y₃ =
      -glennieTerm (specialOps A) d x₁ x₂ x₃ y₁ y₂ y₃ := by
  simp only [glennieTerm, Phi, three, two, special_add_def, special_sub_def, special_Dop_neg_x,
    special_mul_add_right, special_mul_neg_right]
  abel

private lemma special_term_add_x2 (d x₁ x₂ x₂' x₃ y₁ y₂ y₃ : A) :
    glennieTerm (specialOps A) d x₁ (x₂ + x₂') x₃ y₁ y₂ y₃ =
      glennieTerm (specialOps A) d x₁ x₂ x₃ y₁ y₂ y₃ +
        glennieTerm (specialOps A) d x₁ x₂' x₃ y₁ y₂ y₃ := by
  simp only [glennieTerm, Phi, three, two, special_add_def, special_sub_def, special_Dop_add_x,
    special_Dop_add_z, special_Ubr_add_1, special_mul_add_right]
  abel

private lemma special_term_neg_x2 (d x₁ x₂ x₃ y₁ y₂ y₃ : A) :
    glennieTerm (specialOps A) d x₁ (-x₂) x₃ y₁ y₂ y₃ =
      -glennieTerm (specialOps A) d x₁ x₂ x₃ y₁ y₂ y₃ := by
  simp only [glennieTerm, Phi, three, two, special_add_def, special_sub_def, special_Dop_neg_x,
    special_Dop_neg_z, special_Ubr_neg_1, special_mul_add_right, special_mul_neg_right]
  abel

private lemma special_term_add_x3 (d x₁ x₂ x₃ x₃' y₁ y₂ y₃ : A) :
    glennieTerm (specialOps A) d x₁ x₂ (x₃ + x₃') y₁ y₂ y₃ =
      glennieTerm (specialOps A) d x₁ x₂ x₃ y₁ y₂ y₃ +
        glennieTerm (specialOps A) d x₁ x₂ x₃' y₁ y₂ y₃ := by
  simp only [glennieTerm, Phi, three, two, special_add_def, special_sub_def, special_Dop_add_x,
    special_Dop_add_z, special_Ubr_add_2, special_mul_add_right]
  abel

private lemma special_term_neg_x3 (d x₁ x₂ x₃ y₁ y₂ y₃ : A) :
    glennieTerm (specialOps A) d x₁ x₂ (-x₃) y₁ y₂ y₃ =
      -glennieTerm (specialOps A) d x₁ x₂ x₃ y₁ y₂ y₃ := by
  simp only [glennieTerm, Phi, three, two, special_add_def, special_sub_def, special_Dop_neg_x,
    special_Dop_neg_z, special_Ubr_neg_2, special_mul_add_right, special_mul_neg_right]
  abel

private lemma special_term_add_y1 (d x₁ x₂ x₃ y₁ y₁' y₂ y₃ : A) :
    glennieTerm (specialOps A) d x₁ x₂ x₃ (y₁ + y₁') y₂ y₃ =
      glennieTerm (specialOps A) d x₁ x₂ x₃ y₁ y₂ y₃ +
        glennieTerm (specialOps A) d x₁ x₂ x₃ y₁' y₂ y₃ := by
  simp only [glennieTerm, Phi, three, two, special_add_def, special_sub_def, special_Dop_add_y,
    special_mul_add_right]
  abel

private lemma special_term_neg_y1 (d x₁ x₂ x₃ y₁ y₂ y₃ : A) :
    glennieTerm (specialOps A) d x₁ x₂ x₃ (-y₁) y₂ y₃ =
      -glennieTerm (specialOps A) d x₁ x₂ x₃ y₁ y₂ y₃ := by
  simp only [glennieTerm, Phi, three, two, special_add_def, special_sub_def, special_Dop_neg_y,
    special_mul_add_right, special_mul_neg_right]
  abel

private lemma special_term_add_y2 (d x₁ x₂ x₃ y₁ y₂ y₂' y₃ : A) :
    glennieTerm (specialOps A) d x₁ x₂ x₃ y₁ (y₂ + y₂') y₃ =
      glennieTerm (specialOps A) d x₁ x₂ x₃ y₁ y₂ y₃ +
        glennieTerm (specialOps A) d x₁ x₂ x₃ y₁ y₂' y₃ := by
  simp only [glennieTerm, Phi, three, two, special_add_def, special_sub_def, special_Dop_add_y,
    special_Dop_add_z, special_Ubr_add_3, special_mul_add_right]
  abel

private lemma special_term_neg_y2 (d x₁ x₂ x₃ y₁ y₂ y₃ : A) :
    glennieTerm (specialOps A) d x₁ x₂ x₃ y₁ (-y₂) y₃ =
      -glennieTerm (specialOps A) d x₁ x₂ x₃ y₁ y₂ y₃ := by
  simp only [glennieTerm, Phi, three, two, special_add_def, special_sub_def, special_Dop_neg_y,
    special_Dop_neg_z, special_Ubr_neg_3, special_mul_add_right, special_mul_neg_right]
  abel

private lemma special_term_add_y3 (d x₁ x₂ x₃ y₁ y₂ y₃ y₃' : A) :
    glennieTerm (specialOps A) d x₁ x₂ x₃ y₁ y₂ (y₃ + y₃') =
      glennieTerm (specialOps A) d x₁ x₂ x₃ y₁ y₂ y₃ +
        glennieTerm (specialOps A) d x₁ x₂ x₃ y₁ y₂ y₃' := by
  simp only [glennieTerm, Phi, three, two, special_add_def, special_sub_def, special_Dop_add_y,
    special_Dop_add_z, special_Ubr_add_4, special_mul_add_right]
  abel

private lemma special_term_neg_y3 (d x₁ x₂ x₃ y₁ y₂ y₃ : A) :
    glennieTerm (specialOps A) d x₁ x₂ x₃ y₁ y₂ (-y₃) =
      -glennieTerm (specialOps A) d x₁ x₂ x₃ y₁ y₂ y₃ := by
  simp only [glennieTerm, Phi, three, two, special_add_def, special_sub_def, special_Dop_neg_y,
    special_Dop_neg_z, special_Ubr_neg_4, special_mul_add_right, special_mul_neg_right]
  abel

private lemma triadditive_delta2 {J V : Type*} [AddCommGroup J] [AddCommGroup V]
    (M : J → J → J → V)
    (h1 : ∀ x₁ x₂ y z, M (x₁ + x₂) y z = M x₁ y z + M x₂ y z)
    (h2 : ∀ x y₁ y₂ z, M x (y₁ + y₂) z = M x y₁ z + M x y₂ z)
    (h3 : ∀ x y z₁ z₂, M x y (z₁ + z₂) = M x y z₁ + M x y z₂)
    (hn1 : ∀ x y z, M (-x) y z = -M x y z)
    (hn2 : ∀ x y z, M x (-y) z = -M x y z)
    (hn3 : ∀ x y z, M x y (-z) = -M x y z)
    (a b : J) :
    M (a + b) (a + b) (a + b) + M (a - b) (a - b) (a - b) - (M a a a + M a a a) =
      (M a b b + M b a b + M b b a) + (M a b b + M b a b + M b b a) := by
  simp only [sub_eq_add_neg, h1, h2, h3, hn1, hn2, hn3]
  abel

/-- In every special Jordan algebra `A⁺` (`A` associative, unital or not), the polarised
Glennie polynomial `glennieF` vanishes identically. -/
theorem special_glennieF_eq_zero (a b c d : A) : glennieF (specialOps A) a b c d = 0 := by
  have hpsi : ∀ x y : A, glennieTerm (specialOps A) d x x x y y y = 0 := fun x y => by
    change psi (specialOps A) x y d = 0
    exact special_psi_eq_zero x y d
  let g : A → A → A → A := fun x₁ x₂ x₃ =>
    (glennieTerm (specialOps A) d x₁ x₂ x₃ a c c + glennieTerm (specialOps A) d x₁ x₂ x₃ c a c +
        glennieTerm (specialOps A) d x₁ x₂ x₃ c c a) +
      (glennieTerm (specialOps A) d x₁ x₂ x₃ a c c + glennieTerm (specialOps A) d x₁ x₂ x₃ c a c +
        glennieTerm (specialOps A) d x₁ x₂ x₃ c c a)
  have hg_diag : ∀ x : A, g x x x = 0 := fun x => by
    dsimp only [g]
    have htri := triadditive_delta2
      (fun y₁ y₂ y₃ => glennieTerm (specialOps A) d x x x y₁ y₂ y₃)
      (special_term_add_y1 d x x x) (special_term_add_y2 d x x x) (special_term_add_y3 d x x x)
      (special_term_neg_y1 d x x x) (special_term_neg_y2 d x x x) (special_term_neg_y3 d x x x)
      a c
    rw [← htri, hpsi x (a + c), hpsi x (a - c), hpsi x a]
    abel
  have h4F :
      (g a b b + g b a b + g b b a) + (g a b b + g b a b + g b b a) =
        (4 : ℝ) • glennieF (specialOps A) a b c d := by
    dsimp only [g, glennieF]
    simp only [special_add_def]
    have h4 : (4 : ℝ) = 1 + 1 + 1 + 1 := by norm_num
    rw [h4, add_smul, add_smul, add_smul, one_smul]
    abel
  have htri_x := triadditive_delta2 g
    (fun x₁ x₁' x₂ x₃ => by dsimp only [g]; simp only [special_term_add_x1]; abel)
    (fun x₁ x₂ x₂' x₃ => by dsimp only [g]; simp only [special_term_add_x2]; abel)
    (fun x₁ x₂ x₃ x₃' => by dsimp only [g]; simp only [special_term_add_x3]; abel)
    (fun x₁ x₂ x₃ => by dsimp only [g]; simp only [special_term_neg_x1]; abel)
    (fun x₁ x₂ x₃ => by dsimp only [g]; simp only [special_term_neg_x2]; abel)
    (fun x₁ x₂ x₃ => by dsimp only [g]; simp only [special_term_neg_x3]; abel)
    a b
  rw [hg_diag (a + b), hg_diag (a - b), hg_diag a] at htri_x
  have hzero4 : (4 : ℝ) • glennieF (specialOps A) a b c d = 0 := by
    rw [← h4F, ← htri_x]
    abel
  exact (smul_eq_zero.mp hzero4).resolve_left (by norm_num)

end SpecialGlennieF

theorem glennieF_quatWindow_eq_zero (Q : QuaternionicWindow) {a b c d : Albert}
    (ha : a ∈ Q.subalgebra.carrier) (hb : b ∈ Q.subalgebra.carrier)
    (hc : c ∈ Q.subalgebra.carrier) (hd : d ∈ Q.subalgebra.carrier) :
    nativeGlennieF a b c d = 0 := by
  let subOps : JOps Q.subalgebra.carrier :=
    ⟨(· + ·), (· - ·), fun x y => ⟨jordanMul x.1 y.1, Q.subalgebra.product_mem x.1 x.2 y.1 y.2⟩⟩
  let ι := symplecticQuatEmbed Q
  have hsub_val :
      (glennieF subOps ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩).1 = nativeGlennieF a b c d :=
    map_glennieF (o := subOps) (o' := nativeOps) Subtype.val
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩
  have himg_zero :
      ι.map (glennieF subOps ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩) = 0 := by
    rw [map_glennieF (o := subOps) (o' := specialOps (HermitianEmbeddingMatrix 6)) ι.map
      (fun x y => map_add ι.map x y) (fun x y => map_sub ι.map x y) ι.jordan
      ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩]
    exact special_glennieF_eq_zero _ _ _ _
  have hsub_zero : glennieF subOps ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩ = 0 := by
    apply ι.injective
    rw [himg_zero, map_zero]
  rw [← hsub_val, hsub_zero]
  rfl

theorem symmetryOf_mem_subalgebra (B : NativeJordanSubalgebra) {p : Albert}
    (hp : p ∈ B.carrier) : symmetryOf p ∈ B.carrier :=
  B.carrier.sub_mem (B.carrier.smul_mem (2 : ℝ) hp) B.unit_mem

theorem glennie_of_quatWindow (Q : QuaternionicWindow) (p : Fin 4 → Albert)
    (hp : ∀ i, p i ∈ Q.subalgebra.carrier) :
    nativeGlennieF (symmetryOf (p 0)) (symmetryOf (p 1)) (symmetryOf (p 2)) (symmetryOf (p 3)) = 0 :=
  glennieF_quatWindow_eq_zero Q
    (symmetryOf_mem_subalgebra Q.subalgebra (hp 0))
    (symmetryOf_mem_subalgebra Q.subalgebra (hp 1))
    (symmetryOf_mem_subalgebra Q.subalgebra (hp 2))
    (symmetryOf_mem_subalgebra Q.subalgebra (hp 3))

theorem glennie_degenerate (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hdel : tripleDelta (p 0) (p 1) (p 2) = 0) :
    tracePairing
        (nativeGlennieF (symmetryOf (p 0)) (symmetryOf (p 1)) (symmetryOf (p 2)) (symmetryOf (p 3)))
        (nativeGlennieF (symmetryOf (p 0)) (symmetryOf (p 1)) (symmetryOf (p 2)) (symmetryOf (p 3))) =
      9 * 2 ^ 21 * albertCubicNorm (p 0 + p 1 + p 2) * fourPointInvariant p := by
  have hp_vec : ![p 0, p 1, p 2, p 3] = p := by
    funext i
    fin_cases i <;> rfl
  have hfp : fourPointInvariant p = 0 := by
    rw [← hp_vec]
    exact prop_windowdet_zero (hp 0) (hp 1) (hp 2) (hp 3) hdel
  obtain ⟨Q, hQ⟩ := (fourPointInvariant_eq_zero_iff p hp).mp hfp
  have hF0 := glennie_of_quatWindow Q p hQ
  rw [hF0, hfp, mul_zero]
  rw [← zero_smul ℝ (0 : Albert), tracePairing_smul_left, zero_mul]

/-! ## Part 3: Standard complex-window norm identity and nondegenerate reduction -/

theorem glennie_of_standardComplexWindow
    {P₀ P₁ P₂ : Hermitian3} {pD : Albert}
    (h0 : IsAtom (standardComplexWindow.embedding P₀))
    (h1 : IsAtom (standardComplexWindow.embedding P₁))
    (h2 : IsAtom (standardComplexWindow.embedding P₂))
    (hD : IsAtom pD) :
    tracePairing
        (nativeGlennieF
          (symmetryOf (standardComplexWindow.embedding P₀))
          (symmetryOf (standardComplexWindow.embedding P₁))
          (symmetryOf (standardComplexWindow.embedding P₂))
          (symmetryOf pD))
        (nativeGlennieF
          (symmetryOf (standardComplexWindow.embedding P₀))
          (symmetryOf (standardComplexWindow.embedding P₁))
          (symmetryOf (standardComplexWindow.embedding P₂))
          (symmetryOf pD)) =
      9 * 2 ^ 21 *
        albertCubicNorm
          (standardComplexWindow.embedding P₀ + standardComplexWindow.embedding P₁ +
            standardComplexWindow.embedding P₂) *
        fourPointInvariant
          ![standardComplexWindow.embedding P₀, standardComplexWindow.embedding P₁,
            standardComplexWindow.embedding P₂, pD] := by
  let lam := windowLambda
    (2 • (P₀ : ComplexMatrix3) - 1)
    (2 • (P₁ : ComplexMatrix3) - 1)
    (2 • (P₂ : ComplexMatrix3) - 1)
  have hF :
      nativeGlennieF
          (symmetryOf (standardComplexWindow.embedding P₀))
          (symmetryOf (standardComplexWindow.embedding P₁))
          (symmetryOf (standardComplexWindow.embedding P₂))
          (symmetryOf pD) =
        (4 * lam) • windowDef pD :=
    glennieF_window_symm_eq_four_lambda_def P₀ P₁ P₂ pD hD.1
  have hlam2 :
      lam ^ 2 =
        2 ^ 14 *
          albertCubicNorm
            (standardComplexWindow.embedding P₀ + standardComplexWindow.embedding P₁ +
              standardComplexWindow.embedding P₂) *
          tripleDelta
            (standardComplexWindow.embedding P₀)
            (standardComplexWindow.embedding P₁)
            (standardComplexWindow.embedding P₂) :=
    windowLambda_symm_sq_of_isAtom P₀ P₁ P₂ h0 h1 h2
  have hdef :
      tracePairing (windowDef pD) (windowDef pD) =
        72 * (windowProj standardComplexWindow pD : ComplexMatrix3).det.re :=
    tracePairing_defectVec_eq_72_det pD hD
  have hdet :
      fourPointInvariant
          ![standardComplexWindow.embedding P₀, standardComplexWindow.embedding P₁,
            standardComplexWindow.embedding P₂, pD] =
        tripleDelta
            (standardComplexWindow.embedding P₀)
            (standardComplexWindow.embedding P₁)
            (standardComplexWindow.embedding P₂) *
          (windowProj standardComplexWindow pD : ComplexMatrix3).det.re := by
    rw [← windowDelta_eq_tripleDelta standardComplexWindow]
    exact prop_windowdet standardComplexWindow h0 h1 h2 hD ⟨P₀, rfl⟩ ⟨P₁, rfl⟩ ⟨P₂, rfl⟩
  rw [hF, tracePairing_smul_left, tracePairing_smul_right, hdef, hdet]
  have hsq : (4 * lam) * ((4 * lam) * (72 * (windowProj standardComplexWindow pD : ComplexMatrix3).det.re)) =
      16 * 72 * lam ^ 2 * (windowProj standardComplexWindow pD : ComplexMatrix3).det.re := by ring
  rw [hsq, hlam2]
  norm_num [mul_assoc]
  ring

theorem glennie_nondegenerate (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hdel : tripleDelta (p 0) (p 1) (p 2) ≠ 0) :
    tracePairing
        (nativeGlennieF (symmetryOf (p 0)) (symmetryOf (p 1)) (symmetryOf (p 2)) (symmetryOf (p 3)))
        (nativeGlennieF (symmetryOf (p 0)) (symmetryOf (p 1)) (symmetryOf (p 2)) (symmetryOf (p 3))) =
      9 * 2 ^ 21 * albertCubicNorm (p 0 + p 1 + p 2) * fourPointInvariant p := by
  obtain ⟨_, _, _, _, ⟨W, hW0, hW1, hW2, _⟩, _⟩ :=
    lemma_A_window_generated (hp 0) (hp 1) (hp 2) hdel
  rcases hW0 with ⟨P₀, hP₀⟩
  rcases hW1 with ⟨P₁, hP₁⟩
  rcases hW2 with ⟨P₂, hP₂⟩
  obtain ⟨g, hg⟩ := native_complexWindow_conjugate_standard W
  have hg0 : g.linearEquiv (p 0) = standardComplexWindow.embedding P₀ := by rw [← hP₀, hg P₀]
  have hg1 : g.linearEquiv (p 1) = standardComplexWindow.embedding P₁ := by rw [← hP₁, hg P₁]
  have hg2 : g.linearEquiv (p 2) = standardComplexWindow.embedding P₂ := by rw [← hP₂, hg P₂]
  have h0 : IsAtom (standardComplexWindow.embedding P₀) := by rw [← hg0]; exact g.map_isAtom (hp 0)
  have h1 : IsAtom (standardComplexWindow.embedding P₁) := by rw [← hg1]; exact g.map_isAtom (hp 1)
  have h2 : IsAtom (standardComplexWindow.embedding P₂) := by rw [← hg2]; exact g.map_isAtom (hp 2)
  have h3 : IsAtom (g.linearEquiv (p 3)) := g.map_isAtom (hp 3)
  have hmain := glennie_of_standardComplexWindow h0 h1 h2 h3
  rw [← hg0, ← hg1, ← hg2] at hmain
  have hLHS :
      tracePairing
          (nativeGlennieF (symmetryOf (p 0)) (symmetryOf (p 1)) (symmetryOf (p 2)) (symmetryOf (p 3)))
          (nativeGlennieF (symmetryOf (p 0)) (symmetryOf (p 1)) (symmetryOf (p 2)) (symmetryOf (p 3))) =
        tracePairing
          (nativeGlennieF (symmetryOf (g.linearEquiv (p 0))) (symmetryOf (g.linearEquiv (p 1)))
            (symmetryOf (g.linearEquiv (p 2))) (symmetryOf (g.linearEquiv (p 3))))
          (nativeGlennieF (symmetryOf (g.linearEquiv (p 0))) (symmetryOf (g.linearEquiv (p 1)))
            (symmetryOf (g.linearEquiv (p 2))) (symmetryOf (g.linearEquiv (p 3)))) :=
    (tracePairing_nativeGlennieF_aut g (p 0) (p 1) (p 2) (p 3)).symm
  have hN :
      albertCubicNorm (g.linearEquiv (p 0) + g.linearEquiv (p 1) + g.linearEquiv (p 2)) =
        albertCubicNorm (p 0 + p 1 + p 2) := by
    rw [← map_add, ← map_add, g.map_cubicNorm]
  have hvec :
      ![g.linearEquiv (p 0), g.linearEquiv (p 1), g.linearEquiv (p 2), g.linearEquiv (p 3)] =
        fun i => g.linearEquiv (p i) := by
    funext i
    fin_cases i <;> rfl
  have hA :
      fourPointInvariant
          ![g.linearEquiv (p 0), g.linearEquiv (p 1), g.linearEquiv (p 2), g.linearEquiv (p 3)] =
        fourPointInvariant p := by
    rw [hvec]
    exact fourPointInvariant_automorphism_invariant g p
  rw [hLHS, hmain, hN, hA]

/-! ## Part 4: Exported Headline Theorems (the `Pending` statements and Paper Theorem `thm:glennie`) -/

/-- Proof of the statement `AlbertSequential.AppF.Pending.GlennieViolationStatement`. -/
theorem glennieViolationStatement_holds :
    AlbertSequential.AppF.Pending.GlennieViolationStatement := by
  intro p hp
  by_cases hdel : tripleDelta (p 0) (p 1) (p 2) = 0
  · exact glennie_degenerate p hp hdel
  · exact glennie_nondegenerate p hp hdel

/-- Proof of the statement `AlbertSequential.AppF.Pending.GlennieViolationAnyOrder`. -/
theorem glennieViolationAnyOrder_holds :
    AlbertSequential.AppF.Pending.GlennieViolationAnyOrder :=
  AlbertSequential.AppF.Pending.anyOrder_of_statement glennieViolationStatement_holds

/-- Paper Theorem `thm:glennie` (displayed norm-squared identity for four atoms). -/
theorem thm_glennie_normSq (pA pB pC pD : Albert)
    (hA : IsAtom pA) (hB : IsAtom pB) (hC : IsAtom pC) (hD : IsAtom pD) :
    tracePairing
        (nativeGlennieF ((2 : ℝ) • pA - albertUnit) ((2 : ℝ) • pB - albertUnit)
          ((2 : ℝ) • pC - albertUnit) ((2 : ℝ) • pD - albertUnit))
        (nativeGlennieF ((2 : ℝ) • pA - albertUnit) ((2 : ℝ) • pB - albertUnit)
          ((2 : ℝ) • pC - albertUnit) ((2 : ℝ) • pD - albertUnit)) =
      9 * 2 ^ 21 * albertCubicNorm (pA + pB + pC) * fourPointInvariant ![pA, pB, pC, pD] := by
  have hp_atoms : ∀ i : Fin 4, IsAtom (![pA, pB, pC, pD] i) := fun i => by
    fin_cases i <;> assumption
  exact glennieViolationStatement_holds ![pA, pB, pC, pD] hp_atoms

/-- Paper Theorem `thm:glennie` (permutation form over any three atoms in any order). -/
theorem thm_glennie_perm (pA pB pC pD : Albert)
    (hA : IsAtom pA) (hB : IsAtom pB) (hC : IsAtom pC) (hD : IsAtom pD)
    (σ : Equiv.Perm (Fin 4)) :
    let p : Fin 4 → Albert := ![pA, pB, pC, pD]
    let r : Fin 4 → Albert := fun i => (2 : ℝ) • p i - albertUnit
    tracePairing
        (nativeGlennieF (r (σ 0)) (r (σ 1)) (r (σ 2)) (r (σ 3)))
        (nativeGlennieF (r (σ 0)) (r (σ 1)) (r (σ 2)) (r (σ 3))) =
      9 * 2 ^ 21 * albertCubicNorm (p (σ 0) + p (σ 1) + p (σ 2)) *
        fourPointInvariant ![pA, pB, pC, pD] := by
  have hp_atoms : ∀ i : Fin 4, IsAtom (![pA, pB, pC, pD] i) := fun i => by
    fin_cases i <;> assumption
  exact glennieViolationAnyOrder_holds σ ![pA, pB, pC, pD] hp_atoms

/-- Paper Theorem `thm:glennie` (vanishing equivalence: `F(r_A, r_B, r_C, r_D) = 0 ↔ 𝒜 = 0`). -/
theorem thm_glennie_eq_zero_iff (pA pB pC pD : Albert)
    (hA : IsAtom pA) (hB : IsAtom pB) (hC : IsAtom pC) (hD : IsAtom pD) :
    nativeGlennieF ((2 : ℝ) • pA - albertUnit) ((2 : ℝ) • pB - albertUnit)
        ((2 : ℝ) • pC - albertUnit) ((2 : ℝ) • pD - albertUnit) = 0 ↔
      fourPointInvariant ![pA, pB, pC, pD] = 0 := by
  have hp_atoms : ∀ i : Fin 4, IsAtom (![pA, pB, pC, pD] i) := fun i => by
    fin_cases i <;> assumption
  constructor
  · intro hF0
    by_contra hA_ne
    have hdel_ne : tripleDelta pA pB pC ≠ 0 := by
      intro hdel0
      exact hA_ne (prop_windowdet_zero hA hB hC hD hdel0)
    have hN_ne : albertCubicNorm (pA + pB + pC) ≠ 0 := by
      intro hN0
      apply hdel_ne
      unfold tripleDelta
      rw [hN0, zero_mul]
    have hnorm := thm_glennie_normSq pA pB pC pD hA hB hC hD
    rw [hF0] at hnorm
    have hzero_lhs : tracePairing (0 : Albert) 0 = 0 := by
      rw [← zero_smul ℝ (0 : Albert), tracePairing_smul_left, zero_mul]
    rw [hzero_lhs] at hnorm
    have hprod_ne :
        9 * 2 ^ 21 * albertCubicNorm (pA + pB + pC) * fourPointInvariant ![pA, pB, pC, pD] ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (by norm_num) hN_ne) hA_ne
    exact hprod_ne hnorm.symm
  · intro hA0
    obtain ⟨Q, hQ⟩ := (fourPointInvariant_eq_zero_iff ![pA, pB, pC, pD] hp_atoms).mp hA0
    exact glennie_of_quatWindow Q ![pA, pB, pC, pD] hQ

/-- Paper Theorem `thm:glennie` (combined statement, as in core appendix `sec:tet`). -/
theorem thm_glennie (pA pB pC pD : Albert)
    (hA : IsAtom pA) (hB : IsAtom pB) (hC : IsAtom pC) (hD : IsAtom pD) :
    let rA := (2 : ℝ) • pA - albertUnit
    let rB := (2 : ℝ) • pB - albertUnit
    let rC := (2 : ℝ) • pC - albertUnit
    let rD := (2 : ℝ) • pD - albertUnit
    tracePairing (nativeGlennieF rA rB rC rD) (nativeGlennieF rA rB rC rD) =
        9 * 2 ^ 21 * albertCubicNorm (pA + pB + pC) * fourPointInvariant ![pA, pB, pC, pD] ∧
      (∀ σ : Equiv.Perm (Fin 4),
        let p : Fin 4 → Albert := ![pA, pB, pC, pD]
        let r : Fin 4 → Albert := fun i => (2 : ℝ) • p i - albertUnit
        tracePairing (nativeGlennieF (r (σ 0)) (r (σ 1)) (r (σ 2)) (r (σ 3)))
            (nativeGlennieF (r (σ 0)) (r (σ 1)) (r (σ 2)) (r (σ 3))) =
          9 * 2 ^ 21 * albertCubicNorm (p (σ 0) + p (σ 1) + p (σ 2)) *
            fourPointInvariant ![pA, pB, pC, pD]) ∧
      (nativeGlennieF rA rB rC rD = 0 ↔ fourPointInvariant ![pA, pB, pC, pD] = 0) :=
  ⟨thm_glennie_normSq pA pB pC pD hA hB hC hD,
   thm_glennie_perm pA pB pC pD hA hB hC hD,
   thm_glennie_eq_zero_iff pA pB pC pD hA hB hC hD⟩

end

end AlbertSequential.AppF
