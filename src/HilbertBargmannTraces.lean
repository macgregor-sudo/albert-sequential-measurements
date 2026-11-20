/- SPDX-License-Identifier: Apache-2.0 -/
module
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Tactic

/-! Bargmann traces of finite rank products on an arbitrary complex Hilbert space.
The trace is computed by an absolutely summable diagonal in every Hilbert basis. -/
@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace AlbertSequential.Bargmann.Hilbert
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def dyad (a : H) := InnerProductSpace.rankOne ℂ a a
def cycle (a b c d : H) := ⟪a,b⟫_ℂ * ⟪b,c⟫_ℂ * ⟪c,d⟫_ℂ * ⟪d,a⟫_ℂ
def jordanPair (a b : H) := (1/2 : ℂ) • (dyad a * dyad b + dyad b * dyad a)
def doubleTrace (e : HilbertBasis ι ℂ H) (a b c d : H) : ℝ :=
  (∑' i, ⟪e i, (jordanPair a b * jordanPair c d) (e i)⟫_ℂ).re

theorem hasSum_cycle (e : HilbertBasis ι ℂ H) (a b c d : H) :
    HasSum (fun i => ⟪e i, (dyad a * dyad b * dyad c * dyad d) (e i)⟫_ℂ) (cycle a b c d) := by
  apply ((e.hasSum_inner_mul_inner d a).mul_left (⟪a,b⟫_ℂ * ⟪b,c⟫_ℂ * ⟪c,d⟫_ℂ)).congr_fun
  intro i
  simp [dyad,inner_smul_right]
  ring

theorem hasSum_double (e : HilbertBasis ι ℂ H) (a b c d : H) :
    HasSum (fun i => ⟪e i, (jordanPair a b * jordanPair c d) (e i)⟫_ℂ)
      ((1/4 : ℂ) * ((cycle a b c d + cycle a b d c) + (cycle b a c d + cycle b a d c))) := by
  apply (((hasSum_cycle e a b c d).add (hasSum_cycle e a b d c)).add
    ((hasSum_cycle e b a c d).add (hasSum_cycle e b a d c))).mul_left (1/4 : ℂ) |>.congr_fun
  intro i
  simp only [jordanPair,smul_mul_smul,add_mul,mul_add,← mul_assoc,smul_apply,
    add_apply,inner_smul_right,inner_add_right]
  ring

private theorem rev_re (a b c d : H) : (cycle a d c b).re = (cycle a b c d).re := by
  have h : cycle a d c b = star (cycle a b c d) := by
    simp only [cycle,star_mul,Complex.star_def,inner_conj_symm]
    ring
  rw [h,Complex.star_def,Complex.conj_re]

private theorem rotate (a b c d : H) : cycle b c d a = cycle a b c d := by unfold cycle; ring

theorem doubleTrace_eq (e : HilbertBasis ι ℂ H) (a b c d : H) :
    doubleTrace e a b c d = ((cycle a b c d).re + (cycle a b d c).re)/2 := by
  rw [doubleTrace,(hasSum_double e a b c d).tsum_eq]
  simp only [Complex.mul_re,Complex.add_re]
  rw [← rotate b a c d,← rotate b a d c,rev_re a b d c,rev_re a b c d]
  norm_num
  ring

theorem omega_eq (e : HilbertBasis ι ℂ H) (a b c d : H) :
    let t₁ := doubleTrace e a b c d
    let t₂ := doubleTrace e a c b d
    let t₃ := doubleTrace e a d b c
    t₂ + t₃ - t₁ = (cycle a c b d).re ∧
    t₁ + t₃ - t₂ = (cycle a b c d).re ∧
    t₁ + t₂ - t₃ = (cycle a b d c).re := by
  dsimp only
  simp only [doubleTrace_eq,rev_re a b d c,rev_re a c b d,rev_re a b c d]
  constructor
  · ring
  constructor <;> ring
end AlbertSequential.Bargmann.Hilbert
