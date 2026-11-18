module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.Module

/-! The ordinary L2-pair complexification of an arbitrary real inner-product
space. The fresh synonym prevents conflicting coordinatewise scalar instances.
No basis, separability or nonzero-space assumption is used.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace ComplexConjugate
namespace AlbertSequential

def RealHilbertComplexification (H : Type*) := WithLp 2 (H × H)

namespace RealHilbertComplexification
variable {H : Type*} [NormedAddCommGroup H]

instance : NormedAddCommGroup (RealHilbertComplexification H) :=
  inferInstanceAs (NormedAddCommGroup (WithLp 2 (H × H)))

def realPart (u : RealHilbertComplexification H) : H := (WithLp.ofLp u).1
def imagPart (u : RealHilbertComplexification H) : H := (WithLp.ofLp u).2
def pair (x y : H) : RealHilbertComplexification H := WithLp.toLp 2 (x, y)

omit [NormedAddCommGroup H] in
@[simp] theorem realPart_pair (x y : H) : realPart (pair x y) = x := rfl
omit [NormedAddCommGroup H] in
@[simp] theorem imagPart_pair (x y : H) : imagPart (pair x y) = y := rfl
@[simp] theorem realPart_zero : realPart (0 : RealHilbertComplexification H) = 0 := rfl
@[simp] theorem imagPart_zero : imagPart (0 : RealHilbertComplexification H) = 0 := rfl
@[simp] theorem realPart_add (u v : RealHilbertComplexification H) :
    realPart (u + v) = realPart u + realPart v := rfl
@[simp] theorem imagPart_add (u v : RealHilbertComplexification H) :
    imagPart (u + v) = imagPart u + imagPart v := rfl
@[simp] theorem realPart_neg (u : RealHilbertComplexification H) :
    realPart (-u) = -realPart u := rfl
@[simp] theorem imagPart_neg (u : RealHilbertComplexification H) :
    imagPart (-u) = -imagPart u := rfl

omit [NormedAddCommGroup H] in
@[ext] theorem real_imag_ext {u v : RealHilbertComplexification H}
    (hre : realPart u = realPart v) (him : imagPart u = imagPart v) : u = v := by
  apply WithLp.ofLp_injective 2
  exact Prod.ext hre him

variable [InnerProductSpace ℝ H]

instance : SMul ℂ (RealHilbertComplexification H) where
  smul z u := pair (z.re • realPart u - z.im • imagPart u)
    (z.im • realPart u + z.re • imagPart u)

@[simp] theorem realPart_smul (z : ℂ) (u : RealHilbertComplexification H) :
    realPart (z • u) = z.re • realPart u - z.im • imagPart u := rfl
@[simp] theorem imagPart_smul (z : ℂ) (u : RealHilbertComplexification H) :
    imagPart (z • u) = z.im • realPart u + z.re • imagPart u := rfl

instance : Module ℂ (RealHilbertComplexification H) where
  one_smul u := by apply real_imag_ext <;> simp
  mul_smul z w u := by
    apply real_imag_ext <;>
      simp only [realPart_smul, imagPart_smul, Complex.mul_re, Complex.mul_im] <;> module
  smul_zero z := by apply real_imag_ext <;> simp
  smul_add z u v := by
    apply real_imag_ext <;> simp only [realPart_smul, imagPart_smul, realPart_add, imagPart_add] <;> module
  add_smul z w u := by
    apply real_imag_ext <;>
      simp only [realPart_smul, imagPart_smul, realPart_add, imagPart_add,
        Complex.add_re, Complex.add_im] <;> module
  zero_smul u := by apply real_imag_ext <;> simp

omit [InnerProductSpace ℝ H] in
theorem norm_sq (u : RealHilbertComplexification H) :
    ‖u‖ ^ 2 = ‖realPart u‖ ^ 2 + ‖imagPart u‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 u

theorem norm_smul_sq (z : ℂ) (u : RealHilbertComplexification H) :
    ‖z • u‖ ^ 2 = ‖z‖ ^ 2 * ‖u‖ ^ 2 := by
  rw [norm_sq, realPart_smul, imagPart_smul, norm_sub_sq_real, norm_add_sq_real,
    norm_sq, Complex.sq_norm, Complex.normSq_apply]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_left, real_inner_smul_right]
  ring

instance : NormedSpace ℂ (RealHilbertComplexification H) where
  norm_smul_le z u := by
    apply le_of_sq_le_sq _ (mul_nonneg (norm_nonneg z) (norm_nonneg u))
    rw [norm_smul_sq, mul_pow]

def complexPairInner (u v : RealHilbertComplexification H) : ℂ :=
  ⟨⟪realPart u, realPart v⟫_ℝ + ⟪imagPart u, imagPart v⟫_ℝ,
    ⟪realPart u, imagPart v⟫_ℝ - ⟪imagPart u, realPart v⟫_ℝ⟩

instance : InnerProductSpace ℂ (RealHilbertComplexification H) where
  inner := complexPairInner
  norm_sq_eq_re_inner u := by
    change ‖u‖ ^ 2 = ⟪realPart u, realPart u⟫_ℝ + ⟪imagPart u, imagPart u⟫_ℝ
    simp only [real_inner_self_eq_norm_sq, norm_sq]
  conj_inner_symm u v := by
    apply Complex.ext <;> simp only [complexPairInner, Complex.conj_re,
      Complex.conj_im, real_inner_comm]
    all_goals ring
  add_left u v w := by
    apply Complex.ext <;> simp only [complexPairInner, realPart_add, imagPart_add,
      inner_add_left, Complex.add_re, Complex.add_im] <;> ring
  smul_left u v z := by
    apply Complex.ext <;> simp only [complexPairInner, realPart_smul, imagPart_smul,
      inner_add_left, inner_sub_left, real_inner_smul_left, Complex.conj_re,
      Complex.conj_im, Complex.mul_re, Complex.mul_im] <;> ring

@[simp] theorem complex_inner_re (u v : RealHilbertComplexification H) :
    (⟪u, v⟫_ℂ).re = ⟪realPart u, realPart v⟫_ℝ + ⟪imagPart u, imagPart v⟫_ℝ := rfl
@[simp] theorem complex_inner_im (u v : RealHilbertComplexification H) :
    (⟪u, v⟫_ℂ).im = ⟪realPart u, imagPart v⟫_ℝ - ⟪imagPart u, realPart v⟫_ℝ := rfl

instance [CompleteSpace H] : CompleteSpace (RealHilbertComplexification H) :=
  inferInstanceAs (CompleteSpace (WithLp 2 (H × H)))

@[simp] theorem realPart_real_smul (r : ℝ) (u : RealHilbertComplexification H) :
    realPart (r • u) = r • realPart u := by
  change realPart ((r : ℂ) • u) = r • realPart u
  simp only [realPart_smul, Complex.ofReal_re, Complex.ofReal_im, zero_smul, sub_zero]

@[simp] theorem imagPart_real_smul (r : ℝ) (u : RealHilbertComplexification H) :
    imagPart (r • u) = r • imagPart u := by
  change imagPart ((r : ℂ) • u) = r • imagPart u
  simp only [imagPart_smul, Complex.ofReal_re, Complex.ofReal_im, zero_smul, zero_add]

omit [InnerProductSpace ℝ H] in
@[simp] theorem norm_pair_zero (x : H) : ‖pair x (0 : H)‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [norm_sq, realPart_pair, imagPart_pair, norm_zero,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]

def conjugatePair (u : RealHilbertComplexification H) : RealHilbertComplexification H :=
  pair (realPart u) (-imagPart u)

omit [InnerProductSpace ℝ H] in
@[simp] theorem realPart_conjugatePair (u : RealHilbertComplexification H) :
    realPart (conjugatePair u) = realPart u := rfl
omit [InnerProductSpace ℝ H] in
@[simp] theorem imagPart_conjugatePair (u : RealHilbertComplexification H) :
    imagPart (conjugatePair u) = -imagPart u := rfl
omit [InnerProductSpace ℝ H] in
@[simp] theorem conjugatePair_involutive (u : RealHilbertComplexification H) :
    conjugatePair (conjugatePair u) = u := by
  apply real_imag_ext <;> simp

omit [InnerProductSpace ℝ H] in
theorem conjugatePair_norm (u : RealHilbertComplexification H) :
    ‖conjugatePair u‖ = ‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [norm_sq, realPart_conjugatePair, imagPart_conjugatePair, norm_neg]

theorem conjugatePair_complex_smul (z : ℂ) (u : RealHilbertComplexification H) :
    conjugatePair (z • u) = conj z • conjugatePair u := by
  apply real_imag_ext <;> simp only [realPart_conjugatePair, imagPart_conjugatePair,
    realPart_smul, imagPart_smul, Complex.conj_re, Complex.conj_im] <;> module

theorem pair_real_imag_decomposition (u : RealHilbertComplexification H) :
    u = pair (realPart u) 0 + Complex.I • pair (imagPart u) 0 := by
  apply real_imag_ext <;> simp

end RealHilbertComplexification

open RealHilbertComplexification
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def embedRealHilbertSpace : H →ₗᵢ[ℝ] RealHilbertComplexification H where
  toFun x := pair x 0
  map_add' x y := by apply real_imag_ext <;> simp
  map_smul' r x := by apply real_imag_ext <;> simp
  norm_map' x := norm_pair_zero x

def complexConjugation : RealHilbertComplexification H ≃ₗᵢ[ℝ]
    RealHilbertComplexification H where
  toFun := conjugatePair
  invFun := conjugatePair
  left_inv := conjugatePair_involutive
  right_inv := conjugatePair_involutive
  map_add' u v := by
    apply real_imag_ext <;> simp
    all_goals abel
  map_smul' r u := by apply real_imag_ext <;> simp
  norm_map' := conjugatePair_norm

end AlbertSequential
