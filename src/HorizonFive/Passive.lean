/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HorizonFive.Window

/-! # Step 1 of lem:cer:h5:seven: one passive letter

Paper (companion `app:cert:h5`, proof of lem:cer:h5:seven, Step 1): if `F` has degree one in `x_j` and `σ̂(F) = 0`,
then `ν̂(F) = 0`, for any four atoms.  The paper moves the three other atoms into `H₃(ℂ_i)` by
lem:A:three, uses that `M₃(ℂ_i) ⊕ M₃(𝕆)` is associative (Artin), and reads off coefficients of the
free letter.

Lean route (same statement, different bookkeeping):

* `complexToOctonion` puts `ℂ_i` in the first quaternion; octonion products with two complex
  arguments associate (`oct_assoc_*`, by coordinates);
* complex matrices act on octonion matrices on the left (`lmul`) and on the right (`rmul`), and
  these actions form a bimodule (`lmul_mul`, `rmul_mul`, `lmul_rmul`);
* instead of reading off coefficients, an algebra map `ψ : ℝ[G] → End(E × E)`,
  `E = M₃(ℂ) × M₃(𝕆)`, sends `r_i ↦ diag(L_{a_i}, L_{a_i})` (`i ≠ j`) and `r_j ↦ K + N_m`, with
  `K = diag(1, -1)` and `N_m` an off-diagonal square-zero operator; `ψ(r_j)² = 1` for every `m`.
  For `F` of degree one in `x_j`, `ψ(σ̂ F)` applied to a fixed vector is the octonion matrix
  `linVal F` given by the bimodule recursion, and the Albert value of `F` (after lem:A:three) has
  octonion matrix `linVal F` with `m = albertMatrix (g s_j)`.

Headline: `passive_transfer`. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.HorizonFive

open AlbertSequential AlbertSequential.NativeAnalysis

/-! ## Octonions with complex arguments -/

/-- The quaternion of a complex number (`ℂ_i` in the first quaternion). -/
def cq (z : ℂ) : Quaternion ℝ := ⟨z.re, z.im, 0, 0⟩

theorem cq_mul (z w : ℂ) : cq (z * w) = cq z * cq w := by
  (apply Quaternion.ext <;> simp [cq]); all_goals ring

theorem cq_comm (z w : ℂ) : cq z * cq w = cq w * cq z := by
  rw [← cq_mul, ← cq_mul, mul_comm]

theorem cq_star (z : ℂ) : star (cq z) = cq (star z) := by
  apply Quaternion.ext <;> simp [cq]

theorem cq_one : cq 1 = 1 := by
  apply Quaternion.ext <;> simp [cq]

theorem complexToOctonion_eq (z : ℂ) : complexToOctonion z = (cq z, 0) := rfl

theorem cl1 (z : ℂ) (x : Octonion) : (octonionMul (complexToOctonion z) x).1 = cq z * x.1 := by
  change cq z * x.1 - star x.2 * 0 = cq z * x.1
  rw [mul_zero, sub_zero]

theorem cl2 (z : ℂ) (x : Octonion) : (octonionMul (complexToOctonion z) x).2 = x.2 * cq z := by
  change x.2 * cq z + 0 * star x.1 = x.2 * cq z
  rw [zero_mul, add_zero]

theorem cr1 (z : ℂ) (x : Octonion) : (octonionMul x (complexToOctonion z)).1 = x.1 * cq z := by
  change x.1 * cq z - star 0 * x.2 = x.1 * cq z
  rw [star_zero, zero_mul, sub_zero]

theorem cr2 (z : ℂ) (x : Octonion) :
    (octonionMul x (complexToOctonion z)).2 = x.2 * cq (star z) := by
  change 0 * x.1 + x.2 * star (cq z) = x.2 * cq (star z)
  rw [zero_mul, zero_add, cq_star]

/-- `z(wx) = (zw)x` for complex `z, w`. -/
theorem oct_assoc_ll (z w : ℂ) (x : Octonion) :
    octonionMul (complexToOctonion z) (octonionMul (complexToOctonion w) x) =
      octonionMul (complexToOctonion (z * w)) x := by
  apply Prod.ext
  · rw [cl1, cl1, cl1, cq_mul, mul_assoc]
  · rw [cl2, cl2, cl2, cq_mul, mul_assoc, cq_comm w z]

/-- `(xz)w = x(zw)` for complex `z, w`. -/
theorem oct_assoc_rr (z w : ℂ) (x : Octonion) :
    octonionMul (octonionMul x (complexToOctonion z)) (complexToOctonion w) =
      octonionMul x (complexToOctonion (z * w)) := by
  apply Prod.ext
  · rw [cr1, cr1, cr1, cq_mul, mul_assoc]
  · rw [cr2, cr2, cr2, star_mul', cq_mul, mul_assoc]

/-- `z(xw) = (zx)w` for complex `z, w`. -/
theorem oct_assoc_lr (z w : ℂ) (x : Octonion) :
    octonionMul (complexToOctonion z) (octonionMul x (complexToOctonion w)) =
      octonionMul (octonionMul (complexToOctonion z) x) (complexToOctonion w) := by
  apply Prod.ext
  · rw [cl1, cr1, cr1, cl1, mul_assoc]
  · simp only [cl2, cr2, mul_assoc]
    rw [cq_comm (star w) z]

theorem oct_cone_left (x : Octonion) : octonionMul (complexToOctonion 1) x = x := by
  apply Prod.ext
  · rw [cl1, cq_one, one_mul]
  · rw [cl2, cq_one, mul_one]

theorem oct_cone_right (x : Octonion) : octonionMul x (complexToOctonion 1) = x := by
  apply Prod.ext
  · rw [cr1, cq_one, mul_one]
  · rw [cr2, star_one, cq_one, mul_one]

/-! ## The bimodule `M₃(𝕆)` over `M₃(ℂ)` -/

/-- Left action of complex matrices on octonion matrices. -/
def lmul (A : ComplexMatrix3) (m : NativeOctonionMatrix) : NativeOctonionMatrix :=
  fun i k => ∑ l, octonionMul (complexToOctonion (A i l)) (m l k)

/-- Right action of complex matrices on octonion matrices. -/
def rmul (m : NativeOctonionMatrix) (A : ComplexMatrix3) : NativeOctonionMatrix :=
  fun i k => ∑ l, octonionMul (m i l) (complexToOctonion (A l k))

/-- The octonion matrix of a complex matrix. -/
def cmat (A : ComplexMatrix3) : NativeOctonionMatrix := fun i k => complexToOctonion (A i k)

theorem octonionMatrixMul_cmat_left (A : ComplexMatrix3) (m : NativeOctonionMatrix) :
    octonionMatrixMul (cmat A) m = lmul A m := rfl

theorem octonionMatrixMul_cmat_right (A : ComplexMatrix3) (m : NativeOctonionMatrix) :
    octonionMatrixMul m (cmat A) = rmul m A := rfl

theorem lmul_mul (A B : ComplexMatrix3) (m : NativeOctonionMatrix) :
    lmul (A * B) m = lmul A (lmul B m) := by
  funext i k
  simp only [lmul, Matrix.mul_apply, map_sum, octonionMul_finsetSum_left,
    octonionMul_finsetSum_right, oct_assoc_ll]
  exact Finset.sum_comm

theorem rmul_mul (A B : ComplexMatrix3) (m : NativeOctonionMatrix) :
    rmul m (A * B) = rmul (rmul m A) B := by
  funext i k
  simp only [rmul, Matrix.mul_apply, map_sum, octonionMul_finsetSum_left,
    octonionMul_finsetSum_right, oct_assoc_rr]
  exact Finset.sum_comm

theorem lmul_rmul (A B : ComplexMatrix3) (m : NativeOctonionMatrix) :
    lmul A (rmul m B) = rmul (lmul A m) B := by
  funext i k
  simp only [lmul, rmul, octonionMul_finsetSum_left, octonionMul_finsetSum_right, oct_assoc_lr]
  exact Finset.sum_comm

theorem lmul_one (m : NativeOctonionMatrix) : lmul 1 m = m := by
  funext i k
  simp only [lmul]
  rw [Finset.sum_eq_single i]
  · rw [Matrix.one_apply_eq, oct_cone_left]
  · intro l _ hl
    rw [Matrix.one_apply_ne (Ne.symm hl), map_zero, octonionMul_zero_left]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem rmul_one (m : NativeOctonionMatrix) : rmul m 1 = m := by
  funext i k
  simp only [rmul]
  rw [Finset.sum_eq_single k]
  · rw [Matrix.one_apply_eq, oct_cone_right]
  · intro l _ hl
    rw [Matrix.one_apply_ne hl, map_zero, octonionMul_zero_right]
  · intro h; exact absurd (Finset.mem_univ k) h

theorem lmul_add_right (A : ComplexMatrix3) (m n : NativeOctonionMatrix) :
    lmul A (m + n) = lmul A m + lmul A n := by
  funext i k
  simp only [lmul, Pi.add_apply, octonionMul_add_right, Finset.sum_add_distrib]

theorem lmul_smul_right (A : ComplexMatrix3) (r : ℝ) (m : NativeOctonionMatrix) :
    lmul A (r • m) = r • lmul A m := by
  funext i k
  simp only [lmul, Pi.smul_apply, octonionMul_smul_right, Finset.smul_sum]

theorem lmul_add_left (A B : ComplexMatrix3) (m : NativeOctonionMatrix) :
    lmul (A + B) m = lmul A m + lmul B m := by
  funext i k
  simp only [lmul, Matrix.add_apply, map_add, octonionMul_add_left, Finset.sum_add_distrib,
    Pi.add_apply]

theorem lmul_smul_left (r : ℝ) (A : ComplexMatrix3) (m : NativeOctonionMatrix) :
    lmul (r • A) m = r • lmul A m := by
  funext i k
  simp only [lmul, Matrix.smul_apply, map_smul, octonionMul_smul_left, Finset.smul_sum,
    Pi.smul_apply]

theorem rmul_add_left (m n : NativeOctonionMatrix) (A : ComplexMatrix3) :
    rmul (m + n) A = rmul m A + rmul n A := by
  funext i k
  simp only [rmul, Pi.add_apply, octonionMul_add_left, Finset.sum_add_distrib]

theorem rmul_smul_left (r : ℝ) (m : NativeOctonionMatrix) (A : ComplexMatrix3) :
    rmul (r • m) A = r • rmul m A := by
  funext i k
  simp only [rmul, Pi.smul_apply, octonionMul_smul_left, Finset.smul_sum]

theorem rmul_add_right (m : NativeOctonionMatrix) (A B : ComplexMatrix3) :
    rmul m (A + B) = rmul m A + rmul m B := by
  funext i k
  simp only [rmul, Matrix.add_apply, map_add, octonionMul_add_right, Finset.sum_add_distrib,
    Pi.add_apply]

theorem rmul_smul_right (r : ℝ) (m : NativeOctonionMatrix) (A : ComplexMatrix3) :
    rmul m (r • A) = r • rmul m A := by
  funext i k
  simp only [rmul, Matrix.smul_apply, map_smul, octonionMul_smul_right, Finset.smul_sum,
    Pi.smul_apply]

theorem lmul_zero_right (A : ComplexMatrix3) : lmul A 0 = 0 := by
  funext i k
  simp only [lmul, Pi.zero_apply, octonionMul_zero_right, Finset.sum_const_zero]

theorem rmul_zero_left (A : ComplexMatrix3) : rmul 0 A = 0 := by
  funext i k
  simp only [rmul, Pi.zero_apply, octonionMul_zero_left, Finset.sum_const_zero]

theorem rmul_zero_right (m : NativeOctonionMatrix) : rmul m 0 = 0 := by
  funext i k
  simp only [rmul, Matrix.zero_apply, map_zero, octonionMul_zero_right, Finset.sum_const_zero,
    Pi.zero_apply]

/-- `lmul A` as a linear map. -/
def lmulL (A : ComplexMatrix3) : NativeOctonionMatrix →ₗ[ℝ] NativeOctonionMatrix where
  toFun := lmul A
  map_add' := lmul_add_right A
  map_smul' r m := lmul_smul_right A r m

/-- `A ↦ rmul m A` as a linear map. -/
def rmulBy (m : NativeOctonionMatrix) : ComplexMatrix3 →ₗ[ℝ] NativeOctonionMatrix where
  toFun := rmul m
  map_add' := rmul_add_right m
  map_smul' r A := rmul_smul_right r m A

/-! ## The operator model `End(E × E)` -/

/-- `E = M₃(ℂ) × M₃(𝕆)`. -/
abbrev PE := ComplexMatrix3 × NativeOctonionMatrix

/-- The space the operators act on. -/
abbrev PV := PE × PE

/-- Left multiplication by `(A, 0)` in the split-null extension. -/
def LA (A : ComplexMatrix3) : PE →ₗ[ℝ] PE := (LinearMap.mulLeft ℝ A).prodMap (lmulL A)

/-- Left multiplication by `(0, m)` in the split-null extension. -/
def Lam (m : NativeOctonionMatrix) : PE →ₗ[ℝ] PE :=
  (LinearMap.inr ℝ ComplexMatrix3 NativeOctonionMatrix).comp
    ((rmulBy m).comp (LinearMap.fst ℝ ComplexMatrix3 NativeOctonionMatrix))

def Dop (A : ComplexMatrix3) : Module.End ℝ PV := (LA A).prodMap (LA A)

def Kop : Module.End ℝ PV := (LinearMap.id).prodMap (-LinearMap.id)

def Nop (m : NativeOctonionMatrix) : Module.End ℝ PV :=
  ((Lam m).comp (LinearMap.snd ℝ PE PE)).prod ((Lam m).comp (LinearMap.fst ℝ PE PE))

theorem Dop_apply (A : ComplexMatrix3) (v : PV) :
    Dop A v = ((A * v.1.1, lmul A v.1.2), (A * v.2.1, lmul A v.2.2)) := rfl

theorem Kop_apply (v : PV) : Kop v = (v.1, -v.2) := rfl

theorem Nop_apply (m : NativeOctonionMatrix) (v : PV) :
    Nop m v = ((0, rmul m v.2.1), (0, rmul m v.1.1)) := rfl

theorem Dop_mul (A B : ComplexMatrix3) : Dop (A * B) = Dop A * Dop B := by
  apply LinearMap.ext; intro v
  simp only [mul_apply_eq_comp, Dop_apply, mul_assoc, lmul_mul]

theorem Dop_one : Dop 1 = 1 := by
  apply LinearMap.ext; intro v
  simp only [Dop_apply, one_mul, lmul_one, one_apply_eq_self]

theorem Dop_add (A B : ComplexMatrix3) : Dop (A + B) = Dop A + Dop B := by
  apply LinearMap.ext; intro v
  simp only [LinearMap.add_apply, Dop_apply, add_mul, lmul_add_left, Prod.mk_add_mk]

theorem Dop_smul (r : ℝ) (A : ComplexMatrix3) : Dop (r • A) = r • Dop A := by
  apply LinearMap.ext; intro v
  simp only [LinearMap.smul_apply, Dop_apply, smul_mul_assoc, lmul_smul_left, Prod.smul_mk]

theorem Kop_Dop (A : ComplexMatrix3) : Kop * Dop A = Dop A * Kop := by
  apply LinearMap.ext; intro v
  simp only [mul_apply_eq_comp, Dop_apply, Kop_apply, Prod.fst_neg, Prod.snd_neg, mul_neg,
    Prod.neg_mk]
  congr 2
  change -lmul A v.2.2 = lmul A (-v.2.2)
  rw [← neg_one_smul ℝ v.2.2, lmul_smul_right, neg_one_smul]

theorem Nop_add (m n : NativeOctonionMatrix) : Nop (m + n) = Nop m + Nop n := by
  apply LinearMap.ext; intro v
  simp only [LinearMap.add_apply, Nop_apply, rmul_add_left, Prod.mk_add_mk, add_zero]

theorem Nop_smul (r : ℝ) (m : NativeOctonionMatrix) : Nop (r • m) = r • Nop m := by
  apply LinearMap.ext; intro v
  simp only [LinearMap.smul_apply, Nop_apply, rmul_smul_left, Prod.smul_mk, smul_zero]

theorem Nop_zero : Nop 0 = 0 := by
  apply LinearMap.ext; intro v
  simp only [Nop_apply, rmul_zero_left, LinearMap.zero_apply]
  rfl

/-- The image of `r_j` squares to one, whatever `m` is. -/
theorem KN_sq (m : NativeOctonionMatrix) : (Kop + Nop m) * (Kop + Nop m) = 1 := by
  apply LinearMap.ext; intro v
  simp only [mul_apply_eq_comp, LinearMap.add_apply, Kop_apply, Nop_apply, Prod.fst_add,
    Prod.snd_add, Prod.fst_neg, Prod.snd_neg, Prod.neg_mk, Prod.mk_add_mk, one_apply_eq_self,
    zero_add, add_zero, neg_zero, rmul_zero_right]
  have h1 : rmul m (-v.2.1) = -rmul m v.2.1 := by
    rw [← neg_one_smul ℝ v.2.1, rmul_smul_right, neg_one_smul]
  rw [h1]
  ext <;> simp

theorem lmul_neg_right (A : ComplexMatrix3) (x : NativeOctonionMatrix) :
    lmul A (-x) = -lmul A x := by
  rw [← neg_one_smul ℝ x, lmul_smul_right, neg_one_smul]

/-- `N_L D_h + D_h N_L = N_{L h + h L}`. -/
theorem key_left (c h : ComplexMatrix3) (L : NativeOctonionMatrix) :
    (1 / 2 : ℝ) • ((Kop * Dop c + Nop L) * Dop h + Dop h * (Kop * Dop c + Nop L)) =
      Kop * Dop ((1 / 2 : ℝ) • (c * h + h * c)) +
        Nop ((1 / 2 : ℝ) • (lmul h L + rmul L h)) := by
  apply LinearMap.ext; intro v
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;>
  simp only [LinearMap.smul_apply, LinearMap.add_apply, mul_apply_eq_comp, Dop_apply,
    Kop_apply, Nop_apply, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg,
    Prod.smul_fst, Prod.smul_snd, mul_zero, lmul_zero_right, ← rmul_mul, lmul_rmul,
    rmul_add_left, rmul_smul_left, lmul_add_left, lmul_smul_left, ← lmul_mul, add_mul,
    smul_mul_assoc, mul_assoc, mul_neg, smul_add, add_zero, zero_add, lmul_neg_right,
    smul_zero, neg_zero, lmul_add_right] <;>
  module

/-! ## The algebra map `ψ : ℝ[G] → End(E × E)` -/

section Psi
variable (j : Test) (a : Test → ComplexMatrix3) (m : NativeOctonionMatrix)

/-- Images of the symmetries. -/
def uop (i : Test) : Module.End ℝ PV := if i = j then Kop + Nop m else Dop (a i)

theorem uop_sq (ha : ∀ i, i ≠ j → a i * a i = 1) (i : Test) :
    uop j a m i * uop j a m i = 1 := by
  unfold uop
  split_ifs with h
  · exact KN_sq m
  · rw [← Dop_mul, ha i h, Dop_one]

def pop (i : Test) : Module.End ℝ PV := (1 / 2 : ℝ) • (1 + uop j a m i)

theorem pop_idem (ha : ∀ i, i ≠ j → a i * a i = 1) (i : Test) :
    pop j a m i * pop j a m i = pop j a m i := by
  have hu := uop_sq j a m ha i
  simp only [pop, smul_mul_assoc, mul_smul_comm, mul_add, add_mul, one_mul, mul_one, hu,
    smul_smul, smul_add]
  module

def psi (ha : ∀ i, i ≠ j → a i * a i = 1) :
    UniversalProjectionAlgebra 4 →ₐ[ℝ] Module.End ℝ PV :=
  RingQuot.liftAlgHom ℝ ⟨FreeAlgebra.lift ℝ (pop j a m), by
    intro x y h
    cases h with
    | generator i =>
      simp only [map_mul, FreeAlgebra.lift_ι_apply]
      exact pop_idem j a m ha i⟩

theorem psi_tests (ha : ∀ i, i ≠ j → a i * a i = 1) (i : Test) :
    psi j a m ha (universalTests i) = pop j a m i := by
  simp only [psi, universalTests, universalProjection, projectionQuotient]
  rw [RingQuot.liftAlgHom_mkAlgHom_apply]
  simp only [FreeAlgebra.lift_ι_apply]

theorem psi_symm (ha : ∀ i, i ≠ j → a i * a i = 1) (i : Test) :
    psi j a m ha (specialSymmetry i) = uop j a m i := by
  simp only [specialSymmetry, map_sub, map_smul, map_one, psi_tests, pop, smul_smul]
  norm_num

/-- Matrix value (`x_j ↦ a_j`, irrelevant on expressions free of `x_j`). -/
def matVal (F : JPoly Test) : ComplexMatrix3 := (specialTarget ComplexMatrix3).eval a F

/-- The linear readout: the `M₃(𝕆)` part of the evaluation in the split-null extension. -/
def linVal : JPoly Test → NativeOctonionMatrix
  | .one => 0
  | .var i => if i = j then m else 0
  | .add F G => linVal F + linVal G
  | .smul r F => r • linVal F
  | .mul F G => (1 / 2 : ℝ) • (lmul (matVal a G) (linVal F) + rmul (linVal F) (matVal a G) +
      lmul (matVal a F) (linVal G) + rmul (linVal G) (matVal a F))

theorem linVal_free (F : JPoly Test) (hF : F.FreeOf j) : linVal j a m F = 0 := by
  induction hF with
  | one => rfl
  | var x hx => simp only [linVal, ite_eq_right hx]
  | add F G _ _ hF hG => simp only [linVal, hF, hG, add_zero]
  | smul r F _ hF => simp only [linVal, hF, smul_zero]
  | mul F G _ _ hF hG =>
    simp only [linVal, hF, hG, lmul_zero_right, rmul_zero_left, add_zero, smul_zero]

theorem eval_free (F : JPoly Test) (hF : F.FreeOf j) :
    (specialTarget (Module.End ℝ PV)).eval (uop j a m) F = Dop (matVal a F) := by
  induction hF with
  | one => exact Dop_one.symm
  | var x hx => simp only [JTarget.eval, uop, ite_eq_right hx, matVal]
  | add F G _ _ hF hG =>
    simp only [JTarget.eval, matVal] at hF hG ⊢
    rw [hF, hG, Dop_add]
  | smul r F _ hF =>
    simp only [JTarget.eval, matVal] at hF ⊢
    rw [hF, Dop_smul]
  | mul F G _ _ hF hG =>
    simp only [JTarget.eval, matVal] at hF hG ⊢
    rw [hF, hG, specialTarget_mul, specialTarget_mul, Dop_smul, Dop_add, Dop_mul, Dop_mul]

theorem eval_linear (F : JPoly Test) (hF : F.LinearIn j) :
    ∃ c : ComplexMatrix3, (specialTarget (Module.End ℝ PV)).eval (uop j a m) F =
      Kop * Dop c + Nop (linVal j a m F) := by
  induction hF with
  | var =>
    refine ⟨1, ?_⟩
    simp only [JTarget.eval, uop, linVal, ↓reduceIte, Dop_one, mul_one]
  | add F G _ _ hF hG =>
    obtain ⟨c, hc⟩ := hF
    obtain ⟨d, hd⟩ := hG
    refine ⟨c + d, ?_⟩
    change _ + _ = _
    rw [hc, hd, linVal, Dop_add, mul_add, Nop_add]
    abel
  | smul r F _ hF =>
    obtain ⟨c, hc⟩ := hF
    refine ⟨r • c, ?_⟩
    change r • _ = _
    rw [hc, linVal, Dop_smul, Nop_smul, smul_add, mul_smul_comm]
  | mulLeft F G _ hG hF =>
    obtain ⟨c, hc⟩ := hF
    refine ⟨(1 / 2 : ℝ) • (c * matVal a G + matVal a G * c), ?_⟩
    change (specialTarget _).mul _ _ = _
    rw [hc, eval_free j a m G hG, specialTarget_mul, key_left]
    congr 2
    simp only [linVal, linVal_free j a m G hG, lmul_zero_right, rmul_zero_left, add_zero]
  | mulRight F G hF _ hG =>
    obtain ⟨c, hc⟩ := hG
    refine ⟨(1 / 2 : ℝ) • (c * matVal a F + matVal a F * c), ?_⟩
    change (specialTarget _).mul _ _ = _
    rw [hc, eval_free j a m F hF, specialTarget_mul, add_comm (Dop _ * _), key_left]
    congr 2
    simp only [linVal, linVal_free j a m F hF, lmul_zero_right, rmul_zero_left, zero_add]
    try rw [add_comm]

/-- **The readout.** If `σ̂(F) = 0` and `F` has degree one in `x_j`, then `linVal F = 0`. -/
theorem linVal_eq_zero (ha : ∀ i, i ≠ j → a i * a i = 1) (F : JPoly Test) (hF : F.LinearIn j)
    (h0 : specialEval F = 0) : linVal j a m F = 0 := by
  obtain ⟨c, hc⟩ := eval_linear j a m F hF
  have h1 : psi j a m ha (specialEval F) =
      (specialTarget (Module.End ℝ PV)).eval (uop j a m) F := by
    rw [specialEval, specialTarget_eval_hom]
    congr 1
    funext i
    exact psi_symm j a m ha i
  rw [h0, map_zero, hc] at h1
  have h2 := congrArg (fun T : Module.End ℝ PV => (T ((0, 0), (1, 0))).1.2) h1
  simp only [LinearMap.zero_apply, LinearMap.add_apply, mul_apply_eq_comp, Dop_apply,
    Kop_apply, Nop_apply, Prod.fst_add, Prod.snd_add, mul_zero, lmul_zero_right, rmul_one,
    zero_add] at h2
  exact h2.symm

end Psi

/-! ## The Albert side -/

theorem albertCoordinates_albertMatrix (x : Albert) : albertCoordinates (albertMatrix x) = x := by
  apply Prod.ext
  · funext i; fin_cases i <;> rfl
  · funext k; fin_cases k <;> rfl

theorem albertCoordinates_zero : albertCoordinates 0 = 0 := by
  apply Prod.ext
  · funext i; rfl
  · funext k; fin_cases k <;> rfl

theorem albertMatrix_add (x y : Albert) : albertMatrix (x + y) = albertMatrix x + albertMatrix y := by
  funext i k
  fin_cases i <;> fin_cases k <;>
    first
    | exact octonionScalar_add (x.1 0) (y.1 0)
    | exact octonionScalar_add (x.1 1) (y.1 1)
    | exact octonionScalar_add (x.1 2) (y.1 2)
    | rfl
    | exact octonionConj_add (x.2 0) (y.2 0)
    | exact octonionConj_add (x.2 1) (y.2 1)
    | exact octonionConj_add (x.2 2) (y.2 2)

theorem albertMatrix_smul (r : ℝ) (x : Albert) : albertMatrix (r • x) = r • albertMatrix x := by
  funext i k
  fin_cases i <;> fin_cases k <;>
    first
    | exact octonionScalar_smul r (x.1 0)
    | exact octonionScalar_smul r (x.1 1)
    | exact octonionScalar_smul r (x.1 2)
    | rfl
    | exact octonionConj_smul r (x.2 0)
    | exact octonionConj_smul r (x.2 1)
    | exact octonionConj_smul r (x.2 2)

theorem octonionConj_complex (z : ℂ) :
    octonionConj (complexToOctonion z) = complexToOctonion (star z) := by
  apply Prod.ext
  · change star (cq z) = cq (star z)
    exact cq_star z
  · exact neg_zero

theorem albertMatrix_complexHerm (Z : Hermitian3) :
    albertMatrix (complexHermToAlbert Z) = cmat (Z : ComplexMatrix3) := by
  have hZ : star (Z : ComplexMatrix3) = Z := Z.prop
  have hT : ∀ i k, (Z : ComplexMatrix3) k i = star ((Z : ComplexMatrix3) i k) := fun i k => by
    have := congrArg (fun M : ComplexMatrix3 => M k i) hZ
    simp only [Matrix.star_apply] at this
    exact this.symm
  have hD : ∀ i, octonionScalar ((Z : ComplexMatrix3) i i).re =
      complexToOctonion ((Z : ComplexMatrix3) i i) := fun i => by
    have him : ((Z : ComplexMatrix3) i i).im = 0 := by
      have := congrArg Complex.im (hT i i)
      simp only [Complex.star_def, Complex.conj_im] at this
      linarith
    apply Prod.ext
    · apply Quaternion.ext <;> simp [octonionScalar, cq, complexToOctonion_eq, him]
    · rfl
  funext i k
  fin_cases i <;> fin_cases k
  · exact hD 0
  · rfl
  · rfl
  · change octonionConj (complexToOctonion ((Z : ComplexMatrix3) 0 1)) = _
    rw [octonionConj_complex, ← hT]; rfl
  · exact hD 1
  · rfl
  · change octonionConj (complexToOctonion ((Z : ComplexMatrix3) 0 2)) = _
    rw [octonionConj_complex, ← hT]; rfl
  · change octonionConj (complexToOctonion ((Z : ComplexMatrix3) 1 2)) = _
    rw [octonionConj_complex, ← hT]; rfl
  · exact hD 2

/-- Automorphisms commute with Albert evaluation. -/
theorem auto_eval (g : NativeAlbertAutomorphism) {X : Type} (v : X → Albert) (F : JPoly X) :
    g.linearEquiv (albertTarget.eval v F) = albertTarget.eval (fun x => g.linearEquiv (v x)) F := by
  induction F with
  | one => exact g.preserves_unit
  | var x => rfl
  | add F G hF hG =>
    change g.linearEquiv (_ + _) = _ + _
    rw [map_add, hF, hG]
  | smul r F hF =>
    change g.linearEquiv (r • _) = r • _
    rw [map_smul, hF]
  | mul F G hF hG =>
    change g.linearEquiv (jordanMul _ _) = jordanMul _ _
    rw [g.preserves_product, hF, hG]

section AlbertSide
variable (j : Test) (Y : Test → Hermitian3) (y : Albert)

/-- Albert valuation: `x_i ↦ complexHermToAlbert (Y i)` for `i ≠ j`, `x_j ↦ y`. -/
def aval (i : Test) : Albert := if i = j then y else complexHermToAlbert (Y i)

theorem albert_free (F : JPoly Test) (hF : F.FreeOf j) :
    ∃ Z : Hermitian3, (Z : ComplexMatrix3) = matVal (fun i => (Y i : ComplexMatrix3)) F ∧
      complexHermToAlbert Z = albertTarget.eval (aval j Y y) F := by
  obtain ⟨Z, h1, h2⟩ := window_eval standardComplexWindow Y F
  refine ⟨Z, h1, ?_⟩
  rw [← standardComplexWindow_apply, h2]
  apply albertTarget.eval_congr_free _ _ j _ F hF
  intro x hx
  simp only [aval, ite_eq_right hx, standardComplexWindow_apply]

theorem albert_linear (F : JPoly Test) (hF : F.LinearIn j) :
    albertMatrix (albertTarget.eval (aval j Y y) F) =
      linVal j (fun i => (Y i : ComplexMatrix3)) (albertMatrix y) F := by
  induction hF with
  | var => simp only [JTarget.eval, aval, linVal, ↓reduceIte]
  | add F G _ _ hF hG =>
    change albertMatrix (_ + _) = _
    rw [albertMatrix_add, hF, hG]; rfl
  | smul r F _ hF =>
    change albertMatrix (r • _) = _
    rw [albertMatrix_smul, hF]; rfl
  | mulLeft F G _ hG hF =>
    obtain ⟨Z, hZ1, hZ2⟩ := albert_free j Y y G hG
    change albertMatrix (jordanMul _ _) = _
    rw [← hZ2, albertMatrix_jordanMul, albertMatrix_complexHerm, hF,
      octonionMatrixMul_cmat_left, octonionMatrixMul_cmat_right, hZ1]
    simp only [linVal, linVal_free j _ _ G hG, lmul_zero_right, rmul_zero_left, add_zero]
    rw [add_comm]
  | mulRight F G hF _ hG =>
    obtain ⟨Z, hZ1, hZ2⟩ := albert_free j Y y F hF
    change albertMatrix (jordanMul _ _) = _
    rw [← hZ2, albertMatrix_jordanMul, albertMatrix_complexHerm, hG,
      octonionMatrixMul_cmat_left, octonionMatrixMul_cmat_right, hZ1]
    simp only [linVal, linVal_free j _ _ F hF, lmul_zero_right, rmul_zero_left, zero_add]

end AlbertSide

/-! ## Assembly -/

theorem complexHermToAlbert_one : complexHermToAlbert 1 = albertUnit := standardComplexWindow.unit

/-- In the standard window, a Hermitian matrix whose image is idempotent is idempotent. -/
theorem herm_idem_of_atom (X : Hermitian3) (h : IsAtom (complexHermToAlbert X)) :
    (X : ComplexMatrix3) * X = X := by
  let W := standardComplexWindow
  obtain ⟨Z, hZ⟩ := W.product_closed X X
  have h1 := W.preserves_product X X Z hZ
  simp only [W, standardComplexWindow_apply] at h1
  rw [h.1] at h1
  have h2 : Z = X := standardComplexWindow.injective (by simpa using h1)
  rw [h2] at hZ
  have h3 : (1 / 2 : ℝ) • ((X : ComplexMatrix3) * X + X * X) = X * X := by
    rw [← two_smul ℝ ((X : ComplexMatrix3) * X), smul_smul]
    norm_num
  rw [← h3]
  exact hZ.symm

theorem succAbove_surj' (j x : Test) (h : x ≠ j) : ∃ k : Fin 3, j.succAbove k = x :=
  succAbove_surj j x h

/-- Three atoms other than `p j`, moved into the standard complex window. -/
theorem three_in_standard (p : Test → Albert) (hp : ∀ i, IsAtom (p i)) (j : Test) :
    ∃ g : NativeAlbertAutomorphism, ∀ i, i ≠ j →
      standardComplexWindow.Contains (g.linearEquiv (p i)) := by
  obtain ⟨g, hg0, ⟨ξ₀, ξ₁, c, -, -, -, -, -, hg1⟩, hg2, -⟩ :=
    lemma_A_three (fun k => p (j.succAbove k)) (fun k => hp _)
  refine ⟨g, fun i hi => ?_⟩
  obtain ⟨k, rfl⟩ := succAbove_surj j i hi
  fin_cases k
  · change standardComplexWindow.Contains (g.linearEquiv (p (j.succAbove 0)))
    rw [hg0, standardComplexWindow_contains_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl
  · change standardComplexWindow.Contains (g.linearEquiv (p (j.succAbove 1)))
    have hk : ∀ k, (ξ₀ • diagAtom 0 + ξ₁ • diagAtom 1 + slotElem01 (octonionScalar c)).2 k =
        ξ₀ • (diagAtom 0).2 k + ξ₁ • (diagAtom 1).2 k + (slotElem01 (octonionScalar c)).2 k :=
      fun k => rfl
    have hd : ∀ i k, (diagAtom i).2 k = 0 := fun _ _ => rfl
    have s0 : (slotElem01 (octonionScalar c)).2 0 = octonionScalar c := rfl
    have s1 : (slotElem01 (octonionScalar c)).2 1 = 0 := rfl
    have s2 : (slotElem01 (octonionScalar c)).2 2 = 0 := rfl
    rw [hg1, standardComplexWindow_contains_iff, hk 0, hk 1, hk 2]
    simp only [hd, smul_zero, zero_add, s0, s1, s2]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl
  · exact hg2

/-- **Step 1 of lem:cer:h5:seven (proved).** For any four atoms, a Jordan expression of degree one
in `x_j` with special value zero has Albert value zero. -/
theorem passive_transfer (p : Test → Albert) (hp : ∀ i, IsAtom (p i)) (j : Test)
    (F : JPoly Test) (hF : F.LinearIn j) (h0 : specialEval F = 0) : albertEval p F = 0 := by
  classical
  obtain ⟨g, hg⟩ := three_in_standard p hp j
  have hX : ∀ i, ∃ X : Hermitian3, i ≠ j → complexHermToAlbert X = g.linearEquiv (p i) := by
    intro i
    by_cases hi : i = j
    · exact ⟨0, fun h => absurd hi h⟩
    · obtain ⟨X, hX⟩ := hg i hi
      exact ⟨X, fun _ => hX⟩
  choose X hXe using hX
  let Y : Test → Hermitian3 := fun i => (2 : ℝ) • X i - 1
  let y : Albert := g.linearEquiv (nativeSymmetry p j)
  have hval : ∀ i, aval j Y y i = g.linearEquiv (nativeSymmetry p i) := by
    intro i
    by_cases hi : i = j
    · rw [hi]; simp only [aval, ↓reduceIte, y]
    · simp only [aval, ite_eq_right hi, Y, nativeSymmetry, map_sub, map_smul, g.preserves_unit]
      rw [← hXe i hi, ← complexHermToAlbert_one]
      change standardComplexWindow.embedding _ = (2 : ℝ) • standardComplexWindow.embedding _ -
        standardComplexWindow.embedding _
      rw [map_sub, map_smul]
  have hsq : ∀ i, i ≠ j → (Y i : ComplexMatrix3) * Y i = 1 := by
    intro i hi
    have hat : IsAtom (complexHermToAlbert (X i)) := by
      rw [hXe i hi]; exact g.map_isAtom (hp i)
    have hid := herm_idem_of_atom (X i) hat
    change ((2 : ℝ) • (X i : ComplexMatrix3) - 1) * ((2 : ℝ) • (X i : ComplexMatrix3) - 1) = 1
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, hid, one_mul, mul_one, smul_smul]
    module
  have hlin := linVal_eq_zero j (fun i => (Y i : ComplexMatrix3)) (albertMatrix y) hsq F hF h0
  have hA := albert_linear j Y y F hF
  rw [hlin] at hA
  have hE : albertTarget.eval (aval j Y y) F = 0 := by
    rw [← albertCoordinates_albertMatrix (albertTarget.eval _ F), hA, albertCoordinates_zero]
  have hG : g.linearEquiv (albertEval p F) = 0 := by
    rw [albertEval, auto_eval]
    rw [show (fun x => g.linearEquiv (nativeSymmetry p x)) = aval j Y y from
      funext fun i => (hval i).symm]
    exact hE
  exact g.linearEquiv.injective (by rw [hG, map_zero])

end AlbertSequential.HorizonFive
