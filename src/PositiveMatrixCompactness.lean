module

public import Interfaces.InstrumentsAndCompactness
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Bounded

/-! Elementary finite-dimensional PSD bounds, including singular matrices.
Only quadratic-form tests on one and two coordinate vectors are used; no
positive-definite replacement or spectral decomposition is assumed.
-/
@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder
namespace AlbertSequential
open Matrix

theorem isClosed_positive_matrices {n : Type*} [Fintype n] :
    IsClosed {M : Matrix n n ℂ | M.PosSemidef} := by
  classical
  have heq : {M : Matrix n n ℂ | M.PosSemidef} =
      {M : Matrix n n ℂ | M.conjTranspose = M} ∩
      ⋂ v : n → ℂ, {M : Matrix n n ℂ | 0 ≤ star v ⬝ᵥ (M *ᵥ v)} := by
    ext M
    simp [Matrix.posSemidef_iff_dotProduct_mulVec, Matrix.IsHermitian]
  rw [heq]
  refine (isClosed_eq ?_ continuous_id).inter (isClosed_iInter fun v => ?_)
  · fun_prop
  · apply isClosed_le continuous_const
    simp only [Matrix.mulVec, dotProduct]
    fun_prop

theorem positive_quadratic_two_coordinates {n : Type*} [Fintype n]
    {M : Matrix n n ℂ} (hM : M.PosSemidef) (i j : n) (z : ℂ) :
    0 ≤ M i i + M i j * z + star z * M j i + star z * M j j * z := by
  classical
  have h := hM.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j z)
  simpa [star_add, Matrix.mulVec_add, add_dotProduct, dotProduct_add,
    Matrix.mulVec_single, single_dotProduct, Pi.star_single, add_mul, mul_add,
    add_assoc, add_comm, add_left_comm, mul_comm, mul_left_comm, mul_assoc] using h

theorem positive_matrix_entry_re_bounds {n : Type*} [Fintype n]
    {M : Matrix n n ℂ} (hM : M.PosSemidef) (i j : n) :
    -(M i i).re - (M j j).re ≤ 2 * (M i j).re ∧
      2 * (M i j).re ≤ (M i i).re + (M j j).re := by
  have hs := congrArg Complex.re (hM.isHermitian.apply j i)
  have hp := (Complex.nonneg_iff.mp (positive_quadratic_two_coordinates hM i j 1)).1
  have hn := (Complex.nonneg_iff.mp (positive_quadratic_two_coordinates hM i j (-1))).1
  simp [RCLike.star_def] at hs hp hn
  constructor <;> linarith

theorem positive_matrix_entry_im_bounds {n : Type*} [Fintype n]
    {M : Matrix n n ℂ} (hM : M.PosSemidef) (i j : n) :
    -(M i i).re - (M j j).re ≤ 2 * (M i j).im ∧
      2 * (M i j).im ≤ (M i i).re + (M j j).re := by
  have hs := congrArg Complex.im (hM.isHermitian.apply j i)
  have hp := (Complex.nonneg_iff.mp (positive_quadratic_two_coordinates hM i j Complex.I)).1
  have hn := (Complex.nonneg_iff.mp (positive_quadratic_two_coordinates hM i j (-Complex.I))).1
  simp [RCLike.star_def, Complex.mul_re, Complex.mul_im] at hs hp hn
  constructor <;> linarith

theorem positive_matrix_diag_le_trace {n : Type*} [Fintype n]
    {M : Matrix n n ℂ} (hM : M.PosSemidef) (i : n) :
    (M i i).re ≤ (Matrix.trace M).re := by
  classical
  have hd : ∀ k, 0 ≤ (M k k).re := fun k =>
    (Complex.nonneg_iff.mp (hM.diag_nonneg (i := k))).1
  simpa [Matrix.trace] using
    (Finset.single_le_sum (fun k _ => hd k) (Finset.mem_univ i))

theorem positive_matrix_entry_norm_le_twice_trace_bound {n : Type*} [Fintype n]
    {M : Matrix n n ℂ} (hM : M.PosSemidef) {c : ℝ}
    (hc : (Matrix.trace M).re ≤ c) (i j : n) : ‖M i j‖ ≤ 2 * c := by
  have hi := (positive_matrix_diag_le_trace hM i).trans hc
  have hj := (positive_matrix_diag_le_trace hM j).trans hc
  obtain ⟨hrlo, hrhi⟩ := positive_matrix_entry_re_bounds hM i j
  obtain ⟨hilo, hihi⟩ := positive_matrix_entry_im_bounds hM i j
  have hr : |(M i j).re| ≤ c := abs_le.mpr ⟨by linarith, by linarith⟩
  have him : |(M i j).im| ≤ c := abs_le.mpr ⟨by linarith, by linarith⟩
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (by linarith)

theorem isCompact_positive_trace_le {n : Type*} [Fintype n]
    (c : ℝ) :
    IsCompact {M : Matrix n n ℂ | M.PosSemidef ∧ (Matrix.trace M).re ≤ c} := by
  classical
  have hclosed : IsClosed {M : Matrix n n ℂ | M.PosSemidef ∧ (Matrix.trace M).re ≤ c} := by
    have htrace : Continuous (fun M : Matrix n n ℂ => (Matrix.trace M).re) := by
      unfold Matrix.trace
      fun_prop
    exact isClosed_positive_matrices.inter (isClosed_le htrace continuous_const)
  have hbox : IsCompact {M : Matrix n n ℂ |
      ∀ i j, M i j ∈ Metric.closedBall (0 : ℂ) (2 * c)} :=
    isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => isCompact_closedBall _ _
  apply hbox.of_isClosed_subset hclosed
  intro M hM i j
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    positive_matrix_entry_norm_le_twice_trace_bound hM.1 hM.2 i j

theorem isCompact_matrix_density (d : ℕ) :
    IsCompact {ρ : ComplexMatrix d | IsMatrixDensity ρ} := by
  have hclosed : IsClosed {ρ : ComplexMatrix d | IsMatrixDensity ρ} := by
    refine isClosed_positive_matrices.inter (isClosed_eq ?_ continuous_const)
    unfold Matrix.trace
    fun_prop
  apply (isCompact_positive_trace_le (n := Fin d) 1).of_isClosed_subset hclosed
  intro ρ hρ
  refine ⟨hρ.1, ?_⟩
  rw [hρ.2]
  norm_num

end AlbertSequential
