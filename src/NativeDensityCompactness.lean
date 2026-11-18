module

public import NativeAnalysis
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Tactic.Positivity

/-! Positive definiteness and compactness of the exact square-defined native
density set. No order-convexity or Jordan spectral theorem is used. -/

@[expose] public section
noncomputable section
namespace AlbertSequential.NativeAnalysis

theorem tracePairing_self_nonneg (x : Albert) : 0 ≤ tracePairing x x := by
  change 0 ≤ albertTrace (jordanMul x x)
  rw [trace_square_coordinates]
  exact add_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (mul_nonneg (by norm_num)
    (Finset.sum_nonneg fun i _ => add_nonneg Quaternion.normSq_nonneg Quaternion.normSq_nonneg))

theorem tracePairing_self_eq_zero (x : Albert) : tracePairing x x = 0 ↔ x = 0 := by
  constructor
  · intro h
    change albertTrace (jordanMul x x) = 0 at h
    rw [trace_square_coordinates] at h
    have hd : 0 ≤ ∑ i : Fin 3, (x.1 i)^2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have ho : 0 ≤ ∑ i : Fin 3, (Quaternion.normSq (x.2 i).1 + Quaternion.normSq (x.2 i).2) :=
      Finset.sum_nonneg fun i _ => add_nonneg Quaternion.normSq_nonneg Quaternion.normSq_nonneg
    have hdz : (∑ i : Fin 3, (x.1 i)^2) = 0 := by linarith
    have hoz : (∑ i : Fin 3, (Quaternion.normSq (x.2 i).1 + Quaternion.normSq (x.2 i).2)) = 0 := by linarith
    apply Prod.ext
    · funext i
      change x.1 i = 0
      have hi := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (x.1 i)).1 hdz i (Finset.mem_univ i)
      nlinarith [sq_nonneg (x.1 i)]
    · funext i
      have hi := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
        add_nonneg (Quaternion.normSq_nonneg (a := (x.2 i).1))
          (Quaternion.normSq_nonneg (a := (x.2 i).2))).1 hoz i (Finset.mem_univ i)
      apply Prod.ext
      · change (x.2 i).1 = 0
        apply Quaternion.normSq_eq_zero.mp
        have h1 := Quaternion.normSq_nonneg (a := (x.2 i).1)
        have h2 := Quaternion.normSq_nonneg (a := (x.2 i).2)
        linarith
      · change (x.2 i).2 = 0
        apply Quaternion.normSq_eq_zero.mp
        have h1 := Quaternion.normSq_nonneg (a := (x.2 i).1)
        have h2 := Quaternion.normSq_nonneg (a := (x.2 i).2)
        linarith
  · rintro rfl
    change albertTrace (jordanMul 0 0) = 0
    rw [jordanMul_zero_left]
    change (∑ _i : Fin 3, (0 : ℝ)) = 0
    simp only [Finset.sum_const_zero]

theorem tracePairing_positive_definite (x : Albert) :
    0 ≤ tracePairing x x ∧ (tracePairing x x = 0 ↔ x = 0) :=
  ⟨tracePairing_self_nonneg x, tracePairing_self_eq_zero x⟩

/-- The ellipsoid of square roots of trace-one native positive elements. -/
def nativeSquareSphere : Set Albert := {y | albertTrace (jordanMul y y) = 1}

theorem continuous_nativeSquare : Continuous (fun x : Albert => jordanMul x x) := by
  have hid : Continuous (id : Albert → Albert) := continuous_id
  have hc := continuous_jordanMul.comp (hid.prodMk hid)
  exact hc.congr (fun _ => rfl)

theorem isClosed_nativeSquareSphere : IsClosed nativeSquareSphere := by
  have ht : Continuous (fun x : Albert => albertTrace (jordanMul x x)) :=
    continuous_albertTrace.comp continuous_nativeSquare
  exact isClosed_eq ht (continuous_const : Continuous (fun _ : Albert => (1 : ℝ)))

private theorem squareSphere_coordinate_bounds {x : Albert} (hx : x ∈ nativeSquareSphere)
    (i : Fin 3) :
    |x.1 i| ≤ 1 ∧ ‖(x.2 i).1‖ ≤ 1 ∧ ‖(x.2 i).2‖ ≤ 1 := by
  change albertTrace (jordanMul x x) = 1 at hx
  rw [trace_square_coordinates] at hx
  have hd : 0 ≤ ∑ i : Fin 3, (x.1 i)^2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have ho : 0 ≤ ∑ i : Fin 3, (Quaternion.normSq (x.2 i).1 + Quaternion.normSq (x.2 i).2) :=
    Finset.sum_nonneg fun i _ => add_nonneg Quaternion.normSq_nonneg Quaternion.normSq_nonneg
  have hdi : (x.1 i)^2 ≤ ∑ j : Fin 3, (x.1 j)^2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hoi : Quaternion.normSq (x.2 i).1 + Quaternion.normSq (x.2 i).2 ≤
      ∑ j : Fin 3, (Quaternion.normSq (x.2 j).1 + Quaternion.normSq (x.2 j).2) :=
    Finset.single_le_sum (fun j _ => add_nonneg
      (Quaternion.normSq_nonneg (a := (x.2 j).1))
      (Quaternion.normSq_nonneg (a := (x.2 j).2)))
      (Finset.mem_univ i)
  have h1 := Quaternion.normSq_nonneg (a := (x.2 i).1)
  have h2 := Quaternion.normSq_nonneg (a := (x.2 i).2)
  refine ⟨?_, ?_, ?_⟩
  · have hs : (x.1 i)^2 ≤ 1 := by linarith
    rw [abs_le]
    constructor <;> nlinarith
  · have hn : ‖(x.2 i).1‖ * ‖(x.2 i).1‖ ≤ 1 := by
      rw [← Quaternion.normSq_eq_norm_mul_self]
      linarith
    nlinarith [norm_nonneg ((x.2 i).1)]
  · have hn : ‖(x.2 i).2‖ * ‖(x.2 i).2‖ ≤ 1 := by
      rw [← Quaternion.normSq_eq_norm_mul_self]
      linarith
    nlinarith [norm_nonneg ((x.2 i).2)]

theorem isCompact_nativeSquareSphere : IsCompact nativeSquareSphere := by
  let Kd : Set (Fin 3 → ℝ) := Set.pi Set.univ fun _ => Set.Icc (-1 : ℝ) 1
  let Ko : Set (Fin 3 → Octonion) := Set.pi Set.univ fun _ =>
    (Metric.closedBall (0 : Quaternion ℝ) 1) ×ˢ (Metric.closedBall (0 : Quaternion ℝ) 1)
  have hKd : IsCompact Kd := isCompact_univ_pi fun _ => isCompact_Icc
  have hKo : IsCompact Ko := isCompact_univ_pi fun _ =>
    (isCompact_closedBall (0 : Quaternion ℝ) 1).prod (isCompact_closedBall (0 : Quaternion ℝ) 1)
  exact (hKd.prod hKo).of_isClosed_subset isClosed_nativeSquareSphere (by
    intro x hx
    constructor
    · intro i _
      exact abs_le.mp (squareSphere_coordinate_bounds hx i).1
    · intro i _
      have h := squareSphere_coordinate_bounds hx i
      change dist (x.2 i).1 0 ≤ 1 ∧ dist (x.2 i).2 0 ≤ 1
      simpa only [dist_zero_right] using h.2)

theorem density_set_eq_square_image :
    {ρ : Albert | IsDensity ρ} = (fun y => jordanMul y y) '' nativeSquareSphere := by
  ext ρ
  constructor
  · rintro ⟨⟨y, rfl⟩, htr⟩
    exact ⟨y, htr, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, rfl⟩, hy⟩

theorem isCompact_density_set : IsCompact {ρ : Albert | IsDensity ρ} := by
  rw [density_set_eq_square_image]
  exact isCompact_nativeSquareSphere.image continuous_nativeSquare

end AlbertSequential.NativeAnalysis
