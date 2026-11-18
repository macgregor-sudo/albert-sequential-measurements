module

public import CornerAlgebra
public import Interfaces.AlgebraicReconstruction

/-! The exact fixed-base tetrahedron identity of core appendix `sec:tet`.
Only the R1--R3 subset stated there is consumed; no ambient unit, positivity,
nonzero overlap or nonzero corner is assumed. -/

@[expose] public section
noncomputable section
namespace AlbertSequential

theorem tetrahedron_annihilates_base
    {A : Type*} [NonUnitalRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    (X : Fin 4 → A) (o : OverlapData) (R : TriangleData)
    (Q : Fin 3 → ℝ) (hR : CornerRelations X o R Q) :
    tetrahedronDiscriminant o R Q • X 0 = 0 := by
  let r₁ := R 0 1 2
  let r₂ := R 0 2 3
  let r₃ := R 0 3 1
  let ν₁ := o 0 1 * o 1 2 * o 2 0
  let ν₂ := o 0 2 * o 2 3 * o 3 0
  let ν₃ := o 0 3 * o 3 1 * o 1 0
  let q₁ := o 0 2 * Q 0
  let q₂ := o 0 3 * Q 1
  let q₃ := o 0 1 * Q 2
  let b₁ := r₁ ^ 2 - ν₁
  let b₂ := r₂ ^ 2 - ν₂
  let b₃ := r₃ ^ 2 - ν₃
  let b₁₂ := q₁ - r₁ * r₂
  let b₂₃ := q₂ - r₂ * r₃
  let b₁₃ := q₃ - r₃ * r₁
  let H := o 0 1 * o 0 2 * o 0 3 * R 1 2 3
  let σ := H - r₁ * r₂ * r₃ - r₁ * b₂₃ - r₂ * b₁₃ - r₃ * b₁₂
  let g₁ := X 0 * X 1 * X 2 * X 0
  let g₂ := X 0 * X 2 * X 3 * X 0
  let g₃ := X 0 * X 3 * X 1 * X 0
  let g₁' := X 0 * X 2 * X 1 * X 0
  let g₂' := X 0 * X 3 * X 2 * X 0
  let g₃' := X 0 * X 1 * X 3 * X 0
  let n₁ := g₁ - r₁ • X 0
  let n₂ := g₂ - r₂ • X 0
  let n₃ := g₃ - r₃ • X 0
  have hEE := hR.idempotent 0
  have hEg₁ : X 0 * g₁ = g₁ := cornerWord_left _ _ _ hEE
  have hg₁E : g₁ * X 0 = g₁ := cornerWord_right _ _ _ hEE
  have hEg₂ : X 0 * g₂ = g₂ := cornerWord_left _ _ _ hEE
  have hg₂E : g₂ * X 0 = g₂ := cornerWord_right _ _ _ hEE
  have hEg₃ : X 0 * g₃ = g₃ := cornerWord_left _ _ _ hEE
  have hg₃E : g₃ * X 0 = g₃ := cornerWord_right _ _ _ hEE
  have hEn₁ : X 0 * n₁ = n₁ := centeredCorner_left _ _ _ hEE hEg₁
  have hn₁E : n₁ * X 0 = n₁ := centeredCorner_right _ _ _ hEE hg₁E
  have hEn₂ : X 0 * n₂ = n₂ := centeredCorner_left _ _ _ hEE hEg₂
  have hn₂E : n₂ * X 0 = n₂ := centeredCorner_right _ _ _ hEE hg₂E
  have hEn₃ : X 0 * n₃ = n₃ := centeredCorner_left _ _ _ hEE hEg₃
  have hn₃E : n₃ * X 0 = n₃ := centeredCorner_right _ _ _ hEE hg₃E
  -- Reversal uses only the three base-0 R2 fields.
  have hreverse₁ : g₁ + g₁' = (2 * r₁) • X 0 := by
    calc
      g₁ + g₁' = X 0 * (X 1 * X 2 + X 2 * X 1) * X 0 := by
        dsimp only [g₁, g₁']; noncomm_ring
      _ = (2 * r₁) • X 0 := hR.triangle_012
  have hreverse₂ : g₂ + g₂' = (2 * r₂) • X 0 := by
    calc
      g₂ + g₂' = X 0 * (X 2 * X 3 + X 3 * X 2) * X 0 := by
        dsimp only [g₂, g₂']; noncomm_ring
      _ = (2 * r₂) • X 0 := hR.triangle_023
  have hreverse₃ : g₃ + g₃' = (2 * r₃) • X 0 := by
    calc
      g₃ + g₃' = X 0 * (X 3 * X 1 + X 1 * X 3) * X 0 := by
        dsimp only [g₃, g₃']; noncomm_ring
      _ = (2 * r₃) • X 0 := hR.triangle_031
  -- Lengths: three primitive R1 contractions for each pair.
  have hlength₁ : g₁ * g₁' = ν₁ • X 0 := by
    calc
      g₁ * g₁' = (o 2 0 * o 1 2 * o 0 1) • X 0 :=
        cornerWord_reverse_mul _ _ _ _ _ _ hEE
          (hR.pair 2 0 (by decide)) (hR.pair 1 2 (by decide))
          (hR.pair 0 1 (by decide))
      _ = ν₁ • X 0 := by dsimp only [ν₁]; congr 1; ring
  have hlength₂ : g₂ * g₂' = ν₂ • X 0 := by
    calc
      g₂ * g₂' = (o 3 0 * o 2 3 * o 0 2) • X 0 :=
        cornerWord_reverse_mul _ _ _ _ _ _ hEE
          (hR.pair 3 0 (by decide)) (hR.pair 2 3 (by decide))
          (hR.pair 0 2 (by decide))
      _ = ν₂ • X 0 := by dsimp only [ν₂]; congr 1; ring
  have hlength₃ : g₃ * g₃' = ν₃ • X 0 := by
    calc
      g₃ * g₃' = (o 1 0 * o 3 1 * o 0 3) • X 0 :=
        cornerWord_reverse_mul _ _ _ _ _ _ hEE
          (hR.pair 1 0 (by decide)) (hR.pair 3 1 (by decide))
          (hR.pair 0 3 (by decide))
      _ = ν₃ • X 0 := by dsimp only [ν₃]; congr 1; ring
  have hsquare₁ : n₁ * n₁ = b₁ • X 0 :=
    centeredCorner_square _ _ _ _ _ hEE hEg₁ hg₁E hreverse₁ hlength₁
  have hsquare₂ : n₂ * n₂ = b₂ • X 0 :=
    centeredCorner_square _ _ _ _ _ hEE hEg₂ hg₂E hreverse₂ hlength₂
  have hsquare₃ : n₃ * n₃ = b₃ • X 0 :=
    centeredCorner_square _ _ _ _ _ hEE hEg₃ hg₃E hreverse₃ hlength₃
  -- Mixed pairs use exactly the three R3 fields.
  have hmixed₁ : g₁ * g₂ + g₂' * g₁' = (2 * q₁) • X 0 := by
    calc
      g₁ * g₂ + g₂' * g₁' = (2 * o 2 0 * Q 0) • X 0 :=
        cornerWord_mixed _ _ _ _ _ _ hEE (hR.pair 2 0 (by decide)) hR.quadruple_123
      _ = (2 * q₁) • X 0 := by
        rw [hR.overlap_symmetric 2 0]; dsimp only [q₁]; congr 1; ring
  have hmixed₂ : g₂ * g₃ + g₃' * g₂' = (2 * q₂) • X 0 := by
    calc
      g₂ * g₃ + g₃' * g₂' = (2 * o 3 0 * Q 1) • X 0 :=
        cornerWord_mixed _ _ _ _ _ _ hEE (hR.pair 3 0 (by decide)) hR.quadruple_231
      _ = (2 * q₂) • X 0 := by
        rw [hR.overlap_symmetric 3 0]; dsimp only [q₂]; congr 1; ring
  have hmixed₃ : g₃ * g₁ + g₁' * g₃' = (2 * q₃) • X 0 := by
    calc
      g₃ * g₁ + g₁' * g₃' = (2 * o 1 0 * Q 2) • X 0 :=
        cornerWord_mixed _ _ _ _ _ _ hEE (hR.pair 1 0 (by decide)) hR.quadruple_312
      _ = (2 * q₃) • X 0 := by
        rw [hR.overlap_symmetric 1 0]; dsimp only [q₃]; congr 1; ring
  have hanti₁₂ : n₁ * n₂ + n₂ * n₁ = (2 * b₁₂) • X 0 :=
    centeredCorner_anticommutator _ _ _ _ _ _ _ _ hEE
      hEg₁ hg₁E hEg₂ hg₂E hreverse₁ hreverse₂ hmixed₁
  have hanti₂₃ : n₂ * n₃ + n₃ * n₂ = (2 * b₂₃) • X 0 :=
    centeredCorner_anticommutator _ _ _ _ _ _ _ _ hEE
      hEg₂ hg₂E hEg₃ hg₃E hreverse₂ hreverse₃ hmixed₂
  have hanti₁₃ : n₁ * n₃ + n₃ * n₁ = (2 * b₁₃) • X 0 := by
    rw [add_comm]
    exact centeredCorner_anticommutator _ _ _ _ _ _ _ _ hEE
      hEg₃ hg₃E hEg₁ hg₁E hreverse₃ hreverse₁ hmixed₃
  -- The far face is the sole use of R2 at base 1.
  have hfar : g₁ * g₂ * g₃ + g₃' * g₂' * g₁' = (2 * H) • X 0 := by
    calc
      g₁ * g₂ * g₃ + g₃' * g₂' * g₁' =
          (2 * o 2 0 * o 3 0 * o 0 1 * R 1 2 3) • X 0 :=
        cornerWord_far _ _ _ _ _ _ _ _ hEE
          (hR.pair 2 0 (by decide)) (hR.pair 3 0 (by decide))
          hR.triangle_123 (hR.pair 0 1 (by decide))
      _ = (2 * H) • X 0 := by
        rw [hR.overlap_symmetric 2 0, hR.overlap_symmetric 3 0]
        dsimp only [H]; congr 1; ring
  have hg₁ : g₁ = r₁ • X 0 + n₁ := by dsimp only [n₁]; module
  have hg₂ : g₂ = r₂ • X 0 + n₂ := by dsimp only [n₂]; module
  have hg₃ : g₃ = r₃ • X 0 + n₃ := by dsimp only [n₃]; module
  have hg₁' : g₁' = r₁ • X 0 - n₁ := by
    have h : g₁' = (2 * r₁) • X 0 - g₁ := by
      apply eq_sub_iff_add_eq.mpr; simpa only [add_comm] using hreverse₁
    rw [h]; dsimp only [n₁]; module
  have hg₂' : g₂' = r₂ • X 0 - n₂ := by
    have h : g₂' = (2 * r₂) • X 0 - g₂ := by
      apply eq_sub_iff_add_eq.mpr; simpa only [add_comm] using hreverse₂
    rw [h]; dsimp only [n₂]; module
  have hg₃' : g₃' = r₃ • X 0 - n₃ := by
    have h : g₃' = (2 * r₃) • X 0 - g₃ := by
      apply eq_sub_iff_add_eq.mpr; simpa only [add_comm] using hreverse₃
    rw [h]; dsimp only [n₃]; module
  have hexpand := shiftedCorner_triple_expansion (X 0) n₁ n₂ n₃ r₁ r₂ r₃
    hEE hEn₁ hn₁E hEn₂ hn₂E hEn₃ hn₃E
  rw [← hg₁, ← hg₂, ← hg₃, ← hg₁', ← hg₂', ← hg₃',
    hanti₂₃, hanti₁₃, hanti₁₂] at hexpand
  have hvolume : n₁ * n₂ * n₃ - n₃ * n₂ * n₁ = (2 * σ) • X 0 := by
    have hsum := hexpand.symm.trans hfar
    have hsub : n₁ * n₂ * n₃ - n₃ * n₂ * n₁ =
        (2 * H) • X 0 - ((2 * r₁ * r₂ * r₃) • X 0 +
          r₁ • ((2 * b₂₃) • X 0) + r₂ • ((2 * b₁₃) • X 0) +
          r₃ • ((2 * b₁₂) • X 0)) := by
      apply eq_sub_iff_add_eq.mpr
      exact (add_comm _ _).trans hsum
    rw [hsub]
    dsimp only [σ]
    module
  let Γ := n₁ * n₂ * n₃ - b₂₃ • n₁ + b₁₃ • n₂ - b₁₂ • n₃
  have hΓ : Γ = σ • X 0 := by
    calc
      Γ = (1 / 2 : ℝ) • (n₁ * n₂ * n₃ - n₃ * n₂ * n₁) :=
        localUnit_volume_eq_half_reverse _ _ _ _ _ _ _
          hEn₁ hn₂E hEn₃ hanti₁₂ hanti₁₃ hanti₂₃
      _ = σ • X 0 := by rw [hvolume]; module
  have hΓsquare : Γ * Γ =
      (-(b₁ * b₂ * b₃ + 2 * b₁₂ * b₂₃ * b₁₃ -
        b₁ * b₂₃ ^ 2 - b₂ * b₁₃ ^ 2 - b₃ * b₁₂ ^ 2)) • X 0 :=
    localUnit_volume_square _ _ _ _ _ _ _ _ _ _ hn₁E hEn₂ hn₂E hEn₃
      hsquare₁ hsquare₂ hsquare₃ hanti₁₂ hanti₁₃ hanti₂₃
  have hσsquare : Γ * Γ = (σ ^ 2) • X 0 := by
    rw [hΓ]
    simp only [smul_mul_assoc, mul_smul_comm, hEE, smul_smul]
    module
  have hequal := hΓsquare.symm.trans hσsquare
  change (-(b₁ * b₂ * b₃ + 2 * b₁₂ * b₂₃ * b₁₃ -
    b₁ * b₂₃ ^ 2 - b₂ * b₁₃ ^ 2 - b₃ * b₁₂ ^ 2) - σ ^ 2) • X 0 = 0
  rw [sub_smul, hequal, sub_self]

theorem tetrahedronEngine
    (A : Type*) [NonUnitalRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] : TetrahedronEngine A :=
  ⟨tetrahedron_annihilates_base⟩

end AlbertSequential
