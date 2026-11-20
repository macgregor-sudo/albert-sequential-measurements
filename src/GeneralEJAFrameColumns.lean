/- SPDX-License-Identifier: Apache-2.0 -/
module
public import GeneralEJAFrameCommonChart

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  (P : UnitalJordanProduct E) (hfr : P.FormallyReal) {n : ℕ} (c : Fin n → E)
  {r s t : Fin n} (C : P.PeirceTriangleCoordinates hfr c r s t)

local notation "W" => P.frameOffDiagonalSpace c
local notation "τ" => P.canonicalTraceOfFormallyReal hfr
local notation:70 x:70 " ⋆ " y:71 => (2 : ℝ) • P.product x y

structure PeirceFrameColumns where
  tailVector (j : Fin n) (_ : t < j) : W t j
  tail_trace (j : Fin n) (htj : t < j) :
    τ (P.product (tailVector j htj).val (tailVector j htj).val) = 2
  column (j : Fin n) (_ : r < j) : W r t ≃ₗ[ℝ] W r j
  at_second (hrs : r < s) (p : W r t) : (column s hrs p).val = (C.leftChart.symm p).val
  at_third (hrt : r < t) (p : W r t) : (column t hrt p).val = p.val
  at_tail (j : Fin n) (hrj : r < j) (htj : t < j) (p : W r t) :
    (column j hrj p).val = p.val ⋆ (tailVector j htj).val

theorem exists_peirceFrameColumns
    (hc : ∀ j, P.IsPrimitive (c j)) (hor : ∀ i j, i ≠ j → P.product (c i) (c j) = 0)
    (hunit : ∑ j, c j = P.unit) (hrs : r < s) (hst : s < t)
    (hfirst : ∀ j, j ≠ r → j ≠ s → j ≠ t → t < j)
    (hconnected : ∀ i j, i < j → W i j ≠ ⊥) :
    Nonempty (P.PeirceFrameColumns hfr c C) := by
  classical
  have htail (j : Fin n) (htj : t < j) :
      ∃ x : W t j, τ (P.product x.val x.val) = 2 :=
    P.exists_frameOffDiagonal_traceUnit hfr c (hconnected t j htj)
  choose v hv using htail
  have hcols (j : Fin n) (hrj : r < j) :
      ∃ F : W r t ≃ₗ[ℝ] W r j,
        (j = s → ∀ p, (F p).val = (C.leftChart.symm p).val) ∧
        (j = t → ∀ p, (F p).val = p.val) ∧
        (∀ htj : t < j, ∀ p, (F p).val = p.val ⋆ (v j htj).val) := by
    by_cases hjs : j = s
    · subst j
      refine ⟨C.leftChart.symm, fun _ _ => rfl, fun h => (ne_of_lt hst h).elim, ?_⟩
      exact fun hj => (not_lt_of_ge hst.le hj).elim
    by_cases hjt : j = t
    · subst j
      refine ⟨LinearEquiv.refl ℝ (W r t), fun h => (hjs h).elim, fun _ _ => rfl, ?_⟩
      exact fun hj => (lt_irrefl t hj).elim
    have htj := hfirst j (ne_of_gt hrj) hjs hjt
    have hrt := lt_trans hrs hst
    have hv0 : (v j htj).val ≠ 0 := by
      intro h
      have hnorm := hv j htj
      rw [h, P.product.map_zero, LinearMap.zero_apply, map_zero] at hnorm
      norm_num at hnorm
    obtain ⟨F, hF⟩ := P.exists_frameOffDiagonal_scaledRightEquiv c hfr hc hor hunit
      (ne_of_lt hrt) (ne_of_lt hrj) (ne_of_lt htj) (v j htj) hv0
    refine ⟨F, fun h => (hjs h).elim, fun h => (hjt h).elim, ?_⟩
    exact fun _ => hF
  choose F hF using hcols
  exact ⟨{
    tailVector := v
    tail_trace := hv
    column := F
    at_second := fun hrs => (hF s hrs).1 rfl
    at_third := fun hrt => (hF t hrt).2.1 rfl
    at_tail := fun j hrj => (hF j hrj).2.2 }⟩

structure PeirceFrameEdges (K : P.PeirceFrameColumns hfr c C) where
  chart (i j : Fin n) (_ : i < j) : W i j ≃ₗ[ℝ] W r t
  first (j : Fin n) (hrj : r < j) (x : W r j) : K.column j hrj (chart r j hrj x) = x
  later (i j : Fin n) (hri : r < i) (hij : i < j) (x : W i j) :
    (K.column j (lt_trans hri hij) (chart i j hij x)).val =
      (K.column i hri C.unit).val ⋆ x.val

theorem peirceTriangle_unit_ne_zero : C.unit ≠ 0 := by
  intro hu
  have h := C.unit_form
  rw [hu, map_zero] at h
  norm_num at h

theorem exists_peirceFrameEdges
    (K : P.PeirceFrameColumns hfr c C)
    (hc : ∀ j, P.IsPrimitive (c j)) (hor : ∀ i j, i ≠ j → P.product (c i) (c j) = 0)
    (hunit : ∑ j, c j = P.unit) (hrs : r < s) (hst : s < t)
    (hfirst : ∀ j, j ≠ r → j ≠ s → j ≠ t → t < j) :
    Nonempty (P.PeirceFrameEdges hfr c C K) := by
  classical
  have hrlt (i : Fin n) (hi : i ≠ r) : r < i := by
    by_cases his : i = s
    · exact his ▸ hrs
    by_cases hit : i = t
    · exact hit ▸ (lt_trans hrs hst)
    exact lt_trans (lt_trans hrs hst) (hfirst i hi his hit)
  have hz := P.peirceTriangle_unit_ne_zero hfr c C
  have htransports (i : Fin n) (hri : r < i) (j : Fin n) (hij : i < j) :
      ∃ G : W i j ≃ₗ[ℝ] W r j, ∀ x, (G x).val = (K.column i hri C.unit).val ⋆ x.val := by
    let u := K.column i hri C.unit
    have hu : u.val ≠ 0 := fun h => hz ((K.column i hri).injective
      ((Subtype.ext h : u = 0).trans (map_zero (K.column i hri)).symm))
    exact P.exists_frameOffDiagonal_scaledLeftEquiv c hfr hc hor hunit
      (ne_of_lt hri) (ne_of_lt (lt_trans hri hij)) (ne_of_lt hij) u hu
  choose G hG using htransports
  let e (i j : Fin n) (hij : i < j) : W i j ≃ₗ[ℝ] W r t :=
    if hir : i = r then (by subst i; exact (K.column j hij).symm)
    else (G i (hrlt i hir) j hij).trans (K.column j (lt_trans (hrlt i hir) hij)).symm
  refine ⟨{ chart := e, first := ?_, later := ?_ }⟩
  · intro j hrj x
    simp only [e, dite_eq_left rfl, LinearEquiv.apply_symm_apply]
  · intro i j hri hij x
    simp only [e, dite_eq_right (ne_of_gt hri), LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    exact hG i hri j hij x

end AlbertSequential.UnitalJordanProduct
