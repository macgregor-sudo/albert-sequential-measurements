/- SPDX-License-Identifier: Apache-2.0 -/
module
public import HurwitzPeirceAdapter
public import NativeMatrixTrace

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

open NativeAnalysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : UnitalJordanProduct E) (hfr : P.FormallyReal) (c : Fin 3 → E)
    {r s t : Fin 3} (C : P.PeirceTriangleCoordinates hfr c r s t)

local notation "A" => P.frameOffDiagonalSpace c r t
local notation "Mat" => Matrix (Fin 3) (Fin 3) A

private def albertCoordinatesMap : NativeOctonionMatrix →ₗ[ℝ] Albert where
  toFun := albertCoordinates
  map_add' X Y := by
    apply Prod.ext
    · funext i
      exact octonionReal_add (X i i) (Y i i)
    · funext i
      fin_cases i <;> rfl
  map_smul' a X := by
    apply Prod.ext
    · funext i
      exact octonionReal_smul a (X i i)
    · funext i
      fin_cases i <;> rfl

private theorem coordinates_matrix (x : Albert) : albertCoordinates (albertMatrix x) = x := by
  apply Prod.ext
  · funext i
    fin_cases i <;> apply octonionReal_scalar
  · funext i
    fin_cases i <;> rfl

structure NativeAlbertJordanIso where
  map : E ≃ₗ[ℝ] Albert
  unit : map P.unit = albertUnit
  product : ∀ x y, map (P.product x y) = jordanMul (map x) (map y)

theorem exists_nativeAlbertJordanIso_of_coefficients
    (f : P.PeirceCoefficientNativeOctonionIso hfr c C)
    (H : P.PeirceHermitianMatrixEquivalence hfr c C) :
    Nonempty (P.NativeAlbertJordanIso) := by
  let T : Mat →ₗ[ℝ] NativeOctonionMatrix := {
    toFun := fun X i j => f.map (X i j)
    map_add' := fun X Y => funext fun i => funext fun j => f.map.map_add (X i j) (Y i j)
    map_smul' := fun a X => funext fun i => funext fun j => f.map.map_smul a (X i j) }
  have hT : Function.Injective T := by
    intro X Y h
    apply Matrix.ext
    intro i j
    exact f.map.injective (congrFun (congrFun h i) j)
  have hm (X Y : Mat) : T (P.peirceCoefficientMatrixMul hfr c C X Y) =
      octonionMatrixMul (T X) (T Y) := by
    funext i j
    change f.map (P.peirceCoefficientMatrixMul hfr c C X Y i j) =
      ∑ k, octonionMul (f.map (X i k)) (f.map (Y k j))
    rw [P.peirceCoefficientMatrixMul_apply, map_sum]
    exact Finset.sum_congr rfl (fun k _ => f.mul (X i k) (Y k j))
  let M := T.comp H.map
  have hrec (x : E) : albertMatrix (albertCoordinates (M x)) = M x := by
    apply albertMatrix_reconstruct
    intro i j
    change octonionConj (f.map (H.map x i j)) = f.map (H.map x j i)
    rw [← f.conj, ← H.hermitian x i j]
  let g := albertCoordinatesMap.comp M
  have hg₁ : Function.Injective g := by
    intro x y h
    have hxy : M x = M y := (hrec x).symm.trans ((congrArg albertMatrix h).trans (hrec y))
    exact H.injective (hT hxy)
  have hg₂ : Function.Surjective g := by
    intro y
    let Y : Mat := fun i j => f.map.symm (albertMatrix y i j)
    have hY : P.PeirceCoefficientHermitian hfr c C Y := by
      intro i j
      apply f.map.injective
      change f.map (f.map.symm (albertMatrix y j i)) =
        f.map (P.peirceCoefficientConjugate hfr c C (f.map.symm (albertMatrix y i j)))
      rw [f.conj, f.map.apply_symm_apply, f.map.apply_symm_apply, albertMatrix_conjugate y i j]
    obtain ⟨x, hx⟩ := H.onto Y hY
    have hm₀ : M x = albertMatrix y := by
      funext i j
      change f.map (H.map x i j) = _
      rw [hx]
      exact f.map.apply_symm_apply (albertMatrix y i j)
    exact ⟨x, (congrArg albertCoordinates hm₀).trans (coordinates_matrix y)⟩
  let g₀ := LinearEquiv.ofBijective g ⟨hg₁, hg₂⟩
  refine ⟨{ map := g₀, unit := ?_, product := ?_ }⟩
  · change albertCoordinates (M P.unit) = albertUnit
    have hM : M P.unit = albertMatrix albertUnit := by
      funext i j
      change f.map (H.map P.unit i j) = _
      rw [H.unit]
      fin_cases i <;> fin_cases j <;>
        simp [albertMatrix, albertUnit, f.unit, octonionConj_zero]
    rw [hM, coordinates_matrix]
  · intro x y
    change albertCoordinates (M (P.product x y)) =
      jordanMul (albertCoordinates (M x)) (albertCoordinates (M y))
    have hM : M (P.product x y) =
        (1 / 2 : ℝ) • (octonionMatrixMul (M x) (M y) + octonionMatrixMul (M y) (M x)) := by
      change T (H.map (P.product x y)) = _
      rw [H.jordan, P.peirceCoefficientMatrixJordan_apply, map_smul, map_add, hm, hm]
      rfl
    rw [hM, jordanMul, hrec x, hrec y]
    exact albertCoordinatesMap.map_smul _ _

end AlbertSequential.UnitalJordanProduct
