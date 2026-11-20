/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilityQuaternionicSymmetry
public import Mathlib.LinearAlgebra.Matrix.Permutation

/-! The native quaternionic atom chart in the verified matrix sampling model. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open scoped Matrix

/-- A native atom in the standard quaternionic window, on the first positive
chart, is the literal dyad of a unit quaternion vector with real first coordinate. -/
theorem standardQuaternionicAtom_eq_unitDyad_of_diag0_pos (p : Albert) (hp : IsAtom p)
    (hQ : p ∈ standardQuaternionicWindow.subalgebra.carrier) (h0 : 0 < p.1 0) :
    ∃ v : Fin 3 → Quaternion ℝ,
      (v 0).imI = 0 ∧ (v 0).imJ = 0 ∧ (v 0).imK = 0 ∧
      (∑ i, quatNormSq (v i)) = 1 ∧ p = quatDyad quatEmbed1 v 1 := by
  let s := Real.sqrt (p.1 0)
  let w : Fin 3 → Octonion :=
    ![octonionScalar s, (1/s) • octonionConj (p.2 0), (1/s) • octonionConj (p.2 1)]
  have hchart : p = octDyad w ∧ ∑ i, octNormSq (w i) = 1 := isAtom_eq_octDyad hp h0
  have hparts := (mem_standardQuaternionicWindow_iff p).mp hQ
  let v : Fin 3 → Quaternion ℝ := fun i => (w i).1
  have hreal : v 0 = ⟨s, 0, 0, 0⟩ := rfl
  have hquat (i : Fin 3) : quatEmbed1 (v i) = w i := by
    rw [quatEmbed1_apply]
    refine Prod.ext ?_ ?_
    · rfl
    fin_cases i
    · rfl
    · change 0 = (1 / s) • -(p.2 0).2
      rw [hparts.1, neg_zero, smul_zero]
    · change 0 = (1 / s) • -(p.2 1).2
      rw [hparts.2.1, neg_zero, smul_zero]
  have hnorm : ∑ i, quatNormSq (v i) = 1 := by
    rw [← hchart.2]
    apply Finset.sum_congr rfl
    intro i _
    rw [← hquat i]
    exact (assocCD_H.embed_normSq (v i)).symm
  refine ⟨v, ?_, ?_, ?_, hnorm, ?_⟩
  · simp [hreal]
  · simp [hreal]
  · simp [hreal]
  · rw [hchart.1, ← octDyad_eq_quatDyad quatEmbed1 quatEmbed1_isQuatEmbedding]
    congr 1
    exact (funext hquat).symm

/-- The same native chart appears in the normalized quaternionic matrix model. -/
theorem standardQuaternionicAtom_eq_normalizedMatrixDyad_of_diag0_pos
    (p : Albert) (hp : IsAtom p) (hQ : p ∈ standardQuaternionicWindow.subalgebra.carrier)
    (h0 : 0 < p.1 0) :
    ∃ v : Fin 3 → Quaternion ℝ,
      (v 0).imI = 0 ∧ (v 0).imJ = 0 ∧ (v 0).imK = 0 ∧ (∑ i, quatNormSq (v i)) = 1 ∧
      p = quatMatrixToAlbert quatEmbed1 (normalizedQuaternionicMatrixDyad v) := by
  obtain ⟨v, hI, hJ, hK, hn, h⟩ := standardQuaternionicAtom_eq_unitDyad_of_diag0_pos p hp hQ h0
  refine ⟨v, hI, hJ, hK, hn, ?_⟩
  rw [quatMatrixToAlbert_normalizedQuaternionicMatrixDyad, ← h, normalizeAlbert, hp.2,
    inv_one, one_smul]

/-- Quaternionic Householder reflection taking the first coordinate vector to any
unit vector with real first coordinate. -/
theorem quaternionicUnitaryOrbit_of_real_first (v : Fin 3 → Quaternion ℝ)
    (hI : (v 0).imI = 0) (hJ : (v 0).imJ = 0) (hK : (v 0).imK = 0)
    (hv : (∑ i, quatNormSq (v i)) = 1) :
    ∃ U : unitary QuatMatrix3, U.val *ᵥ Pi.single (0 : Fin 3) 1 = v := by
  let e : Fin 3 → Quaternion ℝ := Pi.single 0 1
  by_cases he : v = e
  · exact ⟨1, (Matrix.one_mulVec e).trans he.symm⟩
  let w := e - v
  let a := (v 0).re
  let n := ∑ i, quatNormSq (w i)
  let P := Matrix.vecMulVec w (star w)
  have hw0 : w 0 = (1 - a) • (1 : Quaternion ℝ) := by
    apply Quaternion.ext <;> simp [w, e, a, hI, hJ, hK]
  have hw1 : w 1 = -v 1 := by simp [w, e]
  have hw2 : w 2 = -v 2 := by simp [w, e]
  have hn : n = 2 * (1 - a) := by
    have hV0 : quatNormSq (v 0) = a ^ 2 := by simp [quatNormSq, a, hI, hJ, hK]
    rw [Fin.sum_univ_three, hV0] at hv
    simp [n, Fin.sum_univ_three, hw0, hw1, hw2, quatNormSq] at hv ⊢
    nlinarith
  have hnz : n ≠ 0 := by
    have hN : ∀ q : Quaternion ℝ, quatNormSq q = Quaternion.normSq q :=
      fun q => (Quaternion.normSq_def' (a := q)).symm
    intro hz
    apply he
    symm
    apply sub_eq_zero.mp
    change w = 0
    funext i
    refine Quaternion.normSq_eq_zero.mp ?_
    have hsum : ∑ j, Quaternion.normSq (w j) = 0 := by
      simpa only [n, hN] using hz
    have h := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Quaternion.normSq_nonneg (a := w j))).mp hsum
    exact h i (Finset.mem_univ i)
  have hDot : star w ⬝ᵥ w = n • (1 : Quaternion ℝ) := by
    unfold dotProduct n
    simp only [Pi.star_apply, assocCD_H.star_mul_self, ← Finset.sum_smul]
    rfl
  have hP2 : P * P = n • P := by
    unfold P
    rw [Matrix.vecMulVec_mul_vecMulVec, hDot]
    apply Matrix.ext
    intro i j
    simp
  have hPs : star P = P := by
    apply Matrix.ext
    intro i j
    simp [P, Matrix.star_apply, Matrix.vecMulVec_apply, star_mul]
  let c := 2 / n
  let R : QuatMatrix3 := 1 - c • P
  have hc : c * (c * n) = c + c := by
    dsimp [c]
    field_simp
    ring
  have hRs : star R = R := by simp [R, hPs]
  have hR : R * R = 1 := by
    unfold R
    rw [sub_mul, mul_sub, mul_sub]
    simp only [one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, hP2, smul_smul, hc, add_smul]
    abel
  have hDep : star w ⬝ᵥ e = (1 - a) • (1 : Quaternion ℝ) := by
    simp [dotProduct, e, Pi.single_apply, hw0]
  have hPe : P *ᵥ e = (1 - a) • w := by
    unfold P
    rw [Matrix.vecMulVec_mulVec, hDep]
    funext i
    change w i * ((1-a) • (1 : Quaternion ℝ)) = (1-a) • w i
    rw [mul_smul_comm, mul_one]
  have hcoef : c * (1 - a) = 1 := by
    unfold c
    rw [div_mul_eq_mul_div, ← hn, div_self hnz]
  refine ⟨⟨R, ?_⟩, ?_⟩
  · rw [Unitary.mem_iff]
    exact ⟨by rw [hRs, hR], by rw [hRs, hR]⟩
  · change R *ᵥ e = v
    unfold R
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hPe,
      smul_smul, hcoef, one_smul]
    simp [w]

theorem normalizedQuaternionicMatrixDyad_hermitian (v : Fin 3 → Quaternion ℝ) :
    IsSelfAdjoint (normalizedQuaternionicMatrixDyad v) := by
  change star (normalizedQuaternionicMatrixDyad v) = normalizedQuaternionicMatrixDyad v
  apply Matrix.ext
  intro i j
  simp [normalizedQuaternionicMatrixDyad, Matrix.star_apply, Matrix.vecMulVec_apply, star_mul]

set_option maxHeartbeats 700000 in
/-- Every native atom in the standard quaternionic window lies in the
actual quaternionic unitary conjugation orbit of the first coordinate dyad. -/
theorem standardQuaternionicAtom_in_unitaryOrbit (p : Albert) (hp : IsAtom p)
    (hQ : p ∈ standardQuaternionicWindow.subalgebra.carrier) :
    ∃ U : unitary QuatMatrix3,
      p = quatMatrixToAlbert quatEmbed1 (U.val *
        normalizedQuaternionicMatrixDyad (Pi.single (0 : Fin 3) 1) * star U.val) := by
  have hi : ∃ i : Fin 3, 0 < p.1 i := by
    by_contra! h
    have ht := hp.2
    change ∑ i, p.1 i = 1 at ht
    rw [Fin.sum_univ_three] at ht
    linarith [h 0, h 1, h 2]
  obtain ⟨i, hi⟩ := hi
  let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 i
  let S : QuatMatrix3 := σ.permMatrix (Quaternion ℝ)
  have hss : star S * S = 1 := by
    change (σ.permMatrix (Quaternion ℝ)).conjTranspose * σ.permMatrix (Quaternion ℝ) = 1
    rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul, mul_inv_cancel,
      Matrix.permMatrix_one]
  have hss' : S * star S = 1 := by
    change σ.permMatrix (Quaternion ℝ) * (σ.permMatrix (Quaternion ℝ)).conjTranspose = 1
    rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul, inv_mul_cancel,
      Matrix.permMatrix_one]
  let Sunit : unitary QuatMatrix3 := ⟨S, Unitary.mem_iff.mpr ⟨hss, hss'⟩⟩
  have hpQ : p ∈ (H3Subalgebra .H).carrier := H3Subalgebra_H_eq_standardQuaternionicWindow ▸ hQ
  let x : (H3Subalgebra .H).carrier := ⟨p, hpQ⟩
  let ψ : JordanSubalgebraIso (H3Subalgebra .H) (H3Subalgebra .H) :=
    assocCD_unitaryIso assocCD_H S hss hss'
  let E : QuatHermitian3 ≃ₗ[ℝ] (H3Subalgebra .H).carrier := assocHermEquiv assocCD_H
  let M := E.symm x
  have hM : quatMatrixToAlbert quatEmbed1 M.val = p :=
    congrArg Subtype.val (E.apply_symm_apply x)
  let xp := ψ.toLinearEquiv x
  have hxp : xp.val = quatMatrixToAlbert quatEmbed1 (star S * M.val * S) := rfl
  have hxpAtom : IsAtom xp.val := iso_maps_atom (k := .H) ψ x hp
  have hxpQ : xp.val ∈ standardQuaternionicWindow.subalgebra.carrier :=
    H3Subalgebra_H_eq_standardQuaternionicWindow ▸ xp.property
  have h0 : 0 < xp.val.1 0 := by
    rw [hxp]
    change 0 < ((star S * M.val * S) 0 0).re
    change 0 < (((σ.permMatrix (Quaternion ℝ)).conjTranspose * M.val *
      σ.permMatrix (Quaternion ℝ)) 0 0).re
    rw [Matrix.conjTranspose_permMatrix, PEquiv.toMatrix_toPEquiv_mul,
      PEquiv.mul_toMatrix_toPEquiv]
    change 0 < (M.val (σ.symm 0) (σ.symm 0)).re
    have hσ : σ.symm 0 = i := by simp [σ]
    rw [hσ]
    rw [← hM] at hi
    exact hi
  obtain ⟨v, hI, hJ, hK, hv, hvx⟩ :=
    standardQuaternionicAtom_eq_normalizedMatrixDyad_of_diag0_pos xp.val hxpAtom hxpQ h0
  obtain ⟨U, hU⟩ := quaternionicUnitaryOrbit_of_real_first v hI hJ hK hv
  have hN : star S * M.val * S = normalizedQuaternionicMatrixDyad v := by
    let N : QuatHermitian3 := ⟨normalizedQuaternionicMatrixDyad v, normalizedQuaternionicMatrixDyad_hermitian v⟩
    have hEN : E N = xp := Subtype.ext hvx.symm
    let B : QuatHermitian3 := ⟨star S * M.val * S, by
      rw [selfAdjoint.mem_iff, star_mul, star_mul, star_star, M.property, Matrix.mul_assoc]⟩
    have hEB : E B = xp := Subtype.ext hxp.symm
    exact congrArg Subtype.val (E.injective (hEB.trans hEN.symm))
  rw [← hU, normalizedQuaternionicMatrixDyad_mulVec] at hN
  use Sunit * U
  have hrecover : M.val = (S * U.val) * normalizedQuaternionicMatrixDyad (Pi.single (0 : Fin 3) 1) *
      star (S * U.val) := by
    have h := congrArg (fun N : QuatMatrix3 => S * N * star S) hN
    simpa only [star_mul, Matrix.mul_assoc, ← Matrix.mul_assoc S (star S), hss', Matrix.one_mul,
      ← Matrix.mul_assoc M.val S (star S), Matrix.mul_one] using h
  change p = quatMatrixToAlbert quatEmbed1 ((S * U.val) * _ * star (S * U.val))
  rw [← hrecover, hM]

end AlbertSequential.WindowProbability
