/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ScheduleMatchingSectorMatrices
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace AlbertSequential.MatchingModels

open scoped Quaternion

/-- The entry field of the exact Appendix C.5 projectors. -/
def horizonEntryField : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ {Complex.I, Complex.ofReal (Real.sqrt 2)}

private theorem horizonField_I : Complex.I ∈ horizonEntryField :=
  IntermediateField.mem_adjoin_of_mem ℚ
    (S := {Complex.I, Complex.ofReal (Real.sqrt 2)}) (by simp)

private theorem horizonField_sqrtTwo : Complex.ofReal (Real.sqrt 2) ∈ horizonEntryField :=
  IntermediateField.mem_adjoin_of_mem ℚ
    (S := {Complex.I, Complex.ofReal (Real.sqrt 2)}) (by simp)

private def realEntry (a : ℝ) : Prop := Complex.ofReal a ∈ horizonEntryField

private theorem realEntry_nat (a : ℕ) : realEntry a := by
  unfold realEntry
  rw [Complex.ofReal_natCast]
  exact horizonEntryField.natCast_mem a

private theorem realEntry_zero : realEntry 0 := by simpa using realEntry_nat 0

private theorem realEntry_one : realEntry 1 := by simpa using realEntry_nat 1

private theorem realEntry_add {a b : ℝ} (ha : realEntry a) (hb : realEntry b) : realEntry (a+b) := by
  unfold realEntry at *
  rw [Complex.ofReal_add]
  exact horizonEntryField.add_mem ha hb

private theorem realEntry_neg {a : ℝ} (ha : realEntry a) : realEntry (-a) := by
  unfold realEntry at *
  rw [Complex.ofReal_neg]
  exact horizonEntryField.neg_mem ha

private theorem realEntry_sub {a b : ℝ} (ha : realEntry a) (hb : realEntry b) : realEntry (a-b) := by
  simpa only [sub_eq_add_neg] using realEntry_add ha (realEntry_neg hb)

private theorem realEntry_mul {a b : ℝ} (ha : realEntry a) (hb : realEntry b) : realEntry (a*b) := by
  unfold realEntry at *
  rw [Complex.ofReal_mul]
  exact horizonEntryField.mul_mem ha hb

private theorem realEntry_inv {a : ℝ} (ha : realEntry a) : realEntry a⁻¹ := by
  unfold realEntry at *
  rw [Complex.ofReal_inv]
  exact horizonEntryField.inv_mem ha

private def quaternionEntries (q : Quaternion ℝ) : Prop :=
  realEntry q.re ∧ realEntry q.imI ∧ realEntry q.imJ ∧ realEntry q.imK

private theorem quaternionEntries_star {q : Quaternion ℝ} (h : quaternionEntries q) :
    quaternionEntries (star q) := by
  rcases h with ⟨h1, h2, h3, h4⟩
  simpa only [quaternionEntries, Quaternion.re_star, Quaternion.imI_star,
    Quaternion.imJ_star, Quaternion.imK_star] using
    And.intro h1 (And.intro (realEntry_neg h2) (And.intro (realEntry_neg h3) (realEntry_neg h4)))

private theorem quaternionEntries_mul {q r : Quaternion ℝ}
    (h : quaternionEntries q) (hr : quaternionEntries r) : quaternionEntries (q * r) := by
  rcases h with ⟨q0, q1, q2, q3⟩
  rcases hr with ⟨r0, r1, r2, r3⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Quaternion.re_mul]
    exact realEntry_sub
      (realEntry_sub (realEntry_sub (realEntry_mul q0 r0) (realEntry_mul q1 r1)) (realEntry_mul q2 r2))
      (realEntry_mul q3 r3)
  · rw [Quaternion.imI_mul]
    exact realEntry_sub
      (realEntry_add (realEntry_add (realEntry_mul q0 r1) (realEntry_mul q1 r0)) (realEntry_mul q2 r3))
      (realEntry_mul q3 r2)
  · rw [Quaternion.imJ_mul]
    exact realEntry_add
      (realEntry_add (realEntry_sub (realEntry_mul q0 r2) (realEntry_mul q1 r3)) (realEntry_mul q2 r0))
      (realEntry_mul q3 r1)
  · rw [Quaternion.imK_mul]
    exact realEntry_add
      (realEntry_sub (realEntry_add (realEntry_mul q0 r3) (realEntry_mul q1 r2)) (realEntry_mul q2 r1))
      (realEntry_mul q3 r0)

private theorem quaternionEntries_smul {a : ℝ} {q : Quaternion ℝ}
    (ha : realEntry a) (hq : quaternionEntries q) : quaternionEntries (a • q) :=
  ⟨realEntry_mul ha hq.1, realEntry_mul ha hq.2.1,
    realEntry_mul ha hq.2.2.1, realEntry_mul ha hq.2.2.2⟩

private theorem complexEntry {x y : ℝ} (hx : realEntry x) (hy : realEntry y) :
    (⟨x,y⟩ : ℂ) ∈ horizonEntryField := by
  have h : (⟨x,y⟩ : ℂ) = Complex.ofReal x + Complex.ofReal y * Complex.I := by
    apply Complex.ext <;> simp
  rw [h]
  exact horizonEntryField.add_mem hx (horizonEntryField.mul_mem hy horizonField_I)

private theorem horizonPsi_entry {q : Quaternion ℝ} (hq : quaternionEntries q) (i j : Fin 2) :
    horizonPsi q i j ∈ horizonEntryField := by
  fin_cases i <;> fin_cases j <;> rcases hq with ⟨h0,h1,h2,h3⟩
  · exact complexEntry h0 h1
  · exact complexEntry (realEntry_neg h2) (realEntry_neg h3)
  · exact complexEntry h2 (realEntry_neg h3)
  · exact complexEntry h0 (realEntry_neg h1)

private def rawQuaternionicColumns (b d : ℝ) : Fin 4 → Fin 3 → Quaternion ℝ :=
  ![![1,0,0], ![1,⟨b,0,0,0⟩,0], ![1,⟨0,1,0,0⟩,1],
    ![1,⟨0,0,1,0⟩,⟨0,d,d,0⟩]]

private def columnScale (b : ℝ) : Fin 4 → ℝ := ![1,horizonB b,horizonCD,horizonCD]

private theorem rawQuaternionicColumns_mem (b d : ℝ) (hb : realEntry b) (hd : realEntry d)
    (i : Fin 4) (j : Fin 3) : quaternionEntries (rawQuaternionicColumns b d i j) := by
  fin_cases i <;> fin_cases j <;>
    simp [rawQuaternionicColumns, quaternionEntries, realEntry_zero, realEntry_one, hb, hd]

private theorem columnScale_sq_mem (b : ℝ) (hb : realEntry b) (i : Fin 4) :
    realEntry (columnScale b i ^ 2) := by
  fin_cases i
  · change realEntry ((1 : ℝ) ^ 2)
    rw [one_pow]
    exact realEntry_one
  · change realEntry ((Real.sqrt (1 + b^2))⁻¹ ^ 2)
    rw [inv_pow, Real.sq_sqrt (by positivity : 0 ≤ 1 + b^2), pow_two]
    exact realEntry_inv (realEntry_add realEntry_one (realEntry_mul hb hb))
  · change realEntry ((Real.sqrt 3)⁻¹ ^ 2)
    rw [inv_pow, Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))]
    exact realEntry_inv (realEntry_nat 3)
  · change realEntry ((Real.sqrt 3)⁻¹ ^ 2)
    rw [inv_pow, Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))]
    exact realEntry_inv (realEntry_nat 3)

private theorem scaledQuaternionicColumns (b d : ℝ) (i : Fin 4) (j : Fin 3) :
    horizonQuaternionicColumns b d i j = columnScale b i • rawQuaternionicColumns b d i j := by
  fin_cases i <;> fin_cases j <;>
    (apply Quaternion.ext <;> simp [horizonQuaternionicColumns, columnScale, rawQuaternionicColumns,
      smul_eq_mul] <;> ring)

private theorem quaternionicColumnDyad_mem (b d : ℝ) (hb : realEntry b) (hd : realEntry d)
    (i : Fin 4) (j k : Fin 3) :
    quaternionEntries (horizonQuaternionicColumns b d i j * star (horizonQuaternionicColumns b d i k)) := by
  rw [scaledQuaternionicColumns, scaledQuaternionicColumns]
  rw [star_smul, star_trivial, smul_mul_assoc, mul_smul_comm, smul_smul, ← pow_two]
  exact quaternionEntries_smul (columnScale_sq_mem b hb i)
    (quaternionEntries_mul (rawQuaternionicColumns_mem b d hb hd i j)
      (quaternionEntries_star (rawQuaternionicColumns_mem b d hb hd i k)))

private theorem horizonSectorMatrix_entry (b d : ℝ) (hb : realEntry b) (hd : realEntry d)
    (i : Fin 4) (r s : Fin 6) : horizonSectorMatrix b d i r s ∈ horizonEntryField := by
  let u := horizonQuaternionicColumns b d i
  let ri := fin3ProdFin2Equiv6.symm r
  let si := fin3ProdFin2Equiv6.symm s
  change (horizonPsi (u ri.1) * (horizonPsi (u si.1)).conjTranspose) ri.2 si.2 ∈ horizonEntryField
  rw [← horizonPsi_star, ← horizonPsi_mul]
  exact horizonPsi_entry (quaternionicColumnDyad_mem b d hb hd i ri.1 si.1) _ _

private theorem horizonC12Projection_entry (b d : ℝ) (hb : realEntry b) (hd : realEntry d)
    (i : Fin 4) (r s : Fin 12) : horizonC12Projection b d i r s ∈ horizonEntryField := by
  change blockMat12 _ _ r s ∈ _
  rw [← equiv6Sum6.apply_symm_apply r, ← equiv6Sum6.apply_symm_apply s]
  cases equiv6Sum6.symm r <;> cases equiv6Sum6.symm s <;>
    simp only [blockMat12, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
  · exact horizonSectorMatrix_entry b d hb hd i _ _
  · exact horizonEntryField.zero_mem
  · exact horizonEntryField.zero_mem
  · exact horizonSectorMatrix_entry b (-d) hb (realEntry_neg hd) i _ _

/-- Every entry of the exact four M projections is in Q(√2,i). -/
theorem horizon_M_projection_entry (i : Fin 4) (r s : Fin 12) :
    horizonC12Projection (Real.sqrt 2) (Real.sqrt 2)⁻¹ i r s ∈ horizonEntryField :=
  horizonC12Projection_entry _ _ horizonField_sqrtTwo (realEntry_inv horizonField_sqrtTwo) i r s

/-- Every entry of the exact four S projections is in Q(√2,i). -/
theorem horizon_S_projection_entry (i : Fin 4) (r s : Fin 12) :
    horizonC12Projection 1 (Real.sqrt 2)⁻¹ i r s ∈ horizonEntryField :=
  horizonC12Projection_entry _ _ realEntry_one (realEntry_inv horizonField_sqrtTwo) i r s

end AlbertSequential.MatchingModels
