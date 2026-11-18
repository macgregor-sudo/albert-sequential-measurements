/- SPDX-License-Identifier: Apache-2.0 -/
module

public import LengthSeven.Basic
public import ThreeAtomAndFourPoint
public import ComplexWindowDeterminantAndMax

/-! # Native binding of the trace data, and the overlap bounds

`nativeTraceData p` reads the thirteen traces of four Albert atoms through the
names of `ThirteenTracesAndAform`: `o = fpOverlap`, `R = fpTriangle`, and `om` by MIDDLE
letter through `fpOmega1/2/3` (`fpOmega_k` is the ω whose Jordan-triple middle
letter is `k`; never through the rotated `nativeCornerQ` indices).  The ω index
controls at `fixedS` (all `1/18`) and `maximizerConfig` (all `1/27`) are proved
below; they cannot detect a rotation of the index, so the asymmetric control is
in `LengthSeven.OmegaControl`.

`overlap_bounds_of_fourPoint_pos`: if `𝒜 > 0` then `0 < o_ij < 1` for all
distinct letters (the paper cites thm:fourpoint).  Proof: an
overlap `1` forces equal atoms and an overlap `0` forces orthogonal atoms
(`atom_tracePairing_eq_one_iff`, `atom_tracePairing_eq_zero_iff`); in
both cases the four atoms lie in a quaternionic window (`lemma_A_degenerate`),
where `𝒜 = 0` (`lemma_A_zero_of_quat`). -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.LengthSeven

open AlbertSequential

/-- The thirteen traces of four atoms, ω indexed by the middle letter. -/
def nativeTraceData (p : Fin 4 → Albert) : TraceData where
  o := fpOverlap p
  R := fpTriangle p
  om := ![0, fpOmega1 p, fpOmega2 p, fpOmega3 p]
  o_symm := fpOverlap_symm p
  R_symm12 := fpTriangle_swap12 p
  R_symm23 := fpTriangle_swap23 p

theorem nativeTraceData_o (p : Fin 4 → Albert) (i j : Letter) :
    (nativeTraceData p).o i j = tracePairing (p i) (p j) := rfl

theorem nativeTraceData_R (p : Fin 4 → Albert) (i j k : Letter) :
    (nativeTraceData p).R i j k = tracePairing (jordanMul (p i) (p j)) (p k) := rfl

theorem nativeTraceData_om (p : Fin 4 → Albert) :
    (nativeTraceData p).om 1 = fpOmega1 p ∧ (nativeTraceData p).om 2 = fpOmega2 p ∧
      (nativeTraceData p).om 3 = fpOmega3 p := ⟨rfl, rfl, rfl⟩

/-- ω control at `fixedS`: every `ω_y = 1/18`. -/
theorem nativeTraceData_om_fixedS (y : Letter) (hy : y ≠ 0) :
    (nativeTraceData fixedS).om y = 1 / 18 := by
  have h := (nativeCornerQ_eq_fpOmega fixedS).symm.trans nativeCornerQ_fixedS
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at h0 h1 h2
  have : y = 1 ∨ y = 2 ∨ y = 3 := by revert hy; revert y; decide
  rcases this with rfl | rfl | rfl
  · simpa [nativeTraceData] using h2
  · simpa [nativeTraceData] using h0
  · simpa [nativeTraceData] using h1

/-- ω control at `maximizerConfig` (configuration M): every `ω_y = 1/27`. -/
theorem nativeTraceData_om_maximizer (y : Letter) (hy : y ≠ 0) :
    (nativeTraceData maximizerConfig).om y = 1 / 27 := by
  obtain ⟨-, -, -, -, -, h1, h2, h3, -⟩ := maximizerConfig_traces 1
  have : y = 1 ∨ y = 2 ∨ y = 3 := by revert hy; revert y; decide
  rcases this with rfl | rfl | rfl
  · simpa [nativeTraceData] using h1
  · simpa [nativeTraceData] using h2
  · simpa [nativeTraceData] using h3

/-- `𝒜 > 0 ⇒ 0 < o_ij < 1` for ALL distinct letters (stronger than the pairs with `A`
that lem:cer:negative uses). -/
theorem overlap_bounds_of_fourPoint_pos (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (h : 0 < fourPointInvariant p) (i j : Fin 4) (hij : i ≠ j) :
    0 < tracePairing (p i) (p j) ∧ tracePairing (p i) (p j) < 1 := by
  obtain ⟨h0, h1⟩ := atom_tracePairing_bounds (p i) (p j) (hp i) (hp j)
  have hnd : ¬ (p i = p j ∨ jordanMul (p i) (p j) = 0) := by
    intro hdeg
    obtain ⟨Q, hQ⟩ := lemma_A_degenerate p hp ⟨i, j, hij, hdeg⟩
    have hz := lemma_A_zero_of_quat Q p hp hQ
    linarith
  constructor
  · rcases h0.lt_or_eq with h0 | h0
    · exact h0
    · exact absurd (Or.inr ((atom_tracePairing_eq_zero_iff _ _ (hp i) (hp j)).1 h0.symm)) hnd
  · rcases h1.lt_or_eq with h1 | h1
    · exact h1
    · exact absurd (Or.inl ((atom_tracePairing_eq_one_iff _ _ (hp i) (hp j)).1 h1)) hnd

/-- The same in trace-data form, at `A`: `0 < o_Ax < 1` for `x ≠ A`. -/
theorem nativeTraceData_overlap_bounds (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (h : 0 < fourPointInvariant p) (x : Letter) (hx : x ≠ 0) :
    0 < (nativeTraceData p).o 0 x ∧ (nativeTraceData p).o 0 x < 1 :=
  overlap_bounds_of_fourPoint_pos p hp h 0 x (Ne.symm hx)

end AlbertSequential.LengthSeven
