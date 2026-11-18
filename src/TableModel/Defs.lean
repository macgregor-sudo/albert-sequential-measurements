/- SPDX-License-Identifier: Apache-2.0 -/
module

public import TableModel.Amps
public import LengthSeven.LemmaA.Main

/-! # Table-model identity: the trace dictionary and the word-list bridge

* `toTraces τ`: the interface's `TraceData` (ω by middle letter, `om 1 = ω_B`, …) read as Lemma B's
  `Traces` (`t_1, t_2, t_3` double pairings); `t_1 = (ω_C + ω_D)/2 = dpair 2 3`, etc., so that
  Lemma B's `ω_r = t_1 + t_2 + t_3 - 2 t_r` is `om r` (`toTraces_ω1/2/3`).
* `toParams_toTraces`: Lemma B's comparison parameters at `toTraces τ` are `paramsN` at
  `n_x = o_Ax⁻¹` and `ω = om`.
* `word28_bridge`: Lemma B's `word28` (flattened `wordFI`) is the interface's `word28`.
-/

@[expose] public section

namespace AlbertSequential.LengthSeven.TableModel

open AlbertSequential AlbertSequential.LengthSeven

/-- The interface trace data as Lemma B's thirteen traces. -/
noncomputable def toTraces (τ : TraceData) : LemmaB.Traces where
  oAB := τ.o 0 1
  oAC := τ.o 0 2
  oAD := τ.o 0 3
  oBC := τ.o 1 2
  oCD := τ.o 2 3
  oBD := τ.o 1 3
  RABC := τ.R 0 1 2
  RABD := τ.R 0 1 3
  RACD := τ.R 0 2 3
  RBCD := τ.R 1 2 3
  t1 := τ.dpair 2 3
  t2 := τ.dpair 1 3
  t3 := τ.dpair 1 2

theorem toTraces_ω1 (τ : TraceData) : (toTraces τ).ω1 = τ.om 1 := by
  simp only [LemmaB.Traces.ω1, toTraces, TraceData.dpair]; ring

theorem toTraces_ω2 (τ : TraceData) : (toTraces τ).ω2 = τ.om 2 := by
  simp only [LemmaB.Traces.ω2, toTraces, TraceData.dpair]; ring

theorem toTraces_ω3 (τ : TraceData) : (toTraces τ).ω3 = τ.om 3 := by
  simp only [LemmaB.Traces.ω3, toTraces, TraceData.dpair]; ring

theorem toParams_toTraces (τ : TraceData) :
    (toTraces τ).toParams = LemmaB.TableModel.paramsN (τ.o 0 1)⁻¹ (τ.o 0 2)⁻¹ (τ.o 0 3)⁻¹
      (τ.o 1 2) (τ.o 1 3) (τ.o 2 3) (τ.R 0 1 2) (τ.R 0 1 3) (τ.R 0 2 3) (τ.R 1 2 3)
      (τ.om 1) (τ.om 2) (τ.om 3) := by
  rw [LemmaB.TableModel.toParams_eq, toTraces_ω1, toTraces_ω2, toTraces_ω3]
  rfl

/-- Lemma B's word list is the interface's (same order, chronological lists, `A = 0`). -/
theorem word28_bridge : ∀ k : Fin 28, LemmaB.word28 k = word28 k := by decide

end AlbertSequential.LengthSeven.TableModel
