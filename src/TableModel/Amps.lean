/- SPDX-License-Identifier: Apache-2.0
   Machine-generated file. -/
module

public import LemmaB.Conclusion

/-! # Table-model identity, part 1: the 28 amplitudes as explicit coordinate vectors

For each of the 28 words `w` of eq:cer:W28 (time order), `amp p w` (Lemma B's
`T_{w_k w_{k-1}} ⋯ T_{w_1 A} 1`) is an explicit vector of polynomials in the 13 gauge
parameters, over any field.  Also: the model value of two path vectors in terms of their
amplitudes (`Q_uhat`), and `paramsN`, Lemma B's `Traces.toParams` with `m_x` a free variable. -/

@[expose] public section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace LemmaB.TableModel

variable {K : Type*} [Field K]

/-- `Traces.toParams` with `m_x = n_x` free and `ω_1, ω_2, ω_3 = wB, wC, wD` (same formulas). -/
def paramsN (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) : Params K :=
  let m := nB * nC * nD
  let c1 := RABC * nB * nC
  let c2 := RACD * nC * nD
  let c3 := RABD * nD * nB
  let M12 := c1 * c2 - wC * m
  let M23 := c2 * c3 - wD * m
  let M13 := c1 * c3 - wB * m
  { mB := nB, mC := nC, mD := nD, c1 := c1, c2 := c2, c3 := c3,
    M11 := oBC * nB * nC - c1 ^ 2, M22 := oCD * nC * nD - c2 ^ 2,
    M33 := oBD * nD * nB - c3 ^ 2, M12 := M12, M13 := M13, M23 := M23,
    b := RBCD * m - (c1 * c2 * c3 - c1 * M23 - c2 * M13 - c3 * M12) }

/-- `Traces.toParams` is `paramsN` at `n_x = o_Ax⁻¹`. -/
theorem toParams_eq (τd : Traces) :
    τd.toParams = paramsN τd.oAB⁻¹ τd.oAC⁻¹ τd.oAD⁻¹ τd.oBC τd.oBD τd.oCD τd.RABC τd.RABD
      τd.RACD τd.RBCD τd.ω1 τd.ω2 τd.ω3 := rfl

/-- The form on two single-frame vectors. -/
theorem Q_single (p : Params K) (f f' : Fin 4) (a b : C8 K) :
    Q p (Pi.single f a) (Pi.single f' b) = W p a (T p f f' b) := by
  have hW0 : ∀ v : C8 K, W p 0 v = 0 := fun v => by simp [W]
  have hW0' : ∀ v : C8 K, W p v 0 = 0 := fun v => by simp [W]
  unfold Q
  rw [Finset.sum_eq_single f]
  · rw [Finset.sum_eq_single f']
    · simp
    · intro y _ hy; rw [Pi.single_eq_of_ne hy, T_zero, hW0']
    · simp
  · intro x _ hx
    rw [Pi.single_eq_of_ne hx]
    exact Finset.sum_eq_zero fun y _ => hW0 _
  · simp

/-- The model value of two path vectors `û(w), û(w')` through their amplitudes. -/
theorem Q_uhat (p : Params K) (w w' : List (Fin 4)) :
    Q p (uhat p w) (uhat p w') = ((w.map (mOf p)).prod)⁻¹ * ((w'.map (mOf p)).prod)⁻¹ *
      W p (amp p w) (T p (frameOf p w) (frameOf p w') (amp p w')) := by
  rw [uhat_eq, uhat_eq, Q_smul_left, Q_smul_right, utilde_eq, utilde_eq, Q_single]
  ring

/-- Amplitude of `word28 0 = []` (frame A). -/
def ampV0 (p : Params K) : C8 K :=
  ![1,
    0,
    0,
    0,
    0,
    0,
    0,
    0]

theorem amp0 (p : Params K) : amp p [] = ampV0 p := by
  funext c; fin_cases c <;> simp [ampV0, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem frame0 (p : Params K) : frameOf p [] = 0 := rfl

/-- Amplitude of `word28 1 = [2, 1, 0]` (frame A). -/
def ampV1 (p : Params K) : C8 K :=
  ![p.c1,
    1,
    0,
    0,
    0,
    0,
    0,
    0]

theorem amp1 (p : Params K) : amp p [2, 1, 0] = ampV1 p := by
  funext c; fin_cases c <;> simp [ampV1, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem frame1 (p : Params K) : frameOf p [2, 1, 0] = 0 := rfl

/-- Amplitude of `word28 2 = [3, 2, 0]` (frame A). -/
def ampV2 (p : Params K) : C8 K :=
  ![p.c2,
    0,
    1,
    0,
    0,
    0,
    0,
    0]

theorem amp2 (p : Params K) : amp p [3, 2, 0] = ampV2 p := by
  funext c; fin_cases c <;> simp [ampV2, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem frame2 (p : Params K) : frameOf p [3, 2, 0] = 0 := rfl

/-- Amplitude of `word28 3 = [1, 3, 0]` (frame A). -/
def ampV3 (p : Params K) : C8 K :=
  ![p.c3,
    0,
    0,
    1,
    0,
    0,
    0,
    0]

theorem amp3 (p : Params K) : amp p [1, 3, 0] = ampV3 p := by
  funext c; fin_cases c <;> simp [ampV3, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem frame3 (p : Params K) : frameOf p [1, 3, 0] = 0 := rfl

/-- Amplitude of `word28 4 = [3, 2, 1, 0]` (frame A). -/
def ampV4 (p : Params K) : C8 K :=
  ![p.c1 * p.c2 - p.M12,
    p.c2,
    p.c1,
    0,
    0,
    0,
    1,
    0]

theorem amp4 (p : Params K) : amp p [3, 2, 1, 0] = ampV4 p := by
  funext c; fin_cases c <;> simp [ampV4, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem frame4 (p : Params K) : frameOf p [3, 2, 1, 0] = 0 := rfl

/-- Amplitude of `word28 5 = [2, 3, 1, 0]` (frame A). -/
def ampV5 (p : Params K) : C8 K :=
  ![p.c2 * p.c3 - p.M23,
    0,
    -p.c3,
    -p.c2,
    -1,
    0,
    0,
    0]

theorem amp5 (p : Params K) : amp p [2, 3, 1, 0] = ampV5 p := by
  funext c; fin_cases c <;> simp [ampV5, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem frame5 (p : Params K) : frameOf p [2, 3, 1, 0] = 0 := rfl

/-- Amplitude of `word28 6 = [3, 1, 2, 0]` (frame A). -/
def ampV6 (p : Params K) : C8 K :=
  ![p.c1 * p.c3 - p.M13,
    -p.c3,
    0,
    -p.c1,
    0,
    -1,
    0,
    0]

theorem amp6 (p : Params K) : amp p [3, 1, 2, 0] = ampV6 p := by
  funext c; fin_cases c <;> simp [ampV6, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem frame6 (p : Params K) : frameOf p [3, 1, 2, 0] = 0 := rfl

/-- Amplitude of `word28 7 = [1]` (frame B). -/
def ampV7 (p : Params K) : C8 K :=
  ![1,
    0,
    0,
    0,
    0,
    0,
    0,
    0]

theorem amp7 (p : Params K) : amp p [1] = ampV7 p := by
  funext c; fin_cases c <;> simp [ampV7, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem frame7 (p : Params K) : frameOf p [1] = 1 := rfl

/-- Amplitude of `word28 8 = [2, 1]` (frame B). -/
def ampV8 (p : Params K) : C8 K :=
  ![p.c1,
    1,
    0,
    0,
    0,
    0,
    0,
    0]

theorem amp8 (p : Params K) : amp p [2, 1] = ampV8 p := by
  funext c; fin_cases c <;> simp [ampV8, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem frame8 (p : Params K) : frameOf p [2, 1] = 1 := rfl

/-- Amplitude of `word28 9 = [3, 1]` (frame B). -/
def ampV9 (p : Params K) : C8 K :=
  ![p.c3,
    0,
    0,
    -1,
    0,
    0,
    0,
    0]

theorem amp9 (p : Params K) : amp p [3, 1] = ampV9 p := by
  funext c; fin_cases c <;> simp [ampV9, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem frame9 (p : Params K) : frameOf p [3, 1] = 1 := rfl

/-- Amplitude of `word28 10 = [2, 3, 0, 1]` (frame B). -/
def ampV10 (p : Params K) : C8 K :=
  ![p.c2,
    0,
    -1,
    0,
    0,
    0,
    0,
    0]

theorem amp10 (p : Params K) : amp p [2, 3, 0, 1] = ampV10 p := by
  funext c; fin_cases c <;> simp [ampV10, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem frame10 (p : Params K) : frameOf p [2, 3, 0, 1] = 1 := rfl

/-- Amplitude of `word28 11 = [3, 2, 1]` (frame B). -/
def ampV11 (p : Params K) : C8 K :=
  ![p.c1 * p.c2 - p.M12,
    p.c2,
    p.c1,
    0,
    0,
    0,
    1,
    0]

theorem amp11 (p : Params K) : amp p [3, 2, 1] = ampV11 p := by
  funext c; fin_cases c <;> simp [ampV11, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem frame11 (p : Params K) : frameOf p [3, 2, 1] = 1 := rfl

/-- Amplitude of `word28 12 = [2, 3, 1]` (frame B). -/
def ampV12 (p : Params K) : C8 K :=
  ![p.c2 * p.c3 - p.M23,
    0,
    -p.c3,
    -p.c2,
    -1,
    0,
    0,
    0]

theorem amp12 (p : Params K) : amp p [2, 3, 1] = ampV12 p := by
  funext c; fin_cases c <;> simp [ampV12, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem frame12 (p : Params K) : frameOf p [2, 3, 1] = 1 := rfl

/-- Amplitude of `word28 13 = [1, 3, 2, 1]` (frame B). -/
def ampV13 (p : Params K) : C8 K :=
  ![p.c1 * p.c2 * p.c3 - p.c1 * p.M23 - p.c2 * p.M13 - p.c3 * p.M12 + p.b,
    p.c2 * p.c3 - p.M23,
    p.c1 * p.c3 + p.M13,
    p.c1 * p.c2 - p.M12,
    p.c1,
    -p.c2,
    p.c3,
    1]

theorem amp13 (p : Params K) : amp p [1, 3, 2, 1] = ampV13 p := by
  funext c; fin_cases c <;> simp [ampV13, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem frame13 (p : Params K) : frameOf p [1, 3, 2, 1] = 1 := rfl

/-- Amplitude of `word28 14 = [2]` (frame C). -/
def ampV14 (p : Params K) : C8 K :=
  ![1,
    0,
    0,
    0,
    0,
    0,
    0,
    0]

theorem amp14 (p : Params K) : amp p [2] = ampV14 p := by
  funext c; fin_cases c <;> simp [ampV14, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem frame14 (p : Params K) : frameOf p [2] = 2 := rfl

/-- Amplitude of `word28 15 = [3, 2]` (frame C). -/
def ampV15 (p : Params K) : C8 K :=
  ![p.c2,
    0,
    1,
    0,
    0,
    0,
    0,
    0]

theorem amp15 (p : Params K) : amp p [3, 2] = ampV15 p := by
  funext c; fin_cases c <;> simp [ampV15, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem frame15 (p : Params K) : frameOf p [3, 2] = 2 := rfl

/-- Amplitude of `word28 16 = [1, 2]` (frame C). -/
def ampV16 (p : Params K) : C8 K :=
  ![p.c1,
    -1,
    0,
    0,
    0,
    0,
    0,
    0]

theorem amp16 (p : Params K) : amp p [1, 2] = ampV16 p := by
  funext c; fin_cases c <;> simp [ampV16, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem frame16 (p : Params K) : frameOf p [1, 2] = 2 := rfl

/-- Amplitude of `word28 17 = [3, 1, 0, 2]` (frame C). -/
def ampV17 (p : Params K) : C8 K :=
  ![p.c3,
    0,
    0,
    -1,
    0,
    0,
    0,
    0]

theorem amp17 (p : Params K) : amp p [3, 1, 0, 2] = ampV17 p := by
  funext c; fin_cases c <;> simp [ampV17, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem frame17 (p : Params K) : frameOf p [3, 1, 0, 2] = 2 := rfl

/-- Amplitude of `word28 18 = [1, 3, 2]` (frame C). -/
def ampV18 (p : Params K) : C8 K :=
  ![p.c2 * p.c3 - p.M23,
    0,
    p.c3,
    p.c2,
    1,
    0,
    0,
    0]

theorem amp18 (p : Params K) : amp p [1, 3, 2] = ampV18 p := by
  funext c; fin_cases c <;> simp [ampV18, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem frame18 (p : Params K) : frameOf p [1, 3, 2] = 2 := rfl

/-- Amplitude of `word28 19 = [3, 1, 2]` (frame C). -/
def ampV19 (p : Params K) : C8 K :=
  ![p.c1 * p.c3 - p.M13,
    -p.c3,
    0,
    -p.c1,
    0,
    -1,
    0,
    0]

theorem amp19 (p : Params K) : amp p [3, 1, 2] = ampV19 p := by
  funext c; fin_cases c <;> simp [ampV19, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem frame19 (p : Params K) : frameOf p [3, 1, 2] = 2 := rfl

/-- Amplitude of `word28 20 = [2, 1, 3, 2]` (frame C). -/
def ampV20 (p : Params K) : C8 K :=
  ![p.c1 * p.c2 * p.c3 - p.c1 * p.M23 - p.c2 * p.M13 - p.c3 * p.M12 + p.b,
    p.c2 * p.c3 - p.M23,
    p.c1 * p.c3 - p.M13,
    p.c1 * p.c2 + p.M12,
    p.c1,
    p.c2,
    -p.c3,
    1]

theorem amp20 (p : Params K) : amp p [2, 1, 3, 2] = ampV20 p := by
  funext c; fin_cases c <;> simp [ampV20, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem frame20 (p : Params K) : frameOf p [2, 1, 3, 2] = 2 := rfl

/-- Amplitude of `word28 21 = [3]` (frame D). -/
def ampV21 (p : Params K) : C8 K :=
  ![1,
    0,
    0,
    0,
    0,
    0,
    0,
    0]

theorem amp21 (p : Params K) : amp p [3] = ampV21 p := by
  funext c; fin_cases c <;> simp [ampV21, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem frame21 (p : Params K) : frameOf p [3] = 3 := rfl

/-- Amplitude of `word28 22 = [1, 3]` (frame D). -/
def ampV22 (p : Params K) : C8 K :=
  ![p.c3,
    0,
    0,
    1,
    0,
    0,
    0,
    0]

theorem amp22 (p : Params K) : amp p [1, 3] = ampV22 p := by
  funext c; fin_cases c <;> simp [ampV22, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem frame22 (p : Params K) : frameOf p [1, 3] = 3 := rfl

/-- Amplitude of `word28 23 = [2, 3]` (frame D). -/
def ampV23 (p : Params K) : C8 K :=
  ![p.c2,
    0,
    -1,
    0,
    0,
    0,
    0,
    0]

theorem amp23 (p : Params K) : amp p [2, 3] = ampV23 p := by
  funext c; fin_cases c <;> simp [ampV23, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem frame23 (p : Params K) : frameOf p [2, 3] = 3 := rfl

/-- Amplitude of `word28 24 = [1, 2, 0, 3]` (frame D). -/
def ampV24 (p : Params K) : C8 K :=
  ![p.c1,
    -1,
    0,
    0,
    0,
    0,
    0,
    0]

theorem amp24 (p : Params K) : amp p [1, 2, 0, 3] = ampV24 p := by
  funext c; fin_cases c <;> simp [ampV24, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem frame24 (p : Params K) : frameOf p [1, 2, 0, 3] = 3 := rfl

/-- Amplitude of `word28 25 = [2, 1, 3]` (frame D). -/
def ampV25 (p : Params K) : C8 K :=
  ![p.c1 * p.c3 - p.M13,
    p.c3,
    0,
    p.c1,
    0,
    1,
    0,
    0]

theorem amp25 (p : Params K) : amp p [2, 1, 3] = ampV25 p := by
  funext c; fin_cases c <;> simp [ampV25, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem frame25 (p : Params K) : frameOf p [2, 1, 3] = 3 := rfl

/-- Amplitude of `word28 26 = [1, 2, 3]` (frame D). -/
def ampV26 (p : Params K) : C8 K :=
  ![p.c1 * p.c2 - p.M12,
    -p.c2,
    -p.c1,
    0,
    0,
    0,
    -1,
    0]

theorem amp26 (p : Params K) : amp p [1, 2, 3] = ampV26 p := by
  funext c; fin_cases c <;> simp [ampV26, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem frame26 (p : Params K) : frameOf p [1, 2, 3] = 3 := rfl

/-- Amplitude of `word28 27 = [3, 2, 1, 3]` (frame D). -/
def ampV27 (p : Params K) : C8 K :=
  ![p.c1 * p.c2 * p.c3 - p.c1 * p.M23 - p.c2 * p.M13 - p.c3 * p.M12 + p.b,
    p.c2 * p.c3 + p.M23,
    p.c1 * p.c3 - p.M13,
    p.c1 * p.c2 - p.M12,
    -p.c1,
    p.c2,
    p.c3,
    1]

theorem amp27 (p : Params K) : amp p [3, 2, 1, 3] = ampV27 p := by
  funext c; fin_cases c <;> simp [ampV27, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem frame27 (p : Params K) : frameOf p [3, 2, 1, 3] = 3 := rfl

end LemmaB.TableModel
