/- SPDX-License-Identifier: Apache-2.0
   Machine-generated file. -/
module

public import TableModel.Amps

/-! # Table-model identity, part 2 (frames A, B): the model values in the gauge parameters

`qg_i_j p` is `⟨amp(w_i), T_{f_i f_j} amp(w_j)⟩_𝒞` expanded in the 13 gauge parameters
(any field); `qn_i_j` is its value at `paramsN`, a polynomial in `n_x` and the other ten
traces. -/

@[expose] public section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace LemmaB.TableModel

variable {K : Type*} [Field K]

def qg_0_7 (p : Params K) : K :=
  1

theorem qg_0_7_eq (p : Params K) :
    W p (ampV0 p) (T p 0 1 (ampV7 p)) = qg_0_7 p := by
  simp [qg_0_7, ampV0, ampV7, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_0_7 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_0_7 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      1 := by
  simp only [qg_0_7, paramsN] <;> ring

def qg_0_8 (p : Params K) : K :=
  p.c1

theorem qg_0_8_eq (p : Params K) :
    W p (ampV0 p) (T p 0 1 (ampV8 p)) = qg_0_8 p := by
  simp [qg_0_8, ampV0, ampV8, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_0_8 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_0_8 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * RABC := by
  simp only [qg_0_8, paramsN] <;> ring

def qg_0_9 (p : Params K) : K :=
  p.c3

theorem qg_0_9_eq (p : Params K) :
    W p (ampV0 p) (T p 0 1 (ampV9 p)) = qg_0_9 p := by
  simp [qg_0_9, ampV0, ampV9, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_0_9 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_0_9 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nD * RABD := by
  simp only [qg_0_9, paramsN] <;> ring

def qg_0_10 (p : Params K) : K :=
  p.c2

theorem qg_0_10_eq (p : Params K) :
    W p (ampV0 p) (T p 0 1 (ampV10 p)) = qg_0_10 p := by
  simp [qg_0_10, ampV0, ampV10, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_0_10 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_0_10 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nC * nD * RACD := by
  simp only [qg_0_10, paramsN] <;> ring

def qg_0_11 (p : Params K) : K :=
  p.c1 * p.c2 - p.M12

theorem qg_0_11_eq (p : Params K) :
    W p (ampV0 p) (T p 0 1 (ampV11 p)) = qg_0_11 p := by
  simp [qg_0_11, ampV0, ampV11, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_0_11 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_0_11 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * wC := by
  simp only [qg_0_11, paramsN] <;> ring

def qg_0_12 (p : Params K) : K :=
  p.c2 * p.c3 - p.M23

theorem qg_0_12_eq (p : Params K) :
    W p (ampV0 p) (T p 0 1 (ampV12 p)) = qg_0_12 p := by
  simp [qg_0_12, ampV0, ampV12, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_0_12 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_0_12 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * wD := by
  simp only [qg_0_12, paramsN] <;> ring

def qg_0_13 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 - p.c1 * p.M23 - p.c2 * p.M13 - p.c3 * p.M12 + p.b

theorem qg_0_13_eq (p : Params K) :
    W p (ampV0 p) (T p 0 1 (ampV13 p)) = qg_0_13 p := by
  simp [qg_0_13, ampV0, ampV13, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_0_13 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_0_13 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * RBCD := by
  simp only [qg_0_13, paramsN] <;> ring

def qg_1_7 (p : Params K) : K :=
  p.c1

theorem qg_1_7_eq (p : Params K) :
    W p (ampV1 p) (T p 0 1 (ampV7 p)) = qg_1_7 p := by
  simp [qg_1_7, ampV1, ampV7, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_1_7 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_1_7 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * RABC := by
  simp only [qg_1_7, paramsN] <;> ring

def qg_1_8 (p : Params K) : K :=
  p.c1 ^ 2 + p.M11

theorem qg_1_8_eq (p : Params K) :
    W p (ampV1 p) (T p 0 1 (ampV8 p)) = qg_1_8 p := by
  simp [qg_1_8, ampV1, ampV8, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_1_8 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_1_8 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * oBC := by
  simp only [qg_1_8, paramsN] <;> ring

def qg_1_9 (p : Params K) : K :=
  p.c1 * p.c3 - p.M13

theorem qg_1_9_eq (p : Params K) :
    W p (ampV1 p) (T p 0 1 (ampV9 p)) = qg_1_9 p := by
  simp [qg_1_9, ampV1, ampV9, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_1_9 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_1_9 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * wB := by
  simp only [qg_1_9, paramsN] <;> ring

def qg_1_10 (p : Params K) : K :=
  p.c1 * p.c2 - p.M12

theorem qg_1_10_eq (p : Params K) :
    W p (ampV1 p) (T p 0 1 (ampV10 p)) = qg_1_10 p := by
  simp [qg_1_10, ampV1, ampV10, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_1_10 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_1_10 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * wC := by
  simp only [qg_1_10, paramsN] <;> ring

def qg_1_11 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 + p.c2 * p.M11

theorem qg_1_11_eq (p : Params K) :
    W p (ampV1 p) (T p 0 1 (ampV11 p)) = qg_1_11 p := by
  simp [qg_1_11, ampV1, ampV11, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_1_11 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_1_11 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * nD * oBC * RACD := by
  simp only [qg_1_11, paramsN] <;> ring

def qg_1_12 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 - p.c1 * p.M23 - p.c2 * p.M13 - p.c3 * p.M12 + p.b

theorem qg_1_12_eq (p : Params K) :
    W p (ampV1 p) (T p 0 1 (ampV12 p)) = qg_1_12 p := by
  simp [qg_1_12, ampV1, ampV12, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_1_12 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_1_12 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * RBCD := by
  simp only [qg_1_12, paramsN] <;> ring

def qg_1_13 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 * p.c3 - p.c1 ^ 2 * p.M23 + p.c2 * p.c3 * p.M11 - p.M11 * p.M23

theorem qg_1_13_eq (p : Params K) :
    W p (ampV1 p) (T p 0 1 (ampV13 p)) = qg_1_13 p := by
  simp [qg_1_13, ampV1, ampV13, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_1_13 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_1_13 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC ^ 2 * nD * oBC * wD := by
  simp only [qg_1_13, paramsN] <;> ring

def qg_2_7 (p : Params K) : K :=
  p.c2

theorem qg_2_7_eq (p : Params K) :
    W p (ampV2 p) (T p 0 1 (ampV7 p)) = qg_2_7 p := by
  simp [qg_2_7, ampV2, ampV7, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_2_7 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_2_7 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nC * nD * RACD := by
  simp only [qg_2_7, paramsN] <;> ring

def qg_2_8 (p : Params K) : K :=
  p.c1 * p.c2 + p.M12

theorem qg_2_8_eq (p : Params K) :
    W p (ampV2 p) (T p 0 1 (ampV8 p)) = qg_2_8 p := by
  simp [qg_2_8, ampV2, ampV8, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_2_8 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_2_8 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB * nC ^ 2 * nD * RABC * RACD - nB * nC * nD * wC := by
  simp only [qg_2_8, paramsN] <;> ring

def qg_2_9 (p : Params K) : K :=
  p.c2 * p.c3 - p.M23

theorem qg_2_9_eq (p : Params K) :
    W p (ampV2 p) (T p 0 1 (ampV9 p)) = qg_2_9 p := by
  simp [qg_2_9, ampV2, ampV9, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_2_9 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_2_9 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * wD := by
  simp only [qg_2_9, paramsN] <;> ring

def qg_2_10 (p : Params K) : K :=
  p.c2 ^ 2 - p.M22

theorem qg_2_10_eq (p : Params K) :
    W p (ampV2 p) (T p 0 1 (ampV10 p)) = qg_2_10 p := by
  simp [qg_2_10, ampV2, ampV10, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_2_10 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_2_10 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nC ^ 2 * nD ^ 2 * RACD ^ 2 - nC * nD * oCD := by
  simp only [qg_2_10, paramsN] <;> ring

def qg_2_11 (p : Params K) : K :=
  p.c1 * p.c2 ^ 2 + p.c1 * p.M22

theorem qg_2_11_eq (p : Params K) :
    W p (ampV2 p) (T p 0 1 (ampV11 p)) = qg_2_11 p := by
  simp [qg_2_11, ampV2, ampV11, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_2_11 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_2_11 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * nD * oCD * RABC := by
  simp only [qg_2_11, paramsN] <;> ring

def qg_2_12 (p : Params K) : K :=
  p.c2 ^ 2 * p.c3 - 2 * p.c2 * p.M23 - p.c3 * p.M22

theorem qg_2_12_eq (p : Params K) :
    W p (ampV2 p) (T p 0 1 (ampV12 p)) = qg_2_12 p := by
  simp [qg_2_12, ampV2, ampV12, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_2_12 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_2_12 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB * nC ^ 2 * nD ^ 2 * RACD * wD - nB * nC * nD ^ 2 * oCD * RABD := by
  simp only [qg_2_12, paramsN] <;> ring

def qg_2_13 (p : Params K) : K :=
  p.c1 * p.c2 ^ 2 * p.c3 + p.c1 * p.c3 * p.M22 - p.c2 ^ 2 * p.M13 + 2 * p.c2 * p.b + p.M22 * p.M13 - 2 * p.M12 * p.M23

theorem qg_2_13_eq (p : Params K) :
    W p (ampV2 p) (T p 0 1 (ampV13 p)) = qg_2_13 p := by
  simp [qg_2_13, ampV2, ampV13, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_2_13 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_2_13 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * oCD * RABC * RABD - 2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * wC * wD - nB * nC ^ 2 * nD ^ 2 * oCD * wB + 2 * nB * nC ^ 2 * nD ^ 2 * RACD * RBCD := by
  simp only [qg_2_13, paramsN] <;> ring

def qg_3_7 (p : Params K) : K :=
  p.c3

theorem qg_3_7_eq (p : Params K) :
    W p (ampV3 p) (T p 0 1 (ampV7 p)) = qg_3_7 p := by
  simp [qg_3_7, ampV3, ampV7, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_3_7 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_3_7 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nD * RABD := by
  simp only [qg_3_7, paramsN] <;> ring

def qg_3_8 (p : Params K) : K :=
  p.c1 * p.c3 + p.M13

theorem qg_3_8_eq (p : Params K) :
    W p (ampV3 p) (T p 0 1 (ampV8 p)) = qg_3_8 p := by
  simp [qg_3_8, ampV3, ampV8, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_3_8 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_3_8 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC * nD * RABC * RABD - nB * nC * nD * wB := by
  simp only [qg_3_8, paramsN] <;> ring

def qg_3_9 (p : Params K) : K :=
  p.c3 ^ 2 - p.M33

theorem qg_3_9_eq (p : Params K) :
    W p (ampV3 p) (T p 0 1 (ampV9 p)) = qg_3_9 p := by
  simp [qg_3_9, ampV3, ampV9, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_3_9 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_3_9 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nD ^ 2 * RABD ^ 2 - nB * nD * oBD := by
  simp only [qg_3_9, paramsN] <;> ring

def qg_3_10 (p : Params K) : K :=
  p.c2 * p.c3 - p.M23

theorem qg_3_10_eq (p : Params K) :
    W p (ampV3 p) (T p 0 1 (ampV10 p)) = qg_3_10 p := by
  simp [qg_3_10, ampV3, ampV10, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_3_10 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_3_10 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * wD := by
  simp only [qg_3_10, paramsN] <;> ring

def qg_3_11 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 + p.c1 * p.M23 + p.c2 * p.M13 - p.c3 * p.M12 - p.b

theorem qg_3_11_eq (p : Params K) :
    W p (ampV3 p) (T p 0 1 (ampV11 p)) = qg_3_11 p := by
  simp [qg_3_11, ampV3, ampV11, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_3_11 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_3_11 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC * nD ^ 2 * RABD * wC - nB * nC * nD * RBCD := by
  simp only [qg_3_11, paramsN] <;> ring

def qg_3_12 (p : Params K) : K :=
  p.c2 * p.c3 ^ 2 - p.c2 * p.M33 - 2 * p.c3 * p.M23

theorem qg_3_12_eq (p : Params K) :
    W p (ampV3 p) (T p 0 1 (ampV12 p)) = qg_3_12 p := by
  simp [qg_3_12, ampV3, ampV12, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_3_12 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_3_12 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC * nD ^ 2 * RABD * wD - nB * nC * nD ^ 2 * oBD * RACD := by
  simp only [qg_3_12, paramsN] <;> ring

def qg_3_13 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 ^ 2 + p.c1 * p.c2 * p.M33 - p.c3 ^ 2 * p.M12 - p.M33 * p.M12

theorem qg_3_13_eq (p : Params K) :
    W p (ampV3 p) (T p 0 1 (ampV13 p)) = qg_3_13 p := by
  simp [qg_3_13, ampV3, ampV13, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_3_13 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_3_13 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD ^ 2 * oBD * wC := by
  simp only [qg_3_13, paramsN] <;> ring

def qg_4_7 (p : Params K) : K :=
  p.c1 * p.c2 - p.M12

theorem qg_4_7_eq (p : Params K) :
    W p (ampV4 p) (T p 0 1 (ampV7 p)) = qg_4_7 p := by
  simp [qg_4_7, ampV4, ampV7, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_4_7 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_4_7 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * wC := by
  simp only [qg_4_7, paramsN] <;> ring

def qg_4_8 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 + p.c2 * p.M11

theorem qg_4_8_eq (p : Params K) :
    W p (ampV4 p) (T p 0 1 (ampV8 p)) = qg_4_8 p := by
  simp [qg_4_8, ampV4, ampV8, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_4_8 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_4_8 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * nD * oBC * RACD := by
  simp only [qg_4_8, paramsN] <;> ring

def qg_4_9 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 - p.c1 * p.M23 - p.c2 * p.M13 - p.c3 * p.M12 + p.b

theorem qg_4_9_eq (p : Params K) :
    W p (ampV4 p) (T p 0 1 (ampV9 p)) = qg_4_9 p := by
  simp [qg_4_9, ampV4, ampV9, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_4_9 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_4_9 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * RBCD := by
  simp only [qg_4_9, paramsN] <;> ring

def qg_4_10 (p : Params K) : K :=
  p.c1 * p.c2 ^ 2 - p.c1 * p.M22 - 2 * p.c2 * p.M12

theorem qg_4_10_eq (p : Params K) :
    W p (ampV4 p) (T p 0 1 (ampV10 p)) = qg_4_10 p := by
  simp [qg_4_10, ampV4, ampV10, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_4_10 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_4_10 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB * nC ^ 2 * nD ^ 2 * RACD * wC - nB * nC ^ 2 * nD * oCD * RABC := by
  simp only [qg_4_10, paramsN] <;> ring

def qg_4_11 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 ^ 2 + p.c1 ^ 2 * p.M22 + p.c2 ^ 2 * p.M11 + p.M11 * p.M22

theorem qg_4_11_eq (p : Params K) :
    W p (ampV4 p) (T p 0 1 (ampV11 p)) = qg_4_11 p := by
  simp [qg_4_11, ampV4, ampV11, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_4_11 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_4_11 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * nD * oBC * oCD := by
  simp only [qg_4_11, paramsN] <;> ring

def qg_4_12 (p : Params K) : K :=
  p.c1 * p.c2 ^ 2 * p.c3 - 2 * p.c1 * p.c2 * p.M23 - p.c1 * p.c3 * p.M22 - p.c2 ^ 2 * p.M13 - 2 * p.c2 * p.c3 * p.M12 + 2 * p.c2 * p.b + p.M22 * p.M13

theorem qg_4_12_eq (p : Params K) :
    W p (ampV4 p) (T p 0 1 (ampV12 p)) = qg_4_12 p := by
  simp [qg_4_12, ampV4, ampV12, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_4_12 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_4_12 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB * nC ^ 2 * nD ^ 2 * oCD * wB + 2 * nB * nC ^ 2 * nD ^ 2 * RACD * RBCD := by
  simp only [qg_4_12, paramsN] <;> ring

def qg_4_13 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 ^ 2 * p.c3 + p.c1 ^ 2 * p.c3 * p.M22 + p.c2 ^ 2 * p.c3 * p.M11 + p.c3 * p.M11 * p.M22

theorem qg_4_13_eq (p : Params K) :
    W p (ampV4 p) (T p 0 1 (ampV13 p)) = qg_4_13 p := by
  simp [qg_4_13, ampV4, ampV13, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_4_13 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_4_13 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC ^ 2 * nD ^ 2 * oBC * oCD * RABD := by
  simp only [qg_4_13, paramsN] <;> ring

def qg_5_7 (p : Params K) : K :=
  p.c2 * p.c3 - p.M23

theorem qg_5_7_eq (p : Params K) :
    W p (ampV5 p) (T p 0 1 (ampV7 p)) = qg_5_7 p := by
  simp [qg_5_7, ampV5, ampV7, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_5_7 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_5_7 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * wD := by
  simp only [qg_5_7, paramsN] <;> ring

def qg_5_8 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 - p.c1 * p.M23 - p.c2 * p.M13 - p.c3 * p.M12 + p.b

theorem qg_5_8_eq (p : Params K) :
    W p (ampV5 p) (T p 0 1 (ampV8 p)) = qg_5_8 p := by
  simp [qg_5_8, ampV5, ampV8, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_5_8 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_5_8 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * RBCD := by
  simp only [qg_5_8, paramsN] <;> ring

def qg_5_9 (p : Params K) : K :=
  p.c2 * p.c3 ^ 2 + p.c2 * p.M33

theorem qg_5_9_eq (p : Params K) :
    W p (ampV5 p) (T p 0 1 (ampV9 p)) = qg_5_9 p := by
  simp [qg_5_9, ampV5, ampV9, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_5_9 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_5_9 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD ^ 2 * oBD * RACD := by
  simp only [qg_5_9, paramsN] <;> ring

def qg_5_10 (p : Params K) : K :=
  p.c2 ^ 2 * p.c3 + p.c3 * p.M22

theorem qg_5_10_eq (p : Params K) :
    W p (ampV5 p) (T p 0 1 (ampV10 p)) = qg_5_10 p := by
  simp [qg_5_10, ampV5, ampV10, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_5_10 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_5_10 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD ^ 2 * oCD * RABD := by
  simp only [qg_5_10, paramsN] <;> ring

def qg_5_11 (p : Params K) : K :=
  p.c1 * p.c2 ^ 2 * p.c3 - 2 * p.c1 * p.c2 * p.M23 - p.c1 * p.c3 * p.M22 - p.c2 ^ 2 * p.M13 - 2 * p.c2 * p.c3 * p.M12 + 2 * p.c2 * p.b + p.M22 * p.M13

theorem qg_5_11_eq (p : Params K) :
    W p (ampV5 p) (T p 0 1 (ampV11 p)) = qg_5_11 p := by
  simp [qg_5_11, ampV5, ampV11, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_5_11 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_5_11 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB * nC ^ 2 * nD ^ 2 * oCD * wB + 2 * nB * nC ^ 2 * nD ^ 2 * RACD * RBCD := by
  simp only [qg_5_11, paramsN] <;> ring

def qg_5_12 (p : Params K) : K :=
  p.c2 ^ 2 * p.c3 ^ 2 + p.c2 ^ 2 * p.M33 + p.c3 ^ 2 * p.M22 + p.M22 * p.M33

theorem qg_5_12_eq (p : Params K) :
    W p (ampV5 p) (T p 0 1 (ampV12 p)) = qg_5_12 p := by
  simp [qg_5_12, ampV5, ampV12, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_5_12 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_5_12 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD ^ 2 * oBD * oCD := by
  simp only [qg_5_12, paramsN] <;> ring

def qg_5_13 (p : Params K) : K :=
  p.c1 * p.c2 ^ 2 * p.c3 ^ 2 - p.c1 * p.c2 ^ 2 * p.M33 - 4 * p.c1 * p.c2 * p.c3 * p.M23 - p.c1 * p.c3 ^ 2 * p.M22 - p.c1 * p.M22 * p.M33 + 2 * p.c1 * p.M23 ^ 2 - 2 * p.c2 ^ 2 * p.c3 * p.M13 - 2 * p.c2 * p.c3 ^ 2 * p.M12 + 2 * p.c2 * p.c3 * p.b + 2 * p.c2 * p.M13 * p.M23 + 2 * p.c3 * p.M12 * p.M23 - 2 * p.M23 * p.b

theorem qg_5_13_eq (p : Params K) :
    W p (ampV5 p) (T p 0 1 (ampV13 p)) = qg_5_13 p := by
  simp [qg_5_13, ampV5, ampV13, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_5_13 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_5_13 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB ^ 2 * nC ^ 2 * nD ^ 2 * oBD * oCD * RABC + 2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * RBCD * wD := by
  simp only [qg_5_13, paramsN] <;> ring

def qg_6_7 (p : Params K) : K :=
  p.c1 * p.c3 - p.M13

theorem qg_6_7_eq (p : Params K) :
    W p (ampV6 p) (T p 0 1 (ampV7 p)) = qg_6_7 p := by
  simp [qg_6_7, ampV6, ampV7, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_6_7 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_6_7 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * wB := by
  simp only [qg_6_7, paramsN] <;> ring

def qg_6_8 (p : Params K) : K :=
  p.c1 ^ 2 * p.c3 - 2 * p.c1 * p.M13 - p.c3 * p.M11

theorem qg_6_8_eq (p : Params K) :
    W p (ampV6 p) (T p 0 1 (ampV8 p)) = qg_6_8 p := by
  simp [qg_6_8, ampV6, ampV8, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_6_8 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_6_8 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC ^ 2 * nD * RABC * wB - nB ^ 2 * nC * nD * oBC * RABD := by
  simp only [qg_6_8, paramsN] <;> ring

def qg_6_9 (p : Params K) : K :=
  p.c1 * p.c3 ^ 2 + p.c1 * p.M33

theorem qg_6_9_eq (p : Params K) :
    W p (ampV6 p) (T p 0 1 (ampV9 p)) = qg_6_9 p := by
  simp [qg_6_9, ampV6, ampV9, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_6_9 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_6_9 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD * oBD * RABC := by
  simp only [qg_6_9, paramsN] <;> ring

def qg_6_10 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 + p.c1 * p.M23 - p.c2 * p.M13 + p.c3 * p.M12 - p.b

theorem qg_6_10_eq (p : Params K) :
    W p (ampV6 p) (T p 0 1 (ampV10 p)) = qg_6_10 p := by
  simp [qg_6_10, ampV6, ampV10, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_6_10 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_6_10 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB * nC ^ 2 * nD ^ 2 * RACD * wB - nB * nC * nD * RBCD := by
  simp only [qg_6_10, paramsN] <;> ring

def qg_6_11 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 * p.c3 - p.c1 ^ 2 * p.M23 - 2 * p.c1 * p.c2 * p.M13 - 2 * p.c1 * p.c3 * p.M12 + 2 * p.c1 * p.b - p.c2 * p.c3 * p.M11 + p.M11 * p.M23

theorem qg_6_11_eq (p : Params K) :
    W p (ampV6 p) (T p 0 1 (ampV11 p)) = qg_6_11 p := by
  simp [qg_6_11, ampV6, ampV11, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_6_11 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_6_11 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB ^ 2 * nC ^ 2 * nD * oBC * wD + 2 * nB ^ 2 * nC ^ 2 * nD * RABC * RBCD := by
  simp only [qg_6_11, paramsN] <;> ring

def qg_6_12 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 ^ 2 + p.c1 * p.c2 * p.M33 + p.c3 ^ 2 * p.M12 - 2 * p.c3 * p.b - p.M33 * p.M12 + 2 * p.M13 * p.M23

theorem qg_6_12_eq (p : Params K) :
    W p (ampV6 p) (T p 0 1 (ampV12 p)) = qg_6_12 p := by
  simp [qg_6_12, ampV6, ampV12, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_6_12 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_6_12 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * wB * wD + nB ^ 2 * nC * nD ^ 2 * oBD * wC - 2 * nB ^ 2 * nC * nD ^ 2 * RABD * RBCD := by
  simp only [qg_6_12, paramsN] <;> ring

def qg_6_13 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 * p.c3 ^ 2 - p.c1 ^ 2 * p.c2 * p.M33 - 2 * p.c1 ^ 2 * p.c3 * p.M23 - 4 * p.c1 * p.c2 * p.c3 * p.M13 - 2 * p.c1 * p.c3 ^ 2 * p.M12 + 4 * p.c1 * p.c3 * p.b + 2 * p.c1 * p.M33 * p.M12 - p.c2 * p.c3 ^ 2 * p.M11 + p.c2 * p.M11 * p.M33 + 2 * p.c3 * p.M11 * p.M23

theorem qg_6_13_eq (p : Params K) :
    W p (ampV6 p) (T p 0 1 (ampV13 p)) = qg_6_13 p := by
  simp [qg_6_13, ampV6, ampV13, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_6_13 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_6_13 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -2 * nB ^ 3 * nC ^ 2 * nD ^ 2 * oBC * RABD * wD - 2 * nB ^ 3 * nC ^ 2 * nD ^ 2 * oBD * RABC * wC + 4 * nB ^ 3 * nC ^ 2 * nD ^ 2 * RABC * RABD * RBCD + nB ^ 2 * nC ^ 2 * nD ^ 2 * oBC * oBD * RACD := by
  simp only [qg_6_13, paramsN] <;> ring

end LemmaB.TableModel
