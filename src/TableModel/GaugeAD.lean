/- SPDX-License-Identifier: Apache-2.0
   Machine-generated file. -/
module

public import TableModel.Amps

/-! # Table-model identity, part 2 (frames A, D): the model values in the gauge parameters

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

def qg_0_21 (p : Params K) : K :=
  1

theorem qg_0_21_eq (p : Params K) :
    W p (ampV0 p) (T p 0 3 (ampV21 p)) = qg_0_21 p := by
  simp [qg_0_21, ampV0, ampV21, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_0_21 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_0_21 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      1 := by
  simp only [qg_0_21, paramsN] <;> ring

def qg_0_22 (p : Params K) : K :=
  p.c3

theorem qg_0_22_eq (p : Params K) :
    W p (ampV0 p) (T p 0 3 (ampV22 p)) = qg_0_22 p := by
  simp [qg_0_22, ampV0, ampV22, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_0_22 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_0_22 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nD * RABD := by
  simp only [qg_0_22, paramsN] <;> ring

def qg_0_23 (p : Params K) : K :=
  p.c2

theorem qg_0_23_eq (p : Params K) :
    W p (ampV0 p) (T p 0 3 (ampV23 p)) = qg_0_23 p := by
  simp [qg_0_23, ampV0, ampV23, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_0_23 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_0_23 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nC * nD * RACD := by
  simp only [qg_0_23, paramsN] <;> ring

def qg_0_24 (p : Params K) : K :=
  p.c1

theorem qg_0_24_eq (p : Params K) :
    W p (ampV0 p) (T p 0 3 (ampV24 p)) = qg_0_24 p := by
  simp [qg_0_24, ampV0, ampV24, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_0_24 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_0_24 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * RABC := by
  simp only [qg_0_24, paramsN] <;> ring

def qg_0_25 (p : Params K) : K :=
  p.c1 * p.c3 - p.M13

theorem qg_0_25_eq (p : Params K) :
    W p (ampV0 p) (T p 0 3 (ampV25 p)) = qg_0_25 p := by
  simp [qg_0_25, ampV0, ampV25, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_0_25 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_0_25 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * wB := by
  simp only [qg_0_25, paramsN] <;> ring

def qg_0_26 (p : Params K) : K :=
  p.c1 * p.c2 - p.M12

theorem qg_0_26_eq (p : Params K) :
    W p (ampV0 p) (T p 0 3 (ampV26 p)) = qg_0_26 p := by
  simp [qg_0_26, ampV0, ampV26, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_0_26 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_0_26 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * wC := by
  simp only [qg_0_26, paramsN] <;> ring

def qg_0_27 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 - p.c1 * p.M23 - p.c2 * p.M13 - p.c3 * p.M12 + p.b

theorem qg_0_27_eq (p : Params K) :
    W p (ampV0 p) (T p 0 3 (ampV27 p)) = qg_0_27 p := by
  simp [qg_0_27, ampV0, ampV27, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_0_27 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_0_27 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * RBCD := by
  simp only [qg_0_27, paramsN] <;> ring

def qg_1_21 (p : Params K) : K :=
  p.c1

theorem qg_1_21_eq (p : Params K) :
    W p (ampV1 p) (T p 0 3 (ampV21 p)) = qg_1_21 p := by
  simp [qg_1_21, ampV1, ampV21, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_1_21 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_1_21 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * RABC := by
  simp only [qg_1_21, paramsN] <;> ring

def qg_1_22 (p : Params K) : K :=
  p.c1 * p.c3 + p.M13

theorem qg_1_22_eq (p : Params K) :
    W p (ampV1 p) (T p 0 3 (ampV22 p)) = qg_1_22 p := by
  simp [qg_1_22, ampV1, ampV22, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_1_22 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_1_22 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC * nD * RABC * RABD - nB * nC * nD * wB := by
  simp only [qg_1_22, paramsN] <;> ring

def qg_1_23 (p : Params K) : K :=
  p.c1 * p.c2 - p.M12

theorem qg_1_23_eq (p : Params K) :
    W p (ampV1 p) (T p 0 3 (ampV23 p)) = qg_1_23 p := by
  simp [qg_1_23, ampV1, ampV23, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_1_23 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_1_23 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * wC := by
  simp only [qg_1_23, paramsN] <;> ring

def qg_1_24 (p : Params K) : K :=
  p.c1 ^ 2 - p.M11

theorem qg_1_24_eq (p : Params K) :
    W p (ampV1 p) (T p 0 3 (ampV24 p)) = qg_1_24 p := by
  simp [qg_1_24, ampV1, ampV24, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_1_24 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_1_24 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC ^ 2 * RABC ^ 2 - nB * nC * oBC := by
  simp only [qg_1_24, paramsN] <;> ring

def qg_1_25 (p : Params K) : K :=
  p.c1 ^ 2 * p.c3 + p.c3 * p.M11

theorem qg_1_25_eq (p : Params K) :
    W p (ampV1 p) (T p 0 3 (ampV25 p)) = qg_1_25 p := by
  simp [qg_1_25, ampV1, ampV25, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_1_25 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_1_25 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD * oBC * RABD := by
  simp only [qg_1_25, paramsN] <;> ring

def qg_1_26 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 - 2 * p.c1 * p.M12 - p.c2 * p.M11

theorem qg_1_26_eq (p : Params K) :
    W p (ampV1 p) (T p 0 3 (ampV26 p)) = qg_1_26 p := by
  simp [qg_1_26, ampV1, ampV26, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_1_26 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_1_26 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC ^ 2 * nD * RABC * wC - nB * nC ^ 2 * nD * oBC * RACD := by
  simp only [qg_1_26, paramsN] <;> ring

def qg_1_27 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 * p.c3 - p.c1 ^ 2 * p.M23 + 2 * p.c1 * p.b + p.c2 * p.c3 * p.M11 + p.M11 * p.M23 - 2 * p.M12 * p.M13

theorem qg_1_27_eq (p : Params K) :
    W p (ampV1 p) (T p 0 3 (ampV27 p)) = qg_1_27 p := by
  simp [qg_1_27, ampV1, ampV27, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_1_27 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_1_27 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * oBC * RABD * RACD - 2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * wB * wC - nB ^ 2 * nC ^ 2 * nD * oBC * wD + 2 * nB ^ 2 * nC ^ 2 * nD * RABC * RBCD := by
  simp only [qg_1_27, paramsN] <;> ring

def qg_2_21 (p : Params K) : K :=
  p.c2

theorem qg_2_21_eq (p : Params K) :
    W p (ampV2 p) (T p 0 3 (ampV21 p)) = qg_2_21 p := by
  simp [qg_2_21, ampV2, ampV21, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_2_21 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_2_21 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nC * nD * RACD := by
  simp only [qg_2_21, paramsN] <;> ring

def qg_2_22 (p : Params K) : K :=
  p.c2 * p.c3 + p.M23

theorem qg_2_22_eq (p : Params K) :
    W p (ampV2 p) (T p 0 3 (ampV22 p)) = qg_2_22 p := by
  simp [qg_2_22, ampV2, ampV22, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_2_22 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_2_22 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB * nC * nD ^ 2 * RABD * RACD - nB * nC * nD * wD := by
  simp only [qg_2_22, paramsN] <;> ring

def qg_2_23 (p : Params K) : K :=
  p.c2 ^ 2 - p.M22

theorem qg_2_23_eq (p : Params K) :
    W p (ampV2 p) (T p 0 3 (ampV23 p)) = qg_2_23 p := by
  simp [qg_2_23, ampV2, ampV23, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_2_23 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_2_23 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nC ^ 2 * nD ^ 2 * RACD ^ 2 - nC * nD * oCD := by
  simp only [qg_2_23, paramsN] <;> ring

def qg_2_24 (p : Params K) : K :=
  p.c1 * p.c2 - p.M12

theorem qg_2_24_eq (p : Params K) :
    W p (ampV2 p) (T p 0 3 (ampV24 p)) = qg_2_24 p := by
  simp [qg_2_24, ampV2, ampV24, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_2_24 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_2_24 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * wC := by
  simp only [qg_2_24, paramsN] <;> ring

def qg_2_25 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 + p.c1 * p.M23 - p.c2 * p.M13 + p.c3 * p.M12 - p.b

theorem qg_2_25_eq (p : Params K) :
    W p (ampV2 p) (T p 0 3 (ampV25 p)) = qg_2_25 p := by
  simp [qg_2_25, ampV2, ampV25, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_2_25 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_2_25 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB * nC ^ 2 * nD ^ 2 * RACD * wB - nB * nC * nD * RBCD := by
  simp only [qg_2_25, paramsN] <;> ring

def qg_2_26 (p : Params K) : K :=
  p.c1 * p.c2 ^ 2 - p.c1 * p.M22 - 2 * p.c2 * p.M12

theorem qg_2_26_eq (p : Params K) :
    W p (ampV2 p) (T p 0 3 (ampV26 p)) = qg_2_26 p := by
  simp [qg_2_26, ampV2, ampV26, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_2_26 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_2_26 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB * nC ^ 2 * nD ^ 2 * RACD * wC - nB * nC ^ 2 * nD * oCD * RABC := by
  simp only [qg_2_26, paramsN] <;> ring

def qg_2_27 (p : Params K) : K :=
  p.c1 * p.c2 ^ 2 * p.c3 + p.c1 * p.c3 * p.M22 - p.c2 ^ 2 * p.M13 - p.M22 * p.M13

theorem qg_2_27_eq (p : Params K) :
    W p (ampV2 p) (T p 0 3 (ampV27 p)) = qg_2_27 p := by
  simp [qg_2_27, ampV2, ampV27, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_2_27 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_2_27 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * nD ^ 2 * oCD * wB := by
  simp only [qg_2_27, paramsN] <;> ring

def qg_3_21 (p : Params K) : K :=
  p.c3

theorem qg_3_21_eq (p : Params K) :
    W p (ampV3 p) (T p 0 3 (ampV21 p)) = qg_3_21 p := by
  simp [qg_3_21, ampV3, ampV21, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_3_21 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_3_21 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nD * RABD := by
  simp only [qg_3_21, paramsN] <;> ring

def qg_3_22 (p : Params K) : K :=
  p.c3 ^ 2 + p.M33

theorem qg_3_22_eq (p : Params K) :
    W p (ampV3 p) (T p 0 3 (ampV22 p)) = qg_3_22 p := by
  simp [qg_3_22, ampV3, ampV22, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_3_22 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_3_22 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nD * oBD := by
  simp only [qg_3_22, paramsN] <;> ring

def qg_3_23 (p : Params K) : K :=
  p.c2 * p.c3 - p.M23

theorem qg_3_23_eq (p : Params K) :
    W p (ampV3 p) (T p 0 3 (ampV23 p)) = qg_3_23 p := by
  simp [qg_3_23, ampV3, ampV23, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_3_23 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_3_23 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * wD := by
  simp only [qg_3_23, paramsN] <;> ring

def qg_3_24 (p : Params K) : K :=
  p.c1 * p.c3 - p.M13

theorem qg_3_24_eq (p : Params K) :
    W p (ampV3 p) (T p 0 3 (ampV24 p)) = qg_3_24 p := by
  simp [qg_3_24, ampV3, ampV24, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_3_24 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_3_24 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * wB := by
  simp only [qg_3_24, paramsN] <;> ring

def qg_3_25 (p : Params K) : K :=
  p.c1 * p.c3 ^ 2 + p.c1 * p.M33

theorem qg_3_25_eq (p : Params K) :
    W p (ampV3 p) (T p 0 3 (ampV25 p)) = qg_3_25 p := by
  simp [qg_3_25, ampV3, ampV25, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_3_25 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_3_25 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD * oBD * RABC := by
  simp only [qg_3_25, paramsN] <;> ring

def qg_3_26 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 - p.c1 * p.M23 - p.c2 * p.M13 - p.c3 * p.M12 + p.b

theorem qg_3_26_eq (p : Params K) :
    W p (ampV3 p) (T p 0 3 (ampV26 p)) = qg_3_26 p := by
  simp [qg_3_26, ampV3, ampV26, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_3_26 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_3_26 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * RBCD := by
  simp only [qg_3_26, paramsN] <;> ring

def qg_3_27 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 ^ 2 + p.c1 * p.c2 * p.M33 - p.c3 ^ 2 * p.M12 - p.M33 * p.M12

theorem qg_3_27_eq (p : Params K) :
    W p (ampV3 p) (T p 0 3 (ampV27 p)) = qg_3_27 p := by
  simp [qg_3_27, ampV3, ampV27, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_3_27 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_3_27 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD ^ 2 * oBD * wC := by
  simp only [qg_3_27, paramsN] <;> ring

def qg_4_21 (p : Params K) : K :=
  p.c1 * p.c2 - p.M12

theorem qg_4_21_eq (p : Params K) :
    W p (ampV4 p) (T p 0 3 (ampV21 p)) = qg_4_21 p := by
  simp [qg_4_21, ampV4, ampV21, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_4_21 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_4_21 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * wC := by
  simp only [qg_4_21, paramsN] <;> ring

def qg_4_22 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 + p.c1 * p.M23 + p.c2 * p.M13 - p.c3 * p.M12 - p.b

theorem qg_4_22_eq (p : Params K) :
    W p (ampV4 p) (T p 0 3 (ampV22 p)) = qg_4_22 p := by
  simp [qg_4_22, ampV4, ampV22, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_4_22 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_4_22 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC * nD ^ 2 * RABD * wC - nB * nC * nD * RBCD := by
  simp only [qg_4_22, paramsN] <;> ring

def qg_4_23 (p : Params K) : K :=
  p.c1 * p.c2 ^ 2 - p.c1 * p.M22 - 2 * p.c2 * p.M12

theorem qg_4_23_eq (p : Params K) :
    W p (ampV4 p) (T p 0 3 (ampV23 p)) = qg_4_23 p := by
  simp [qg_4_23, ampV4, ampV23, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_4_23 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_4_23 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB * nC ^ 2 * nD ^ 2 * RACD * wC - nB * nC ^ 2 * nD * oCD * RABC := by
  simp only [qg_4_23, paramsN] <;> ring

def qg_4_24 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 - 2 * p.c1 * p.M12 - p.c2 * p.M11

theorem qg_4_24_eq (p : Params K) :
    W p (ampV4 p) (T p 0 3 (ampV24 p)) = qg_4_24 p := by
  simp [qg_4_24, ampV4, ampV24, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_4_24 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_4_24 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC ^ 2 * nD * RABC * wC - nB * nC ^ 2 * nD * oBC * RACD := by
  simp only [qg_4_24, paramsN] <;> ring

def qg_4_25 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 * p.c3 + p.c1 ^ 2 * p.M23 - 2 * p.c1 * p.b + p.c2 * p.c3 * p.M11 - p.M11 * p.M23 + 2 * p.M12 * p.M13

theorem qg_4_25_eq (p : Params K) :
    W p (ampV4 p) (T p 0 3 (ampV25 p)) = qg_4_25 p := by
  simp [qg_4_25, ampV4, ampV25, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_4_25 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_4_25 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * wB * wC + nB ^ 2 * nC ^ 2 * nD * oBC * wD - 2 * nB ^ 2 * nC ^ 2 * nD * RABC * RBCD := by
  simp only [qg_4_25, paramsN] <;> ring

def qg_4_26 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 ^ 2 - p.c1 ^ 2 * p.M22 - 4 * p.c1 * p.c2 * p.M12 - p.c2 ^ 2 * p.M11 - p.M11 * p.M22 + 2 * p.M12 ^ 2

theorem qg_4_26_eq (p : Params K) :
    W p (ampV4 p) (T p 0 3 (ampV26 p)) = qg_4_26 p := by
  simp [qg_4_26, ampV4, ampV26, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_4_26 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_4_26 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * wC ^ 2 - nB * nC ^ 2 * nD * oBC * oCD := by
  simp only [qg_4_26, paramsN] <;> ring

def qg_4_27 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 ^ 2 * p.c3 + p.c1 ^ 2 * p.c3 * p.M22 + p.c2 ^ 2 * p.c3 * p.M11 + p.c3 * p.M11 * p.M22

theorem qg_4_27_eq (p : Params K) :
    W p (ampV4 p) (T p 0 3 (ampV27 p)) = qg_4_27 p := by
  simp [qg_4_27, ampV4, ampV27, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_4_27 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_4_27 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC ^ 2 * nD ^ 2 * oBC * oCD * RABD := by
  simp only [qg_4_27, paramsN] <;> ring

def qg_5_21 (p : Params K) : K :=
  p.c2 * p.c3 - p.M23

theorem qg_5_21_eq (p : Params K) :
    W p (ampV5 p) (T p 0 3 (ampV21 p)) = qg_5_21 p := by
  simp [qg_5_21, ampV5, ampV21, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_5_21 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_5_21 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * wD := by
  simp only [qg_5_21, paramsN] <;> ring

def qg_5_22 (p : Params K) : K :=
  p.c2 * p.c3 ^ 2 - p.c2 * p.M33 - 2 * p.c3 * p.M23

theorem qg_5_22_eq (p : Params K) :
    W p (ampV5 p) (T p 0 3 (ampV22 p)) = qg_5_22 p := by
  simp [qg_5_22, ampV5, ampV22, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_5_22 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_5_22 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC * nD ^ 2 * RABD * wD - nB * nC * nD ^ 2 * oBD * RACD := by
  simp only [qg_5_22, paramsN] <;> ring

def qg_5_23 (p : Params K) : K :=
  p.c2 ^ 2 * p.c3 + p.c3 * p.M22

theorem qg_5_23_eq (p : Params K) :
    W p (ampV5 p) (T p 0 3 (ampV23 p)) = qg_5_23 p := by
  simp [qg_5_23, ampV5, ampV23, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_5_23 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_5_23 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD ^ 2 * oCD * RABD := by
  simp only [qg_5_23, paramsN] <;> ring

def qg_5_24 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 - p.c1 * p.M23 + p.c2 * p.M13 + p.c3 * p.M12 - p.b

theorem qg_5_24_eq (p : Params K) :
    W p (ampV5 p) (T p 0 3 (ampV24 p)) = qg_5_24 p := by
  simp [qg_5_24, ampV5, ampV24, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_5_24 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_5_24 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC ^ 2 * nD * RABC * wD - nB * nC * nD * RBCD := by
  simp only [qg_5_24, paramsN] <;> ring

def qg_5_25 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 ^ 2 - p.c1 * p.c2 * p.M33 - 2 * p.c1 * p.c3 * p.M23 - 2 * p.c2 * p.c3 * p.M13 - p.c3 ^ 2 * p.M12 + 2 * p.c3 * p.b + p.M33 * p.M12

theorem qg_5_25_eq (p : Params K) :
    W p (ampV5 p) (T p 0 3 (ampV25 p)) = qg_5_25 p := by
  simp [qg_5_25, ampV5, ampV25, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_5_25 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_5_25 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB ^ 2 * nC * nD ^ 2 * oBD * wC + 2 * nB ^ 2 * nC * nD ^ 2 * RABD * RBCD := by
  simp only [qg_5_25, paramsN] <;> ring

def qg_5_26 (p : Params K) : K :=
  p.c1 * p.c2 ^ 2 * p.c3 + p.c1 * p.c3 * p.M22 + p.c2 ^ 2 * p.M13 - 2 * p.c2 * p.b - p.M22 * p.M13 + 2 * p.M12 * p.M23

theorem qg_5_26_eq (p : Params K) :
    W p (ampV5 p) (T p 0 3 (ampV26 p)) = qg_5_26 p := by
  simp [qg_5_26, ampV5, ampV26, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_5_26 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_5_26 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * wC * wD + nB * nC ^ 2 * nD ^ 2 * oCD * wB - 2 * nB * nC ^ 2 * nD ^ 2 * RACD * RBCD := by
  simp only [qg_5_26, paramsN] <;> ring

def qg_5_27 (p : Params K) : K :=
  p.c1 * p.c2 ^ 2 * p.c3 ^ 2 - p.c1 * p.c2 ^ 2 * p.M33 - 4 * p.c1 * p.c2 * p.c3 * p.M23 - p.c1 * p.c3 ^ 2 * p.M22 + p.c1 * p.M22 * p.M33 - 2 * p.c2 ^ 2 * p.c3 * p.M13 - 2 * p.c2 * p.c3 ^ 2 * p.M12 + 4 * p.c2 * p.c3 * p.b + 2 * p.c2 * p.M33 * p.M12 + 2 * p.c3 * p.M22 * p.M13

theorem qg_5_27_eq (p : Params K) :
    W p (ampV5 p) (T p 0 3 (ampV27 p)) = qg_5_27 p := by
  simp [qg_5_27, ampV5, ampV27, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_5_27 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_5_27 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -2 * nB ^ 2 * nC ^ 2 * nD ^ 3 * oBD * RACD * wC - 2 * nB ^ 2 * nC ^ 2 * nD ^ 3 * oCD * RABD * wB + 4 * nB ^ 2 * nC ^ 2 * nD ^ 3 * RABD * RACD * RBCD + nB ^ 2 * nC ^ 2 * nD ^ 2 * oBD * oCD * RABC := by
  simp only [qg_5_27, paramsN] <;> ring

def qg_6_21 (p : Params K) : K :=
  p.c1 * p.c3 - p.M13

theorem qg_6_21_eq (p : Params K) :
    W p (ampV6 p) (T p 0 3 (ampV21 p)) = qg_6_21 p := by
  simp [qg_6_21, ampV6, ampV21, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_6_21 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_6_21 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * wB := by
  simp only [qg_6_21, paramsN] <;> ring

def qg_6_22 (p : Params K) : K :=
  p.c1 * p.c3 ^ 2 - p.c1 * p.M33 - 2 * p.c3 * p.M13

theorem qg_6_22_eq (p : Params K) :
    W p (ampV6 p) (T p 0 3 (ampV22 p)) = qg_6_22 p := by
  simp [qg_6_22, ampV6, ampV22, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_6_22 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_6_22 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC * nD ^ 2 * RABD * wB - nB ^ 2 * nC * nD * oBD * RABC := by
  simp only [qg_6_22, paramsN] <;> ring

def qg_6_23 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 + p.c1 * p.M23 - p.c2 * p.M13 + p.c3 * p.M12 - p.b

theorem qg_6_23_eq (p : Params K) :
    W p (ampV6 p) (T p 0 3 (ampV23 p)) = qg_6_23 p := by
  simp [qg_6_23, ampV6, ampV23, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_6_23 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_6_23 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB * nC ^ 2 * nD ^ 2 * RACD * wB - nB * nC * nD * RBCD := by
  simp only [qg_6_23, paramsN] <;> ring

def qg_6_24 (p : Params K) : K :=
  p.c1 ^ 2 * p.c3 + p.c3 * p.M11

theorem qg_6_24_eq (p : Params K) :
    W p (ampV6 p) (T p 0 3 (ampV24 p)) = qg_6_24 p := by
  simp [qg_6_24, ampV6, ampV24, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_6_24 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_6_24 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD * oBC * RABD := by
  simp only [qg_6_24, paramsN] <;> ring

def qg_6_25 (p : Params K) : K :=
  p.c1 ^ 2 * p.c3 ^ 2 - p.c1 ^ 2 * p.M33 - 4 * p.c1 * p.c3 * p.M13 - p.c3 ^ 2 * p.M11 - p.M11 * p.M33 + 2 * p.M13 ^ 2

theorem qg_6_25_eq (p : Params K) :
    W p (ampV6 p) (T p 0 3 (ampV25 p)) = qg_6_25 p := by
  simp [qg_6_25, ampV6, ampV25, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_6_25 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_6_25 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * wB ^ 2 - nB ^ 2 * nC * nD * oBC * oBD := by
  simp only [qg_6_25, paramsN] <;> ring

def qg_6_26 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 * p.c3 + p.c1 ^ 2 * p.M23 - 2 * p.c1 * p.b + p.c2 * p.c3 * p.M11 - p.M11 * p.M23 + 2 * p.M12 * p.M13

theorem qg_6_26_eq (p : Params K) :
    W p (ampV6 p) (T p 0 3 (ampV26 p)) = qg_6_26 p := by
  simp [qg_6_26, ampV6, ampV26, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_6_26 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_6_26 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * wB * wC + nB ^ 2 * nC ^ 2 * nD * oBC * wD - 2 * nB ^ 2 * nC ^ 2 * nD * RABC * RBCD := by
  simp only [qg_6_26, paramsN] <;> ring

def qg_6_27 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 * p.c3 ^ 2 - p.c1 ^ 2 * p.c2 * p.M33 - 2 * p.c1 ^ 2 * p.c3 * p.M23 - 4 * p.c1 * p.c2 * p.c3 * p.M13 - 2 * p.c1 * p.c3 ^ 2 * p.M12 + 2 * p.c1 * p.c3 * p.b + 2 * p.c1 * p.M13 * p.M23 - p.c2 * p.c3 ^ 2 * p.M11 - p.c2 * p.M11 * p.M33 + 2 * p.c2 * p.M13 ^ 2 + 2 * p.c3 * p.M12 * p.M13 - 2 * p.M13 * p.b

theorem qg_6_27_eq (p : Params K) :
    W p (ampV6 p) (T p 0 3 (ampV27 p)) = qg_6_27 p := by
  simp [qg_6_27, ampV6, ampV27, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_6_27 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_6_27 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB ^ 2 * nC ^ 2 * nD ^ 2 * oBC * oBD * RACD + 2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * RBCD * wB := by
  simp only [qg_6_27, paramsN] <;> ring

end LemmaB.TableModel
