/- SPDX-License-Identifier: Apache-2.0
   Machine-generated file. -/
module

public import TableModel.Amps

/-! # Table-model identity, part 2 (frames B, D): the model values in the gauge parameters

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

def qg_7_21 (p : Params K) : K :=
  p.c3

theorem qg_7_21_eq (p : Params K) :
    W p (ampV7 p) (T p 1 3 (ampV21 p)) = qg_7_21 p := by
  simp [qg_7_21, ampV7, ampV21, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_7_21 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_7_21 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nD * RABD := by
  simp only [qg_7_21, paramsN] <;> ring

def qg_7_22 (p : Params K) : K :=
  p.c3 ^ 2 + p.M33

theorem qg_7_22_eq (p : Params K) :
    W p (ampV7 p) (T p 1 3 (ampV22 p)) = qg_7_22 p := by
  simp [qg_7_22, ampV7, ampV22, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_7_22 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_7_22 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nD * oBD := by
  simp only [qg_7_22, paramsN] <;> ring

def qg_7_23 (p : Params K) : K :=
  p.c2 * p.c3 - p.M23

theorem qg_7_23_eq (p : Params K) :
    W p (ampV7 p) (T p 1 3 (ampV23 p)) = qg_7_23 p := by
  simp [qg_7_23, ampV7, ampV23, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_7_23 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_7_23 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * wD := by
  simp only [qg_7_23, paramsN] <;> ring

def qg_7_24 (p : Params K) : K :=
  p.c1 * p.c3 - p.M13

theorem qg_7_24_eq (p : Params K) :
    W p (ampV7 p) (T p 1 3 (ampV24 p)) = qg_7_24 p := by
  simp [qg_7_24, ampV7, ampV24, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_7_24 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_7_24 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * wB := by
  simp only [qg_7_24, paramsN] <;> ring

def qg_7_25 (p : Params K) : K :=
  p.c1 * p.c3 ^ 2 + p.c1 * p.M33

theorem qg_7_25_eq (p : Params K) :
    W p (ampV7 p) (T p 1 3 (ampV25 p)) = qg_7_25 p := by
  simp [qg_7_25, ampV7, ampV25, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_7_25 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_7_25 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD * oBD * RABC := by
  simp only [qg_7_25, paramsN] <;> ring

def qg_7_26 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 - p.c1 * p.M23 - p.c2 * p.M13 - p.c3 * p.M12 + p.b

theorem qg_7_26_eq (p : Params K) :
    W p (ampV7 p) (T p 1 3 (ampV26 p)) = qg_7_26 p := by
  simp [qg_7_26, ampV7, ampV26, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_7_26 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_7_26 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * RBCD := by
  simp only [qg_7_26, paramsN] <;> ring

def qg_7_27 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 ^ 2 + p.c1 * p.c2 * p.M33 - p.c3 ^ 2 * p.M12 - p.M33 * p.M12

theorem qg_7_27_eq (p : Params K) :
    W p (ampV7 p) (T p 1 3 (ampV27 p)) = qg_7_27 p := by
  simp [qg_7_27, ampV7, ampV27, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_7_27 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_7_27 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD ^ 2 * oBD * wC := by
  simp only [qg_7_27, paramsN] <;> ring

def qg_8_21 (p : Params K) : K :=
  p.c1 * p.c3 - p.M13

theorem qg_8_21_eq (p : Params K) :
    W p (ampV8 p) (T p 1 3 (ampV21 p)) = qg_8_21 p := by
  simp [qg_8_21, ampV8, ampV21, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_8_21 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_8_21 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * wB := by
  simp only [qg_8_21, paramsN] <;> ring

def qg_8_22 (p : Params K) : K :=
  p.c1 * p.c3 ^ 2 + p.c1 * p.M33

theorem qg_8_22_eq (p : Params K) :
    W p (ampV8 p) (T p 1 3 (ampV22 p)) = qg_8_22 p := by
  simp [qg_8_22, ampV8, ampV22, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_8_22 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_8_22 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD * oBD * RABC := by
  simp only [qg_8_22, paramsN] <;> ring

def qg_8_23 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 - p.c1 * p.M23 - p.c2 * p.M13 - p.c3 * p.M12 + p.b

theorem qg_8_23_eq (p : Params K) :
    W p (ampV8 p) (T p 1 3 (ampV23 p)) = qg_8_23 p := by
  simp [qg_8_23, ampV8, ampV23, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_8_23 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_8_23 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * RBCD := by
  simp only [qg_8_23, paramsN] <;> ring

def qg_8_24 (p : Params K) : K :=
  p.c1 ^ 2 * p.c3 - 2 * p.c1 * p.M13 - p.c3 * p.M11

theorem qg_8_24_eq (p : Params K) :
    W p (ampV8 p) (T p 1 3 (ampV24 p)) = qg_8_24 p := by
  simp [qg_8_24, ampV8, ampV24, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_8_24 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_8_24 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC ^ 2 * nD * RABC * wB - nB ^ 2 * nC * nD * oBC * RABD := by
  simp only [qg_8_24, paramsN] <;> ring

def qg_8_25 (p : Params K) : K :=
  p.c1 ^ 2 * p.c3 ^ 2 + p.c1 ^ 2 * p.M33 + p.c3 ^ 2 * p.M11 + p.M11 * p.M33

theorem qg_8_25_eq (p : Params K) :
    W p (ampV8 p) (T p 1 3 (ampV25 p)) = qg_8_25 p := by
  simp [qg_8_25, ampV8, ampV25, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_8_25 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_8_25 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD * oBC * oBD := by
  simp only [qg_8_25, paramsN] <;> ring

def qg_8_26 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 * p.c3 - p.c1 ^ 2 * p.M23 - 2 * p.c1 * p.c2 * p.M13 - 2 * p.c1 * p.c3 * p.M12 + 2 * p.c1 * p.b - p.c2 * p.c3 * p.M11 + p.M11 * p.M23

theorem qg_8_26_eq (p : Params K) :
    W p (ampV8 p) (T p 1 3 (ampV26 p)) = qg_8_26 p := by
  simp [qg_8_26, ampV8, ampV26, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_8_26 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_8_26 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB ^ 2 * nC ^ 2 * nD * oBC * wD + 2 * nB ^ 2 * nC ^ 2 * nD * RABC * RBCD := by
  simp only [qg_8_26, paramsN] <;> ring

def qg_8_27 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 * p.c3 ^ 2 + p.c1 ^ 2 * p.c2 * p.M33 + p.c2 * p.c3 ^ 2 * p.M11 + p.c2 * p.M11 * p.M33

theorem qg_8_27_eq (p : Params K) :
    W p (ampV8 p) (T p 1 3 (ampV27 p)) = qg_8_27 p := by
  simp [qg_8_27, ampV8, ampV27, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_8_27 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_8_27 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC ^ 2 * nD ^ 2 * oBC * oBD * RACD := by
  simp only [qg_8_27, paramsN] <;> ring

def qg_9_21 (p : Params K) : K :=
  p.c3 ^ 2 + p.M33

theorem qg_9_21_eq (p : Params K) :
    W p (ampV9 p) (T p 1 3 (ampV21 p)) = qg_9_21 p := by
  simp [qg_9_21, ampV9, ampV21, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_9_21 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_9_21 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nD * oBD := by
  simp only [qg_9_21, paramsN] <;> ring

def qg_9_22 (p : Params K) : K :=
  p.c3 ^ 3 + p.c3 * p.M33

theorem qg_9_22_eq (p : Params K) :
    W p (ampV9 p) (T p 1 3 (ampV22 p)) = qg_9_22 p := by
  simp [qg_9_22, ampV9, ampV22, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_9_22 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_9_22 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nD ^ 2 * oBD * RABD := by
  simp only [qg_9_22, paramsN] <;> ring

def qg_9_23 (p : Params K) : K :=
  p.c2 * p.c3 ^ 2 + p.c2 * p.M33

theorem qg_9_23_eq (p : Params K) :
    W p (ampV9 p) (T p 1 3 (ampV23 p)) = qg_9_23 p := by
  simp [qg_9_23, ampV9, ampV23, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_9_23 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_9_23 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD ^ 2 * oBD * RACD := by
  simp only [qg_9_23, paramsN] <;> ring

def qg_9_24 (p : Params K) : K :=
  p.c1 * p.c3 ^ 2 + p.c1 * p.M33

theorem qg_9_24_eq (p : Params K) :
    W p (ampV9 p) (T p 1 3 (ampV24 p)) = qg_9_24 p := by
  simp [qg_9_24, ampV9, ampV24, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_9_24 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_9_24 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD * oBD * RABC := by
  simp only [qg_9_24, paramsN] <;> ring

def qg_9_25 (p : Params K) : K :=
  p.c1 * p.c3 ^ 3 + p.c1 * p.c3 * p.M33 - p.c3 ^ 2 * p.M13 - p.M33 * p.M13

theorem qg_9_25_eq (p : Params K) :
    W p (ampV9 p) (T p 1 3 (ampV25 p)) = qg_9_25 p := by
  simp [qg_9_25, ampV9, ampV25, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_9_25 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_9_25 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD ^ 2 * oBD * wB := by
  simp only [qg_9_25, paramsN] <;> ring

def qg_9_26 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 ^ 2 + p.c1 * p.c2 * p.M33 - p.c3 ^ 2 * p.M12 - p.M33 * p.M12

theorem qg_9_26_eq (p : Params K) :
    W p (ampV9 p) (T p 1 3 (ampV26 p)) = qg_9_26 p := by
  simp [qg_9_26, ampV9, ampV26, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_9_26 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_9_26 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD ^ 2 * oBD * wC := by
  simp only [qg_9_26, paramsN] <;> ring

def qg_9_27 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 ^ 3 + p.c1 * p.c2 * p.c3 * p.M33 - p.c1 * p.c3 ^ 2 * p.M23 - p.c1 * p.M33 * p.M23 - p.c2 * p.c3 ^ 2 * p.M13 - p.c2 * p.M33 * p.M13 - p.c3 ^ 3 * p.M12 + p.c3 ^ 2 * p.b - p.c3 * p.M33 * p.M12 + p.M33 * p.b

theorem qg_9_27_eq (p : Params K) :
    W p (ampV9 p) (T p 1 3 (ampV27 p)) = qg_9_27 p := by
  simp [qg_9_27, ampV9, ampV27, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_9_27 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_9_27 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD ^ 2 * oBD * RBCD := by
  simp only [qg_9_27, paramsN] <;> ring

def qg_10_21 (p : Params K) : K :=
  p.c2 * p.c3 + p.M23

theorem qg_10_21_eq (p : Params K) :
    W p (ampV10 p) (T p 1 3 (ampV21 p)) = qg_10_21 p := by
  simp [qg_10_21, ampV10, ampV21, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_10_21 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_10_21 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB * nC * nD ^ 2 * RABD * RACD - nB * nC * nD * wD := by
  simp only [qg_10_21, paramsN] <;> ring

def qg_10_22 (p : Params K) : K :=
  p.c2 * p.c3 ^ 2 + p.c2 * p.M33

theorem qg_10_22_eq (p : Params K) :
    W p (ampV10 p) (T p 1 3 (ampV22 p)) = qg_10_22 p := by
  simp [qg_10_22, ampV10, ampV22, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_10_22 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_10_22 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD ^ 2 * oBD * RACD := by
  simp only [qg_10_22, paramsN] <;> ring

def qg_10_23 (p : Params K) : K :=
  p.c2 ^ 2 * p.c3 + p.c3 * p.M22

theorem qg_10_23_eq (p : Params K) :
    W p (ampV10 p) (T p 1 3 (ampV23 p)) = qg_10_23 p := by
  simp [qg_10_23, ampV10, ampV23, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_10_23 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_10_23 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD ^ 2 * oCD * RABD := by
  simp only [qg_10_23, paramsN] <;> ring

def qg_10_24 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 + p.c1 * p.M23 - p.c2 * p.M13 + p.c3 * p.M12 + p.b

theorem qg_10_24_eq (p : Params K) :
    W p (ampV10 p) (T p 1 3 (ampV24 p)) = qg_10_24 p := by
  simp [qg_10_24, ampV10, ampV24, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_10_24 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_10_24 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      4 * nB ^ 2 * nC ^ 2 * nD ^ 2 * RABC * RABD * RACD - 2 * nB ^ 2 * nC ^ 2 * nD * RABC * wD - 2 * nB ^ 2 * nC * nD ^ 2 * RABD * wC + nB * nC * nD * RBCD := by
  simp only [qg_10_24, paramsN] <;> ring

def qg_10_25 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 ^ 2 + p.c1 * p.c2 * p.M33 - p.c3 ^ 2 * p.M12 - p.M33 * p.M12

theorem qg_10_25_eq (p : Params K) :
    W p (ampV10 p) (T p 1 3 (ampV25 p)) = qg_10_25 p := by
  simp [qg_10_25, ampV10, ampV25, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_10_25 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_10_25 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD ^ 2 * oBD * wC := by
  simp only [qg_10_25, paramsN] <;> ring

def qg_10_26 (p : Params K) : K :=
  p.c1 * p.c2 ^ 2 * p.c3 + p.c1 * p.c3 * p.M22 - p.c2 ^ 2 * p.M13 + 2 * p.c2 * p.b + p.M22 * p.M13 - 2 * p.M12 * p.M23

theorem qg_10_26_eq (p : Params K) :
    W p (ampV10 p) (T p 1 3 (ampV26 p)) = qg_10_26 p := by
  simp [qg_10_26, ampV10, ampV26, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_10_26 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_10_26 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * oCD * RABC * RABD - 2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * wC * wD - nB * nC ^ 2 * nD ^ 2 * oCD * wB + 2 * nB * nC ^ 2 * nD ^ 2 * RACD * RBCD := by
  simp only [qg_10_26, paramsN] <;> ring

def qg_10_27 (p : Params K) : K :=
  p.c1 * p.c2 ^ 2 * p.c3 ^ 2 + p.c1 * p.c2 ^ 2 * p.M33 - p.c1 * p.c3 ^ 2 * p.M22 - p.c1 * p.M22 * p.M33 - 2 * p.c2 * p.c3 ^ 2 * p.M12 - 2 * p.c2 * p.M33 * p.M12

theorem qg_10_27_eq (p : Params K) :
    W p (ampV10 p) (T p 1 3 (ampV27 p)) = qg_10_27 p := by
  simp [qg_10_27, ampV10, ampV27, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_10_27 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_10_27 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC ^ 2 * nD ^ 3 * oBD * RACD * wC - nB ^ 2 * nC ^ 2 * nD ^ 2 * oBD * oCD * RABC := by
  simp only [qg_10_27, paramsN] <;> ring

def qg_11_21 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 - p.c1 * p.M23 - p.c2 * p.M13 - p.c3 * p.M12 + p.b

theorem qg_11_21_eq (p : Params K) :
    W p (ampV11 p) (T p 1 3 (ampV21 p)) = qg_11_21 p := by
  simp [qg_11_21, ampV11, ampV21, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_11_21 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_11_21 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * RBCD := by
  simp only [qg_11_21, paramsN] <;> ring

def qg_11_22 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 ^ 2 + p.c1 * p.c2 * p.M33 - p.c3 ^ 2 * p.M12 - p.M33 * p.M12

theorem qg_11_22_eq (p : Params K) :
    W p (ampV11 p) (T p 1 3 (ampV22 p)) = qg_11_22 p := by
  simp [qg_11_22, ampV11, ampV22, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_11_22 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_11_22 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD ^ 2 * oBD * wC := by
  simp only [qg_11_22, paramsN] <;> ring

def qg_11_23 (p : Params K) : K :=
  p.c1 * p.c2 ^ 2 * p.c3 - 2 * p.c1 * p.c2 * p.M23 - p.c1 * p.c3 * p.M22 - p.c2 ^ 2 * p.M13 - 2 * p.c2 * p.c3 * p.M12 + 2 * p.c2 * p.b + p.M22 * p.M13

theorem qg_11_23_eq (p : Params K) :
    W p (ampV11 p) (T p 1 3 (ampV23 p)) = qg_11_23 p := by
  simp [qg_11_23, ampV11, ampV23, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_11_23 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_11_23 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB * nC ^ 2 * nD ^ 2 * oCD * wB + 2 * nB * nC ^ 2 * nD ^ 2 * RACD * RBCD := by
  simp only [qg_11_23, paramsN] <;> ring

def qg_11_24 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 * p.c3 - p.c1 ^ 2 * p.M23 - 2 * p.c1 * p.c2 * p.M13 - 2 * p.c1 * p.c3 * p.M12 - p.c2 * p.c3 * p.M11 - p.M11 * p.M23 + 2 * p.M12 * p.M13

theorem qg_11_24_eq (p : Params K) :
    W p (ampV11 p) (T p 1 3 (ampV24 p)) = qg_11_24 p := by
  simp [qg_11_24, ampV11, ampV24, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_11_24 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_11_24 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * oBC * RABD * RACD + 2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * wB * wC + nB ^ 2 * nC ^ 2 * nD * oBC * wD := by
  simp only [qg_11_24, paramsN] <;> ring

def qg_11_25 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 * p.c3 ^ 2 + p.c1 ^ 2 * p.c2 * p.M33 + p.c2 * p.c3 ^ 2 * p.M11 + p.c2 * p.M11 * p.M33

theorem qg_11_25_eq (p : Params K) :
    W p (ampV11 p) (T p 1 3 (ampV25 p)) = qg_11_25 p := by
  simp [qg_11_25, ampV11, ampV25, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_11_25 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_11_25 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC ^ 2 * nD ^ 2 * oBC * oBD * RACD := by
  simp only [qg_11_25, paramsN] <;> ring

def qg_11_26 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 ^ 2 * p.c3 - 2 * p.c1 ^ 2 * p.c2 * p.M23 - p.c1 ^ 2 * p.c3 * p.M22 - 2 * p.c1 * p.c2 ^ 2 * p.M13 - 4 * p.c1 * p.c2 * p.c3 * p.M12 + 2 * p.c1 * p.c2 * p.b + 2 * p.c1 * p.M12 * p.M23 - p.c2 ^ 2 * p.c3 * p.M11 + 2 * p.c2 * p.M12 * p.M13 - p.c3 * p.M11 * p.M22 + 2 * p.c3 * p.M12 ^ 2 - 2 * p.M12 * p.b

theorem qg_11_26_eq (p : Params K) :
    W p (ampV11 p) (T p 1 3 (ampV26 p)) = qg_11_26 p := by
  simp [qg_11_26, ampV11, ampV26, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_11_26 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_11_26 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB ^ 2 * nC ^ 2 * nD ^ 2 * oBC * oCD * RABD + 2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * RBCD * wC := by
  simp only [qg_11_26, paramsN] <;> ring

def qg_11_27 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 ^ 2 * p.c3 ^ 2 + p.c1 ^ 2 * p.c2 ^ 2 * p.M33 + p.c1 ^ 2 * p.c3 ^ 2 * p.M22 + p.c1 ^ 2 * p.M22 * p.M33 + p.c2 ^ 2 * p.c3 ^ 2 * p.M11 + p.c2 ^ 2 * p.M11 * p.M33 + p.c3 ^ 2 * p.M11 * p.M22 + p.M11 * p.M22 * p.M33

theorem qg_11_27_eq (p : Params K) :
    W p (ampV11 p) (T p 1 3 (ampV27 p)) = qg_11_27 p := by
  simp [qg_11_27, ampV11, ampV27, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_11_27 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_11_27 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC ^ 2 * nD ^ 2 * oBC * oBD * oCD := by
  simp only [qg_11_27, paramsN] <;> ring

def qg_12_21 (p : Params K) : K :=
  p.c2 * p.c3 ^ 2 + p.c2 * p.M33

theorem qg_12_21_eq (p : Params K) :
    W p (ampV12 p) (T p 1 3 (ampV21 p)) = qg_12_21 p := by
  simp [qg_12_21, ampV12, ampV21, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_12_21 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_12_21 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD ^ 2 * oBD * RACD := by
  simp only [qg_12_21, paramsN] <;> ring

def qg_12_22 (p : Params K) : K :=
  p.c2 * p.c3 ^ 3 + p.c2 * p.c3 * p.M33 - p.c3 ^ 2 * p.M23 - p.M33 * p.M23

theorem qg_12_22_eq (p : Params K) :
    W p (ampV12 p) (T p 1 3 (ampV22 p)) = qg_12_22 p := by
  simp [qg_12_22, ampV12, ampV22, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_12_22 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_12_22 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD ^ 2 * oBD * wD := by
  simp only [qg_12_22, paramsN] <;> ring

def qg_12_23 (p : Params K) : K :=
  p.c2 ^ 2 * p.c3 ^ 2 + p.c2 ^ 2 * p.M33 + p.c3 ^ 2 * p.M22 + p.M22 * p.M33

theorem qg_12_23_eq (p : Params K) :
    W p (ampV12 p) (T p 1 3 (ampV23 p)) = qg_12_23 p := by
  simp [qg_12_23, ampV12, ampV23, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_12_23 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_12_23 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD ^ 2 * oBD * oCD := by
  simp only [qg_12_23, paramsN] <;> ring

def qg_12_24 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 ^ 2 + p.c1 * p.c2 * p.M33 + p.c3 ^ 2 * p.M12 + p.M33 * p.M12

theorem qg_12_24_eq (p : Params K) :
    W p (ampV12 p) (T p 1 3 (ampV24 p)) = qg_12_24 p := by
  simp [qg_12_24, ampV12, ampV24, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_12_24 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_12_24 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * oBD * RABC * RACD - nB ^ 2 * nC * nD ^ 2 * oBD * wC := by
  simp only [qg_12_24, paramsN] <;> ring

def qg_12_25 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 ^ 3 + p.c1 * p.c2 * p.c3 * p.M33 - p.c1 * p.c3 ^ 2 * p.M23 - p.c1 * p.M33 * p.M23 - p.c2 * p.c3 ^ 2 * p.M13 - p.c2 * p.M33 * p.M13 - p.c3 ^ 3 * p.M12 + p.c3 ^ 2 * p.b - p.c3 * p.M33 * p.M12 + p.M33 * p.b

theorem qg_12_25_eq (p : Params K) :
    W p (ampV12 p) (T p 1 3 (ampV25 p)) = qg_12_25 p := by
  simp [qg_12_25, ampV12, ampV25, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_12_25 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_12_25 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD ^ 2 * oBD * RBCD := by
  simp only [qg_12_25, paramsN] <;> ring

def qg_12_26 (p : Params K) : K :=
  p.c1 * p.c2 ^ 2 * p.c3 ^ 2 + p.c1 * p.c2 ^ 2 * p.M33 + p.c1 * p.c3 ^ 2 * p.M22 + p.c1 * p.M22 * p.M33

theorem qg_12_26_eq (p : Params K) :
    W p (ampV12 p) (T p 1 3 (ampV26 p)) = qg_12_26 p := by
  simp [qg_12_26, ampV12, ampV26, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_12_26 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_12_26 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC ^ 2 * nD ^ 2 * oBD * oCD * RABC := by
  simp only [qg_12_26, paramsN] <;> ring

def qg_12_27 (p : Params K) : K :=
  p.c1 * p.c2 ^ 2 * p.c3 ^ 3 + p.c1 * p.c2 ^ 2 * p.c3 * p.M33 - 2 * p.c1 * p.c2 * p.c3 ^ 2 * p.M23 - 2 * p.c1 * p.c2 * p.M33 * p.M23 - p.c1 * p.c3 ^ 3 * p.M22 - p.c1 * p.c3 * p.M22 * p.M33 - p.c2 ^ 2 * p.c3 ^ 2 * p.M13 - p.c2 ^ 2 * p.M33 * p.M13 - 2 * p.c2 * p.c3 ^ 3 * p.M12 + 2 * p.c2 * p.c3 ^ 2 * p.b - 2 * p.c2 * p.c3 * p.M33 * p.M12 + 2 * p.c2 * p.M33 * p.b + p.c3 ^ 2 * p.M22 * p.M13 + p.M22 * p.M33 * p.M13

theorem qg_12_27_eq (p : Params K) :
    W p (ampV12 p) (T p 1 3 (ampV27 p)) = qg_12_27 p := by
  simp [qg_12_27, ampV12, ampV27, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_12_27 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_12_27 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB ^ 2 * nC ^ 2 * nD ^ 3 * oBD * oCD * wB + 2 * nB ^ 2 * nC ^ 2 * nD ^ 3 * oBD * RACD * RBCD := by
  simp only [qg_12_27, paramsN] <;> ring

def qg_13_21 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 ^ 2 - p.c1 * p.c2 * p.M33 - 2 * p.c1 * p.c3 * p.M23 - 2 * p.c2 * p.c3 * p.M13 - p.c3 ^ 2 * p.M12 + 2 * p.c3 * p.b + p.M33 * p.M12

theorem qg_13_21_eq (p : Params K) :
    W p (ampV13 p) (T p 1 3 (ampV21 p)) = qg_13_21 p := by
  simp [qg_13_21, ampV13, ampV21, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_13_21 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_13_21 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB ^ 2 * nC * nD ^ 2 * oBD * wC + 2 * nB ^ 2 * nC * nD ^ 2 * RABD * RBCD := by
  simp only [qg_13_21, paramsN] <;> ring

def qg_13_22 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 ^ 3 + p.c1 * p.c2 * p.c3 * p.M33 - p.c1 * p.c3 ^ 2 * p.M23 - p.c1 * p.M33 * p.M23 - p.c2 * p.c3 ^ 2 * p.M13 - p.c2 * p.M33 * p.M13 - p.c3 ^ 3 * p.M12 + p.c3 ^ 2 * p.b - p.c3 * p.M33 * p.M12 + p.M33 * p.b

theorem qg_13_22_eq (p : Params K) :
    W p (ampV13 p) (T p 1 3 (ampV22 p)) = qg_13_22 p := by
  simp [qg_13_22, ampV13, ampV22, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_13_22 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_13_22 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD ^ 2 * oBD * RBCD := by
  simp only [qg_13_22, paramsN] <;> ring

def qg_13_23 (p : Params K) : K :=
  p.c1 * p.c2 ^ 2 * p.c3 ^ 2 - p.c1 * p.c2 ^ 2 * p.M33 - 4 * p.c1 * p.c2 * p.c3 * p.M23 - p.c1 * p.c3 ^ 2 * p.M22 - p.c1 * p.M22 * p.M33 + 2 * p.c1 * p.M23 ^ 2 - 2 * p.c2 ^ 2 * p.c3 * p.M13 - 2 * p.c2 * p.c3 ^ 2 * p.M12 + 2 * p.c2 * p.c3 * p.b + 2 * p.c2 * p.M13 * p.M23 + 2 * p.c3 * p.M12 * p.M23 - 2 * p.M23 * p.b

theorem qg_13_23_eq (p : Params K) :
    W p (ampV13 p) (T p 1 3 (ampV23 p)) = qg_13_23 p := by
  simp [qg_13_23, ampV13, ampV23, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_13_23 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_13_23 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB ^ 2 * nC ^ 2 * nD ^ 2 * oBD * oCD * RABC + 2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * RBCD * wD := by
  simp only [qg_13_23, paramsN] <;> ring

def qg_13_24 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 * p.c3 ^ 2 - p.c1 ^ 2 * p.c2 * p.M33 - 2 * p.c1 ^ 2 * p.c3 * p.M23 - 4 * p.c1 * p.c2 * p.c3 * p.M13 - 2 * p.c1 * p.c3 ^ 2 * p.M12 + 2 * p.c1 * p.c3 * p.b + 2 * p.c1 * p.M13 * p.M23 - p.c2 * p.c3 ^ 2 * p.M11 - p.c2 * p.M11 * p.M33 + 2 * p.c2 * p.M13 ^ 2 + 2 * p.c3 * p.M12 * p.M13 - 2 * p.M13 * p.b

theorem qg_13_24_eq (p : Params K) :
    W p (ampV13 p) (T p 1 3 (ampV24 p)) = qg_13_24 p := by
  simp [qg_13_24, ampV13, ampV24, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_13_24 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_13_24 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB ^ 2 * nC ^ 2 * nD ^ 2 * oBC * oBD * RACD + 2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * RBCD * wB := by
  simp only [qg_13_24, paramsN] <;> ring

def qg_13_25 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 * p.c3 ^ 3 + p.c1 ^ 2 * p.c2 * p.c3 * p.M33 - p.c1 ^ 2 * p.c3 ^ 2 * p.M23 - p.c1 ^ 2 * p.M33 * p.M23 + p.c2 * p.c3 ^ 3 * p.M11 + p.c2 * p.c3 * p.M11 * p.M33 - p.c3 ^ 2 * p.M11 * p.M23 - p.M11 * p.M33 * p.M23

theorem qg_13_25_eq (p : Params K) :
    W p (ampV13 p) (T p 1 3 (ampV25 p)) = qg_13_25 p := by
  simp [qg_13_25, ampV13, ampV25, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_13_25 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_13_25 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 3 * nC ^ 2 * nD ^ 2 * oBC * oBD * wD := by
  simp only [qg_13_25, paramsN] <;> ring

def qg_13_26 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 ^ 2 * p.c3 ^ 2 - p.c1 ^ 2 * p.c2 ^ 2 * p.M33 - 4 * p.c1 ^ 2 * p.c2 * p.c3 * p.M23 - p.c1 ^ 2 * p.c3 ^ 2 * p.M22 - p.c1 ^ 2 * p.M22 * p.M33 + 2 * p.c1 ^ 2 * p.M23 ^ 2 - 4 * p.c1 * p.c2 ^ 2 * p.c3 * p.M13 - 4 * p.c1 * p.c2 * p.c3 ^ 2 * p.M12 + 4 * p.c1 * p.c2 * p.c3 * p.b + 4 * p.c1 * p.c2 * p.M13 * p.M23 + 4 * p.c1 * p.c3 * p.M12 * p.M23 - 4 * p.c1 * p.M23 * p.b - p.c2 ^ 2 * p.c3 ^ 2 * p.M11 - p.c2 ^ 2 * p.M11 * p.M33 + 2 * p.c2 ^ 2 * p.M13 ^ 2 + 4 * p.c2 * p.c3 * p.M12 * p.M13 - 4 * p.c2 * p.M13 * p.b - p.c3 ^ 2 * p.M11 * p.M22 + 2 * p.c3 ^ 2 * p.M12 ^ 2 - 4 * p.c3 * p.M12 * p.b - p.M11 * p.M22 * p.M33 + 2 * p.b ^ 2

theorem qg_13_26_eq (p : Params K) :
    W p (ampV13 p) (T p 1 3 (ampV26 p)) = qg_13_26 p := by
  simp [qg_13_26, ampV13, ampV26, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_13_26 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_13_26 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB ^ 2 * nC ^ 2 * nD ^ 2 * oBC * oBD * oCD + 2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * RBCD ^ 2 := by
  simp only [qg_13_26, paramsN] <;> ring

def qg_13_27 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 ^ 2 * p.c3 ^ 3 + p.c1 ^ 2 * p.c2 ^ 2 * p.c3 * p.M33 + p.c1 ^ 2 * p.c3 ^ 3 * p.M22 + p.c1 ^ 2 * p.c3 * p.M22 * p.M33 + p.c2 ^ 2 * p.c3 ^ 3 * p.M11 + p.c2 ^ 2 * p.c3 * p.M11 * p.M33 + p.c3 ^ 3 * p.M11 * p.M22 + p.c3 * p.M11 * p.M22 * p.M33

theorem qg_13_27_eq (p : Params K) :
    W p (ampV13 p) (T p 1 3 (ampV27 p)) = qg_13_27 p := by
  simp [qg_13_27, ampV13, ampV27, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_13_27 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_13_27 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 3 * nC ^ 2 * nD ^ 3 * oBC * oBD * oCD * RABD := by
  simp only [qg_13_27, paramsN] <;> ring

end LemmaB.TableModel
