/- SPDX-License-Identifier: Apache-2.0
   Machine-generated file. -/
module

public import TableModel.Amps

/-! # Table-model identity, part 2 (frames D, D): the model values in the gauge parameters

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

def qg_21_21 (p : Params K) : K :=
  p.mD

theorem qg_21_21_eq (p : Params K) :
    W p (ampV21 p) (T p 3 3 (ampV21 p)) = qg_21_21 p := by
  simp [qg_21_21, ampV21, ampV21, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_21_21 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_21_21 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nD := by
  simp only [qg_21_21, paramsN] <;> ring

def qg_21_22 (p : Params K) : K :=
  p.mD * p.c3

theorem qg_21_22_eq (p : Params K) :
    W p (ampV21 p) (T p 3 3 (ampV22 p)) = qg_21_22 p := by
  simp [qg_21_22, ampV21, ampV22, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_21_22 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_21_22 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nD ^ 2 * RABD := by
  simp only [qg_21_22, paramsN] <;> ring

def qg_21_23 (p : Params K) : K :=
  p.mD * p.c2

theorem qg_21_23_eq (p : Params K) :
    W p (ampV21 p) (T p 3 3 (ampV23 p)) = qg_21_23 p := by
  simp [qg_21_23, ampV21, ampV23, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_21_23 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_21_23 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nC * nD ^ 2 * RACD := by
  simp only [qg_21_23, paramsN] <;> ring

def qg_21_24 (p : Params K) : K :=
  p.mD * p.c1

theorem qg_21_24_eq (p : Params K) :
    W p (ampV21 p) (T p 3 3 (ampV24 p)) = qg_21_24 p := by
  simp [qg_21_24, ampV21, ampV24, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_21_24 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_21_24 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * RABC := by
  simp only [qg_21_24, paramsN] <;> ring

def qg_21_25 (p : Params K) : K :=
  p.mD * p.c1 * p.c3 - p.mD * p.M13

theorem qg_21_25_eq (p : Params K) :
    W p (ampV21 p) (T p 3 3 (ampV25 p)) = qg_21_25 p := by
  simp [qg_21_25, ampV21, ampV25, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_21_25 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_21_25 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD ^ 2 * wB := by
  simp only [qg_21_25, paramsN] <;> ring

def qg_21_26 (p : Params K) : K :=
  p.mD * p.c1 * p.c2 - p.mD * p.M12

theorem qg_21_26_eq (p : Params K) :
    W p (ampV21 p) (T p 3 3 (ampV26 p)) = qg_21_26 p := by
  simp [qg_21_26, ampV21, ampV26, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_21_26 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_21_26 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD ^ 2 * wC := by
  simp only [qg_21_26, paramsN] <;> ring

def qg_21_27 (p : Params K) : K :=
  p.mD * p.c1 * p.c2 * p.c3 - p.mD * p.c1 * p.M23 - p.mD * p.c2 * p.M13 - p.mD * p.c3 * p.M12 + p.mD * p.b

theorem qg_21_27_eq (p : Params K) :
    W p (ampV21 p) (T p 3 3 (ampV27 p)) = qg_21_27 p := by
  simp [qg_21_27, ampV21, ampV27, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_21_27 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_21_27 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD ^ 2 * RBCD := by
  simp only [qg_21_27, paramsN] <;> ring

def qg_22_22 (p : Params K) : K :=
  p.mD * p.c3 ^ 2 + p.mD * p.M33

theorem qg_22_22_eq (p : Params K) :
    W p (ampV22 p) (T p 3 3 (ampV22 p)) = qg_22_22 p := by
  simp [qg_22_22, ampV22, ampV22, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_22_22 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_22_22 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nD ^ 2 * oBD := by
  simp only [qg_22_22, paramsN] <;> ring

def qg_22_23 (p : Params K) : K :=
  p.mD * p.c2 * p.c3 - p.mD * p.M23

theorem qg_22_23_eq (p : Params K) :
    W p (ampV22 p) (T p 3 3 (ampV23 p)) = qg_22_23 p := by
  simp [qg_22_23, ampV22, ampV23, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_22_23 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_22_23 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD ^ 2 * wD := by
  simp only [qg_22_23, paramsN] <;> ring

def qg_22_24 (p : Params K) : K :=
  p.mD * p.c1 * p.c3 - p.mD * p.M13

theorem qg_22_24_eq (p : Params K) :
    W p (ampV22 p) (T p 3 3 (ampV24 p)) = qg_22_24 p := by
  simp [qg_22_24, ampV22, ampV24, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_22_24 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_22_24 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD ^ 2 * wB := by
  simp only [qg_22_24, paramsN] <;> ring

def qg_22_25 (p : Params K) : K :=
  p.mD * p.c1 * p.c3 ^ 2 + p.mD * p.c1 * p.M33

theorem qg_22_25_eq (p : Params K) :
    W p (ampV22 p) (T p 3 3 (ampV25 p)) = qg_22_25 p := by
  simp [qg_22_25, ampV22, ampV25, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_22_25 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_22_25 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD ^ 2 * oBD * RABC := by
  simp only [qg_22_25, paramsN] <;> ring

def qg_22_26 (p : Params K) : K :=
  p.mD * p.c1 * p.c2 * p.c3 - p.mD * p.c1 * p.M23 - p.mD * p.c2 * p.M13 - p.mD * p.c3 * p.M12 + p.mD * p.b

theorem qg_22_26_eq (p : Params K) :
    W p (ampV22 p) (T p 3 3 (ampV26 p)) = qg_22_26 p := by
  simp [qg_22_26, ampV22, ampV26, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_22_26 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_22_26 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD ^ 2 * RBCD := by
  simp only [qg_22_26, paramsN] <;> ring

def qg_22_27 (p : Params K) : K :=
  p.mD * p.c1 * p.c2 * p.c3 ^ 2 + p.mD * p.c1 * p.c2 * p.M33 - p.mD * p.c3 ^ 2 * p.M12 - p.mD * p.M33 * p.M12

theorem qg_22_27_eq (p : Params K) :
    W p (ampV22 p) (T p 3 3 (ampV27 p)) = qg_22_27 p := by
  simp [qg_22_27, ampV22, ampV27, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_22_27 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_22_27 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD ^ 3 * oBD * wC := by
  simp only [qg_22_27, paramsN] <;> ring

def qg_23_23 (p : Params K) : K :=
  p.mD * p.c2 ^ 2 + p.mD * p.M22

theorem qg_23_23_eq (p : Params K) :
    W p (ampV23 p) (T p 3 3 (ampV23 p)) = qg_23_23 p := by
  simp [qg_23_23, ampV23, ampV23, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_23_23 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_23_23 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nC * nD ^ 2 * oCD := by
  simp only [qg_23_23, paramsN] <;> ring

def qg_23_24 (p : Params K) : K :=
  p.mD * p.c1 * p.c2 + p.mD * p.M12

theorem qg_23_24_eq (p : Params K) :
    W p (ampV23 p) (T p 3 3 (ampV24 p)) = qg_23_24 p := by
  simp [qg_23_24, ampV23, ampV24, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_23_24 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_23_24 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB * nC ^ 2 * nD ^ 2 * RABC * RACD - nB * nC * nD ^ 2 * wC := by
  simp only [qg_23_24, paramsN] <;> ring

def qg_23_25 (p : Params K) : K :=
  p.mD * p.c1 * p.c2 * p.c3 - p.mD * p.c1 * p.M23 - p.mD * p.c2 * p.M13 - p.mD * p.c3 * p.M12 + p.mD * p.b

theorem qg_23_25_eq (p : Params K) :
    W p (ampV23 p) (T p 3 3 (ampV25 p)) = qg_23_25 p := by
  simp [qg_23_25, ampV23, ampV25, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_23_25 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_23_25 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD ^ 2 * RBCD := by
  simp only [qg_23_25, paramsN] <;> ring

def qg_23_26 (p : Params K) : K :=
  p.mD * p.c1 * p.c2 ^ 2 + p.mD * p.c1 * p.M22

theorem qg_23_26_eq (p : Params K) :
    W p (ampV23 p) (T p 3 3 (ampV26 p)) = qg_23_26 p := by
  simp [qg_23_26, ampV23, ampV26, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_23_26 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_23_26 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * nD ^ 2 * oCD * RABC := by
  simp only [qg_23_26, paramsN] <;> ring

def qg_23_27 (p : Params K) : K :=
  p.mD * p.c1 * p.c2 ^ 2 * p.c3 - 2 * p.mD * p.c1 * p.c2 * p.M23 - p.mD * p.c1 * p.c3 * p.M22 - p.mD * p.c2 ^ 2 * p.M13 - 2 * p.mD * p.c2 * p.c3 * p.M12 + 2 * p.mD * p.c2 * p.b + p.mD * p.M22 * p.M13

theorem qg_23_27_eq (p : Params K) :
    W p (ampV23 p) (T p 3 3 (ampV27 p)) = qg_23_27 p := by
  simp [qg_23_27, ampV23, ampV27, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_23_27 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_23_27 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB * nC ^ 2 * nD ^ 3 * oCD * wB + 2 * nB * nC ^ 2 * nD ^ 3 * RACD * RBCD := by
  simp only [qg_23_27, paramsN] <;> ring

def qg_24_24 (p : Params K) : K :=
  p.mD * p.c1 ^ 2 + p.mD * p.M11

theorem qg_24_24_eq (p : Params K) :
    W p (ampV24 p) (T p 3 3 (ampV24 p)) = qg_24_24 p := by
  simp [qg_24_24, ampV24, ampV24, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_24_24 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_24_24 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * oBC := by
  simp only [qg_24_24, paramsN] <;> ring

def qg_24_25 (p : Params K) : K :=
  p.mD * p.c1 ^ 2 * p.c3 - 2 * p.mD * p.c1 * p.M13 - p.mD * p.c3 * p.M11

theorem qg_24_25_eq (p : Params K) :
    W p (ampV24 p) (T p 3 3 (ampV25 p)) = qg_24_25 p := by
  simp [qg_24_25, ampV24, ampV25, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_24_25 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_24_25 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * RABC * wB - nB ^ 2 * nC * nD ^ 2 * oBC * RABD := by
  simp only [qg_24_25, paramsN] <;> ring

def qg_24_26 (p : Params K) : K :=
  p.mD * p.c1 ^ 2 * p.c2 + p.mD * p.c2 * p.M11

theorem qg_24_26_eq (p : Params K) :
    W p (ampV24 p) (T p 3 3 (ampV26 p)) = qg_24_26 p := by
  simp [qg_24_26, ampV24, ampV26, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_24_26 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_24_26 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * nD ^ 2 * oBC * RACD := by
  simp only [qg_24_26, paramsN] <;> ring

def qg_24_27 (p : Params K) : K :=
  p.mD * p.c1 ^ 2 * p.c2 * p.c3 - p.mD * p.c1 ^ 2 * p.M23 - 2 * p.mD * p.c1 * p.c2 * p.M13 - 2 * p.mD * p.c1 * p.c3 * p.M12 - p.mD * p.c2 * p.c3 * p.M11 - p.mD * p.M11 * p.M23 + 2 * p.mD * p.M12 * p.M13

theorem qg_24_27_eq (p : Params K) :
    W p (ampV24 p) (T p 3 3 (ampV27 p)) = qg_24_27 p := by
  simp [qg_24_27, ampV24, ampV27, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_24_27 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_24_27 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -2 * nB ^ 2 * nC ^ 2 * nD ^ 3 * oBC * RABD * RACD + 2 * nB ^ 2 * nC ^ 2 * nD ^ 3 * wB * wC + nB ^ 2 * nC ^ 2 * nD ^ 2 * oBC * wD := by
  simp only [qg_24_27, paramsN] <;> ring

def qg_25_25 (p : Params K) : K :=
  p.mD * p.c1 ^ 2 * p.c3 ^ 2 + p.mD * p.c1 ^ 2 * p.M33 + p.mD * p.c3 ^ 2 * p.M11 + p.mD * p.M11 * p.M33

theorem qg_25_25_eq (p : Params K) :
    W p (ampV25 p) (T p 3 3 (ampV25 p)) = qg_25_25 p := by
  simp [qg_25_25, ampV25, ampV25, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_25_25 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_25_25 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD ^ 2 * oBC * oBD := by
  simp only [qg_25_25, paramsN] <;> ring

def qg_25_26 (p : Params K) : K :=
  p.mD * p.c1 ^ 2 * p.c2 * p.c3 - p.mD * p.c1 ^ 2 * p.M23 - 2 * p.mD * p.c1 * p.c2 * p.M13 - 2 * p.mD * p.c1 * p.c3 * p.M12 + 2 * p.mD * p.c1 * p.b - p.mD * p.c2 * p.c3 * p.M11 + p.mD * p.M11 * p.M23

theorem qg_25_26_eq (p : Params K) :
    W p (ampV25 p) (T p 3 3 (ampV26 p)) = qg_25_26 p := by
  simp [qg_25_26, ampV25, ampV26, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_25_26 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_25_26 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB ^ 2 * nC ^ 2 * nD ^ 2 * oBC * wD + 2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * RABC * RBCD := by
  simp only [qg_25_26, paramsN] <;> ring

def qg_25_27 (p : Params K) : K :=
  p.mD * p.c1 ^ 2 * p.c2 * p.c3 ^ 2 + p.mD * p.c1 ^ 2 * p.c2 * p.M33 + p.mD * p.c2 * p.c3 ^ 2 * p.M11 + p.mD * p.c2 * p.M11 * p.M33

theorem qg_25_27_eq (p : Params K) :
    W p (ampV25 p) (T p 3 3 (ampV27 p)) = qg_25_27 p := by
  simp [qg_25_27, ampV25, ampV27, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_25_27 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_25_27 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC ^ 2 * nD ^ 3 * oBC * oBD * RACD := by
  simp only [qg_25_27, paramsN] <;> ring

def qg_26_26 (p : Params K) : K :=
  p.mD * p.c1 ^ 2 * p.c2 ^ 2 + p.mD * p.c1 ^ 2 * p.M22 + p.mD * p.c2 ^ 2 * p.M11 + p.mD * p.M11 * p.M22

theorem qg_26_26_eq (p : Params K) :
    W p (ampV26 p) (T p 3 3 (ampV26 p)) = qg_26_26 p := by
  simp [qg_26_26, ampV26, ampV26, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_26_26 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_26_26 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * nD ^ 2 * oBC * oCD := by
  simp only [qg_26_26, paramsN] <;> ring

def qg_26_27 (p : Params K) : K :=
  p.mD * p.c1 ^ 2 * p.c2 ^ 2 * p.c3 - 2 * p.mD * p.c1 ^ 2 * p.c2 * p.M23 - p.mD * p.c1 ^ 2 * p.c3 * p.M22 - 2 * p.mD * p.c1 * p.c2 ^ 2 * p.M13 - 4 * p.mD * p.c1 * p.c2 * p.c3 * p.M12 + 2 * p.mD * p.c1 * p.c2 * p.b + 2 * p.mD * p.c1 * p.M12 * p.M23 - p.mD * p.c2 ^ 2 * p.c3 * p.M11 + 2 * p.mD * p.c2 * p.M12 * p.M13 - p.mD * p.c3 * p.M11 * p.M22 + 2 * p.mD * p.c3 * p.M12 ^ 2 - 2 * p.mD * p.M12 * p.b

theorem qg_26_27_eq (p : Params K) :
    W p (ampV26 p) (T p 3 3 (ampV27 p)) = qg_26_27 p := by
  simp [qg_26_27, ampV26, ampV27, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_26_27 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_26_27 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB ^ 2 * nC ^ 2 * nD ^ 3 * oBC * oCD * RABD + 2 * nB ^ 2 * nC ^ 2 * nD ^ 3 * RBCD * wC := by
  simp only [qg_26_27, paramsN] <;> ring

def qg_27_27 (p : Params K) : K :=
  p.mD * p.c1 ^ 2 * p.c2 ^ 2 * p.c3 ^ 2 + p.mD * p.c1 ^ 2 * p.c2 ^ 2 * p.M33 + p.mD * p.c1 ^ 2 * p.c3 ^ 2 * p.M22 + p.mD * p.c1 ^ 2 * p.M22 * p.M33 + p.mD * p.c2 ^ 2 * p.c3 ^ 2 * p.M11 + p.mD * p.c2 ^ 2 * p.M11 * p.M33 + p.mD * p.c3 ^ 2 * p.M11 * p.M22 + p.mD * p.M11 * p.M22 * p.M33

theorem qg_27_27_eq (p : Params K) :
    W p (ampV27 p) (T p 3 3 (ampV27 p)) = qg_27_27 p := by
  simp [qg_27_27, ampV27, ampV27, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_27_27 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_27_27 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC ^ 2 * nD ^ 3 * oBC * oBD * oCD := by
  simp only [qg_27_27, paramsN] <;> ring

end LemmaB.TableModel
