/- SPDX-License-Identifier: Apache-2.0
   Machine-generated file. -/
module

public import TableModel.Amps

/-! # Table-model identity, part 2 (frames B, B): the model values in the gauge parameters

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

def qg_7_7 (p : Params K) : K :=
  p.mB

theorem qg_7_7_eq (p : Params K) :
    W p (ampV7 p) (T p 1 1 (ampV7 p)) = qg_7_7 p := by
  simp [qg_7_7, ampV7, ampV7, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_7_7 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_7_7 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB := by
  simp only [qg_7_7, paramsN] <;> ring

def qg_7_8 (p : Params K) : K :=
  p.mB * p.c1

theorem qg_7_8_eq (p : Params K) :
    W p (ampV7 p) (T p 1 1 (ampV8 p)) = qg_7_8 p := by
  simp [qg_7_8, ampV7, ampV8, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_7_8 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_7_8 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * RABC := by
  simp only [qg_7_8, paramsN] <;> ring

def qg_7_9 (p : Params K) : K :=
  p.mB * p.c3

theorem qg_7_9_eq (p : Params K) :
    W p (ampV7 p) (T p 1 1 (ampV9 p)) = qg_7_9 p := by
  simp [qg_7_9, ampV7, ampV9, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_7_9 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_7_9 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nD * RABD := by
  simp only [qg_7_9, paramsN] <;> ring

def qg_7_10 (p : Params K) : K :=
  p.mB * p.c2

theorem qg_7_10_eq (p : Params K) :
    W p (ampV7 p) (T p 1 1 (ampV10 p)) = qg_7_10 p := by
  simp [qg_7_10, ampV7, ampV10, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_7_10 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_7_10 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * RACD := by
  simp only [qg_7_10, paramsN] <;> ring

def qg_7_11 (p : Params K) : K :=
  p.mB * p.c1 * p.c2 - p.mB * p.M12

theorem qg_7_11_eq (p : Params K) :
    W p (ampV7 p) (T p 1 1 (ampV11 p)) = qg_7_11 p := by
  simp [qg_7_11, ampV7, ampV11, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_7_11 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_7_11 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD * wC := by
  simp only [qg_7_11, paramsN] <;> ring

def qg_7_12 (p : Params K) : K :=
  p.mB * p.c2 * p.c3 - p.mB * p.M23

theorem qg_7_12_eq (p : Params K) :
    W p (ampV7 p) (T p 1 1 (ampV12 p)) = qg_7_12 p := by
  simp [qg_7_12, ampV7, ampV12, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_7_12 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_7_12 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD * wD := by
  simp only [qg_7_12, paramsN] <;> ring

def qg_7_13 (p : Params K) : K :=
  p.mB * p.c1 * p.c2 * p.c3 - p.mB * p.c1 * p.M23 - p.mB * p.c2 * p.M13 - p.mB * p.c3 * p.M12 + p.mB * p.b

theorem qg_7_13_eq (p : Params K) :
    W p (ampV7 p) (T p 1 1 (ampV13 p)) = qg_7_13 p := by
  simp [qg_7_13, ampV7, ampV13, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_7_13 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_7_13 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD * RBCD := by
  simp only [qg_7_13, paramsN] <;> ring

def qg_8_8 (p : Params K) : K :=
  p.mB * p.c1 ^ 2 + p.mB * p.M11

theorem qg_8_8_eq (p : Params K) :
    W p (ampV8 p) (T p 1 1 (ampV8 p)) = qg_8_8 p := by
  simp [qg_8_8, ampV8, ampV8, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_8_8 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_8_8 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * oBC := by
  simp only [qg_8_8, paramsN] <;> ring

def qg_8_9 (p : Params K) : K :=
  p.mB * p.c1 * p.c3 - p.mB * p.M13

theorem qg_8_9_eq (p : Params K) :
    W p (ampV8 p) (T p 1 1 (ampV9 p)) = qg_8_9 p := by
  simp [qg_8_9, ampV8, ampV9, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_8_9 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_8_9 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD * wB := by
  simp only [qg_8_9, paramsN] <;> ring

def qg_8_10 (p : Params K) : K :=
  p.mB * p.c1 * p.c2 - p.mB * p.M12

theorem qg_8_10_eq (p : Params K) :
    W p (ampV8 p) (T p 1 1 (ampV10 p)) = qg_8_10 p := by
  simp [qg_8_10, ampV8, ampV10, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_8_10 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_8_10 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD * wC := by
  simp only [qg_8_10, paramsN] <;> ring

def qg_8_11 (p : Params K) : K :=
  p.mB * p.c1 ^ 2 * p.c2 + p.mB * p.c2 * p.M11

theorem qg_8_11_eq (p : Params K) :
    W p (ampV8 p) (T p 1 1 (ampV11 p)) = qg_8_11 p := by
  simp [qg_8_11, ampV8, ampV11, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_8_11 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_8_11 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC ^ 2 * nD * oBC * RACD := by
  simp only [qg_8_11, paramsN] <;> ring

def qg_8_12 (p : Params K) : K :=
  p.mB * p.c1 * p.c2 * p.c3 - p.mB * p.c1 * p.M23 - p.mB * p.c2 * p.M13 - p.mB * p.c3 * p.M12 + p.mB * p.b

theorem qg_8_12_eq (p : Params K) :
    W p (ampV8 p) (T p 1 1 (ampV12 p)) = qg_8_12 p := by
  simp [qg_8_12, ampV8, ampV12, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_8_12 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_8_12 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD * RBCD := by
  simp only [qg_8_12, paramsN] <;> ring

def qg_8_13 (p : Params K) : K :=
  p.mB * p.c1 ^ 2 * p.c2 * p.c3 - p.mB * p.c1 ^ 2 * p.M23 + p.mB * p.c2 * p.c3 * p.M11 - p.mB * p.M11 * p.M23

theorem qg_8_13_eq (p : Params K) :
    W p (ampV8 p) (T p 1 1 (ampV13 p)) = qg_8_13 p := by
  simp [qg_8_13, ampV8, ampV13, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_8_13 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_8_13 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 3 * nC ^ 2 * nD * oBC * wD := by
  simp only [qg_8_13, paramsN] <;> ring

def qg_9_9 (p : Params K) : K :=
  p.mB * p.c3 ^ 2 + p.mB * p.M33

theorem qg_9_9_eq (p : Params K) :
    W p (ampV9 p) (T p 1 1 (ampV9 p)) = qg_9_9 p := by
  simp [qg_9_9, ampV9, ampV9, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_9_9 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_9_9 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nD * oBD := by
  simp only [qg_9_9, paramsN] <;> ring

def qg_9_10 (p : Params K) : K :=
  p.mB * p.c2 * p.c3 + p.mB * p.M23

theorem qg_9_10_eq (p : Params K) :
    W p (ampV9 p) (T p 1 1 (ampV10 p)) = qg_9_10 p := by
  simp [qg_9_10, ampV9, ampV10, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_9_10 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_9_10 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC * nD ^ 2 * RABD * RACD - nB ^ 2 * nC * nD * wD := by
  simp only [qg_9_10, paramsN] <;> ring

def qg_9_11 (p : Params K) : K :=
  p.mB * p.c1 * p.c2 * p.c3 - p.mB * p.c1 * p.M23 - p.mB * p.c2 * p.M13 - p.mB * p.c3 * p.M12 + p.mB * p.b

theorem qg_9_11_eq (p : Params K) :
    W p (ampV9 p) (T p 1 1 (ampV11 p)) = qg_9_11 p := by
  simp [qg_9_11, ampV9, ampV11, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_9_11 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_9_11 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD * RBCD := by
  simp only [qg_9_11, paramsN] <;> ring

def qg_9_12 (p : Params K) : K :=
  p.mB * p.c2 * p.c3 ^ 2 + p.mB * p.c2 * p.M33

theorem qg_9_12_eq (p : Params K) :
    W p (ampV9 p) (T p 1 1 (ampV12 p)) = qg_9_12 p := by
  simp [qg_9_12, ampV9, ampV12, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_9_12 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_9_12 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD ^ 2 * oBD * RACD := by
  simp only [qg_9_12, paramsN] <;> ring

def qg_9_13 (p : Params K) : K :=
  p.mB * p.c1 * p.c2 * p.c3 ^ 2 - p.mB * p.c1 * p.c2 * p.M33 - 2 * p.mB * p.c1 * p.c3 * p.M23 - 2 * p.mB * p.c2 * p.c3 * p.M13 - p.mB * p.c3 ^ 2 * p.M12 + 2 * p.mB * p.c3 * p.b + p.mB * p.M33 * p.M12

theorem qg_9_13_eq (p : Params K) :
    W p (ampV9 p) (T p 1 1 (ampV13 p)) = qg_9_13 p := by
  simp [qg_9_13, ampV9, ampV13, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_9_13 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_9_13 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB ^ 3 * nC * nD ^ 2 * oBD * wC + 2 * nB ^ 3 * nC * nD ^ 2 * RABD * RBCD := by
  simp only [qg_9_13, paramsN] <;> ring

def qg_10_10 (p : Params K) : K :=
  p.mB * p.c2 ^ 2 + p.mB * p.M22

theorem qg_10_10_eq (p : Params K) :
    W p (ampV10 p) (T p 1 1 (ampV10 p)) = qg_10_10 p := by
  simp [qg_10_10, ampV10, ampV10, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_10_10 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_10_10 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * oCD := by
  simp only [qg_10_10, paramsN] <;> ring

def qg_10_11 (p : Params K) : K :=
  p.mB * p.c1 * p.c2 ^ 2 - p.mB * p.c1 * p.M22 - 2 * p.mB * p.c2 * p.M12

theorem qg_10_11_eq (p : Params K) :
    W p (ampV10 p) (T p 1 1 (ampV11 p)) = qg_10_11 p := by
  simp [qg_10_11, ampV10, ampV11, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_10_11 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_10_11 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * RACD * wC - nB ^ 2 * nC ^ 2 * nD * oCD * RABC := by
  simp only [qg_10_11, paramsN] <;> ring

def qg_10_12 (p : Params K) : K :=
  p.mB * p.c2 ^ 2 * p.c3 + p.mB * p.c3 * p.M22

theorem qg_10_12_eq (p : Params K) :
    W p (ampV10 p) (T p 1 1 (ampV12 p)) = qg_10_12 p := by
  simp [qg_10_12, ampV10, ampV12, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_10_12 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_10_12 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD ^ 2 * oCD * RABD := by
  simp only [qg_10_12, paramsN] <;> ring

def qg_10_13 (p : Params K) : K :=
  p.mB * p.c1 * p.c2 ^ 2 * p.c3 - 2 * p.mB * p.c1 * p.c2 * p.M23 - p.mB * p.c1 * p.c3 * p.M22 - p.mB * p.c2 ^ 2 * p.M13 - 2 * p.mB * p.c2 * p.c3 * p.M12 - p.mB * p.M22 * p.M13 + 2 * p.mB * p.M12 * p.M23

theorem qg_10_13_eq (p : Params K) :
    W p (ampV10 p) (T p 1 1 (ampV13 p)) = qg_10_13 p := by
  simp [qg_10_13, ampV10, ampV13, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_10_13 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_10_13 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -2 * nB ^ 3 * nC ^ 2 * nD ^ 2 * oCD * RABC * RABD + 2 * nB ^ 3 * nC ^ 2 * nD ^ 2 * wC * wD + nB ^ 2 * nC ^ 2 * nD ^ 2 * oCD * wB := by
  simp only [qg_10_13, paramsN] <;> ring

def qg_11_11 (p : Params K) : K :=
  p.mB * p.c1 ^ 2 * p.c2 ^ 2 + p.mB * p.c1 ^ 2 * p.M22 + p.mB * p.c2 ^ 2 * p.M11 + p.mB * p.M11 * p.M22

theorem qg_11_11_eq (p : Params K) :
    W p (ampV11 p) (T p 1 1 (ampV11 p)) = qg_11_11 p := by
  simp [qg_11_11, ampV11, ampV11, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_11_11 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_11_11 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC ^ 2 * nD * oBC * oCD := by
  simp only [qg_11_11, paramsN] <;> ring

def qg_11_12 (p : Params K) : K :=
  p.mB * p.c1 * p.c2 ^ 2 * p.c3 - 2 * p.mB * p.c1 * p.c2 * p.M23 - p.mB * p.c1 * p.c3 * p.M22 - p.mB * p.c2 ^ 2 * p.M13 - 2 * p.mB * p.c2 * p.c3 * p.M12 + 2 * p.mB * p.c2 * p.b + p.mB * p.M22 * p.M13

theorem qg_11_12_eq (p : Params K) :
    W p (ampV11 p) (T p 1 1 (ampV12 p)) = qg_11_12 p := by
  simp [qg_11_12, ampV11, ampV12, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_11_12 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_11_12 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB ^ 2 * nC ^ 2 * nD ^ 2 * oCD * wB + 2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * RACD * RBCD := by
  simp only [qg_11_12, paramsN] <;> ring

def qg_11_13 (p : Params K) : K :=
  p.mB * p.c1 ^ 2 * p.c2 ^ 2 * p.c3 + p.mB * p.c1 ^ 2 * p.c3 * p.M22 + p.mB * p.c2 ^ 2 * p.c3 * p.M11 + p.mB * p.c3 * p.M11 * p.M22

theorem qg_11_13_eq (p : Params K) :
    W p (ampV11 p) (T p 1 1 (ampV13 p)) = qg_11_13 p := by
  simp [qg_11_13, ampV11, ampV13, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_11_13 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_11_13 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 3 * nC ^ 2 * nD ^ 2 * oBC * oCD * RABD := by
  simp only [qg_11_13, paramsN] <;> ring

def qg_12_12 (p : Params K) : K :=
  p.mB * p.c2 ^ 2 * p.c3 ^ 2 + p.mB * p.c2 ^ 2 * p.M33 + p.mB * p.c3 ^ 2 * p.M22 + p.mB * p.M22 * p.M33

theorem qg_12_12_eq (p : Params K) :
    W p (ampV12 p) (T p 1 1 (ampV12 p)) = qg_12_12 p := by
  simp [qg_12_12, ampV12, ampV12, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_12_12 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_12_12 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD ^ 2 * oBD * oCD := by
  simp only [qg_12_12, paramsN] <;> ring

def qg_12_13 (p : Params K) : K :=
  p.mB * p.c1 * p.c2 ^ 2 * p.c3 ^ 2 - p.mB * p.c1 * p.c2 ^ 2 * p.M33 - 4 * p.mB * p.c1 * p.c2 * p.c3 * p.M23 - p.mB * p.c1 * p.c3 ^ 2 * p.M22 - p.mB * p.c1 * p.M22 * p.M33 + 2 * p.mB * p.c1 * p.M23 ^ 2 - 2 * p.mB * p.c2 ^ 2 * p.c3 * p.M13 - 2 * p.mB * p.c2 * p.c3 ^ 2 * p.M12 + 2 * p.mB * p.c2 * p.c3 * p.b + 2 * p.mB * p.c2 * p.M13 * p.M23 + 2 * p.mB * p.c3 * p.M12 * p.M23 - 2 * p.mB * p.M23 * p.b

theorem qg_12_13_eq (p : Params K) :
    W p (ampV12 p) (T p 1 1 (ampV13 p)) = qg_12_13 p := by
  simp [qg_12_13, ampV12, ampV13, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_12_13 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_12_13 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB ^ 3 * nC ^ 2 * nD ^ 2 * oBD * oCD * RABC + 2 * nB ^ 3 * nC ^ 2 * nD ^ 2 * RBCD * wD := by
  simp only [qg_12_13, paramsN] <;> ring

def qg_13_13 (p : Params K) : K :=
  p.mB * p.c1 ^ 2 * p.c2 ^ 2 * p.c3 ^ 2 + p.mB * p.c1 ^ 2 * p.c2 ^ 2 * p.M33 + p.mB * p.c1 ^ 2 * p.c3 ^ 2 * p.M22 + p.mB * p.c1 ^ 2 * p.M22 * p.M33 + p.mB * p.c2 ^ 2 * p.c3 ^ 2 * p.M11 + p.mB * p.c2 ^ 2 * p.M11 * p.M33 + p.mB * p.c3 ^ 2 * p.M11 * p.M22 + p.mB * p.M11 * p.M22 * p.M33

theorem qg_13_13_eq (p : Params K) :
    W p (ampV13 p) (T p 1 1 (ampV13 p)) = qg_13_13 p := by
  simp [qg_13_13, ampV13, ampV13, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_13_13 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_13_13 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 3 * nC ^ 2 * nD ^ 2 * oBC * oBD * oCD := by
  simp only [qg_13_13, paramsN] <;> ring

end LemmaB.TableModel
