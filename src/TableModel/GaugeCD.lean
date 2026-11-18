/- SPDX-License-Identifier: Apache-2.0
   Machine-generated file. -/
module

public import TableModel.Amps

/-! # Table-model identity, part 2 (frames C, D): the model values in the gauge parameters

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

def qg_14_21 (p : Params K) : K :=
  p.c2

theorem qg_14_21_eq (p : Params K) :
    W p (ampV14 p) (T p 2 3 (ampV21 p)) = qg_14_21 p := by
  simp [qg_14_21, ampV14, ampV21, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_14_21 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_14_21 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nC * nD * RACD := by
  simp only [qg_14_21, paramsN] <;> ring

def qg_14_22 (p : Params K) : K :=
  p.c2 * p.c3 - p.M23

theorem qg_14_22_eq (p : Params K) :
    W p (ampV14 p) (T p 2 3 (ampV22 p)) = qg_14_22 p := by
  simp [qg_14_22, ampV14, ampV22, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_14_22 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_14_22 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * wD := by
  simp only [qg_14_22, paramsN] <;> ring

def qg_14_23 (p : Params K) : K :=
  p.c2 ^ 2 + p.M22

theorem qg_14_23_eq (p : Params K) :
    W p (ampV14 p) (T p 2 3 (ampV23 p)) = qg_14_23 p := by
  simp [qg_14_23, ampV14, ampV23, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_14_23 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_14_23 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nC * nD * oCD := by
  simp only [qg_14_23, paramsN] <;> ring

def qg_14_24 (p : Params K) : K :=
  p.c1 * p.c2 + p.M12

theorem qg_14_24_eq (p : Params K) :
    W p (ampV14 p) (T p 2 3 (ampV24 p)) = qg_14_24 p := by
  simp [qg_14_24, ampV14, ampV24, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_14_24 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_14_24 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB * nC ^ 2 * nD * RABC * RACD - nB * nC * nD * wC := by
  simp only [qg_14_24, paramsN] <;> ring

def qg_14_25 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 - p.c1 * p.M23 - p.c2 * p.M13 - p.c3 * p.M12 + p.b

theorem qg_14_25_eq (p : Params K) :
    W p (ampV14 p) (T p 2 3 (ampV25 p)) = qg_14_25 p := by
  simp [qg_14_25, ampV14, ampV25, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_14_25 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_14_25 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * RBCD := by
  simp only [qg_14_25, paramsN] <;> ring

def qg_14_26 (p : Params K) : K :=
  p.c1 * p.c2 ^ 2 + p.c1 * p.M22

theorem qg_14_26_eq (p : Params K) :
    W p (ampV14 p) (T p 2 3 (ampV26 p)) = qg_14_26 p := by
  simp [qg_14_26, ampV14, ampV26, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_14_26 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_14_26 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * nD * oCD * RABC := by
  simp only [qg_14_26, paramsN] <;> ring

def qg_14_27 (p : Params K) : K :=
  p.c1 * p.c2 ^ 2 * p.c3 - 2 * p.c1 * p.c2 * p.M23 - p.c1 * p.c3 * p.M22 - p.c2 ^ 2 * p.M13 - 2 * p.c2 * p.c3 * p.M12 + 2 * p.c2 * p.b + p.M22 * p.M13

theorem qg_14_27_eq (p : Params K) :
    W p (ampV14 p) (T p 2 3 (ampV27 p)) = qg_14_27 p := by
  simp [qg_14_27, ampV14, ampV27, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_14_27 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_14_27 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB * nC ^ 2 * nD ^ 2 * oCD * wB + 2 * nB * nC ^ 2 * nD ^ 2 * RACD * RBCD := by
  simp only [qg_14_27, paramsN] <;> ring

def qg_15_21 (p : Params K) : K :=
  p.c2 ^ 2 + p.M22

theorem qg_15_21_eq (p : Params K) :
    W p (ampV15 p) (T p 2 3 (ampV21 p)) = qg_15_21 p := by
  simp [qg_15_21, ampV15, ampV21, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_15_21 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_15_21 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nC * nD * oCD := by
  simp only [qg_15_21, paramsN] <;> ring

def qg_15_22 (p : Params K) : K :=
  p.c2 ^ 2 * p.c3 + p.c3 * p.M22

theorem qg_15_22_eq (p : Params K) :
    W p (ampV15 p) (T p 2 3 (ampV22 p)) = qg_15_22 p := by
  simp [qg_15_22, ampV15, ampV22, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_15_22 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_15_22 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD ^ 2 * oCD * RABD := by
  simp only [qg_15_22, paramsN] <;> ring

def qg_15_23 (p : Params K) : K :=
  p.c2 ^ 3 + p.c2 * p.M22

theorem qg_15_23_eq (p : Params K) :
    W p (ampV15 p) (T p 2 3 (ampV23 p)) = qg_15_23 p := by
  simp [qg_15_23, ampV15, ampV23, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_15_23 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_15_23 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nC ^ 2 * nD ^ 2 * oCD * RACD := by
  simp only [qg_15_23, paramsN] <;> ring

def qg_15_24 (p : Params K) : K :=
  p.c1 * p.c2 ^ 2 + p.c1 * p.M22

theorem qg_15_24_eq (p : Params K) :
    W p (ampV15 p) (T p 2 3 (ampV24 p)) = qg_15_24 p := by
  simp [qg_15_24, ampV15, ampV24, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_15_24 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_15_24 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * nD * oCD * RABC := by
  simp only [qg_15_24, paramsN] <;> ring

def qg_15_25 (p : Params K) : K :=
  p.c1 * p.c2 ^ 2 * p.c3 + p.c1 * p.c3 * p.M22 - p.c2 ^ 2 * p.M13 - p.M22 * p.M13

theorem qg_15_25_eq (p : Params K) :
    W p (ampV15 p) (T p 2 3 (ampV25 p)) = qg_15_25 p := by
  simp [qg_15_25, ampV15, ampV25, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_15_25 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_15_25 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * nD ^ 2 * oCD * wB := by
  simp only [qg_15_25, paramsN] <;> ring

def qg_15_26 (p : Params K) : K :=
  p.c1 * p.c2 ^ 3 + p.c1 * p.c2 * p.M22 - p.c2 ^ 2 * p.M12 - p.M22 * p.M12

theorem qg_15_26_eq (p : Params K) :
    W p (ampV15 p) (T p 2 3 (ampV26 p)) = qg_15_26 p := by
  simp [qg_15_26, ampV15, ampV26, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_15_26 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_15_26 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * nD ^ 2 * oCD * wC := by
  simp only [qg_15_26, paramsN] <;> ring

def qg_15_27 (p : Params K) : K :=
  p.c1 * p.c2 ^ 3 * p.c3 - p.c1 * p.c2 ^ 2 * p.M23 + p.c1 * p.c2 * p.c3 * p.M22 - p.c1 * p.M22 * p.M23 - p.c2 ^ 3 * p.M13 - p.c2 ^ 2 * p.c3 * p.M12 + p.c2 ^ 2 * p.b - p.c2 * p.M22 * p.M13 - p.c3 * p.M22 * p.M12 + p.M22 * p.b

theorem qg_15_27_eq (p : Params K) :
    W p (ampV15 p) (T p 2 3 (ampV27 p)) = qg_15_27 p := by
  simp [qg_15_27, ampV15, ampV27, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_15_27 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_15_27 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * nD ^ 2 * oCD * RBCD := by
  simp only [qg_15_27, paramsN] <;> ring

def qg_16_21 (p : Params K) : K :=
  p.c1 * p.c2 - p.M12

theorem qg_16_21_eq (p : Params K) :
    W p (ampV16 p) (T p 2 3 (ampV21 p)) = qg_16_21 p := by
  simp [qg_16_21, ampV16, ampV21, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_16_21 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_16_21 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * wC := by
  simp only [qg_16_21, paramsN] <;> ring

def qg_16_22 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 - p.c1 * p.M23 - p.c2 * p.M13 - p.c3 * p.M12 + p.b

theorem qg_16_22_eq (p : Params K) :
    W p (ampV16 p) (T p 2 3 (ampV22 p)) = qg_16_22 p := by
  simp [qg_16_22, ampV16, ampV22, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_16_22 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_16_22 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * RBCD := by
  simp only [qg_16_22, paramsN] <;> ring

def qg_16_23 (p : Params K) : K :=
  p.c1 * p.c2 ^ 2 + p.c1 * p.M22

theorem qg_16_23_eq (p : Params K) :
    W p (ampV16 p) (T p 2 3 (ampV23 p)) = qg_16_23 p := by
  simp [qg_16_23, ampV16, ampV23, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_16_23 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_16_23 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * nD * oCD * RABC := by
  simp only [qg_16_23, paramsN] <;> ring

def qg_16_24 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 + p.c2 * p.M11

theorem qg_16_24_eq (p : Params K) :
    W p (ampV16 p) (T p 2 3 (ampV24 p)) = qg_16_24 p := by
  simp [qg_16_24, ampV16, ampV24, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_16_24 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_16_24 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * nD * oBC * RACD := by
  simp only [qg_16_24, paramsN] <;> ring

def qg_16_25 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 * p.c3 - p.c1 ^ 2 * p.M23 - 2 * p.c1 * p.c2 * p.M13 - 2 * p.c1 * p.c3 * p.M12 + 2 * p.c1 * p.b - p.c2 * p.c3 * p.M11 + p.M11 * p.M23

theorem qg_16_25_eq (p : Params K) :
    W p (ampV16 p) (T p 2 3 (ampV25 p)) = qg_16_25 p := by
  simp [qg_16_25, ampV16, ampV25, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_16_25 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_16_25 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB ^ 2 * nC ^ 2 * nD * oBC * wD + 2 * nB ^ 2 * nC ^ 2 * nD * RABC * RBCD := by
  simp only [qg_16_25, paramsN] <;> ring

def qg_16_26 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 ^ 2 + p.c1 ^ 2 * p.M22 + p.c2 ^ 2 * p.M11 + p.M11 * p.M22

theorem qg_16_26_eq (p : Params K) :
    W p (ampV16 p) (T p 2 3 (ampV26 p)) = qg_16_26 p := by
  simp [qg_16_26, ampV16, ampV26, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_16_26 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_16_26 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * nD * oBC * oCD := by
  simp only [qg_16_26, paramsN] <;> ring

def qg_16_27 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 ^ 2 * p.c3 - 2 * p.c1 ^ 2 * p.c2 * p.M23 - p.c1 ^ 2 * p.c3 * p.M22 - 2 * p.c1 * p.c2 ^ 2 * p.M13 - 4 * p.c1 * p.c2 * p.c3 * p.M12 + 2 * p.c1 * p.c2 * p.b + 2 * p.c1 * p.M12 * p.M23 - p.c2 ^ 2 * p.c3 * p.M11 + 2 * p.c2 * p.M12 * p.M13 - p.c3 * p.M11 * p.M22 + 2 * p.c3 * p.M12 ^ 2 - 2 * p.M12 * p.b

theorem qg_16_27_eq (p : Params K) :
    W p (ampV16 p) (T p 2 3 (ampV27 p)) = qg_16_27 p := by
  simp [qg_16_27, ampV16, ampV27, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_16_27 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_16_27 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB ^ 2 * nC ^ 2 * nD ^ 2 * oBC * oCD * RABD + 2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * RBCD * wC := by
  simp only [qg_16_27, paramsN] <;> ring

def qg_17_21 (p : Params K) : K :=
  p.c2 * p.c3 - p.M23

theorem qg_17_21_eq (p : Params K) :
    W p (ampV17 p) (T p 2 3 (ampV21 p)) = qg_17_21 p := by
  simp [qg_17_21, ampV17, ampV21, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_17_21 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_17_21 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * wD := by
  simp only [qg_17_21, paramsN] <;> ring

def qg_17_22 (p : Params K) : K :=
  p.c2 * p.c3 ^ 2 - p.c2 * p.M33 - 2 * p.c3 * p.M23

theorem qg_17_22_eq (p : Params K) :
    W p (ampV17 p) (T p 2 3 (ampV22 p)) = qg_17_22 p := by
  simp [qg_17_22, ampV17, ampV22, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_17_22 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_17_22 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC * nD ^ 2 * RABD * wD - nB * nC * nD ^ 2 * oBD * RACD := by
  simp only [qg_17_22, paramsN] <;> ring

def qg_17_23 (p : Params K) : K :=
  p.c2 ^ 2 * p.c3 + p.c3 * p.M22

theorem qg_17_23_eq (p : Params K) :
    W p (ampV17 p) (T p 2 3 (ampV23 p)) = qg_17_23 p := by
  simp [qg_17_23, ampV17, ampV23, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_17_23 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_17_23 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD ^ 2 * oCD * RABD := by
  simp only [qg_17_23, paramsN] <;> ring

def qg_17_24 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 - p.c1 * p.M23 + p.c2 * p.M13 + p.c3 * p.M12 + p.b

theorem qg_17_24_eq (p : Params K) :
    W p (ampV17 p) (T p 2 3 (ampV24 p)) = qg_17_24 p := by
  simp [qg_17_24, ampV17, ampV24, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_17_24 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_17_24 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      4 * nB ^ 2 * nC ^ 2 * nD ^ 2 * RABC * RABD * RACD - 2 * nB ^ 2 * nC * nD ^ 2 * RABD * wC - 2 * nB * nC ^ 2 * nD ^ 2 * RACD * wB + nB * nC * nD * RBCD := by
  simp only [qg_17_24, paramsN] <;> ring

def qg_17_25 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 ^ 2 - p.c1 * p.c2 * p.M33 - 2 * p.c1 * p.c3 * p.M23 - 2 * p.c2 * p.c3 * p.M13 - p.c3 ^ 2 * p.M12 - p.M33 * p.M12 + 2 * p.M13 * p.M23

theorem qg_17_25_eq (p : Params K) :
    W p (ampV17 p) (T p 2 3 (ampV25 p)) = qg_17_25 p := by
  simp [qg_17_25, ampV17, ampV25, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_17_25 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_17_25 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * oBD * RABC * RACD + 2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * wB * wD + nB ^ 2 * nC * nD ^ 2 * oBD * wC := by
  simp only [qg_17_25, paramsN] <;> ring

def qg_17_26 (p : Params K) : K :=
  p.c1 * p.c2 ^ 2 * p.c3 + p.c1 * p.c3 * p.M22 + p.c2 ^ 2 * p.M13 + p.M22 * p.M13

theorem qg_17_26_eq (p : Params K) :
    W p (ampV17 p) (T p 2 3 (ampV26 p)) = qg_17_26 p := by
  simp [qg_17_26, ampV17, ampV26, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_17_26 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_17_26 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * oCD * RABC * RABD - nB * nC ^ 2 * nD ^ 2 * oCD * wB := by
  simp only [qg_17_26, paramsN] <;> ring

def qg_17_27 (p : Params K) : K :=
  p.c1 * p.c2 ^ 2 * p.c3 ^ 2 - p.c1 * p.c2 ^ 2 * p.M33 - 4 * p.c1 * p.c2 * p.c3 * p.M23 - p.c1 * p.c3 ^ 2 * p.M22 - p.c1 * p.M22 * p.M33 + 2 * p.c1 * p.M23 ^ 2 - 2 * p.c2 ^ 2 * p.c3 * p.M13 - 2 * p.c2 * p.c3 ^ 2 * p.M12 + 2 * p.c2 * p.c3 * p.b + 2 * p.c2 * p.M13 * p.M23 + 2 * p.c3 * p.M12 * p.M23 - 2 * p.M23 * p.b

theorem qg_17_27_eq (p : Params K) :
    W p (ampV17 p) (T p 2 3 (ampV27 p)) = qg_17_27 p := by
  simp [qg_17_27, ampV17, ampV27, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_17_27 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_17_27 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB ^ 2 * nC ^ 2 * nD ^ 2 * oBD * oCD * RABC + 2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * RBCD * wD := by
  simp only [qg_17_27, paramsN] <;> ring

def qg_18_21 (p : Params K) : K :=
  p.c2 ^ 2 * p.c3 + p.c3 * p.M22

theorem qg_18_21_eq (p : Params K) :
    W p (ampV18 p) (T p 2 3 (ampV21 p)) = qg_18_21 p := by
  simp [qg_18_21, ampV18, ampV21, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_18_21 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_18_21 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD ^ 2 * oCD * RABD := by
  simp only [qg_18_21, paramsN] <;> ring

def qg_18_22 (p : Params K) : K :=
  p.c2 ^ 2 * p.c3 ^ 2 + p.c2 ^ 2 * p.M33 + p.c3 ^ 2 * p.M22 + p.M22 * p.M33

theorem qg_18_22_eq (p : Params K) :
    W p (ampV18 p) (T p 2 3 (ampV22 p)) = qg_18_22 p := by
  simp [qg_18_22, ampV18, ampV22, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_18_22 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_18_22 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD ^ 2 * oBD * oCD := by
  simp only [qg_18_22, paramsN] <;> ring

def qg_18_23 (p : Params K) : K :=
  p.c2 ^ 3 * p.c3 - p.c2 ^ 2 * p.M23 + p.c2 * p.c3 * p.M22 - p.M22 * p.M23

theorem qg_18_23_eq (p : Params K) :
    W p (ampV18 p) (T p 2 3 (ampV23 p)) = qg_18_23 p := by
  simp [qg_18_23, ampV18, ampV23, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_18_23 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_18_23 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * nD ^ 2 * oCD * wD := by
  simp only [qg_18_23, paramsN] <;> ring

def qg_18_24 (p : Params K) : K :=
  p.c1 * p.c2 ^ 2 * p.c3 + p.c1 * p.c3 * p.M22 - p.c2 ^ 2 * p.M13 - p.M22 * p.M13

theorem qg_18_24_eq (p : Params K) :
    W p (ampV18 p) (T p 2 3 (ampV24 p)) = qg_18_24 p := by
  simp [qg_18_24, ampV18, ampV24, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_18_24 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_18_24 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * nD ^ 2 * oCD * wB := by
  simp only [qg_18_24, paramsN] <;> ring

def qg_18_25 (p : Params K) : K :=
  p.c1 * p.c2 ^ 2 * p.c3 ^ 2 + p.c1 * p.c2 ^ 2 * p.M33 + p.c1 * p.c3 ^ 2 * p.M22 + p.c1 * p.M22 * p.M33

theorem qg_18_25_eq (p : Params K) :
    W p (ampV18 p) (T p 2 3 (ampV25 p)) = qg_18_25 p := by
  simp [qg_18_25, ampV18, ampV25, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_18_25 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_18_25 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC ^ 2 * nD ^ 2 * oBD * oCD * RABC := by
  simp only [qg_18_25, paramsN] <;> ring

def qg_18_26 (p : Params K) : K :=
  p.c1 * p.c2 ^ 3 * p.c3 - p.c1 * p.c2 ^ 2 * p.M23 + p.c1 * p.c2 * p.c3 * p.M22 - p.c1 * p.M22 * p.M23 - p.c2 ^ 3 * p.M13 - p.c2 ^ 2 * p.c3 * p.M12 + p.c2 ^ 2 * p.b - p.c2 * p.M22 * p.M13 - p.c3 * p.M22 * p.M12 + p.M22 * p.b

theorem qg_18_26_eq (p : Params K) :
    W p (ampV18 p) (T p 2 3 (ampV26 p)) = qg_18_26 p := by
  simp [qg_18_26, ampV18, ampV26, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_18_26 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_18_26 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * nD ^ 2 * oCD * RBCD := by
  simp only [qg_18_26, paramsN] <;> ring

def qg_18_27 (p : Params K) : K :=
  p.c1 * p.c2 ^ 3 * p.c3 ^ 2 + p.c1 * p.c2 ^ 3 * p.M33 + p.c1 * p.c2 * p.c3 ^ 2 * p.M22 + p.c1 * p.c2 * p.M22 * p.M33 - p.c2 ^ 2 * p.c3 ^ 2 * p.M12 - p.c2 ^ 2 * p.M33 * p.M12 - p.c3 ^ 2 * p.M22 * p.M12 - p.M22 * p.M33 * p.M12

theorem qg_18_27_eq (p : Params K) :
    W p (ampV18 p) (T p 2 3 (ampV27 p)) = qg_18_27 p := by
  simp [qg_18_27, ampV18, ampV27, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_18_27 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_18_27 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC ^ 2 * nD ^ 3 * oBD * oCD * wC := by
  simp only [qg_18_27, paramsN] <;> ring

def qg_19_21 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 - p.c1 * p.M23 - p.c2 * p.M13 - p.c3 * p.M12 + p.b

theorem qg_19_21_eq (p : Params K) :
    W p (ampV19 p) (T p 2 3 (ampV21 p)) = qg_19_21 p := by
  simp [qg_19_21, ampV19, ampV21, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_19_21 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_19_21 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * RBCD := by
  simp only [qg_19_21, paramsN] <;> ring

def qg_19_22 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 ^ 2 - p.c1 * p.c2 * p.M33 - 2 * p.c1 * p.c3 * p.M23 - 2 * p.c2 * p.c3 * p.M13 - p.c3 ^ 2 * p.M12 + 2 * p.c3 * p.b + p.M33 * p.M12

theorem qg_19_22_eq (p : Params K) :
    W p (ampV19 p) (T p 2 3 (ampV22 p)) = qg_19_22 p := by
  simp [qg_19_22, ampV19, ampV22, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_19_22 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_19_22 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB ^ 2 * nC * nD ^ 2 * oBD * wC + 2 * nB ^ 2 * nC * nD ^ 2 * RABD * RBCD := by
  simp only [qg_19_22, paramsN] <;> ring

def qg_19_23 (p : Params K) : K :=
  p.c1 * p.c2 ^ 2 * p.c3 + p.c1 * p.c3 * p.M22 - p.c2 ^ 2 * p.M13 - p.M22 * p.M13

theorem qg_19_23_eq (p : Params K) :
    W p (ampV19 p) (T p 2 3 (ampV23 p)) = qg_19_23 p := by
  simp [qg_19_23, ampV19, ampV23, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_19_23 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_19_23 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * nD ^ 2 * oCD * wB := by
  simp only [qg_19_23, paramsN] <;> ring

def qg_19_24 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 * p.c3 - p.c1 ^ 2 * p.M23 + 2 * p.c1 * p.b + p.c2 * p.c3 * p.M11 + p.M11 * p.M23 - 2 * p.M12 * p.M13

theorem qg_19_24_eq (p : Params K) :
    W p (ampV19 p) (T p 2 3 (ampV24 p)) = qg_19_24 p := by
  simp [qg_19_24, ampV19, ampV24, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_19_24 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_19_24 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * oBC * RABD * RACD - 2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * wB * wC - nB ^ 2 * nC ^ 2 * nD * oBC * wD + 2 * nB ^ 2 * nC ^ 2 * nD * RABC * RBCD := by
  simp only [qg_19_24, paramsN] <;> ring

def qg_19_25 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 * p.c3 ^ 2 - p.c1 ^ 2 * p.c2 * p.M33 - 2 * p.c1 ^ 2 * p.c3 * p.M23 - 4 * p.c1 * p.c2 * p.c3 * p.M13 - 2 * p.c1 * p.c3 ^ 2 * p.M12 + 2 * p.c1 * p.c3 * p.b + 2 * p.c1 * p.M13 * p.M23 - p.c2 * p.c3 ^ 2 * p.M11 - p.c2 * p.M11 * p.M33 + 2 * p.c2 * p.M13 ^ 2 + 2 * p.c3 * p.M12 * p.M13 - 2 * p.M13 * p.b

theorem qg_19_25_eq (p : Params K) :
    W p (ampV19 p) (T p 2 3 (ampV25 p)) = qg_19_25 p := by
  simp [qg_19_25, ampV19, ampV25, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_19_25 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_19_25 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB ^ 2 * nC ^ 2 * nD ^ 2 * oBC * oBD * RACD + 2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * RBCD * wB := by
  simp only [qg_19_25, paramsN] <;> ring

def qg_19_26 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 ^ 2 * p.c3 + p.c1 ^ 2 * p.c3 * p.M22 + p.c2 ^ 2 * p.c3 * p.M11 + p.c3 * p.M11 * p.M22

theorem qg_19_26_eq (p : Params K) :
    W p (ampV19 p) (T p 2 3 (ampV26 p)) = qg_19_26 p := by
  simp [qg_19_26, ampV19, ampV26, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_19_26 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_19_26 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC ^ 2 * nD ^ 2 * oBC * oCD * RABD := by
  simp only [qg_19_26, paramsN] <;> ring

def qg_19_27 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 ^ 2 * p.c3 ^ 2 - p.c1 ^ 2 * p.c2 ^ 2 * p.M33 - 4 * p.c1 ^ 2 * p.c2 * p.c3 * p.M23 - p.c1 ^ 2 * p.c3 ^ 2 * p.M22 - p.c1 ^ 2 * p.M22 * p.M33 + 2 * p.c1 ^ 2 * p.M23 ^ 2 - 4 * p.c1 * p.c2 ^ 2 * p.c3 * p.M13 - 4 * p.c1 * p.c2 * p.c3 ^ 2 * p.M12 + 4 * p.c1 * p.c2 * p.c3 * p.b + 4 * p.c1 * p.c2 * p.M13 * p.M23 + 4 * p.c1 * p.c3 * p.M12 * p.M23 - 4 * p.c1 * p.M23 * p.b - p.c2 ^ 2 * p.c3 ^ 2 * p.M11 - p.c2 ^ 2 * p.M11 * p.M33 + 2 * p.c2 ^ 2 * p.M13 ^ 2 + 4 * p.c2 * p.c3 * p.M12 * p.M13 - 4 * p.c2 * p.M13 * p.b - p.c3 ^ 2 * p.M11 * p.M22 + 2 * p.c3 ^ 2 * p.M12 ^ 2 - 4 * p.c3 * p.M12 * p.b - p.M11 * p.M22 * p.M33 + 2 * p.b ^ 2

theorem qg_19_27_eq (p : Params K) :
    W p (ampV19 p) (T p 2 3 (ampV27 p)) = qg_19_27 p := by
  simp [qg_19_27, ampV19, ampV27, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_19_27 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_19_27 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB ^ 2 * nC ^ 2 * nD ^ 2 * oBC * oBD * oCD + 2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * RBCD ^ 2 := by
  simp only [qg_19_27, paramsN] <;> ring

def qg_20_21 (p : Params K) : K :=
  p.c1 * p.c2 ^ 2 * p.c3 + p.c1 * p.c3 * p.M22 - p.c2 ^ 2 * p.M13 - p.M22 * p.M13

theorem qg_20_21_eq (p : Params K) :
    W p (ampV20 p) (T p 2 3 (ampV21 p)) = qg_20_21 p := by
  simp [qg_20_21, ampV20, ampV21, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_20_21 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_20_21 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * nD ^ 2 * oCD * wB := by
  simp only [qg_20_21, paramsN] <;> ring

def qg_20_22 (p : Params K) : K :=
  p.c1 * p.c2 ^ 2 * p.c3 ^ 2 + p.c1 * p.c2 ^ 2 * p.M33 + p.c1 * p.c3 ^ 2 * p.M22 + p.c1 * p.M22 * p.M33

theorem qg_20_22_eq (p : Params K) :
    W p (ampV20 p) (T p 2 3 (ampV22 p)) = qg_20_22 p := by
  simp [qg_20_22, ampV20, ampV22, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_20_22 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_20_22 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC ^ 2 * nD ^ 2 * oBD * oCD * RABC := by
  simp only [qg_20_22, paramsN] <;> ring

def qg_20_23 (p : Params K) : K :=
  p.c1 * p.c2 ^ 3 * p.c3 - p.c1 * p.c2 ^ 2 * p.M23 + p.c1 * p.c2 * p.c3 * p.M22 - p.c1 * p.M22 * p.M23 - p.c2 ^ 3 * p.M13 - p.c2 ^ 2 * p.c3 * p.M12 + p.c2 ^ 2 * p.b - p.c2 * p.M22 * p.M13 - p.c3 * p.M22 * p.M12 + p.M22 * p.b

theorem qg_20_23_eq (p : Params K) :
    W p (ampV20 p) (T p 2 3 (ampV23 p)) = qg_20_23 p := by
  simp [qg_20_23, ampV20, ampV23, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_20_23 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_20_23 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * nD ^ 2 * oCD * RBCD := by
  simp only [qg_20_23, paramsN] <;> ring

def qg_20_24 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 ^ 2 * p.c3 + p.c1 ^ 2 * p.c3 * p.M22 - 2 * p.c1 * p.c2 ^ 2 * p.M13 - 2 * p.c1 * p.M22 * p.M13 - p.c2 ^ 2 * p.c3 * p.M11 - p.c3 * p.M11 * p.M22

theorem qg_20_24_eq (p : Params K) :
    W p (ampV20 p) (T p 2 3 (ampV24 p)) = qg_20_24 p := by
  simp [qg_20_24, ampV20, ampV24, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_20_24 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_20_24 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC ^ 3 * nD ^ 2 * oCD * RABC * wB - nB ^ 2 * nC ^ 2 * nD ^ 2 * oBC * oCD * RABD := by
  simp only [qg_20_24, paramsN] <;> ring

def qg_20_25 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 ^ 2 * p.c3 ^ 2 + p.c1 ^ 2 * p.c2 ^ 2 * p.M33 + p.c1 ^ 2 * p.c3 ^ 2 * p.M22 + p.c1 ^ 2 * p.M22 * p.M33 + p.c2 ^ 2 * p.c3 ^ 2 * p.M11 + p.c2 ^ 2 * p.M11 * p.M33 + p.c3 ^ 2 * p.M11 * p.M22 + p.M11 * p.M22 * p.M33

theorem qg_20_25_eq (p : Params K) :
    W p (ampV20 p) (T p 2 3 (ampV25 p)) = qg_20_25 p := by
  simp [qg_20_25, ampV20, ampV25, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_20_25 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_20_25 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC ^ 2 * nD ^ 2 * oBC * oBD * oCD := by
  simp only [qg_20_25, paramsN] <;> ring

def qg_20_26 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 ^ 3 * p.c3 - p.c1 ^ 2 * p.c2 ^ 2 * p.M23 + p.c1 ^ 2 * p.c2 * p.c3 * p.M22 - p.c1 ^ 2 * p.M22 * p.M23 - 2 * p.c1 * p.c2 ^ 3 * p.M13 - 2 * p.c1 * p.c2 ^ 2 * p.c3 * p.M12 + 2 * p.c1 * p.c2 ^ 2 * p.b - 2 * p.c1 * p.c2 * p.M22 * p.M13 - 2 * p.c1 * p.c3 * p.M22 * p.M12 + 2 * p.c1 * p.M22 * p.b - p.c2 ^ 3 * p.c3 * p.M11 + p.c2 ^ 2 * p.M11 * p.M23 - p.c2 * p.c3 * p.M11 * p.M22 + p.M11 * p.M22 * p.M23

theorem qg_20_26_eq (p : Params K) :
    W p (ampV20 p) (T p 2 3 (ampV26 p)) = qg_20_26 p := by
  simp [qg_20_26, ampV20, ampV26, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_20_26 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_20_26 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB ^ 2 * nC ^ 3 * nD ^ 2 * oBC * oCD * wD + 2 * nB ^ 2 * nC ^ 3 * nD ^ 2 * oCD * RABC * RBCD := by
  simp only [qg_20_26, paramsN] <;> ring

def qg_20_27 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 ^ 3 * p.c3 ^ 2 + p.c1 ^ 2 * p.c2 ^ 3 * p.M33 + p.c1 ^ 2 * p.c2 * p.c3 ^ 2 * p.M22 + p.c1 ^ 2 * p.c2 * p.M22 * p.M33 + p.c2 ^ 3 * p.c3 ^ 2 * p.M11 + p.c2 ^ 3 * p.M11 * p.M33 + p.c2 * p.c3 ^ 2 * p.M11 * p.M22 + p.c2 * p.M11 * p.M22 * p.M33

theorem qg_20_27_eq (p : Params K) :
    W p (ampV20 p) (T p 2 3 (ampV27 p)) = qg_20_27 p := by
  simp [qg_20_27, ampV20, ampV27, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_20_27 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_20_27 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC ^ 3 * nD ^ 3 * oBC * oBD * oCD * RACD := by
  simp only [qg_20_27, paramsN] <;> ring

end LemmaB.TableModel
