/- SPDX-License-Identifier: Apache-2.0
   Machine-generated file. -/
module

public import TableModel.Amps

/-! # Table-model identity, part 2 (frames C, C): the model values in the gauge parameters

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

def qg_14_14 (p : Params K) : K :=
  p.mC

theorem qg_14_14_eq (p : Params K) :
    W p (ampV14 p) (T p 2 2 (ampV14 p)) = qg_14_14 p := by
  simp [qg_14_14, ampV14, ampV14, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_14_14 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_14_14 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nC := by
  simp only [qg_14_14, paramsN] <;> ring

def qg_14_15 (p : Params K) : K :=
  p.mC * p.c2

theorem qg_14_15_eq (p : Params K) :
    W p (ampV14 p) (T p 2 2 (ampV15 p)) = qg_14_15 p := by
  simp [qg_14_15, ampV14, ampV15, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_14_15 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_14_15 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nC ^ 2 * nD * RACD := by
  simp only [qg_14_15, paramsN] <;> ring

def qg_14_16 (p : Params K) : K :=
  p.mC * p.c1

theorem qg_14_16_eq (p : Params K) :
    W p (ampV14 p) (T p 2 2 (ampV16 p)) = qg_14_16 p := by
  simp [qg_14_16, ampV14, ampV16, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_14_16 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_14_16 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * RABC := by
  simp only [qg_14_16, paramsN] <;> ring

def qg_14_17 (p : Params K) : K :=
  p.mC * p.c3

theorem qg_14_17_eq (p : Params K) :
    W p (ampV14 p) (T p 2 2 (ampV17 p)) = qg_14_17 p := by
  simp [qg_14_17, ampV14, ampV17, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_14_17 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_14_17 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * RABD := by
  simp only [qg_14_17, paramsN] <;> ring

def qg_14_18 (p : Params K) : K :=
  p.mC * p.c2 * p.c3 - p.mC * p.M23

theorem qg_14_18_eq (p : Params K) :
    W p (ampV14 p) (T p 2 2 (ampV18 p)) = qg_14_18 p := by
  simp [qg_14_18, ampV14, ampV18, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_14_18 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_14_18 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * nD * wD := by
  simp only [qg_14_18, paramsN] <;> ring

def qg_14_19 (p : Params K) : K :=
  p.mC * p.c1 * p.c3 - p.mC * p.M13

theorem qg_14_19_eq (p : Params K) :
    W p (ampV14 p) (T p 2 2 (ampV19 p)) = qg_14_19 p := by
  simp [qg_14_19, ampV14, ampV19, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_14_19 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_14_19 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * nD * wB := by
  simp only [qg_14_19, paramsN] <;> ring

def qg_14_20 (p : Params K) : K :=
  p.mC * p.c1 * p.c2 * p.c3 - p.mC * p.c1 * p.M23 - p.mC * p.c2 * p.M13 - p.mC * p.c3 * p.M12 + p.mC * p.b

theorem qg_14_20_eq (p : Params K) :
    W p (ampV14 p) (T p 2 2 (ampV20 p)) = qg_14_20 p := by
  simp [qg_14_20, ampV14, ampV20, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_14_20 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_14_20 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * nD * RBCD := by
  simp only [qg_14_20, paramsN] <;> ring

def qg_15_15 (p : Params K) : K :=
  p.mC * p.c2 ^ 2 + p.mC * p.M22

theorem qg_15_15_eq (p : Params K) :
    W p (ampV15 p) (T p 2 2 (ampV15 p)) = qg_15_15 p := by
  simp [qg_15_15, ampV15, ampV15, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_15_15 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_15_15 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nC ^ 2 * nD * oCD := by
  simp only [qg_15_15, paramsN] <;> ring

def qg_15_16 (p : Params K) : K :=
  p.mC * p.c1 * p.c2 - p.mC * p.M12

theorem qg_15_16_eq (p : Params K) :
    W p (ampV15 p) (T p 2 2 (ampV16 p)) = qg_15_16 p := by
  simp [qg_15_16, ampV15, ampV16, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_15_16 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_15_16 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * nD * wC := by
  simp only [qg_15_16, paramsN] <;> ring

def qg_15_17 (p : Params K) : K :=
  p.mC * p.c2 * p.c3 - p.mC * p.M23

theorem qg_15_17_eq (p : Params K) :
    W p (ampV15 p) (T p 2 2 (ampV17 p)) = qg_15_17 p := by
  simp [qg_15_17, ampV15, ampV17, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_15_17 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_15_17 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * nD * wD := by
  simp only [qg_15_17, paramsN] <;> ring

def qg_15_18 (p : Params K) : K :=
  p.mC * p.c2 ^ 2 * p.c3 + p.mC * p.c3 * p.M22

theorem qg_15_18_eq (p : Params K) :
    W p (ampV15 p) (T p 2 2 (ampV18 p)) = qg_15_18 p := by
  simp [qg_15_18, ampV15, ampV18, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_15_18 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_15_18 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * nD ^ 2 * oCD * RABD := by
  simp only [qg_15_18, paramsN] <;> ring

def qg_15_19 (p : Params K) : K :=
  p.mC * p.c1 * p.c2 * p.c3 - p.mC * p.c1 * p.M23 - p.mC * p.c2 * p.M13 - p.mC * p.c3 * p.M12 + p.mC * p.b

theorem qg_15_19_eq (p : Params K) :
    W p (ampV15 p) (T p 2 2 (ampV19 p)) = qg_15_19 p := by
  simp [qg_15_19, ampV15, ampV19, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_15_19 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_15_19 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * nD * RBCD := by
  simp only [qg_15_19, paramsN] <;> ring

def qg_15_20 (p : Params K) : K :=
  p.mC * p.c1 * p.c2 ^ 2 * p.c3 + p.mC * p.c1 * p.c3 * p.M22 - p.mC * p.c2 ^ 2 * p.M13 - p.mC * p.M22 * p.M13

theorem qg_15_20_eq (p : Params K) :
    W p (ampV15 p) (T p 2 2 (ampV20 p)) = qg_15_20 p := by
  simp [qg_15_20, ampV15, ampV20, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_15_20 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_15_20 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 3 * nD ^ 2 * oCD * wB := by
  simp only [qg_15_20, paramsN] <;> ring

def qg_16_16 (p : Params K) : K :=
  p.mC * p.c1 ^ 2 + p.mC * p.M11

theorem qg_16_16_eq (p : Params K) :
    W p (ampV16 p) (T p 2 2 (ampV16 p)) = qg_16_16 p := by
  simp [qg_16_16, ampV16, ampV16, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_16_16 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_16_16 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * oBC := by
  simp only [qg_16_16, paramsN] <;> ring

def qg_16_17 (p : Params K) : K :=
  p.mC * p.c1 * p.c3 + p.mC * p.M13

theorem qg_16_17_eq (p : Params K) :
    W p (ampV16 p) (T p 2 2 (ampV17 p)) = qg_16_17 p := by
  simp [qg_16_17, ampV16, ampV17, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_16_17 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_16_17 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC ^ 2 * nD * RABC * RABD - nB * nC ^ 2 * nD * wB := by
  simp only [qg_16_17, paramsN] <;> ring

def qg_16_18 (p : Params K) : K :=
  p.mC * p.c1 * p.c2 * p.c3 - p.mC * p.c1 * p.M23 - p.mC * p.c2 * p.M13 - p.mC * p.c3 * p.M12 + p.mC * p.b

theorem qg_16_18_eq (p : Params K) :
    W p (ampV16 p) (T p 2 2 (ampV18 p)) = qg_16_18 p := by
  simp [qg_16_18, ampV16, ampV18, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_16_18 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_16_18 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * nD * RBCD := by
  simp only [qg_16_18, paramsN] <;> ring

def qg_16_19 (p : Params K) : K :=
  p.mC * p.c1 ^ 2 * p.c3 + p.mC * p.c3 * p.M11

theorem qg_16_19_eq (p : Params K) :
    W p (ampV16 p) (T p 2 2 (ampV19 p)) = qg_16_19 p := by
  simp [qg_16_19, ampV16, ampV19, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_16_19 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_16_19 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC ^ 2 * nD * oBC * RABD := by
  simp only [qg_16_19, paramsN] <;> ring

def qg_16_20 (p : Params K) : K :=
  p.mC * p.c1 ^ 2 * p.c2 * p.c3 - p.mC * p.c1 ^ 2 * p.M23 - 2 * p.mC * p.c1 * p.c2 * p.M13 - 2 * p.mC * p.c1 * p.c3 * p.M12 + 2 * p.mC * p.c1 * p.b - p.mC * p.c2 * p.c3 * p.M11 + p.mC * p.M11 * p.M23

theorem qg_16_20_eq (p : Params K) :
    W p (ampV16 p) (T p 2 2 (ampV20 p)) = qg_16_20 p := by
  simp [qg_16_20, ampV16, ampV20, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_16_20 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_16_20 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB ^ 2 * nC ^ 3 * nD * oBC * wD + 2 * nB ^ 2 * nC ^ 3 * nD * RABC * RBCD := by
  simp only [qg_16_20, paramsN] <;> ring

def qg_17_17 (p : Params K) : K :=
  p.mC * p.c3 ^ 2 + p.mC * p.M33

theorem qg_17_17_eq (p : Params K) :
    W p (ampV17 p) (T p 2 2 (ampV17 p)) = qg_17_17 p := by
  simp [qg_17_17, ampV17, ampV17, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_17_17 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_17_17 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * oBD := by
  simp only [qg_17_17, paramsN] <;> ring

def qg_17_18 (p : Params K) : K :=
  p.mC * p.c2 * p.c3 ^ 2 - p.mC * p.c2 * p.M33 - 2 * p.mC * p.c3 * p.M23

theorem qg_17_18_eq (p : Params K) :
    W p (ampV17 p) (T p 2 2 (ampV18 p)) = qg_17_18 p := by
  simp [qg_17_18, ampV17, ampV18, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_17_18 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_17_18 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * RABD * wD - nB * nC ^ 2 * nD ^ 2 * oBD * RACD := by
  simp only [qg_17_18, paramsN] <;> ring

def qg_17_19 (p : Params K) : K :=
  p.mC * p.c1 * p.c3 ^ 2 + p.mC * p.c1 * p.M33

theorem qg_17_19_eq (p : Params K) :
    W p (ampV17 p) (T p 2 2 (ampV19 p)) = qg_17_19 p := by
  simp [qg_17_19, ampV17, ampV19, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_17_19 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_17_19 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC ^ 2 * nD * oBD * RABC := by
  simp only [qg_17_19, paramsN] <;> ring

def qg_17_20 (p : Params K) : K :=
  p.mC * p.c1 * p.c2 * p.c3 ^ 2 - p.mC * p.c1 * p.c2 * p.M33 - 2 * p.mC * p.c1 * p.c3 * p.M23 - 2 * p.mC * p.c2 * p.c3 * p.M13 - p.mC * p.c3 ^ 2 * p.M12 - p.mC * p.M33 * p.M12 + 2 * p.mC * p.M13 * p.M23

theorem qg_17_20_eq (p : Params K) :
    W p (ampV17 p) (T p 2 2 (ampV20 p)) = qg_17_20 p := by
  simp [qg_17_20, ampV17, ampV20, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_17_20 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_17_20 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -2 * nB ^ 2 * nC ^ 3 * nD ^ 2 * oBD * RABC * RACD + 2 * nB ^ 2 * nC ^ 3 * nD ^ 2 * wB * wD + nB ^ 2 * nC ^ 2 * nD ^ 2 * oBD * wC := by
  simp only [qg_17_20, paramsN] <;> ring

def qg_18_18 (p : Params K) : K :=
  p.mC * p.c2 ^ 2 * p.c3 ^ 2 + p.mC * p.c2 ^ 2 * p.M33 + p.mC * p.c3 ^ 2 * p.M22 + p.mC * p.M22 * p.M33

theorem qg_18_18_eq (p : Params K) :
    W p (ampV18 p) (T p 2 2 (ampV18 p)) = qg_18_18 p := by
  simp [qg_18_18, ampV18, ampV18, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_18_18 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_18_18 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * nD ^ 2 * oBD * oCD := by
  simp only [qg_18_18, paramsN] <;> ring

def qg_18_19 (p : Params K) : K :=
  p.mC * p.c1 * p.c2 * p.c3 ^ 2 - p.mC * p.c1 * p.c2 * p.M33 - 2 * p.mC * p.c1 * p.c3 * p.M23 - 2 * p.mC * p.c2 * p.c3 * p.M13 - p.mC * p.c3 ^ 2 * p.M12 + 2 * p.mC * p.c3 * p.b + p.mC * p.M33 * p.M12

theorem qg_18_19_eq (p : Params K) :
    W p (ampV18 p) (T p 2 2 (ampV19 p)) = qg_18_19 p := by
  simp [qg_18_19, ampV18, ampV19, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_18_19 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_18_19 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB ^ 2 * nC ^ 2 * nD ^ 2 * oBD * wC + 2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * RABD * RBCD := by
  simp only [qg_18_19, paramsN] <;> ring

def qg_18_20 (p : Params K) : K :=
  p.mC * p.c1 * p.c2 ^ 2 * p.c3 ^ 2 + p.mC * p.c1 * p.c2 ^ 2 * p.M33 + p.mC * p.c1 * p.c3 ^ 2 * p.M22 + p.mC * p.c1 * p.M22 * p.M33

theorem qg_18_20_eq (p : Params K) :
    W p (ampV18 p) (T p 2 2 (ampV20 p)) = qg_18_20 p := by
  simp [qg_18_20, ampV18, ampV20, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_18_20 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_18_20 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC ^ 3 * nD ^ 2 * oBD * oCD * RABC := by
  simp only [qg_18_20, paramsN] <;> ring

def qg_19_19 (p : Params K) : K :=
  p.mC * p.c1 ^ 2 * p.c3 ^ 2 + p.mC * p.c1 ^ 2 * p.M33 + p.mC * p.c3 ^ 2 * p.M11 + p.mC * p.M11 * p.M33

theorem qg_19_19_eq (p : Params K) :
    W p (ampV19 p) (T p 2 2 (ampV19 p)) = qg_19_19 p := by
  simp [qg_19_19, ampV19, ampV19, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_19_19 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_19_19 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC ^ 2 * nD * oBC * oBD := by
  simp only [qg_19_19, paramsN] <;> ring

def qg_19_20 (p : Params K) : K :=
  p.mC * p.c1 ^ 2 * p.c2 * p.c3 ^ 2 - p.mC * p.c1 ^ 2 * p.c2 * p.M33 - 2 * p.mC * p.c1 ^ 2 * p.c3 * p.M23 - 4 * p.mC * p.c1 * p.c2 * p.c3 * p.M13 - 2 * p.mC * p.c1 * p.c3 ^ 2 * p.M12 + 2 * p.mC * p.c1 * p.c3 * p.b + 2 * p.mC * p.c1 * p.M13 * p.M23 - p.mC * p.c2 * p.c3 ^ 2 * p.M11 - p.mC * p.c2 * p.M11 * p.M33 + 2 * p.mC * p.c2 * p.M13 ^ 2 + 2 * p.mC * p.c3 * p.M12 * p.M13 - 2 * p.mC * p.M13 * p.b

theorem qg_19_20_eq (p : Params K) :
    W p (ampV19 p) (T p 2 2 (ampV20 p)) = qg_19_20 p := by
  simp [qg_19_20, ampV19, ampV20, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_19_20 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_19_20 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB ^ 2 * nC ^ 3 * nD ^ 2 * oBC * oBD * RACD + 2 * nB ^ 2 * nC ^ 3 * nD ^ 2 * RBCD * wB := by
  simp only [qg_19_20, paramsN] <;> ring

def qg_20_20 (p : Params K) : K :=
  p.mC * p.c1 ^ 2 * p.c2 ^ 2 * p.c3 ^ 2 + p.mC * p.c1 ^ 2 * p.c2 ^ 2 * p.M33 + p.mC * p.c1 ^ 2 * p.c3 ^ 2 * p.M22 + p.mC * p.c1 ^ 2 * p.M22 * p.M33 + p.mC * p.c2 ^ 2 * p.c3 ^ 2 * p.M11 + p.mC * p.c2 ^ 2 * p.M11 * p.M33 + p.mC * p.c3 ^ 2 * p.M11 * p.M22 + p.mC * p.M11 * p.M22 * p.M33

theorem qg_20_20_eq (p : Params K) :
    W p (ampV20 p) (T p 2 2 (ampV20 p)) = qg_20_20 p := by
  simp [qg_20_20, ampV20, ampV20, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_20_20 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_20_20 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC ^ 3 * nD ^ 2 * oBC * oBD * oCD := by
  simp only [qg_20_20, paramsN] <;> ring

end LemmaB.TableModel
