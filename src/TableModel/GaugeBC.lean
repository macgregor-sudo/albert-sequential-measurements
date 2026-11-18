/- SPDX-License-Identifier: Apache-2.0
   Machine-generated file. -/
module

public import TableModel.Amps

/-! # Table-model identity, part 2 (frames B, C): the model values in the gauge parameters

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

def qg_7_14 (p : Params K) : K :=
  p.c1

theorem qg_7_14_eq (p : Params K) :
    W p (ampV7 p) (T p 1 2 (ampV14 p)) = qg_7_14 p := by
  simp [qg_7_14, ampV7, ampV14, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_7_14 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_7_14 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * RABC := by
  simp only [qg_7_14, paramsN] <;> ring

def qg_7_15 (p : Params K) : K :=
  p.c1 * p.c2 - p.M12

theorem qg_7_15_eq (p : Params K) :
    W p (ampV7 p) (T p 1 2 (ampV15 p)) = qg_7_15 p := by
  simp [qg_7_15, ampV7, ampV15, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_7_15 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_7_15 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * wC := by
  simp only [qg_7_15, paramsN] <;> ring

def qg_7_16 (p : Params K) : K :=
  p.c1 ^ 2 + p.M11

theorem qg_7_16_eq (p : Params K) :
    W p (ampV7 p) (T p 1 2 (ampV16 p)) = qg_7_16 p := by
  simp [qg_7_16, ampV7, ampV16, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_7_16 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_7_16 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * oBC := by
  simp only [qg_7_16, paramsN] <;> ring

def qg_7_17 (p : Params K) : K :=
  p.c1 * p.c3 + p.M13

theorem qg_7_17_eq (p : Params K) :
    W p (ampV7 p) (T p 1 2 (ampV17 p)) = qg_7_17 p := by
  simp [qg_7_17, ampV7, ampV17, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_7_17 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_7_17 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC * nD * RABC * RABD - nB * nC * nD * wB := by
  simp only [qg_7_17, paramsN] <;> ring

def qg_7_18 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 - p.c1 * p.M23 - p.c2 * p.M13 - p.c3 * p.M12 + p.b

theorem qg_7_18_eq (p : Params K) :
    W p (ampV7 p) (T p 1 2 (ampV18 p)) = qg_7_18 p := by
  simp [qg_7_18, ampV7, ampV18, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_7_18 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_7_18 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * RBCD := by
  simp only [qg_7_18, paramsN] <;> ring

def qg_7_19 (p : Params K) : K :=
  p.c1 ^ 2 * p.c3 + p.c3 * p.M11

theorem qg_7_19_eq (p : Params K) :
    W p (ampV7 p) (T p 1 2 (ampV19 p)) = qg_7_19 p := by
  simp [qg_7_19, ampV7, ampV19, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_7_19 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_7_19 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD * oBC * RABD := by
  simp only [qg_7_19, paramsN] <;> ring

def qg_7_20 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 * p.c3 - p.c1 ^ 2 * p.M23 - 2 * p.c1 * p.c2 * p.M13 - 2 * p.c1 * p.c3 * p.M12 + 2 * p.c1 * p.b - p.c2 * p.c3 * p.M11 + p.M11 * p.M23

theorem qg_7_20_eq (p : Params K) :
    W p (ampV7 p) (T p 1 2 (ampV20 p)) = qg_7_20 p := by
  simp [qg_7_20, ampV7, ampV20, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_7_20 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_7_20 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB ^ 2 * nC ^ 2 * nD * oBC * wD + 2 * nB ^ 2 * nC ^ 2 * nD * RABC * RBCD := by
  simp only [qg_7_20, paramsN] <;> ring

def qg_8_14 (p : Params K) : K :=
  p.c1 ^ 2 + p.M11

theorem qg_8_14_eq (p : Params K) :
    W p (ampV8 p) (T p 1 2 (ampV14 p)) = qg_8_14 p := by
  simp [qg_8_14, ampV8, ampV14, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_8_14 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_8_14 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * oBC := by
  simp only [qg_8_14, paramsN] <;> ring

def qg_8_15 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 + p.c2 * p.M11

theorem qg_8_15_eq (p : Params K) :
    W p (ampV8 p) (T p 1 2 (ampV15 p)) = qg_8_15 p := by
  simp [qg_8_15, ampV8, ampV15, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_8_15 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_8_15 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * nD * oBC * RACD := by
  simp only [qg_8_15, paramsN] <;> ring

def qg_8_16 (p : Params K) : K :=
  p.c1 ^ 3 + p.c1 * p.M11

theorem qg_8_16_eq (p : Params K) :
    W p (ampV8 p) (T p 1 2 (ampV16 p)) = qg_8_16 p := by
  simp [qg_8_16, ampV8, ampV16, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_8_16 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_8_16 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC ^ 2 * oBC * RABC := by
  simp only [qg_8_16, paramsN] <;> ring

def qg_8_17 (p : Params K) : K :=
  p.c1 ^ 2 * p.c3 + p.c3 * p.M11

theorem qg_8_17_eq (p : Params K) :
    W p (ampV8 p) (T p 1 2 (ampV17 p)) = qg_8_17 p := by
  simp [qg_8_17, ampV8, ampV17, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_8_17 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_8_17 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD * oBC * RABD := by
  simp only [qg_8_17, paramsN] <;> ring

def qg_8_18 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 * p.c3 - p.c1 ^ 2 * p.M23 + p.c2 * p.c3 * p.M11 - p.M11 * p.M23

theorem qg_8_18_eq (p : Params K) :
    W p (ampV8 p) (T p 1 2 (ampV18 p)) = qg_8_18 p := by
  simp [qg_8_18, ampV8, ampV18, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_8_18 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_8_18 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC ^ 2 * nD * oBC * wD := by
  simp only [qg_8_18, paramsN] <;> ring

def qg_8_19 (p : Params K) : K :=
  p.c1 ^ 3 * p.c3 - p.c1 ^ 2 * p.M13 + p.c1 * p.c3 * p.M11 - p.M11 * p.M13

theorem qg_8_19_eq (p : Params K) :
    W p (ampV8 p) (T p 1 2 (ampV19 p)) = qg_8_19 p := by
  simp [qg_8_19, ampV8, ampV19, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_8_19 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_8_19 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC ^ 2 * nD * oBC * wB := by
  simp only [qg_8_19, paramsN] <;> ring

def qg_8_20 (p : Params K) : K :=
  p.c1 ^ 3 * p.c2 * p.c3 - p.c1 ^ 3 * p.M23 - p.c1 ^ 2 * p.c2 * p.M13 - p.c1 ^ 2 * p.c3 * p.M12 + p.c1 ^ 2 * p.b + p.c1 * p.c2 * p.c3 * p.M11 - p.c1 * p.M11 * p.M23 - p.c2 * p.M11 * p.M13 - p.c3 * p.M11 * p.M12 + p.M11 * p.b

theorem qg_8_20_eq (p : Params K) :
    W p (ampV8 p) (T p 1 2 (ampV20 p)) = qg_8_20 p := by
  simp [qg_8_20, ampV8, ampV20, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_8_20 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_8_20 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC ^ 2 * nD * oBC * RBCD := by
  simp only [qg_8_20, paramsN] <;> ring

def qg_9_14 (p : Params K) : K :=
  p.c1 * p.c3 - p.M13

theorem qg_9_14_eq (p : Params K) :
    W p (ampV9 p) (T p 1 2 (ampV14 p)) = qg_9_14 p := by
  simp [qg_9_14, ampV9, ampV14, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_9_14 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_9_14 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * wB := by
  simp only [qg_9_14, paramsN] <;> ring

def qg_9_15 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 - p.c1 * p.M23 - p.c2 * p.M13 - p.c3 * p.M12 + p.b

theorem qg_9_15_eq (p : Params K) :
    W p (ampV9 p) (T p 1 2 (ampV15 p)) = qg_9_15 p := by
  simp [qg_9_15, ampV9, ampV15, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_9_15 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_9_15 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * RBCD := by
  simp only [qg_9_15, paramsN] <;> ring

def qg_9_16 (p : Params K) : K :=
  p.c1 ^ 2 * p.c3 + p.c3 * p.M11

theorem qg_9_16_eq (p : Params K) :
    W p (ampV9 p) (T p 1 2 (ampV16 p)) = qg_9_16 p := by
  simp [qg_9_16, ampV9, ampV16, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_9_16 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_9_16 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD * oBC * RABD := by
  simp only [qg_9_16, paramsN] <;> ring

def qg_9_17 (p : Params K) : K :=
  p.c1 * p.c3 ^ 2 + p.c1 * p.M33

theorem qg_9_17_eq (p : Params K) :
    W p (ampV9 p) (T p 1 2 (ampV17 p)) = qg_9_17 p := by
  simp [qg_9_17, ampV9, ampV17, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_9_17 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_9_17 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD * oBD * RABC := by
  simp only [qg_9_17, paramsN] <;> ring

def qg_9_18 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 ^ 2 - p.c1 * p.c2 * p.M33 - 2 * p.c1 * p.c3 * p.M23 - 2 * p.c2 * p.c3 * p.M13 - p.c3 ^ 2 * p.M12 + 2 * p.c3 * p.b + p.M33 * p.M12

theorem qg_9_18_eq (p : Params K) :
    W p (ampV9 p) (T p 1 2 (ampV18 p)) = qg_9_18 p := by
  simp [qg_9_18, ampV9, ampV18, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_9_18 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_9_18 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB ^ 2 * nC * nD ^ 2 * oBD * wC + 2 * nB ^ 2 * nC * nD ^ 2 * RABD * RBCD := by
  simp only [qg_9_18, paramsN] <;> ring

def qg_9_19 (p : Params K) : K :=
  p.c1 ^ 2 * p.c3 ^ 2 + p.c1 ^ 2 * p.M33 + p.c3 ^ 2 * p.M11 + p.M11 * p.M33

theorem qg_9_19_eq (p : Params K) :
    W p (ampV9 p) (T p 1 2 (ampV19 p)) = qg_9_19 p := by
  simp [qg_9_19, ampV9, ampV19, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_9_19 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_9_19 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD * oBC * oBD := by
  simp only [qg_9_19, paramsN] <;> ring

def qg_9_20 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 * p.c3 ^ 2 - p.c1 ^ 2 * p.c2 * p.M33 - 2 * p.c1 ^ 2 * p.c3 * p.M23 - 4 * p.c1 * p.c2 * p.c3 * p.M13 - 2 * p.c1 * p.c3 ^ 2 * p.M12 + 2 * p.c1 * p.c3 * p.b + 2 * p.c1 * p.M13 * p.M23 - p.c2 * p.c3 ^ 2 * p.M11 - p.c2 * p.M11 * p.M33 + 2 * p.c2 * p.M13 ^ 2 + 2 * p.c3 * p.M12 * p.M13 - 2 * p.M13 * p.b

theorem qg_9_20_eq (p : Params K) :
    W p (ampV9 p) (T p 1 2 (ampV20 p)) = qg_9_20 p := by
  simp [qg_9_20, ampV9, ampV20, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_9_20 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_9_20 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB ^ 2 * nC ^ 2 * nD ^ 2 * oBC * oBD * RACD + 2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * RBCD * wB := by
  simp only [qg_9_20, paramsN] <;> ring

def qg_10_14 (p : Params K) : K :=
  p.c1 * p.c2 - p.M12

theorem qg_10_14_eq (p : Params K) :
    W p (ampV10 p) (T p 1 2 (ampV14 p)) = qg_10_14 p := by
  simp [qg_10_14, ampV10, ampV14, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_10_14 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_10_14 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * wC := by
  simp only [qg_10_14, paramsN] <;> ring

def qg_10_15 (p : Params K) : K :=
  p.c1 * p.c2 ^ 2 - p.c1 * p.M22 - 2 * p.c2 * p.M12

theorem qg_10_15_eq (p : Params K) :
    W p (ampV10 p) (T p 1 2 (ampV15 p)) = qg_10_15 p := by
  simp [qg_10_15, ampV10, ampV15, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_10_15 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_10_15 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB * nC ^ 2 * nD ^ 2 * RACD * wC - nB * nC ^ 2 * nD * oCD * RABC := by
  simp only [qg_10_15, paramsN] <;> ring

def qg_10_16 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 + p.c2 * p.M11

theorem qg_10_16_eq (p : Params K) :
    W p (ampV10 p) (T p 1 2 (ampV16 p)) = qg_10_16 p := by
  simp [qg_10_16, ampV10, ampV16, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_10_16 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_10_16 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * nD * oBC * RACD := by
  simp only [qg_10_16, paramsN] <;> ring

def qg_10_17 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 + p.c1 * p.M23 + p.c2 * p.M13 - p.c3 * p.M12 + p.b

theorem qg_10_17_eq (p : Params K) :
    W p (ampV10 p) (T p 1 2 (ampV17 p)) = qg_10_17 p := by
  simp [qg_10_17, ampV10, ampV17, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_10_17 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_10_17 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      4 * nB ^ 2 * nC ^ 2 * nD ^ 2 * RABC * RABD * RACD - 2 * nB ^ 2 * nC ^ 2 * nD * RABC * wD - 2 * nB * nC ^ 2 * nD ^ 2 * RACD * wB + nB * nC * nD * RBCD := by
  simp only [qg_10_17, paramsN] <;> ring

def qg_10_18 (p : Params K) : K :=
  p.c1 * p.c2 ^ 2 * p.c3 - 2 * p.c1 * p.c2 * p.M23 - p.c1 * p.c3 * p.M22 - p.c2 ^ 2 * p.M13 - 2 * p.c2 * p.c3 * p.M12 - p.M22 * p.M13 + 2 * p.M12 * p.M23

theorem qg_10_18_eq (p : Params K) :
    W p (ampV10 p) (T p 1 2 (ampV18 p)) = qg_10_18 p := by
  simp [qg_10_18, ampV10, ampV18, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_10_18 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_10_18 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * oCD * RABC * RABD + 2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * wC * wD + nB * nC ^ 2 * nD ^ 2 * oCD * wB := by
  simp only [qg_10_18, paramsN] <;> ring

def qg_10_19 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 * p.c3 + p.c1 ^ 2 * p.M23 + p.c2 * p.c3 * p.M11 + p.M11 * p.M23

theorem qg_10_19_eq (p : Params K) :
    W p (ampV10 p) (T p 1 2 (ampV19 p)) = qg_10_19 p := by
  simp [qg_10_19, ampV10, ampV19, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_10_19 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_10_19 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * oBC * RABD * RACD - nB ^ 2 * nC ^ 2 * nD * oBC * wD := by
  simp only [qg_10_19, paramsN] <;> ring

def qg_10_20 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 ^ 2 * p.c3 - 2 * p.c1 ^ 2 * p.c2 * p.M23 - p.c1 ^ 2 * p.c3 * p.M22 - 2 * p.c1 * p.c2 ^ 2 * p.M13 - 4 * p.c1 * p.c2 * p.c3 * p.M12 + 2 * p.c1 * p.c2 * p.b + 2 * p.c1 * p.M12 * p.M23 - p.c2 ^ 2 * p.c3 * p.M11 + 2 * p.c2 * p.M12 * p.M13 - p.c3 * p.M11 * p.M22 + 2 * p.c3 * p.M12 ^ 2 - 2 * p.M12 * p.b

theorem qg_10_20_eq (p : Params K) :
    W p (ampV10 p) (T p 1 2 (ampV20 p)) = qg_10_20 p := by
  simp [qg_10_20, ampV10, ampV20, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_10_20 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_10_20 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB ^ 2 * nC ^ 2 * nD ^ 2 * oBC * oCD * RABD + 2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * RBCD * wC := by
  simp only [qg_10_20, paramsN] <;> ring

def qg_11_14 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 + p.c2 * p.M11

theorem qg_11_14_eq (p : Params K) :
    W p (ampV11 p) (T p 1 2 (ampV14 p)) = qg_11_14 p := by
  simp [qg_11_14, ampV11, ampV14, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_11_14 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_11_14 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * nD * oBC * RACD := by
  simp only [qg_11_14, paramsN] <;> ring

def qg_11_15 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 ^ 2 + p.c1 ^ 2 * p.M22 + p.c2 ^ 2 * p.M11 + p.M11 * p.M22

theorem qg_11_15_eq (p : Params K) :
    W p (ampV11 p) (T p 1 2 (ampV15 p)) = qg_11_15 p := by
  simp [qg_11_15, ampV11, ampV15, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_11_15 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_11_15 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * nD * oBC * oCD := by
  simp only [qg_11_15, paramsN] <;> ring

def qg_11_16 (p : Params K) : K :=
  p.c1 ^ 3 * p.c2 - p.c1 ^ 2 * p.M12 + p.c1 * p.c2 * p.M11 - p.M11 * p.M12

theorem qg_11_16_eq (p : Params K) :
    W p (ampV11 p) (T p 1 2 (ampV16 p)) = qg_11_16 p := by
  simp [qg_11_16, ampV11, ampV16, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_11_16 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_11_16 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC ^ 2 * nD * oBC * wC := by
  simp only [qg_11_16, paramsN] <;> ring

def qg_11_17 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 * p.c3 - p.c1 ^ 2 * p.M23 + p.c2 * p.c3 * p.M11 - p.M11 * p.M23

theorem qg_11_17_eq (p : Params K) :
    W p (ampV11 p) (T p 1 2 (ampV17 p)) = qg_11_17 p := by
  simp [qg_11_17, ampV11, ampV17, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_11_17 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_11_17 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC ^ 2 * nD * oBC * wD := by
  simp only [qg_11_17, paramsN] <;> ring

def qg_11_18 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 ^ 2 * p.c3 + p.c1 ^ 2 * p.c3 * p.M22 + p.c2 ^ 2 * p.c3 * p.M11 + p.c3 * p.M11 * p.M22

theorem qg_11_18_eq (p : Params K) :
    W p (ampV11 p) (T p 1 2 (ampV18 p)) = qg_11_18 p := by
  simp [qg_11_18, ampV11, ampV18, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_11_18 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_11_18 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC ^ 2 * nD ^ 2 * oBC * oCD * RABD := by
  simp only [qg_11_18, paramsN] <;> ring

def qg_11_19 (p : Params K) : K :=
  p.c1 ^ 3 * p.c2 * p.c3 - p.c1 ^ 3 * p.M23 - p.c1 ^ 2 * p.c2 * p.M13 - p.c1 ^ 2 * p.c3 * p.M12 + p.c1 ^ 2 * p.b + p.c1 * p.c2 * p.c3 * p.M11 - p.c1 * p.M11 * p.M23 - p.c2 * p.M11 * p.M13 - p.c3 * p.M11 * p.M12 + p.M11 * p.b

theorem qg_11_19_eq (p : Params K) :
    W p (ampV11 p) (T p 1 2 (ampV19 p)) = qg_11_19 p := by
  simp [qg_11_19, ampV11, ampV19, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_11_19 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_11_19 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC ^ 2 * nD * oBC * RBCD := by
  simp only [qg_11_19, paramsN] <;> ring

def qg_11_20 (p : Params K) : K :=
  p.c1 ^ 3 * p.c2 ^ 2 * p.c3 + p.c1 ^ 3 * p.c3 * p.M22 - p.c1 ^ 2 * p.c2 ^ 2 * p.M13 - p.c1 ^ 2 * p.M22 * p.M13 + p.c1 * p.c2 ^ 2 * p.c3 * p.M11 + p.c1 * p.c3 * p.M11 * p.M22 - p.c2 ^ 2 * p.M11 * p.M13 - p.M11 * p.M22 * p.M13

theorem qg_11_20_eq (p : Params K) :
    W p (ampV11 p) (T p 1 2 (ampV20 p)) = qg_11_20 p := by
  simp [qg_11_20, ampV11, ampV20, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_11_20 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_11_20 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC ^ 3 * nD ^ 2 * oBC * oCD * wB := by
  simp only [qg_11_20, paramsN] <;> ring

def qg_12_14 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 - p.c1 * p.M23 - p.c2 * p.M13 - p.c3 * p.M12 + p.b

theorem qg_12_14_eq (p : Params K) :
    W p (ampV12 p) (T p 1 2 (ampV14 p)) = qg_12_14 p := by
  simp [qg_12_14, ampV12, ampV14, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_12_14 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_12_14 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * RBCD := by
  simp only [qg_12_14, paramsN] <;> ring

def qg_12_15 (p : Params K) : K :=
  p.c1 * p.c2 ^ 2 * p.c3 - 2 * p.c1 * p.c2 * p.M23 - p.c1 * p.c3 * p.M22 - p.c2 ^ 2 * p.M13 - 2 * p.c2 * p.c3 * p.M12 + 2 * p.c2 * p.b + p.M22 * p.M13

theorem qg_12_15_eq (p : Params K) :
    W p (ampV12 p) (T p 1 2 (ampV15 p)) = qg_12_15 p := by
  simp [qg_12_15, ampV12, ampV15, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_12_15 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_12_15 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB * nC ^ 2 * nD ^ 2 * oCD * wB + 2 * nB * nC ^ 2 * nD ^ 2 * RACD * RBCD := by
  simp only [qg_12_15, paramsN] <;> ring

def qg_12_16 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 * p.c3 - p.c1 ^ 2 * p.M23 + p.c2 * p.c3 * p.M11 - p.M11 * p.M23

theorem qg_12_16_eq (p : Params K) :
    W p (ampV12 p) (T p 1 2 (ampV16 p)) = qg_12_16 p := by
  simp [qg_12_16, ampV12, ampV16, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_12_16 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_12_16 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC ^ 2 * nD * oBC * wD := by
  simp only [qg_12_16, paramsN] <;> ring

def qg_12_17 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 ^ 2 + p.c1 * p.c2 * p.M33 - p.c3 ^ 2 * p.M12 + 2 * p.c3 * p.b + p.M33 * p.M12 - 2 * p.M13 * p.M23

theorem qg_12_17_eq (p : Params K) :
    W p (ampV12 p) (T p 1 2 (ampV17 p)) = qg_12_17 p := by
  simp [qg_12_17, ampV12, ampV17, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_12_17 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_12_17 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * oBD * RABC * RACD - 2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * wB * wD - nB ^ 2 * nC * nD ^ 2 * oBD * wC + 2 * nB ^ 2 * nC * nD ^ 2 * RABD * RBCD := by
  simp only [qg_12_17, paramsN] <;> ring

def qg_12_18 (p : Params K) : K :=
  p.c1 * p.c2 ^ 2 * p.c3 ^ 2 - p.c1 * p.c2 ^ 2 * p.M33 - 4 * p.c1 * p.c2 * p.c3 * p.M23 - p.c1 * p.c3 ^ 2 * p.M22 - p.c1 * p.M22 * p.M33 + 2 * p.c1 * p.M23 ^ 2 - 2 * p.c2 ^ 2 * p.c3 * p.M13 - 2 * p.c2 * p.c3 ^ 2 * p.M12 + 2 * p.c2 * p.c3 * p.b + 2 * p.c2 * p.M13 * p.M23 + 2 * p.c3 * p.M12 * p.M23 - 2 * p.M23 * p.b

theorem qg_12_18_eq (p : Params K) :
    W p (ampV12 p) (T p 1 2 (ampV18 p)) = qg_12_18 p := by
  simp [qg_12_18, ampV12, ampV18, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_12_18 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_12_18 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB ^ 2 * nC ^ 2 * nD ^ 2 * oBD * oCD * RABC + 2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * RBCD * wD := by
  simp only [qg_12_18, paramsN] <;> ring

def qg_12_19 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 * p.c3 ^ 2 + p.c1 ^ 2 * p.c2 * p.M33 + p.c2 * p.c3 ^ 2 * p.M11 + p.c2 * p.M11 * p.M33

theorem qg_12_19_eq (p : Params K) :
    W p (ampV12 p) (T p 1 2 (ampV19 p)) = qg_12_19 p := by
  simp [qg_12_19, ampV12, ampV19, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_12_19 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_12_19 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC ^ 2 * nD ^ 2 * oBC * oBD * RACD := by
  simp only [qg_12_19, paramsN] <;> ring

def qg_12_20 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 ^ 2 * p.c3 ^ 2 - p.c1 ^ 2 * p.c2 ^ 2 * p.M33 - 4 * p.c1 ^ 2 * p.c2 * p.c3 * p.M23 - p.c1 ^ 2 * p.c3 ^ 2 * p.M22 - p.c1 ^ 2 * p.M22 * p.M33 + 2 * p.c1 ^ 2 * p.M23 ^ 2 - 4 * p.c1 * p.c2 ^ 2 * p.c3 * p.M13 - 4 * p.c1 * p.c2 * p.c3 ^ 2 * p.M12 + 4 * p.c1 * p.c2 * p.c3 * p.b + 4 * p.c1 * p.c2 * p.M13 * p.M23 + 4 * p.c1 * p.c3 * p.M12 * p.M23 - 4 * p.c1 * p.M23 * p.b - p.c2 ^ 2 * p.c3 ^ 2 * p.M11 - p.c2 ^ 2 * p.M11 * p.M33 + 2 * p.c2 ^ 2 * p.M13 ^ 2 + 4 * p.c2 * p.c3 * p.M12 * p.M13 - 4 * p.c2 * p.M13 * p.b - p.c3 ^ 2 * p.M11 * p.M22 + 2 * p.c3 ^ 2 * p.M12 ^ 2 - 4 * p.c3 * p.M12 * p.b - p.M11 * p.M22 * p.M33 + 2 * p.b ^ 2

theorem qg_12_20_eq (p : Params K) :
    W p (ampV12 p) (T p 1 2 (ampV20 p)) = qg_12_20 p := by
  simp [qg_12_20, ampV12, ampV20, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_12_20 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_12_20 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB ^ 2 * nC ^ 2 * nD ^ 2 * oBC * oBD * oCD + 2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * RBCD ^ 2 := by
  simp only [qg_12_20, paramsN] <;> ring

def qg_13_14 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 * p.c3 - p.c1 ^ 2 * p.M23 + p.c2 * p.c3 * p.M11 - p.M11 * p.M23

theorem qg_13_14_eq (p : Params K) :
    W p (ampV13 p) (T p 1 2 (ampV14 p)) = qg_13_14 p := by
  simp [qg_13_14, ampV13, ampV14, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_13_14 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_13_14 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC ^ 2 * nD * oBC * wD := by
  simp only [qg_13_14, paramsN] <;> ring

def qg_13_15 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 ^ 2 * p.c3 + p.c1 ^ 2 * p.c3 * p.M22 + p.c2 ^ 2 * p.c3 * p.M11 + p.c3 * p.M11 * p.M22

theorem qg_13_15_eq (p : Params K) :
    W p (ampV13 p) (T p 1 2 (ampV15 p)) = qg_13_15 p := by
  simp [qg_13_15, ampV13, ampV15, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_13_15 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_13_15 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC ^ 2 * nD ^ 2 * oBC * oCD * RABD := by
  simp only [qg_13_15, paramsN] <;> ring

def qg_13_16 (p : Params K) : K :=
  p.c1 ^ 3 * p.c2 * p.c3 - p.c1 ^ 3 * p.M23 - p.c1 ^ 2 * p.c2 * p.M13 - p.c1 ^ 2 * p.c3 * p.M12 + p.c1 ^ 2 * p.b + p.c1 * p.c2 * p.c3 * p.M11 - p.c1 * p.M11 * p.M23 - p.c2 * p.M11 * p.M13 - p.c3 * p.M11 * p.M12 + p.M11 * p.b

theorem qg_13_16_eq (p : Params K) :
    W p (ampV13 p) (T p 1 2 (ampV16 p)) = qg_13_16 p := by
  simp [qg_13_16, ampV13, ampV16, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_13_16 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_13_16 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC ^ 2 * nD * oBC * RBCD := by
  simp only [qg_13_16, paramsN] <;> ring

def qg_13_17 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 * p.c3 ^ 2 - p.c1 ^ 2 * p.c2 * p.M33 - 2 * p.c1 ^ 2 * p.c3 * p.M23 + p.c2 * p.c3 ^ 2 * p.M11 - p.c2 * p.M11 * p.M33 - 2 * p.c3 * p.M11 * p.M23

theorem qg_13_17_eq (p : Params K) :
    W p (ampV13 p) (T p 1 2 (ampV17 p)) = qg_13_17 p := by
  simp [qg_13_17, ampV13, ampV17, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_13_17 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_13_17 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 3 * nC ^ 2 * nD ^ 2 * oBC * RABD * wD - nB ^ 2 * nC ^ 2 * nD ^ 2 * oBC * oBD * RACD := by
  simp only [qg_13_17, paramsN] <;> ring

def qg_13_18 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 ^ 2 * p.c3 ^ 2 + p.c1 ^ 2 * p.c2 ^ 2 * p.M33 + p.c1 ^ 2 * p.c3 ^ 2 * p.M22 + p.c1 ^ 2 * p.M22 * p.M33 + p.c2 ^ 2 * p.c3 ^ 2 * p.M11 + p.c2 ^ 2 * p.M11 * p.M33 + p.c3 ^ 2 * p.M11 * p.M22 + p.M11 * p.M22 * p.M33

theorem qg_13_18_eq (p : Params K) :
    W p (ampV13 p) (T p 1 2 (ampV18 p)) = qg_13_18 p := by
  simp [qg_13_18, ampV13, ampV18, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_13_18 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_13_18 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC ^ 2 * nD ^ 2 * oBC * oBD * oCD := by
  simp only [qg_13_18, paramsN] <;> ring

def qg_13_19 (p : Params K) : K :=
  p.c1 ^ 3 * p.c2 * p.c3 ^ 2 - p.c1 ^ 3 * p.c2 * p.M33 - 2 * p.c1 ^ 3 * p.c3 * p.M23 - 2 * p.c1 ^ 2 * p.c2 * p.c3 * p.M13 - p.c1 ^ 2 * p.c3 ^ 2 * p.M12 + 2 * p.c1 ^ 2 * p.c3 * p.b + p.c1 ^ 2 * p.M33 * p.M12 + p.c1 * p.c2 * p.c3 ^ 2 * p.M11 - p.c1 * p.c2 * p.M11 * p.M33 - 2 * p.c1 * p.c3 * p.M11 * p.M23 - 2 * p.c2 * p.c3 * p.M11 * p.M13 - p.c3 ^ 2 * p.M11 * p.M12 + 2 * p.c3 * p.M11 * p.b + p.M11 * p.M33 * p.M12

theorem qg_13_19_eq (p : Params K) :
    W p (ampV13 p) (T p 1 2 (ampV19 p)) = qg_13_19 p := by
  simp [qg_13_19, ampV13, ampV19, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_13_19 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_13_19 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB ^ 3 * nC ^ 2 * nD ^ 2 * oBC * oBD * wC + 2 * nB ^ 3 * nC ^ 2 * nD ^ 2 * oBC * RABD * RBCD := by
  simp only [qg_13_19, paramsN] <;> ring

def qg_13_20 (p : Params K) : K :=
  p.c1 ^ 3 * p.c2 ^ 2 * p.c3 ^ 2 + p.c1 ^ 3 * p.c2 ^ 2 * p.M33 + p.c1 ^ 3 * p.c3 ^ 2 * p.M22 + p.c1 ^ 3 * p.M22 * p.M33 + p.c1 * p.c2 ^ 2 * p.c3 ^ 2 * p.M11 + p.c1 * p.c2 ^ 2 * p.M11 * p.M33 + p.c1 * p.c3 ^ 2 * p.M11 * p.M22 + p.c1 * p.M11 * p.M22 * p.M33

theorem qg_13_20_eq (p : Params K) :
    W p (ampV13 p) (T p 1 2 (ampV20 p)) = qg_13_20 p := by
  simp [qg_13_20, ampV13, ampV20, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_13_20 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_13_20 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 3 * nC ^ 3 * nD ^ 2 * oBC * oBD * oCD * RABC := by
  simp only [qg_13_20, paramsN] <;> ring

end LemmaB.TableModel
