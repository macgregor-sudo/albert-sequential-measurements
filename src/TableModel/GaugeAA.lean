/- SPDX-License-Identifier: Apache-2.0
   Machine-generated file. -/
module

public import TableModel.Amps

/-! # Table-model identity, part 2 (frames A, A): the model values in the gauge parameters

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

def qg_0_0 (p : Params K) : K :=
  1

theorem qg_0_0_eq (p : Params K) :
    W p (ampV0 p) (T p 0 0 (ampV0 p)) = qg_0_0 p := by
  simp [qg_0_0, ampV0, ampV0, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_0_0 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_0_0 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      1 := by
  simp only [qg_0_0, paramsN] <;> ring

def qg_0_1 (p : Params K) : K :=
  p.c1

theorem qg_0_1_eq (p : Params K) :
    W p (ampV0 p) (T p 0 0 (ampV1 p)) = qg_0_1 p := by
  simp [qg_0_1, ampV0, ampV1, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_0_1 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_0_1 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * RABC := by
  simp only [qg_0_1, paramsN] <;> ring

def qg_0_2 (p : Params K) : K :=
  p.c2

theorem qg_0_2_eq (p : Params K) :
    W p (ampV0 p) (T p 0 0 (ampV2 p)) = qg_0_2 p := by
  simp [qg_0_2, ampV0, ampV2, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_0_2 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_0_2 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nC * nD * RACD := by
  simp only [qg_0_2, paramsN] <;> ring

def qg_0_3 (p : Params K) : K :=
  p.c3

theorem qg_0_3_eq (p : Params K) :
    W p (ampV0 p) (T p 0 0 (ampV3 p)) = qg_0_3 p := by
  simp [qg_0_3, ampV0, ampV3, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_0_3 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_0_3 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nD * RABD := by
  simp only [qg_0_3, paramsN] <;> ring

def qg_0_4 (p : Params K) : K :=
  p.c1 * p.c2 - p.M12

theorem qg_0_4_eq (p : Params K) :
    W p (ampV0 p) (T p 0 0 (ampV4 p)) = qg_0_4 p := by
  simp [qg_0_4, ampV0, ampV4, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_0_4 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_0_4 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * wC := by
  simp only [qg_0_4, paramsN] <;> ring

def qg_0_5 (p : Params K) : K :=
  p.c2 * p.c3 - p.M23

theorem qg_0_5_eq (p : Params K) :
    W p (ampV0 p) (T p 0 0 (ampV5 p)) = qg_0_5 p := by
  simp [qg_0_5, ampV0, ampV5, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_0_5 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_0_5 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * wD := by
  simp only [qg_0_5, paramsN] <;> ring

def qg_0_6 (p : Params K) : K :=
  p.c1 * p.c3 - p.M13

theorem qg_0_6_eq (p : Params K) :
    W p (ampV0 p) (T p 0 0 (ampV6 p)) = qg_0_6 p := by
  simp [qg_0_6, ampV0, ampV6, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_0_6 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_0_6 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * wB := by
  simp only [qg_0_6, paramsN] <;> ring

def qg_1_1 (p : Params K) : K :=
  p.c1 ^ 2 + p.M11

theorem qg_1_1_eq (p : Params K) :
    W p (ampV1 p) (T p 0 0 (ampV1 p)) = qg_1_1 p := by
  simp [qg_1_1, ampV1, ampV1, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_1_1 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_1_1 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * oBC := by
  simp only [qg_1_1, paramsN] <;> ring

def qg_1_2 (p : Params K) : K :=
  p.c1 * p.c2 + p.M12

theorem qg_1_2_eq (p : Params K) :
    W p (ampV1 p) (T p 0 0 (ampV2 p)) = qg_1_2 p := by
  simp [qg_1_2, ampV1, ampV2, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_1_2 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_1_2 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB * nC ^ 2 * nD * RABC * RACD - nB * nC * nD * wC := by
  simp only [qg_1_2, paramsN] <;> ring

def qg_1_3 (p : Params K) : K :=
  p.c1 * p.c3 + p.M13

theorem qg_1_3_eq (p : Params K) :
    W p (ampV1 p) (T p 0 0 (ampV3 p)) = qg_1_3 p := by
  simp [qg_1_3, ampV1, ampV3, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_1_3 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_1_3 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC * nD * RABC * RABD - nB * nC * nD * wB := by
  simp only [qg_1_3, paramsN] <;> ring

def qg_1_4 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 + p.c2 * p.M11

theorem qg_1_4_eq (p : Params K) :
    W p (ampV1 p) (T p 0 0 (ampV4 p)) = qg_1_4 p := by
  simp [qg_1_4, ampV1, ampV4, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_1_4 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_1_4 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * nD * oBC * RACD := by
  simp only [qg_1_4, paramsN] <;> ring

def qg_1_5 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 - p.c1 * p.M23 - p.c2 * p.M13 - p.c3 * p.M12 + p.b

theorem qg_1_5_eq (p : Params K) :
    W p (ampV1 p) (T p 0 0 (ampV5 p)) = qg_1_5 p := by
  simp [qg_1_5, ampV1, ampV5, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_1_5 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_1_5 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * RBCD := by
  simp only [qg_1_5, paramsN] <;> ring

def qg_1_6 (p : Params K) : K :=
  p.c1 ^ 2 * p.c3 - 2 * p.c1 * p.M13 - p.c3 * p.M11

theorem qg_1_6_eq (p : Params K) :
    W p (ampV1 p) (T p 0 0 (ampV6 p)) = qg_1_6 p := by
  simp [qg_1_6, ampV1, ampV6, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_1_6 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_1_6 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC ^ 2 * nD * RABC * wB - nB ^ 2 * nC * nD * oBC * RABD := by
  simp only [qg_1_6, paramsN] <;> ring

def qg_2_2 (p : Params K) : K :=
  p.c2 ^ 2 + p.M22

theorem qg_2_2_eq (p : Params K) :
    W p (ampV2 p) (T p 0 0 (ampV2 p)) = qg_2_2 p := by
  simp [qg_2_2, ampV2, ampV2, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_2_2 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_2_2 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nC * nD * oCD := by
  simp only [qg_2_2, paramsN] <;> ring

def qg_2_3 (p : Params K) : K :=
  p.c2 * p.c3 + p.M23

theorem qg_2_3_eq (p : Params K) :
    W p (ampV2 p) (T p 0 0 (ampV3 p)) = qg_2_3 p := by
  simp [qg_2_3, ampV2, ampV3, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_2_3 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_2_3 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB * nC * nD ^ 2 * RABD * RACD - nB * nC * nD * wD := by
  simp only [qg_2_3, paramsN] <;> ring

def qg_2_4 (p : Params K) : K :=
  p.c1 * p.c2 ^ 2 + p.c1 * p.M22

theorem qg_2_4_eq (p : Params K) :
    W p (ampV2 p) (T p 0 0 (ampV4 p)) = qg_2_4 p := by
  simp [qg_2_4, ampV2, ampV4, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_2_4 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_2_4 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * nD * oCD * RABC := by
  simp only [qg_2_4, paramsN] <;> ring

def qg_2_5 (p : Params K) : K :=
  p.c2 ^ 2 * p.c3 - 2 * p.c2 * p.M23 - p.c3 * p.M22

theorem qg_2_5_eq (p : Params K) :
    W p (ampV2 p) (T p 0 0 (ampV5 p)) = qg_2_5 p := by
  simp [qg_2_5, ampV2, ampV5, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_2_5 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_2_5 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB * nC ^ 2 * nD ^ 2 * RACD * wD - nB * nC * nD ^ 2 * oCD * RABD := by
  simp only [qg_2_5, paramsN] <;> ring

def qg_2_6 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 - p.c1 * p.M23 - p.c2 * p.M13 - p.c3 * p.M12 + p.b

theorem qg_2_6_eq (p : Params K) :
    W p (ampV2 p) (T p 0 0 (ampV6 p)) = qg_2_6 p := by
  simp [qg_2_6, ampV2, ampV6, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_2_6 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_2_6 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * RBCD := by
  simp only [qg_2_6, paramsN] <;> ring

def qg_3_3 (p : Params K) : K :=
  p.c3 ^ 2 + p.M33

theorem qg_3_3_eq (p : Params K) :
    W p (ampV3 p) (T p 0 0 (ampV3 p)) = qg_3_3 p := by
  simp [qg_3_3, ampV3, ampV3, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_3_3 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_3_3 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nD * oBD := by
  simp only [qg_3_3, paramsN] <;> ring

def qg_3_4 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 + p.c1 * p.M23 + p.c2 * p.M13 - p.c3 * p.M12 - p.b

theorem qg_3_4_eq (p : Params K) :
    W p (ampV3 p) (T p 0 0 (ampV4 p)) = qg_3_4 p := by
  simp [qg_3_4, ampV3, ampV4, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_3_4 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_3_4 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC * nD ^ 2 * RABD * wC - nB * nC * nD * RBCD := by
  simp only [qg_3_4, paramsN] <;> ring

def qg_3_5 (p : Params K) : K :=
  p.c2 * p.c3 ^ 2 - p.c2 * p.M33 - 2 * p.c3 * p.M23

theorem qg_3_5_eq (p : Params K) :
    W p (ampV3 p) (T p 0 0 (ampV5 p)) = qg_3_5 p := by
  simp [qg_3_5, ampV3, ampV5, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_3_5 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_3_5 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC * nD ^ 2 * RABD * wD - nB * nC * nD ^ 2 * oBD * RACD := by
  simp only [qg_3_5, paramsN] <;> ring

def qg_3_6 (p : Params K) : K :=
  p.c1 * p.c3 ^ 2 - p.c1 * p.M33 - 2 * p.c3 * p.M13

theorem qg_3_6_eq (p : Params K) :
    W p (ampV3 p) (T p 0 0 (ampV6 p)) = qg_3_6 p := by
  simp [qg_3_6, ampV3, ampV6, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_3_6 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_3_6 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC * nD ^ 2 * RABD * wB - nB ^ 2 * nC * nD * oBD * RABC := by
  simp only [qg_3_6, paramsN] <;> ring

def qg_4_4 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 ^ 2 + p.c1 ^ 2 * p.M22 + p.c2 ^ 2 * p.M11 + p.M11 * p.M22

theorem qg_4_4_eq (p : Params K) :
    W p (ampV4 p) (T p 0 0 (ampV4 p)) = qg_4_4 p := by
  simp [qg_4_4, ampV4, ampV4, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_4_4 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_4_4 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * nD * oBC * oCD := by
  simp only [qg_4_4, paramsN] <;> ring

def qg_4_5 (p : Params K) : K :=
  p.c1 * p.c2 ^ 2 * p.c3 - 2 * p.c1 * p.c2 * p.M23 - p.c1 * p.c3 * p.M22 - p.c2 ^ 2 * p.M13 - 2 * p.c2 * p.c3 * p.M12 + 2 * p.c2 * p.b + p.M22 * p.M13

theorem qg_4_5_eq (p : Params K) :
    W p (ampV4 p) (T p 0 0 (ampV5 p)) = qg_4_5 p := by
  simp [qg_4_5, ampV4, ampV5, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_4_5 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_4_5 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB * nC ^ 2 * nD ^ 2 * oCD * wB + 2 * nB * nC ^ 2 * nD ^ 2 * RACD * RBCD := by
  simp only [qg_4_5, paramsN] <;> ring

def qg_4_6 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 * p.c3 - p.c1 ^ 2 * p.M23 - 2 * p.c1 * p.c2 * p.M13 - 2 * p.c1 * p.c3 * p.M12 + 2 * p.c1 * p.b - p.c2 * p.c3 * p.M11 + p.M11 * p.M23

theorem qg_4_6_eq (p : Params K) :
    W p (ampV4 p) (T p 0 0 (ampV6 p)) = qg_4_6 p := by
  simp [qg_4_6, ampV4, ampV6, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_4_6 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_4_6 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB ^ 2 * nC ^ 2 * nD * oBC * wD + 2 * nB ^ 2 * nC ^ 2 * nD * RABC * RBCD := by
  simp only [qg_4_6, paramsN] <;> ring

def qg_5_5 (p : Params K) : K :=
  p.c2 ^ 2 * p.c3 ^ 2 + p.c2 ^ 2 * p.M33 + p.c3 ^ 2 * p.M22 + p.M22 * p.M33

theorem qg_5_5_eq (p : Params K) :
    W p (ampV5 p) (T p 0 0 (ampV5 p)) = qg_5_5 p := by
  simp [qg_5_5, ampV5, ampV5, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_5_5 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_5_5 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD ^ 2 * oBD * oCD := by
  simp only [qg_5_5, paramsN] <;> ring

def qg_5_6 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 ^ 2 + p.c1 * p.c2 * p.M33 + p.c3 ^ 2 * p.M12 - 2 * p.c3 * p.b - p.M33 * p.M12 + 2 * p.M13 * p.M23

theorem qg_5_6_eq (p : Params K) :
    W p (ampV5 p) (T p 0 0 (ampV6 p)) = qg_5_6 p := by
  simp [qg_5_6, ampV5, ampV6, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_5_6 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_5_6 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * wB * wD + nB ^ 2 * nC * nD ^ 2 * oBD * wC - 2 * nB ^ 2 * nC * nD ^ 2 * RABD * RBCD := by
  simp only [qg_5_6, paramsN] <;> ring

def qg_6_6 (p : Params K) : K :=
  p.c1 ^ 2 * p.c3 ^ 2 + p.c1 ^ 2 * p.M33 + p.c3 ^ 2 * p.M11 + p.M11 * p.M33

theorem qg_6_6_eq (p : Params K) :
    W p (ampV6 p) (T p 0 0 (ampV6 p)) = qg_6_6 p := by
  simp [qg_6_6, ampV6, ampV6, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_6_6 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_6_6 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD * oBC * oBD := by
  simp only [qg_6_6, paramsN] <;> ring

end LemmaB.TableModel
