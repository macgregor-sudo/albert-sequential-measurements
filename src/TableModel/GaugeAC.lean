/- SPDX-License-Identifier: Apache-2.0
   Machine-generated file. -/
module

public import TableModel.Amps

/-! # Table-model identity, part 2 (frames A, C): the model values in the gauge parameters

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

def qg_0_14 (p : Params K) : K :=
  1

theorem qg_0_14_eq (p : Params K) :
    W p (ampV0 p) (T p 0 2 (ampV14 p)) = qg_0_14 p := by
  simp [qg_0_14, ampV0, ampV14, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_0_14 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_0_14 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      1 := by
  simp only [qg_0_14, paramsN] <;> ring

def qg_0_15 (p : Params K) : K :=
  p.c2

theorem qg_0_15_eq (p : Params K) :
    W p (ampV0 p) (T p 0 2 (ampV15 p)) = qg_0_15 p := by
  simp [qg_0_15, ampV0, ampV15, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_0_15 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_0_15 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nC * nD * RACD := by
  simp only [qg_0_15, paramsN] <;> ring

def qg_0_16 (p : Params K) : K :=
  p.c1

theorem qg_0_16_eq (p : Params K) :
    W p (ampV0 p) (T p 0 2 (ampV16 p)) = qg_0_16 p := by
  simp [qg_0_16, ampV0, ampV16, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_0_16 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_0_16 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * RABC := by
  simp only [qg_0_16, paramsN] <;> ring

def qg_0_17 (p : Params K) : K :=
  p.c3

theorem qg_0_17_eq (p : Params K) :
    W p (ampV0 p) (T p 0 2 (ampV17 p)) = qg_0_17 p := by
  simp [qg_0_17, ampV0, ampV17, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_0_17 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_0_17 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nD * RABD := by
  simp only [qg_0_17, paramsN] <;> ring

def qg_0_18 (p : Params K) : K :=
  p.c2 * p.c3 - p.M23

theorem qg_0_18_eq (p : Params K) :
    W p (ampV0 p) (T p 0 2 (ampV18 p)) = qg_0_18 p := by
  simp [qg_0_18, ampV0, ampV18, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_0_18 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_0_18 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * wD := by
  simp only [qg_0_18, paramsN] <;> ring

def qg_0_19 (p : Params K) : K :=
  p.c1 * p.c3 - p.M13

theorem qg_0_19_eq (p : Params K) :
    W p (ampV0 p) (T p 0 2 (ampV19 p)) = qg_0_19 p := by
  simp [qg_0_19, ampV0, ampV19, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_0_19 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_0_19 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * wB := by
  simp only [qg_0_19, paramsN] <;> ring

def qg_0_20 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 - p.c1 * p.M23 - p.c2 * p.M13 - p.c3 * p.M12 + p.b

theorem qg_0_20_eq (p : Params K) :
    W p (ampV0 p) (T p 0 2 (ampV20 p)) = qg_0_20 p := by
  simp [qg_0_20, ampV0, ampV20, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_0_20 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_0_20 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * RBCD := by
  simp only [qg_0_20, paramsN] <;> ring

def qg_1_14 (p : Params K) : K :=
  p.c1

theorem qg_1_14_eq (p : Params K) :
    W p (ampV1 p) (T p 0 2 (ampV14 p)) = qg_1_14 p := by
  simp [qg_1_14, ampV1, ampV14, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_1_14 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_1_14 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * RABC := by
  simp only [qg_1_14, paramsN] <;> ring

def qg_1_15 (p : Params K) : K :=
  p.c1 * p.c2 + p.M12

theorem qg_1_15_eq (p : Params K) :
    W p (ampV1 p) (T p 0 2 (ampV15 p)) = qg_1_15 p := by
  simp [qg_1_15, ampV1, ampV15, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_1_15 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_1_15 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB * nC ^ 2 * nD * RABC * RACD - nB * nC * nD * wC := by
  simp only [qg_1_15, paramsN] <;> ring

def qg_1_16 (p : Params K) : K :=
  p.c1 ^ 2 - p.M11

theorem qg_1_16_eq (p : Params K) :
    W p (ampV1 p) (T p 0 2 (ampV16 p)) = qg_1_16 p := by
  simp [qg_1_16, ampV1, ampV16, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_1_16 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_1_16 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC ^ 2 * RABC ^ 2 - nB * nC * oBC := by
  simp only [qg_1_16, paramsN] <;> ring

def qg_1_17 (p : Params K) : K :=
  p.c1 * p.c3 - p.M13

theorem qg_1_17_eq (p : Params K) :
    W p (ampV1 p) (T p 0 2 (ampV17 p)) = qg_1_17 p := by
  simp [qg_1_17, ampV1, ampV17, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_1_17 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_1_17 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * wB := by
  simp only [qg_1_17, paramsN] <;> ring

def qg_1_18 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 - p.c1 * p.M23 + p.c2 * p.M13 + p.c3 * p.M12 - p.b

theorem qg_1_18_eq (p : Params K) :
    W p (ampV1 p) (T p 0 2 (ampV18 p)) = qg_1_18 p := by
  simp [qg_1_18, ampV1, ampV18, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_1_18 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_1_18 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC ^ 2 * nD * RABC * wD - nB * nC * nD * RBCD := by
  simp only [qg_1_18, paramsN] <;> ring

def qg_1_19 (p : Params K) : K :=
  p.c1 ^ 2 * p.c3 - 2 * p.c1 * p.M13 - p.c3 * p.M11

theorem qg_1_19_eq (p : Params K) :
    W p (ampV1 p) (T p 0 2 (ampV19 p)) = qg_1_19 p := by
  simp [qg_1_19, ampV1, ampV19, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_1_19 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_1_19 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC ^ 2 * nD * RABC * wB - nB ^ 2 * nC * nD * oBC * RABD := by
  simp only [qg_1_19, paramsN] <;> ring

def qg_1_20 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 * p.c3 - p.c1 ^ 2 * p.M23 + p.c2 * p.c3 * p.M11 - p.M11 * p.M23

theorem qg_1_20_eq (p : Params K) :
    W p (ampV1 p) (T p 0 2 (ampV20 p)) = qg_1_20 p := by
  simp [qg_1_20, ampV1, ampV20, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_1_20 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_1_20 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC ^ 2 * nD * oBC * wD := by
  simp only [qg_1_20, paramsN] <;> ring

def qg_2_14 (p : Params K) : K :=
  p.c2

theorem qg_2_14_eq (p : Params K) :
    W p (ampV2 p) (T p 0 2 (ampV14 p)) = qg_2_14 p := by
  simp [qg_2_14, ampV2, ampV14, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_2_14 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_2_14 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nC * nD * RACD := by
  simp only [qg_2_14, paramsN] <;> ring

def qg_2_15 (p : Params K) : K :=
  p.c2 ^ 2 + p.M22

theorem qg_2_15_eq (p : Params K) :
    W p (ampV2 p) (T p 0 2 (ampV15 p)) = qg_2_15 p := by
  simp [qg_2_15, ampV2, ampV15, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_2_15 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_2_15 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nC * nD * oCD := by
  simp only [qg_2_15, paramsN] <;> ring

def qg_2_16 (p : Params K) : K :=
  p.c1 * p.c2 - p.M12

theorem qg_2_16_eq (p : Params K) :
    W p (ampV2 p) (T p 0 2 (ampV16 p)) = qg_2_16 p := by
  simp [qg_2_16, ampV2, ampV16, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_2_16 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_2_16 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * wC := by
  simp only [qg_2_16, paramsN] <;> ring

def qg_2_17 (p : Params K) : K :=
  p.c2 * p.c3 - p.M23

theorem qg_2_17_eq (p : Params K) :
    W p (ampV2 p) (T p 0 2 (ampV17 p)) = qg_2_17 p := by
  simp [qg_2_17, ampV2, ampV17, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_2_17 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_2_17 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * wD := by
  simp only [qg_2_17, paramsN] <;> ring

def qg_2_18 (p : Params K) : K :=
  p.c2 ^ 2 * p.c3 + p.c3 * p.M22

theorem qg_2_18_eq (p : Params K) :
    W p (ampV2 p) (T p 0 2 (ampV18 p)) = qg_2_18 p := by
  simp [qg_2_18, ampV2, ampV18, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_2_18 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_2_18 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD ^ 2 * oCD * RABD := by
  simp only [qg_2_18, paramsN] <;> ring

def qg_2_19 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 - p.c1 * p.M23 - p.c2 * p.M13 - p.c3 * p.M12 + p.b

theorem qg_2_19_eq (p : Params K) :
    W p (ampV2 p) (T p 0 2 (ampV19 p)) = qg_2_19 p := by
  simp [qg_2_19, ampV2, ampV19, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_2_19 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_2_19 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * RBCD := by
  simp only [qg_2_19, paramsN] <;> ring

def qg_2_20 (p : Params K) : K :=
  p.c1 * p.c2 ^ 2 * p.c3 + p.c1 * p.c3 * p.M22 - p.c2 ^ 2 * p.M13 - p.M22 * p.M13

theorem qg_2_20_eq (p : Params K) :
    W p (ampV2 p) (T p 0 2 (ampV20 p)) = qg_2_20 p := by
  simp [qg_2_20, ampV2, ampV20, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_2_20 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_2_20 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * nD ^ 2 * oCD * wB := by
  simp only [qg_2_20, paramsN] <;> ring

def qg_3_14 (p : Params K) : K :=
  p.c3

theorem qg_3_14_eq (p : Params K) :
    W p (ampV3 p) (T p 0 2 (ampV14 p)) = qg_3_14 p := by
  simp [qg_3_14, ampV3, ampV14, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_3_14 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_3_14 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nD * RABD := by
  simp only [qg_3_14, paramsN] <;> ring

def qg_3_15 (p : Params K) : K :=
  p.c2 * p.c3 + p.M23

theorem qg_3_15_eq (p : Params K) :
    W p (ampV3 p) (T p 0 2 (ampV15 p)) = qg_3_15 p := by
  simp [qg_3_15, ampV3, ampV15, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_3_15 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_3_15 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB * nC * nD ^ 2 * RABD * RACD - nB * nC * nD * wD := by
  simp only [qg_3_15, paramsN] <;> ring

def qg_3_16 (p : Params K) : K :=
  p.c1 * p.c3 - p.M13

theorem qg_3_16_eq (p : Params K) :
    W p (ampV3 p) (T p 0 2 (ampV16 p)) = qg_3_16 p := by
  simp [qg_3_16, ampV3, ampV16, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_3_16 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_3_16 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * wB := by
  simp only [qg_3_16, paramsN] <;> ring

def qg_3_17 (p : Params K) : K :=
  p.c3 ^ 2 - p.M33

theorem qg_3_17_eq (p : Params K) :
    W p (ampV3 p) (T p 0 2 (ampV17 p)) = qg_3_17 p := by
  simp [qg_3_17, ampV3, ampV17, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_3_17 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_3_17 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nD ^ 2 * RABD ^ 2 - nB * nD * oBD := by
  simp only [qg_3_17, paramsN] <;> ring

def qg_3_18 (p : Params K) : K :=
  p.c2 * p.c3 ^ 2 + p.c2 * p.M33

theorem qg_3_18_eq (p : Params K) :
    W p (ampV3 p) (T p 0 2 (ampV18 p)) = qg_3_18 p := by
  simp [qg_3_18, ampV3, ampV18, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_3_18 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_3_18 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD ^ 2 * oBD * RACD := by
  simp only [qg_3_18, paramsN] <;> ring

def qg_3_19 (p : Params K) : K :=
  p.c1 * p.c3 ^ 2 - p.c1 * p.M33 - 2 * p.c3 * p.M13

theorem qg_3_19_eq (p : Params K) :
    W p (ampV3 p) (T p 0 2 (ampV19 p)) = qg_3_19 p := by
  simp [qg_3_19, ampV3, ampV19, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_3_19 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_3_19 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC * nD ^ 2 * RABD * wB - nB ^ 2 * nC * nD * oBD * RABC := by
  simp only [qg_3_19, paramsN] <;> ring

def qg_3_20 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 ^ 2 + p.c1 * p.c2 * p.M33 - p.c3 ^ 2 * p.M12 + 2 * p.c3 * p.b + p.M33 * p.M12 - 2 * p.M13 * p.M23

theorem qg_3_20_eq (p : Params K) :
    W p (ampV3 p) (T p 0 2 (ampV20 p)) = qg_3_20 p := by
  simp [qg_3_20, ampV3, ampV20, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_3_20 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_3_20 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * oBD * RABC * RACD - 2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * wB * wD - nB ^ 2 * nC * nD ^ 2 * oBD * wC + 2 * nB ^ 2 * nC * nD ^ 2 * RABD * RBCD := by
  simp only [qg_3_20, paramsN] <;> ring

def qg_4_14 (p : Params K) : K :=
  p.c1 * p.c2 - p.M12

theorem qg_4_14_eq (p : Params K) :
    W p (ampV4 p) (T p 0 2 (ampV14 p)) = qg_4_14 p := by
  simp [qg_4_14, ampV4, ampV14, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_4_14 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_4_14 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * wC := by
  simp only [qg_4_14, paramsN] <;> ring

def qg_4_15 (p : Params K) : K :=
  p.c1 * p.c2 ^ 2 + p.c1 * p.M22

theorem qg_4_15_eq (p : Params K) :
    W p (ampV4 p) (T p 0 2 (ampV15 p)) = qg_4_15 p := by
  simp [qg_4_15, ampV4, ampV15, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_4_15 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_4_15 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC ^ 2 * nD * oCD * RABC := by
  simp only [qg_4_15, paramsN] <;> ring

def qg_4_16 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 - 2 * p.c1 * p.M12 - p.c2 * p.M11

theorem qg_4_16_eq (p : Params K) :
    W p (ampV4 p) (T p 0 2 (ampV16 p)) = qg_4_16 p := by
  simp [qg_4_16, ampV4, ampV16, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_4_16 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_4_16 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC ^ 2 * nD * RABC * wC - nB * nC ^ 2 * nD * oBC * RACD := by
  simp only [qg_4_16, paramsN] <;> ring

def qg_4_17 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 - p.c1 * p.M23 - p.c2 * p.M13 - p.c3 * p.M12 + p.b

theorem qg_4_17_eq (p : Params K) :
    W p (ampV4 p) (T p 0 2 (ampV17 p)) = qg_4_17 p := by
  simp [qg_4_17, ampV4, ampV17, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_4_17 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_4_17 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * RBCD := by
  simp only [qg_4_17, paramsN] <;> ring

def qg_4_18 (p : Params K) : K :=
  p.c1 * p.c2 ^ 2 * p.c3 + p.c1 * p.c3 * p.M22 + p.c2 ^ 2 * p.M13 - 2 * p.c2 * p.b - p.M22 * p.M13 + 2 * p.M12 * p.M23

theorem qg_4_18_eq (p : Params K) :
    W p (ampV4 p) (T p 0 2 (ampV18 p)) = qg_4_18 p := by
  simp [qg_4_18, ampV4, ampV18, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_4_18 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_4_18 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * wC * wD + nB * nC ^ 2 * nD ^ 2 * oCD * wB - 2 * nB * nC ^ 2 * nD ^ 2 * RACD * RBCD := by
  simp only [qg_4_18, paramsN] <;> ring

def qg_4_19 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 * p.c3 - p.c1 ^ 2 * p.M23 - 2 * p.c1 * p.c2 * p.M13 - 2 * p.c1 * p.c3 * p.M12 + 2 * p.c1 * p.b - p.c2 * p.c3 * p.M11 + p.M11 * p.M23

theorem qg_4_19_eq (p : Params K) :
    W p (ampV4 p) (T p 0 2 (ampV19 p)) = qg_4_19 p := by
  simp [qg_4_19, ampV4, ampV19, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_4_19 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_4_19 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB ^ 2 * nC ^ 2 * nD * oBC * wD + 2 * nB ^ 2 * nC ^ 2 * nD * RABC * RBCD := by
  simp only [qg_4_19, paramsN] <;> ring

def qg_4_20 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 ^ 2 * p.c3 + p.c1 ^ 2 * p.c3 * p.M22 - 2 * p.c1 * p.c2 * p.b - 2 * p.c1 * p.M22 * p.M13 + 2 * p.c1 * p.M12 * p.M23 + p.c2 ^ 2 * p.c3 * p.M11 - 2 * p.c2 * p.M11 * p.M23 + 2 * p.c2 * p.M12 * p.M13 - p.c3 * p.M11 * p.M22 + 2 * p.c3 * p.M12 ^ 2 - 2 * p.M12 * p.b

theorem qg_4_20_eq (p : Params K) :
    W p (ampV4 p) (T p 0 2 (ampV20 p)) = qg_4_20 p := by
  simp [qg_4_20, ampV4, ampV20, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_4_20 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_4_20 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC ^ 3 * nD ^ 2 * oBC * RACD * wD + 2 * nB ^ 2 * nC ^ 3 * nD ^ 2 * oCD * RABC * wB - 4 * nB ^ 2 * nC ^ 3 * nD ^ 2 * RABC * RACD * RBCD - nB ^ 2 * nC ^ 2 * nD ^ 2 * oBC * oCD * RABD + 2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * RBCD * wC := by
  simp only [qg_4_20, paramsN] <;> ring

def qg_5_14 (p : Params K) : K :=
  p.c2 * p.c3 - p.M23

theorem qg_5_14_eq (p : Params K) :
    W p (ampV5 p) (T p 0 2 (ampV14 p)) = qg_5_14 p := by
  simp [qg_5_14, ampV5, ampV14, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_5_14 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_5_14 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * wD := by
  simp only [qg_5_14, paramsN] <;> ring

def qg_5_15 (p : Params K) : K :=
  p.c2 ^ 2 * p.c3 - 2 * p.c2 * p.M23 - p.c3 * p.M22

theorem qg_5_15_eq (p : Params K) :
    W p (ampV5 p) (T p 0 2 (ampV15 p)) = qg_5_15 p := by
  simp [qg_5_15, ampV5, ampV15, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_5_15 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_5_15 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB * nC ^ 2 * nD ^ 2 * RACD * wD - nB * nC * nD ^ 2 * oCD * RABD := by
  simp only [qg_5_15, paramsN] <;> ring

def qg_5_16 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 - p.c1 * p.M23 + p.c2 * p.M13 + p.c3 * p.M12 - p.b

theorem qg_5_16_eq (p : Params K) :
    W p (ampV5 p) (T p 0 2 (ampV16 p)) = qg_5_16 p := by
  simp [qg_5_16, ampV5, ampV16, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_5_16 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_5_16 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC ^ 2 * nD * RABC * wD - nB * nC * nD * RBCD := by
  simp only [qg_5_16, paramsN] <;> ring

def qg_5_17 (p : Params K) : K :=
  p.c2 * p.c3 ^ 2 + p.c2 * p.M33

theorem qg_5_17_eq (p : Params K) :
    W p (ampV5 p) (T p 0 2 (ampV17 p)) = qg_5_17 p := by
  simp [qg_5_17, ampV5, ampV17, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_5_17 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_5_17 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD ^ 2 * oBD * RACD := by
  simp only [qg_5_17, paramsN] <;> ring

def qg_5_18 (p : Params K) : K :=
  p.c2 ^ 2 * p.c3 ^ 2 - p.c2 ^ 2 * p.M33 - 4 * p.c2 * p.c3 * p.M23 - p.c3 ^ 2 * p.M22 - p.M22 * p.M33 + 2 * p.M23 ^ 2

theorem qg_5_18_eq (p : Params K) :
    W p (ampV5 p) (T p 0 2 (ampV18 p)) = qg_5_18 p := by
  simp [qg_5_18, ampV5, ampV18, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_5_18 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_5_18 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * wD ^ 2 - nB * nC * nD ^ 2 * oBD * oCD := by
  simp only [qg_5_18, paramsN] <;> ring

def qg_5_19 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 ^ 2 + p.c1 * p.c2 * p.M33 + p.c3 ^ 2 * p.M12 - 2 * p.c3 * p.b - p.M33 * p.M12 + 2 * p.M13 * p.M23

theorem qg_5_19_eq (p : Params K) :
    W p (ampV5 p) (T p 0 2 (ampV19 p)) = qg_5_19 p := by
  simp [qg_5_19, ampV5, ampV19, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_5_19 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_5_19 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * wB * wD + nB ^ 2 * nC * nD ^ 2 * oBD * wC - 2 * nB ^ 2 * nC * nD ^ 2 * RABD * RBCD := by
  simp only [qg_5_19, paramsN] <;> ring

def qg_5_20 (p : Params K) : K :=
  p.c1 * p.c2 ^ 2 * p.c3 ^ 2 - p.c1 * p.c2 ^ 2 * p.M33 - 4 * p.c1 * p.c2 * p.c3 * p.M23 - p.c1 * p.c3 ^ 2 * p.M22 - p.c1 * p.M22 * p.M33 + 2 * p.c1 * p.M23 ^ 2 - 2 * p.c2 ^ 2 * p.c3 * p.M13 - 2 * p.c2 * p.c3 ^ 2 * p.M12 + 2 * p.c2 * p.c3 * p.b + 2 * p.c2 * p.M13 * p.M23 + 2 * p.c3 * p.M12 * p.M23 - 2 * p.M23 * p.b

theorem qg_5_20_eq (p : Params K) :
    W p (ampV5 p) (T p 0 2 (ampV20 p)) = qg_5_20 p := by
  simp [qg_5_20, ampV5, ampV20, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_5_20 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_5_20 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB ^ 2 * nC ^ 2 * nD ^ 2 * oBD * oCD * RABC + 2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * RBCD * wD := by
  simp only [qg_5_20, paramsN] <;> ring

def qg_6_14 (p : Params K) : K :=
  p.c1 * p.c3 - p.M13

theorem qg_6_14_eq (p : Params K) :
    W p (ampV6 p) (T p 0 2 (ampV14 p)) = qg_6_14 p := by
  simp [qg_6_14, ampV6, ampV14, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_6_14 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_6_14 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * wB := by
  simp only [qg_6_14, paramsN] <;> ring

def qg_6_15 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 - p.c1 * p.M23 - p.c2 * p.M13 - p.c3 * p.M12 + p.b

theorem qg_6_15_eq (p : Params K) :
    W p (ampV6 p) (T p 0 2 (ampV15 p)) = qg_6_15 p := by
  simp [qg_6_15, ampV6, ampV15, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_6_15 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_6_15 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB * nC * nD * RBCD := by
  simp only [qg_6_15, paramsN] <;> ring

def qg_6_16 (p : Params K) : K :=
  p.c1 ^ 2 * p.c3 + p.c3 * p.M11

theorem qg_6_16_eq (p : Params K) :
    W p (ampV6 p) (T p 0 2 (ampV16 p)) = qg_6_16 p := by
  simp [qg_6_16, ampV6, ampV16, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_6_16 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_6_16 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD * oBC * RABD := by
  simp only [qg_6_16, paramsN] <;> ring

def qg_6_17 (p : Params K) : K :=
  p.c1 * p.c3 ^ 2 + p.c1 * p.M33

theorem qg_6_17_eq (p : Params K) :
    W p (ampV6 p) (T p 0 2 (ampV17 p)) = qg_6_17 p := by
  simp [qg_6_17, ampV6, ampV17, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_6_17 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_6_17 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD * oBD * RABC := by
  simp only [qg_6_17, paramsN] <;> ring

def qg_6_18 (p : Params K) : K :=
  p.c1 * p.c2 * p.c3 ^ 2 - p.c1 * p.c2 * p.M33 - 2 * p.c1 * p.c3 * p.M23 - 2 * p.c2 * p.c3 * p.M13 - p.c3 ^ 2 * p.M12 + 2 * p.c3 * p.b + p.M33 * p.M12

theorem qg_6_18_eq (p : Params K) :
    W p (ampV6 p) (T p 0 2 (ampV18 p)) = qg_6_18 p := by
  simp [qg_6_18, ampV6, ampV18, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_6_18 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_6_18 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB ^ 2 * nC * nD ^ 2 * oBD * wC + 2 * nB ^ 2 * nC * nD ^ 2 * RABD * RBCD := by
  simp only [qg_6_18, paramsN] <;> ring

def qg_6_19 (p : Params K) : K :=
  p.c1 ^ 2 * p.c3 ^ 2 + p.c1 ^ 2 * p.M33 + p.c3 ^ 2 * p.M11 + p.M11 * p.M33

theorem qg_6_19_eq (p : Params K) :
    W p (ampV6 p) (T p 0 2 (ampV19 p)) = qg_6_19 p := by
  simp [qg_6_19, ampV6, ampV19, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_6_19 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_6_19 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      nB ^ 2 * nC * nD * oBC * oBD := by
  simp only [qg_6_19, paramsN] <;> ring

def qg_6_20 (p : Params K) : K :=
  p.c1 ^ 2 * p.c2 * p.c3 ^ 2 - p.c1 ^ 2 * p.c2 * p.M33 - 2 * p.c1 ^ 2 * p.c3 * p.M23 - 4 * p.c1 * p.c2 * p.c3 * p.M13 - 2 * p.c1 * p.c3 ^ 2 * p.M12 + 2 * p.c1 * p.c3 * p.b + 2 * p.c1 * p.M13 * p.M23 - p.c2 * p.c3 ^ 2 * p.M11 - p.c2 * p.M11 * p.M33 + 2 * p.c2 * p.M13 ^ 2 + 2 * p.c3 * p.M12 * p.M13 - 2 * p.M13 * p.b

theorem qg_6_20_eq (p : Params K) :
    W p (ampV6 p) (T p 0 2 (ampV20 p)) = qg_6_20 p := by
  simp [qg_6_20, ampV6, ampV20, W, Params.A11, Params.A22, Params.A33, Params.A12,
    Params.A13, Params.A23, Params.Dhat, Params.detM, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;> ring

theorem qn_6_20 (nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD : K) :
    qg_6_20 (paramsN nB nC nD oBC oBD oCD RABC RABD RACD RBCD wB wC wD) =
      -nB ^ 2 * nC ^ 2 * nD ^ 2 * oBC * oBD * RACD + 2 * nB ^ 2 * nC ^ 2 * nD ^ 2 * RBCD * wB := by
  simp only [qg_6_20, paramsN] <;> ring

end LemmaB.TableModel
