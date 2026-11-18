/- SPDX-License-Identifier: Apache-2.0 -/
module

public import FiveTest.RatAlbert
public import ThreeAtomAndFourPoint
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # The reflection `r = 2p₂ − e` and the reflected quadruple

Paper (companion, before `thm:five:refl`): for `𝖥 = (p₀,…,p₄)`, reflect `p₃` and `p₄` in `p₂`:
`(A,B,C,D) = (p₀, p₁, U_r p₃, U_r p₄)`, `r = 2p₂ − e`.

**Indexing (pinned).** The Lean `pentadF i` IS the paper's `p_i` for every `i = 0,…,4`:
`pentadF 0 = E₁₁`, `pentadF 1 = p(1,1,0)`, `pentadF 2 = p(1,i,1)` (the distinguished atom,
overlap 1/3 with the others), `pentadF 3 = p(1,j,0)`, `pentadF 4 = p(1,ℓ,0)`
(`pentadF_eq_cast`: each is the rational dyad of exactly that column, `octDyad v = v v†`,
entry `(a,b) = v_a v̄_b`).  So the reflecting test is Lean index 2 and the reflected tests are
Lean indices 3 and 4; the quadruple letters are `A,B,C,D = 0,1,2,3 : Fin 4` with
`C = U_r (pentadF 3)`, `D = U_r (pentadF 4)`.

Everything below is exact: native objects are casts of rational ones, identities are
checked by `decide` over `ℚ` and transported by the cast homomorphisms. -/

set_option autoImplicit false

@[expose] public section

namespace AlbertSequential.FiveTest

/-! ## Rational data -/

namespace QO
def K : QO := ⟨⟨0, 0, 0, 1⟩, QQ.zero⟩
def S : QO := ⟨QQ.zero, ⟨0, 1, 0, 0⟩⟩
def mk8 (a b c d e f g h : ℚ) : QO := ⟨⟨a, b, c, d⟩, ⟨e, f, g, h⟩⟩
end QO

/-- The paper's five atoms over `ℚ`, built from the printed columns. -/
def qpent : Fin 5 → QA
  | 0 => QA.diag0
  | 1 => (QA.dyad QO.one QO.one QO.zero).smul (1 / 2)
  | 2 => (QA.dyad QO.one QO.I QO.one).smul (1 / 3)
  | 3 => (QA.dyad QO.one QO.J QO.zero).smul (1 / 2)
  | 4 => (QA.dyad QO.one QO.L QO.zero).smul (1 / 2)

/-- `r = 2 p₂ − e` over `ℚ`. -/
def qr : QA := ((qpent 2).smul 2).sub QA.unit

/-- `U_r p₃` in coordinates (computed, then checked by `decide` in `qU3_eq`). -/
def qC : QA :=
  ⟨5 / 18, 5 / 18, 4 / 9, QO.mk8 0 (2 / 9) (1 / 6) 0 0 0 0 0, QO.mk8 (1 / 9) 0 0 (-1 / 3) 0 0 0 0,
    QO.mk8 0 (1 / 9) (-1 / 3) 0 0 0 0 0⟩

/-- `U_r p₄` in coordinates. -/
def qD : QA :=
  ⟨5 / 18, 5 / 18, 4 / 9, QO.mk8 0 (2 / 9) 0 0 (1 / 6) 0 0 0, QO.mk8 (1 / 9) 0 0 0 0 (-1 / 3) 0 0,
    QO.mk8 0 (1 / 9) 0 0 (-1 / 3) 0 0 0⟩

theorem qU3_eq : qr.U (qpent 3) = qC := by decide +kernel
theorem qU4_eq : qr.U (qpent 4) = qD := by decide +kernel

/-- The paper's printed formula `U_r p₃ = p(−1−2ij, 2i−j, 2−2ij)` (with `ij = k` in the Lean
Cayley–Dickson convention) and `U_r p₄ = p(−1−2iℓ, 2i−ℓ, 2−2iℓ)` (`iℓ = octS`), each
normalised by `1/18`. -/
theorem qC_paper :
    (QA.dyad (QO.mk8 (-1) 0 0 (-2) 0 0 0 0) (QO.mk8 0 2 (-1) 0 0 0 0 0)
      (QO.mk8 2 0 0 (-2) 0 0 0 0)).smul (1 / 18) = qC := by decide +kernel
theorem qD_paper :
    (QA.dyad (QO.mk8 (-1) 0 0 0 0 (-2) 0 0) (QO.mk8 0 2 0 0 (-1) 0 0 0)
      (QO.mk8 2 0 0 0 0 (-2) 0 0)).smul (1 / 18) = qD := by decide +kernel
theorem qIJ_eq_K : QO.I.mul QO.J = QO.K := by decide +kernel
theorem qIL_eq_S : QO.I.mul QO.L = QO.S := by decide +kernel

def qquad : Fin 4 → QA := ![qpent 0, qpent 1, qC, qD]

/-! ## Native definitions -/

noncomputable section

/-- The reflection `r = 2 p₂ − e` (paper index 2 = Lean `pentadF 2`). -/
def reflR : Albert := (2 : ℝ) • pentadF 2 - albertUnit

/-- The reflected quadruple `(A,B,C,D) = (p₀, p₁, U_r p₃, U_r p₄)`. -/
def reflQuad : Fin 4 → Albert :=
  ![pentadF 0, pentadF 1, quadraticMap reflR (pentadF 3), quadraticMap reflR (pentadF 4)]

theorem pentadF_eq_cast (i : Fin 5) : pentadF i = castA (qpent i) := by
  fin_cases i
  · exact castA_diag0.symm
  · change (1 / 2 : ℝ) • octDyad ![octOne, octOne, 0] =
      castA ((QA.dyad QO.one QO.one QO.zero).smul (1 / 2))
    rw [castA_smul, castA_dyad, castO_one, castO_zero]; norm_num
  · change (1 / 3 : ℝ) • octDyad ![octOne, octI, octOne] =
      castA ((QA.dyad QO.one QO.I QO.one).smul (1 / 3))
    rw [castA_smul, castA_dyad, castO_one, castO_I]; norm_num
  · change (1 / 2 : ℝ) • octDyad ![octOne, octJ, 0] =
      castA ((QA.dyad QO.one QO.J QO.zero).smul (1 / 2))
    rw [castA_smul, castA_dyad, castO_one, castO_J, castO_zero]; norm_num
  · change (1 / 2 : ℝ) • octDyad ![octOne, octL, 0] =
      castA ((QA.dyad QO.one QO.L QO.zero).smul (1 / 2))
    rw [castA_smul, castA_dyad, castO_one, castO_L, castO_zero]; norm_num

theorem reflR_eq_cast : reflR = castA qr := by
  rw [reflR, qr, castA_sub, castA_smul, castA_unit, pentadF_eq_cast]; norm_num

theorem reflC_eq_cast : quadraticMap reflR (pentadF 3) = castA qC := by
  rw [reflR_eq_cast, pentadF_eq_cast, ← castA_U, qU3_eq]

theorem reflD_eq_cast : quadraticMap reflR (pentadF 4) = castA qD := by
  rw [reflR_eq_cast, pentadF_eq_cast, ← castA_U, qU4_eq]

theorem reflQuad_eq_cast (i : Fin 4) : reflQuad i = castA (qquad i) := by
  fin_cases i
  · exact pentadF_eq_cast 0
  · exact pentadF_eq_cast 1
  · exact reflC_eq_cast
  · exact reflD_eq_cast

/-- The four elements are atoms (`C`, `D` by the reflection automorphism). -/
theorem reflQuad_isAtom (i : Fin 4) : IsAtom (reflQuad i) := by
  fin_cases i
  · exact pentadF_isAtom 0
  · exact pentadF_isAtom 1
  · exact NativeAnalysis.atomReflection_preserves_atom (pentadF 2) (pentadF_isAtom 2) _
      (pentadF_isAtom 3)
  · exact NativeAnalysis.atomReflection_preserves_atom (pentadF 2) (pentadF_isAtom 2) _
      (pentadF_isAtom 4)

/-- Exact rational check of the atom property (independent of the automorphism route). -/
theorem qquad_atom : ∀ i, (qquad i).jmul (qquad i) = qquad i ∧ (qquad i).tr = 1 := by decide +kernel

/-! ## The thirteen traces -/

theorem fpOverlap_reflQuad (i j : Fin 4) :
    fpOverlap reflQuad i j = (((qquad i).tp (qquad j) : ℚ) : ℝ) := by
  rw [fpOverlap, reflQuad_eq_cast, reflQuad_eq_cast, castA_tp]

theorem fpTriangle_reflQuad (i j k : Fin 4) :
    fpTriangle reflQuad i j k = ((((qquad i).jmul (qquad j)).tp (qquad k) : ℚ) : ℝ) := by
  rw [fpTriangle, reflQuad_eq_cast, reflQuad_eq_cast, reflQuad_eq_cast, castA_tp, castA_jmul]

theorem tp_jmul_cast (a b c d : QA) :
    tracePairing (jordanMul (castA a) (castA b)) (jordanMul (castA c) (castA d)) =
      (((a.jmul b).tp (c.jmul d) : ℚ) : ℝ) := by
  rw [castA_tp, castA_jmul, castA_jmul]

theorem q_overlaps :
    (qquad 0).tp (qquad 1) = 1 / 2 ∧ (qquad 0).tp (qquad 2) = 5 / 18 ∧
    (qquad 0).tp (qquad 3) = 5 / 18 ∧ (qquad 1).tp (qquad 2) = 5 / 18 ∧
    (qquad 1).tp (qquad 3) = 5 / 18 ∧ (qquad 2).tp (qquad 3) = 1 / 2 := by decide +kernel

theorem q_triangles :
    ((qquad 0).jmul (qquad 1)).tp (qquad 2) = 5 / 36 ∧
    ((qquad 0).jmul (qquad 1)).tp (qquad 3) = 5 / 36 ∧
    ((qquad 0).jmul (qquad 2)).tp (qquad 3) = 5 / 36 ∧
    ((qquad 1).jmul (qquad 2)).tp (qquad 3) = 5 / 36 := by decide +kernel

theorem q_doublePairs :
    ((qquad 0).jmul (qquad 1)).tp ((qquad 2).jmul (qquad 3)) = 5 / 72 ∧
    ((qquad 0).jmul (qquad 2)).tp ((qquad 1).jmul (qquad 3)) = 43 / 648 ∧
    ((qquad 0).jmul (qquad 3)).tp ((qquad 1).jmul (qquad 2)) = 43 / 648 := by decide +kernel

/-- The six overlaps (paper: `o_AB = o_CD = 1/2`, the other four `5/18`). -/
theorem reflQuad_overlaps :
    fpOverlap reflQuad 0 1 = 1 / 2 ∧ fpOverlap reflQuad 0 2 = 5 / 18 ∧
    fpOverlap reflQuad 0 3 = 5 / 18 ∧ fpOverlap reflQuad 1 2 = 5 / 18 ∧
    fpOverlap reflQuad 1 3 = 5 / 18 ∧ fpOverlap reflQuad 2 3 = 1 / 2 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := q_overlaps
  simp only [fpOverlap_reflQuad, h1, h2, h3, h4, h5, h6]
  norm_num

/-- The four triangles (paper: all `5/36`). -/
theorem reflQuad_triangles :
    fpTriangle reflQuad 0 1 2 = 5 / 36 ∧ fpTriangle reflQuad 0 1 3 = 5 / 36 ∧
    fpTriangle reflQuad 0 2 3 = 5 / 36 ∧ fpTriangle reflQuad 1 2 3 = 5 / 36 := by
  obtain ⟨h1, h2, h3, h4⟩ := q_triangles
  simp only [fpTriangle_reflQuad, h1, h2, h3, h4]
  norm_num

/-- The double pairings (paper: `(t₁,t₂,t₃) = (5/72, 43/648, 43/648)`). -/
theorem reflQuad_doublePairs :
    fpDoublePair1 reflQuad = 5 / 72 ∧ fpDoublePair2 reflQuad = 43 / 648 ∧
    fpDoublePair3 reflQuad = 43 / 648 := by
  obtain ⟨h1, h2, h3⟩ := q_doublePairs
  simp only [fpDoublePair1, fpDoublePair2, fpDoublePair3, reflQuad_eq_cast, tp_jmul_cast,
    h1, h2, h3]
  norm_num

/-- ω by middle letter (paper: `(ω₁,ω₂,ω₃) = (41/648, 5/72, 5/72)`; pairwise not all equal,
so this quadruple is an asymmetric ω control for `ω_B ≠ ω_C`). -/
theorem reflQuad_omegas :
    fpOmega1 reflQuad = 41 / 648 ∧ fpOmega2 reflQuad = 5 / 72 ∧ fpOmega3 reflQuad = 5 / 72 := by
  obtain ⟨h1, h2, h3⟩ := reflQuad_doublePairs
  simp only [fpOmega1, fpOmega2, fpOmega3, h1, h2, h3]
  norm_num

/-- `𝒜 = 1/11664` (paper, before thm:five:refl). -/
theorem fourPointInvariant_reflQuad : fourPointInvariant reflQuad = 1 / 11664 := by
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := reflQuad_overlaps
  obtain ⟨r1, r2, r3, r4⟩ := reflQuad_triangles
  obtain ⟨w1, w2, w3⟩ := reflQuad_omegas
  rw [fourPointInvariant, o1, o2, o3, o4, o5, o6, r1, r2, r3, r4, w1, w2, w3, fourPointOmegaPoly]
  norm_num

theorem fourPointInvariant_reflQuad_pos : 0 < fourPointInvariant reflQuad := by
  rw [fourPointInvariant_reflQuad]; norm_num

/-- By the four-point theorem the reflected quadruple generates `J`. -/
theorem reflQuad_generatesAlbert : GeneratesAlbert reflQuad :=
  (fourPointInvariant_pos_iff reflQuad reflQuad_isAtom).1 fourPointInvariant_reflQuad_pos

/-- The trace relation (prop:fp:tracerel) holds for the quadruple (general lemma),
and the computed values satisfy it: `5/72 + 2·43/648 = 1/2 − … ` (checked numerically here). -/
theorem reflQuad_trace_relation :
    fpDoublePair1 reflQuad + fpDoublePair2 reflQuad + fpDoublePair3 reflQuad =
      1 / 2
        - 1 / 2 * (fpOverlap reflQuad 0 1 + fpOverlap reflQuad 0 2 + fpOverlap reflQuad 0 3
            + fpOverlap reflQuad 1 2 + fpOverlap reflQuad 1 3 + fpOverlap reflQuad 2 3)
        + 1 / 2 * (fpOverlap reflQuad 0 1 * fpOverlap reflQuad 2 3
            + fpOverlap reflQuad 0 2 * fpOverlap reflQuad 1 3
            + fpOverlap reflQuad 0 3 * fpOverlap reflQuad 1 2)
        + fpTriangle reflQuad 0 1 2 + fpTriangle reflQuad 0 1 3 + fpTriangle reflQuad 0 2 3
        + fpTriangle reflQuad 1 2 3 :=
  albert_fourAtom_trace_relation reflQuad reflQuad_isAtom

/-- The same relation on the computed numbers (a consistency check of the values). -/
example : (5 / 72 + 43 / 648 + 43 / 648 : ℚ) =
    1 / 2 - 1 / 2 * (1 / 2 + 5 / 18 + 5 / 18 + 5 / 18 + 5 / 18 + 1 / 2)
      + 1 / 2 * (1 / 2 * (1 / 2) + 5 / 18 * (5 / 18) + 5 / 18 * (5 / 18))
      + 4 * (5 / 36) := by norm_num

end

end AlbertSequential.FiveTest
