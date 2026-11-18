/- SPDX-License-Identifier: Apache-2.0 -/
module

public import SubalgebraCoordsAndLine
public import ThirteenTracesAndAform
public import AlgebraicMomentBinding
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
-- build order only: keeps large modules from compiling concurrently (memory)
import BlockB.ElevenSupport

/-!
# The Pentad, Arity, and Quaternionic/Special Helly Theorems

Formalizes parts of core `sec:five` and of the appendix on proper subalgebras (`thm:pentad`, `prop:arity`, `lem:five:helly`, `cor:helly`, and negative control
`lineHellyCounterexample6`) in `PentadArityAndHelly.lean`.
-/

@[expose] public section

namespace AlbertSequential

noncomputable section

open scoped ComplexOrder

/-! ## Section 0: Coordinate, Dyad, and Spectral Projection Helpers -/

private theorem oct_ext {x y : Octonion}
    (h0 : x.1.re = y.1.re) (h1 : x.1.imI = y.1.imI) (h2 : x.1.imJ = y.1.imJ) (h3 : x.1.imK = y.1.imK)
    (h4 : x.2.re = y.2.re) (h5 : x.2.imI = y.2.imI) (h6 : x.2.imJ = y.2.imJ) (h7 : x.2.imK = y.2.imK) :
    x = y := by
  apply Prod.ext <;> apply Quaternion.ext <;> assumption

private theorem albert_ext {x y : Albert}
    (hd0 : x.1 0 = y.1 0) (hd1 : x.1 1 = y.1 1) (hd2 : x.1 2 = y.1 2)
    (ho0 : x.2 0 = y.2 0) (ho1 : x.2 1 = y.2 1) (ho2 : x.2 2 = y.2 2) : x = y := by
  apply Prod.ext <;> funext k <;> fin_cases k <;> assumption

def mkAlbert (d : Fin 3 → ℝ) (o : Fin 3 → Octonion) : Albert := (d, o)
@[simp] private theorem mkAlbert_fst (d : Fin 3 → ℝ) (o : Fin 3 → Octonion) : (mkAlbert d o).1 = d := rfl
@[simp] private theorem mkAlbert_snd (d : Fin 3 → ℝ) (o : Fin 3 → Octonion) : (mkAlbert d o).2 = o := rfl

@[simp] private theorem oct_zero_fst : (0 : Octonion).1 = 0 := rfl
@[simp] private theorem oct_zero_snd : (0 : Octonion).2 = 0 := rfl
@[simp] private theorem oct_add_fst (x y : Octonion) : (x + y).1 = x.1 + y.1 := rfl
@[simp] private theorem oct_add_snd (x y : Octonion) : (x + y).2 = x.2 + y.2 := rfl
@[simp] private theorem oct_sub_fst (x y : Octonion) : (x - y).1 = x.1 - y.1 := rfl
@[simp] private theorem oct_sub_snd (x y : Octonion) : (x - y).2 = x.2 - y.2 := rfl
@[simp] private theorem oct_neg_fst (x : Octonion) : (-x).1 = -x.1 := rfl
@[simp] private theorem oct_neg_snd (x : Octonion) : (-x).2 = -x.2 := rfl
@[simp] private theorem oct_smul_fst (r : ℝ) (x : Octonion) : (r • x).1 = r • x.1 := rfl
@[simp] private theorem oct_smul_snd (r : ℝ) (x : Octonion) : (r • x).2 = r • x.2 := rfl

private theorem octNormSq_zero : octNormSq 0 = 0 := by
  rw [octNormSq, octDot_zero_left]

private theorem albert_zero_fst (j : Fin 3) : (0 : Albert).1 j = 0 := rfl
private theorem albert_zero_snd (k : Fin 3) : (0 : Albert).2 k = 0 := rfl
private theorem albert_add_fst (x y : Albert) (j : Fin 3) : (x + y).1 j = x.1 j + y.1 j := rfl
private theorem albert_add_snd (x y : Albert) (k : Fin 3) : (x + y).2 k = x.2 k + y.2 k := rfl
private theorem albert_sub_fst (x y : Albert) (j : Fin 3) : (x - y).1 j = x.1 j - y.1 j := rfl
private theorem albert_sub_snd (x y : Albert) (k : Fin 3) : (x - y).2 k = x.2 k - y.2 k := rfl
private theorem albert_neg_fst (x : Albert) (j : Fin 3) : (-x).1 j = -x.1 j := rfl
private theorem albert_neg_snd (x : Albert) (k : Fin 3) : (-x).2 k = -x.2 k := rfl
private theorem albert_smul_fst (r : ℝ) (x : Albert) (j : Fin 3) : (r • x).1 j = r * x.1 j := rfl
private theorem albert_smul_snd (r : ℝ) (x : Albert) (k : Fin 3) : (r • x).2 k = r • x.2 k := rfl

private theorem diagAtom_fst (i j : Fin 3) : (diagAtom i).1 j = if j = i then 1 else 0 := rfl
private theorem diagAtom_snd (i k : Fin 3) : (diagAtom i).2 k = 0 := rfl
private theorem albertUnit_fst (j : Fin 3) : albertUnit.1 j = 1 := rfl
private theorem albertUnit_snd (k : Fin 3) : albertUnit.2 k = 0 := rfl

private theorem slotElem01_fst (a : Octonion) (j : Fin 3) : (slotElem01 a).1 j = 0 := rfl
private theorem slotElem01_snd_0 (a : Octonion) : (slotElem01 a).2 0 = a := rfl
private theorem slotElem01_snd_1 (a : Octonion) : (slotElem01 a).2 1 = 0 := rfl
private theorem slotElem01_snd_2 (a : Octonion) : (slotElem01 a).2 2 = 0 := rfl
private theorem slotElem02_fst (a : Octonion) (j : Fin 3) : (slotElem02 a).1 j = 0 := rfl
private theorem slotElem02_snd_0 (a : Octonion) : (slotElem02 a).2 0 = 0 := rfl
private theorem slotElem02_snd_1 (a : Octonion) : (slotElem02 a).2 1 = a := rfl
private theorem slotElem02_snd_2 (a : Octonion) : (slotElem02 a).2 2 = 0 := rfl
private theorem slotElem12_fst (a : Octonion) (j : Fin 3) : (slotElem12 a).1 j = 0 := rfl
private theorem slotElem12_snd_0 (a : Octonion) : (slotElem12 a).2 0 = 0 := rfl
private theorem slotElem12_snd_1 (a : Octonion) : (slotElem12 a).2 1 = 0 := rfl
private theorem slotElem12_snd_2 (a : Octonion) : (slotElem12 a).2 2 = a := rfl

private theorem albert_decompose_slots (x : Albert) :
    x = x.1 0 • diagAtom 0 + x.1 1 • diagAtom 1 + x.1 2 • diagAtom 2 +
      slotElem01 (x.2 0) + slotElem02 (x.2 1) + slotElem12 (x.2 2) := by
  apply albert_ext <;>
    simp [albert_add_fst, albert_add_snd, albert_smul_fst, albert_smul_snd,
      diagAtom_fst, diagAtom_snd, slotElem01_fst, slotElem01_snd_0, slotElem01_snd_1,
      slotElem01_snd_2, slotElem02_fst, slotElem02_snd_0, slotElem02_snd_1, slotElem02_snd_2,
      slotElem12_fst, slotElem12_snd_0, slotElem12_snd_1, slotElem12_snd_2]

private theorem jordanMul_diagAtom0_mk (x : Albert) :
    jordanMul (diagAtom 0) x =
      mkAlbert ![x.1 0, 0, 0] ![(1 / 2 : ℝ) • x.2 0, (1 / 2 : ℝ) • x.2 1, 0] :=
  jordanMul_diagAtom0 x

private theorem jordanMul_diagAtom2_mk (x : Albert) :
    jordanMul (diagAtom 2) x =
      mkAlbert ![0, 0, x.1 2] ![0, (1 / 2 : ℝ) • x.2 1, (1 / 2 : ℝ) • x.2 2] :=
  jordanMul_diagAtom2 x

@[simp] private theorem q_add_re (a b : Quaternion ℝ) : (a + b).re = a.re + b.re := rfl
@[simp] private theorem q_add_imI (a b : Quaternion ℝ) : (a + b).imI = a.imI + b.imI := rfl
@[simp] private theorem q_add_imJ (a b : Quaternion ℝ) : (a + b).imJ = a.imJ + b.imJ := rfl
@[simp] private theorem q_smul_re (r : ℝ) (a : Quaternion ℝ) : (r • a).re = r * a.re := rfl
@[simp] private theorem q_smul_imI (r : ℝ) (a : Quaternion ℝ) : (r • a).imI = r * a.imI := rfl
@[simp] private theorem q_smul_imJ (r : ℝ) (a : Quaternion ℝ) : (r • a).imJ = r * a.imJ := rfl
@[simp] private theorem q_neg_re (a : Quaternion ℝ) : (-a).re = -a.re := rfl
@[simp] private theorem q_neg_imI (a : Quaternion ℝ) : (-a).imI = -a.imI := rfl
@[simp] private theorem q_neg_imJ (a : Quaternion ℝ) : (-a).imJ = -a.imJ := rfl

private theorem albertTrace_zero_local : albertTrace 0 = 0 := by
  simp [albertTrace, albert_zero_fst]

private theorem tracePairing_unit_right_local (x : Albert) :
    tracePairing x albertUnit = albertTrace x := by
  unfold tracePairing; rw [jordanMul_albertUnit_right]

private theorem quadraticMap_compl_diagAtom0_eq (x : Albert) :
    quadraticMap (albertUnit - diagAtom 0) x = mkAlbert ![0, x.1 1, x.1 2] ![0, 0, x.2 2] := by
  have h1 : jordanMul (albertUnit - diagAtom 0) x =
      mkAlbert ![0, x.1 1, x.1 2] ![(1 / 2 : ℝ) • x.2 0, (1 / 2 : ℝ) • x.2 1, x.2 2] := by
    rw [jordanMul_sub_left, jordanMul_albertUnit_left, jordanMul_diagAtom0_mk]
    apply albert_ext <;>
      simp [albert_sub_fst, albert_sub_snd] <;> module
  have hff : jordanMul (albertUnit - diagAtom 0) (albertUnit - diagAtom 0) = albertUnit - diagAtom 0 := by
    simp only [jordanMul_sub_left, jordanMul_sub_right, jordanMul_albertUnit_left,
      jordanMul_albertUnit_right, (diagAtom_isAtom 0).1]
    abel
  unfold quadraticMap
  rw [two_nsmul, hff, h1]
  have h2 : jordanMul (albertUnit - diagAtom 0)
      (mkAlbert ![0, x.1 1, x.1 2] ![(1 / 2 : ℝ) • x.2 0, (1 / 2 : ℝ) • x.2 1, x.2 2]) =
      mkAlbert ![0, x.1 1, x.1 2] ![(1 / 4 : ℝ) • x.2 0, (1 / 4 : ℝ) • x.2 1, x.2 2] := by
    rw [jordanMul_sub_left, jordanMul_albertUnit_left, jordanMul_diagAtom0_mk]
    apply albert_ext <;> simp [albert_sub_fst, albert_sub_snd, smul_smul] <;>
      ((try rw [← sub_smul]); norm_num)
  rw [h2]
  apply albert_ext <;>
    simp [albert_add_fst, albert_add_snd, albert_sub_fst, albert_sub_snd] <;> module

private theorem octDyad_fst (v : Fin 3 → Octonion) (i : Fin 3) :
    (octDyad v).1 i = octNormSq (v i) := rfl
private theorem octDyad_snd_0 (v : Fin 3 → Octonion) :
    (octDyad v).2 0 = octonionMul (v 0) (octonionConj (v 1)) := rfl
private theorem octDyad_snd_1 (v : Fin 3 → Octonion) :
    (octDyad v).2 1 = octonionMul (v 0) (octonionConj (v 2)) := rfl
private theorem octDyad_snd_2 (v : Fin 3 → Octonion) :
    (octDyad v).2 2 = octonionMul (v 1) (octonionConj (v 2)) := rfl

private theorem octDyad_smul (r : ℝ) (v : Fin 3 → Octonion) :
    octDyad (fun i => r • v i) = (r ^ 2) • octDyad v := by
  apply albert_ext
  · simp [albert_smul_fst, octDyad_fst, octNormSq_smul]
  · simp [albert_smul_fst, octDyad_fst, octNormSq_smul]
  · simp [albert_smul_fst, octDyad_fst, octNormSq_smul]
  · simp [albert_smul_snd, octDyad_snd_0, octonionConj_smul, octonionMul_smul_left,
      octonionMul_smul_right, smul_smul, pow_two]
  · simp [albert_smul_snd, octDyad_snd_1, octonionConj_smul, octonionMul_smul_left,
      octonionMul_smul_right, smul_smul, pow_two]
  · simp [albert_smul_snd, octDyad_snd_2, octonionConj_smul, octonionMul_smul_left,
      octonionMul_smul_right, smul_smul, pow_two]

private theorem isAtom_scaled_octDyad (φ : Quaternion ℝ →ₗ[ℝ] Octonion) (hφ : IsQuatEmbedding φ)
    (r : ℝ) (hr : 0 < r) (v : Fin 3 → Octonion) (hv : ∀ i, v i ∈ Set.range φ)
    (hnorm : ∑ i : Fin 3, octNormSq (v i) = r) :
    IsAtom (r⁻¹ • octDyad v) := by
  let s : ℝ := (Real.sqrt r)⁻¹
  have hs2 : s ^ 2 = r⁻¹ := by
    dsimp only [s]
    rw [inv_pow, Real.sq_sqrt hr.le]
  have hdy : r⁻¹ • octDyad v = octDyad (fun i => s • v i) := by
    rw [octDyad_smul, hs2]
  rw [hdy]
  refine octDyad_isAtom φ hφ (fun i => s • v i) ?_ ?_
  · intro i
    rcases hv i with ⟨q, hq⟩
    refine ⟨s • q, ?_⟩
    rw [map_smul, hq]
  · simp only [octNormSq_smul, ← Finset.mul_sum, hnorm, hs2]
    exact inv_mul_cancel₀ hr.ne'

private theorem octNormSq_I : octNormSq octI = 1 := by
  rw [octNormSq_eq_coords]; simp [octI]
private theorem octNormSq_J : octNormSq octJ = 1 := by
  rw [octNormSq_eq_coords]; simp [octJ]
private theorem octNormSq_K : octNormSq octK = 1 := by
  rw [octNormSq_eq_coords]; simp [octK]
private theorem octNormSq_L : octNormSq octL = 1 := by
  rw [octNormSq_eq_coords]; simp [octL]
private theorem octNormSq_S : octNormSq octS = 1 := by
  rw [octNormSq_eq_coords]; simp [octS]

private theorem octonionConj_I : octonionConj octI = -octI := by
  apply oct_ext <;> simp only [octonionConj, oct_neg_fst, oct_neg_snd] <;> simp [octI]
private theorem octonionConj_J : octonionConj octJ = -octJ := by
  apply oct_ext <;> simp only [octonionConj, oct_neg_fst, oct_neg_snd] <;> simp [octJ]
private theorem octonionConj_K : octonionConj octK = -octK := by
  apply oct_ext <;> simp only [octonionConj, oct_neg_fst, oct_neg_snd] <;> simp [octK]
private theorem octonionConj_L : octonionConj octL = -octL := by
  apply oct_ext <;> simp only [octonionConj, oct_neg_fst, oct_neg_snd] <;> simp [octL]

private theorem octDot_symm (x y : Octonion) : octDot x y = octDot y x := by
  rw [octDot_eq_coords, octDot_eq_coords]; ring

private theorem octMul_J_I : octonionMul octJ octI = -octK := by
  apply oct_ext <;> simp only [octonionMul, oct_neg_fst, oct_neg_snd] <;> simp [octJ, octI, octK]

private theorem octMul_L_I : octonionMul octL octI = -octS := by
  apply oct_ext <;> simp only [octonionMul, oct_neg_fst, oct_neg_snd] <;> simp [octL, octI, octS]

private theorem octDot_unit_basis :
    octDot octOne octI = 0 ∧ octDot octOne octJ = 0 ∧ octDot octOne octK = 0 ∧ octDot octOne octL = 0 ∧
    octDot octI octJ = 0 ∧ octDot octI octK = 0 ∧ octDot octI octL = 0 ∧
    octDot octJ octK = 0 ∧ octDot octJ octL = 0 ∧ octDot octK octL = 0 := by
  repeat' constructor
  all_goals (rw [octDot_eq_coords]; simp [octOne, octonionScalar, octI, octJ, octK, octL])

private theorem octDot_quat_S :
    octDot octOne octS = 0 ∧ octDot octI octS = 0 ∧ octDot octL octS = 0 := by
  repeat' constructor
  all_goals (rw [octDot_eq_coords]; simp [octOne, octonionScalar, octI, octL, octS])

private theorem octOne_mem_range_quat (φ : Quaternion ℝ →ₗ[ℝ] Octonion) (hφ : IsQuatEmbedding φ) :
    octOne ∈ Set.range φ := ⟨1, by rw [hφ.map_one]; rfl⟩

private theorem quatEmbed1_mem_of_snd_zero (a : Octonion) (ha : a.2 = 0) :
    a ∈ Set.range quatEmbed1 := by
  refine ⟨a.1, ?_⟩
  apply oct_ext <;> simp [quatEmbed1_apply, ha]

private theorem lineSubalgebra_finrank (q : Albert) (hq : IsAtom q) :
    Module.finrank ℝ (lineSubalgebra q hq).carrier = 11 := by
  have : Module.Finite ℝ Octonion :=
    inferInstanceAs (FiniteDimensional ℝ (Quaternion ℝ × Quaternion ℝ))
  obtain ⟨g, hg⟩ := atom_to_diagAtom0 q hq
  let L0 := lineSubalgebra (diagAtom 0) (diagAtom_isAtom 0)
  let eqvL : (lineSubalgebra q hq).carrier ≃ₗ[ℝ] L0.carrier :=
    { toFun := fun x => ⟨g.linearEquiv x.1, by
        rw [mem_lineSubalgebra_iff, ← hg, ← g.preserves_product,
          (mem_lineSubalgebra_iff q hq x.1).mp x.2, map_smul, g.map_tracePairing]⟩
      invFun := fun y => ⟨g.linearEquiv.symm y.1, by
        rw [mem_lineSubalgebra_iff]
        apply g.linearEquiv.injective
        rw [g.preserves_product, map_smul, ← g.map_tracePairing q (g.linearEquiv.symm y.1),
          LinearEquiv.apply_symm_apply, hg]
        exact (mem_lineSubalgebra_iff (diagAtom 0) (diagAtom_isAtom 0) y.1).mp y.2⟩
      left_inv := fun x => Subtype.ext (g.linearEquiv.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (g.linearEquiv.apply_symm_apply y.1)
      map_add' := fun x y => Subtype.ext (g.linearEquiv.map_add x.1 y.1)
      map_smul' := fun r x => Subtype.ext (g.linearEquiv.map_smul r x.1) }
  have hmem0 : ∀ y : Albert, y ∈ L0.carrier ↔ y.2 0 = 0 ∧ y.2 1 = 0 := fun y => by
    rw [mem_lineSubalgebra_iff]
    constructor
    · intro h
      have h0 : (jordanMul (diagAtom 0) y).2 0 = (tracePairing (diagAtom 0) y • diagAtom 0).2 0 :=
        congrArg (fun a : Albert => a.2 0) h
      have h1 : (jordanMul (diagAtom 0) y).2 1 = (tracePairing (diagAtom 0) y • diagAtom 0).2 1 :=
        congrArg (fun a : Albert => a.2 1) h
      rw [jordanMul_diagAtom0, albert_smul_snd, diagAtom_snd, smul_zero] at h0 h1
      exact ⟨by
        have hs0 : ((1 / 2 : ℝ) • y.2 0) = 0 := h0
        simpa using congrArg (fun u : Octonion => (2 : ℝ) • u) hs0, by
        have hs1 : ((1 / 2 : ℝ) • y.2 1) = 0 := h1
        simpa using congrArg (fun u : Octonion => (2 : ℝ) • u) hs1⟩
    · intro ⟨hy0, hy1⟩
      apply albert_ext
      · rw [jordanMul_diagAtom0, albert_smul_fst, diagAtom_fst, tracePairing_eq_coords]
        simp [diagAtom_fst, diagAtom_snd, octDot_zero_left]
      · rw [jordanMul_diagAtom0, albert_smul_fst, diagAtom_fst]; simp
      · rw [jordanMul_diagAtom0, albert_smul_fst, diagAtom_fst]; simp
      · simp [jordanMul_diagAtom0, albert_smul_snd, diagAtom_snd, hy0]
      · simp [jordanMul_diagAtom0, albert_smul_snd, diagAtom_snd, hy1]
      · simp [jordanMul_diagAtom0, albert_smul_snd, diagAtom_snd]
  let eqvCoord : L0.carrier ≃ₗ[ℝ] ((Fin 3 → ℝ) × Octonion) :=
    { toFun := fun y => (y.1.1, y.1.2 2)
      invFun := fun p => ⟨(p.1, ![0, 0, p.2]), (hmem0 _).mpr ⟨rfl, rfl⟩⟩
      left_inv := fun y => by
        have hy := (hmem0 y.1).mp y.2
        apply Subtype.ext
        apply albert_ext <;> simp [hy.1, hy.2]
      right_inv := fun p => by apply Prod.ext <;> rfl
      map_add' := fun x y => by apply Prod.ext <;> rfl
      map_smul' := fun r x => by apply Prod.ext <;> rfl }
  rw [eqvL.finrank_eq, eqvCoord.finrank_eq, Module.finrank_prod, Module.finrank_fin_fun,
    oct_finrank]

private def vecIp {d : ℕ} (u v : Fin d → ℂ) : ℂ :=
  ∑ i : Fin d, star (u i) * v i

private theorem vecIp_smul_right {d : ℕ} (c : ℂ) (u v : Fin d → ℂ) :
    vecIp u (c • v) = c * vecIp u v := by
  simp only [vecIp, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

private theorem vecIp_smul_left {d : ℕ} (c : ℂ) (u v : Fin d → ℂ) :
    vecIp (c • u) v = star c * vecIp u v := by
  simp only [vecIp, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

private theorem vecIp_add_right {d : ℕ} (u v w : Fin d → ℂ) :
    vecIp u (v + w) = vecIp u v + vecIp u w := by
  simp only [vecIp, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem vecIp_sub_right {d : ℕ} (u v w : Fin d → ℂ) :
    vecIp u (v - w) = vecIp u v - vecIp u w := by
  simp only [vecIp, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

private theorem vecIp_conj {d : ℕ} (u v : Fin d → ℂ) :
    star (vecIp u v) = vecIp v u := by
  simp only [vecIp, star_sum, star_mul', star_star]
  refine Finset.sum_congr rfl fun i _ => mul_comm _ _

private theorem vecIp_self_eq_zero {d : ℕ} (u : Fin d → ℂ) :
    vecIp u u = 0 ↔ u = 0 := by
  constructor
  · intro h
    have hre : (vecIp u u).re = 0 := by rw [h, Complex.zero_re]
    simp only [vecIp, Complex.re_sum] at hre
    have hterm : ∀ i : Fin d, (star (u i) * u i).re = (u i).re ^ 2 + (u i).im ^ 2 := fun i => by
      simp [sq]
    simp_rw [hterm] at hre
    have hnn : ∀ i : Fin d, 0 ≤ (u i).re ^ 2 + (u i).im ^ 2 := fun i =>
      add_nonneg (sq_nonneg _) (sq_nonneg _)
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnn i)).mp hre
    funext i
    have hi := hall i (Finset.mem_univ i)
    have h1 : (u i).re ^ 2 = 0 := by linarith [sq_nonneg (u i).re, sq_nonneg (u i).im]
    have h2 : (u i).im ^ 2 = 0 := by linarith [sq_nonneg (u i).re, sq_nonneg (u i).im]
    exact Complex.ext (sq_eq_zero_iff.mp h1) (sq_eq_zero_iff.mp h2)
  · intro h; subst h; simp [vecIp]

private theorem vecIp_self_re_pos {d : ℕ} {u : Fin d → ℂ} (hu : u ≠ 0) :
    0 < (vecIp u u).re := by
  have hge : 0 ≤ (vecIp u u).re := by
    simp only [vecIp, Complex.re_sum]
    refine Finset.sum_nonneg fun i _ => ?_
    have h1 : (star (u i) * u i).re = (u i).re ^ 2 + (u i).im ^ 2 := by simp [sq]
    rw [h1]
    exact add_nonneg (sq_nonneg _) (sq_nonneg _)
  have him : (vecIp u u).im = 0 := by
    have hs : star (vecIp u u) = vecIp u u := vecIp_conj u u
    have him' := congrArg Complex.im hs
    simp only [Complex.star_def, Complex.conj_im] at him'
    linarith
  have hne : (vecIp u u).re ≠ 0 := fun h0 => by
    have hzero : vecIp u u = 0 := Complex.ext h0 him
    exact hu ((vecIp_self_eq_zero u).mp hzero)
  exact lt_of_le_of_ne hge (Ne.symm hne)

private theorem hermitian_idempotent_spectral_rank {d k : ℕ}
    (P : HermitianEmbeddingMatrix d) (hH : P.IsHermitian) (hId : P * P = P)
    (hTr : Matrix.trace P = (k : ℂ)) :
    ∃ cols : Fin k → (Fin d → ℂ),
      (∀ r, vecIp (cols r) (cols r) = 1) ∧
      (∀ r s, r ≠ s → vecIp (cols r) (cols s) = 0) ∧
      ∀ a b, P a b = ∑ r : Fin k, cols r a * star (cols r b) := by
  let U : HermitianEmbeddingMatrix d := hH.eigenvectorUnitary
  let μ : Fin d → ℝ := hH.eigenvalues
  have hUU : U.conjTranspose * U = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self hH.eigenvectorUnitary
  have hUUt : U * U.conjTranspose = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using
      Unitary.coe_mul_star_self hH.eigenvectorUnitary
  have hspec : P = U * Matrix.diagonal (fun i => (μ i : ℂ)) * U.conjTranspose := by
    simpa [U, μ, Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.star_eq_conjTranspose] using
      hH.spectral_theorem
  have hdiag : U.conjTranspose * P * U = Matrix.diagonal (fun i => (μ i : ℂ)) := by
    rw [hspec]
    calc
      U.conjTranspose * (U * Matrix.diagonal (fun i => (μ i : ℂ)) * U.conjTranspose) * U
        = (U.conjTranspose * U) * Matrix.diagonal (fun i => (μ i : ℂ)) * (U.conjTranspose * U) := by
            simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal (fun i => (μ i : ℂ)) := by rw [hUU, one_mul, mul_one]
  have hdiag_sq : Matrix.diagonal (fun i => (μ i : ℂ)) * Matrix.diagonal (fun i => (μ i : ℂ)) =
      Matrix.diagonal (fun i => (μ i : ℂ)) := by
    calc
      Matrix.diagonal (fun i => (μ i : ℂ)) * Matrix.diagonal (fun i => (μ i : ℂ))
        = (U.conjTranspose * P * U) * (U.conjTranspose * P * U) := by rw [hdiag]
      _ = U.conjTranspose * P * (U * U.conjTranspose) * P * U := by simp only [Matrix.mul_assoc]
      _ = U.conjTranspose * (P * P) * U := by rw [hUUt, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = U.conjTranspose * P * U := by rw [hId]
      _ = Matrix.diagonal (fun i => (μ i : ℂ)) := hdiag
  have hμ01 : ∀ i : Fin d, μ i = 0 ∨ μ i = 1 := fun i => by
    have hi := congrFun (congrFun hdiag_sq i) i
    rw [Matrix.diagonal_mul_diagonal] at hi
    simp only [Matrix.diagonal_apply_eq] at hi
    have hre := congrArg Complex.re hi
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hre
    have hfac : μ i * (μ i - 1) = 0 := by linarith
    rcases mul_eq_zero.mp hfac with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  have htr_sum : ∑ i : Fin d, μ i = k := by
    have htrP : Matrix.trace P = ∑ i : Fin d, (μ i : ℂ) := by
      calc
        Matrix.trace P = Matrix.trace (U * Matrix.diagonal (fun i => (μ i : ℂ)) * U.conjTranspose) := by
          rw [hspec]
        _ = Matrix.trace ((U.conjTranspose * U) * Matrix.diagonal (fun i => (μ i : ℂ))) := by
          rw [Matrix.trace_mul_cycle]
        _ = Matrix.trace (Matrix.diagonal (fun i => (μ i : ℂ))) := by rw [hUU, one_mul]
        _ = ∑ i : Fin d, (μ i : ℂ) := Matrix.trace_diagonal _
    rw [hTr] at htrP
    have hre := congrArg Complex.re htrP
    simp only [Complex.natCast_re, Complex.re_sum, Complex.ofReal_re] at hre
    exact hre.symm
  classical
  let S : Finset (Fin d) := Finset.univ.filter (fun i => μ i = 1)
  have hS_sum : ∑ i : Fin d, μ i = S.card := by
    have hsplit : ∑ i : Fin d, μ i = (∑ i ∈ S, μ i) + ∑ i ∈ Sᶜ, μ i :=
      (Finset.sum_add_sum_compl S μ).symm
    have h1 : ∑ i ∈ S, μ i = (S.card : ℝ) := by
      rw [Finset.sum_congr rfl fun i hi => (Finset.mem_filter.mp hi).2,
        Finset.sum_const, nsmul_eq_mul, mul_one]
    have h0 : ∑ i ∈ Sᶜ, μ i = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have hne : μ i ≠ 1 := fun h => (Finset.mem_compl.mp hi) (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
      exact (hμ01 i).resolve_right hne
    rw [hsplit, h1, h0, add_zero]
  have hScard : S.card = k := by exact_mod_cast (hS_sum.symm.trans htr_sum)
  let eqv := (Fintype.equivFinOfCardEq (n := k) (by rw [Fintype.card_coe S]; exact hScard)).symm
  let cols : Fin k → (Fin d → ℂ) := fun r a => U a (eqv r).1
  refine ⟨cols, ?_, ?_, ?_⟩
  · intro r
    have hcol : vecIp (cols r) (cols r) = (U.conjTranspose * U) (eqv r).1 (eqv r).1 := by
      simp [vecIp, cols, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [hcol, hUU, Matrix.one_apply_eq]
  · intro r s hrs
    have hne : (eqv r).1 ≠ (eqv s).1 := fun h => hrs (eqv.injective (Subtype.ext h))
    have hcol : vecIp (cols r) (cols s) = (U.conjTranspose * U) (eqv r).1 (eqv s).1 := by
      simp [vecIp, cols, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [hcol, hUU, Matrix.one_apply_ne hne]
  · intro a b
    have hP : P a b = ∑ i : Fin d, U a i * (μ i : ℂ) * star (U b i) := by
      conv_lhs => rw [hspec]
      simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply]
      simp [mul_ite, Finset.sum_ite_eq']
    rw [hP]
    have hzero : ∀ i : Fin d, i ∉ S → U a i * (μ i : ℂ) * star (U b i) = 0 := fun i hi => by
      have hne : μ i ≠ 1 := fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
      rw [(hμ01 i).resolve_right hne]
      simp
    have hS_sub : ∑ i : Fin d, U a i * (μ i : ℂ) * star (U b i) =
        ∑ i ∈ S, U a i * star (U b i) := by
      rw [← Finset.sum_filter_of_ne (p := fun i => i ∈ S) fun i _ hne => by
        by_contra hni; exact hne (hzero i hni)]
      refine Finset.sum_congr (by ext i; simp) fun i hi => ?_
      have h1 : μ i = 1 := (Finset.mem_filter.mp hi).2
      rw [h1, Complex.ofReal_one, mul_one]
    rw [hS_sub]
    have heqv_sum := Fintype.sum_equiv eqv
      (fun r : Fin k => cols r a * star (cols r b))
      (fun i : S => U a i.1 * star (U b i.1))
      (fun r => rfl)
    rw [← Finset.sum_coe_sort S, ← heqv_sum]

private theorem trace_psd_mul_sq_nonneg {d : ℕ} {σ : HermitianEmbeddingMatrix d}
    (hσ : σ.PosSemidef) (X : HermitianEmbeddingMatrix d) :
    0 ≤ (Matrix.trace (σ * (star X * X))).re := by
  have hσH : σ.IsHermitian := hσ.isHermitian
  let U : HermitianEmbeddingMatrix d := hσH.eigenvectorUnitary
  let μ : Fin d → ℝ := hσH.eigenvalues
  have hUU : U.conjTranspose * U = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self hσH.eigenvectorUnitary
  have hspec : σ = U * Matrix.diagonal (fun i => (μ i : ℂ)) * U.conjTranspose := by
    simpa [U, μ, Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.star_eq_conjTranspose] using
      hσH.spectral_theorem
  have hμ : ∀ i : Fin d, 0 ≤ μ i := fun i => by
    let col : Fin d → ℂ := fun a => U a i
    have hdot := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hσ).2 col
    have heq : star col ⬝ᵥ Matrix.mulVec σ col = (μ i : ℂ) := by
      have hcol_mul : star col ⬝ᵥ Matrix.mulVec σ col = (U.conjTranspose * σ * U) i i := by
        simp only [dotProduct, Matrix.mulVec, col, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Finset.mul_sum, Finset.sum_mul, mul_assoc]
        rw [Finset.sum_comm]
        rfl
      have hdiag : U.conjTranspose * σ * U = Matrix.diagonal (fun j => (μ j : ℂ)) := by
        rw [hspec]
        calc
          U.conjTranspose * (U * Matrix.diagonal (fun j => (μ j : ℂ)) * U.conjTranspose) * U
            = (U.conjTranspose * U) * Matrix.diagonal (fun j => (μ j : ℂ)) * (U.conjTranspose * U) := by
                simp only [Matrix.mul_assoc]
          _ = Matrix.diagonal (fun j => (μ j : ℂ)) := by rw [hUU, one_mul, mul_one]
      rw [hcol_mul, hdiag, Matrix.diagonal_apply_eq]
    rw [heq] at hdot
    exact Complex.nonneg_iff.mp hdot |>.1
  let D : HermitianEmbeddingMatrix d := Matrix.diagonal (fun i => (Real.sqrt (μ i) : ℂ))
  have hD2 : D * D = Matrix.diagonal (fun i => (μ i : ℂ)) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1; ext i; exact_mod_cast Real.mul_self_sqrt (hμ i)
  have hD_herm : D.conjTranspose = D := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [D]
    · simp [D, hij, Ne.symm hij]
  have hσ_fac : σ = (U * D) * (U * D).conjTranspose := by
    rw [Matrix.conjTranspose_mul, hD_herm, hspec, ← hD2]
    simp only [Matrix.mul_assoc]
  let Y := X * (U * D)
  have htr_eq : Matrix.trace (σ * (star X * X)) = Matrix.trace (Y.conjTranspose * Y) := by
    rw [hσ_fac, Matrix.star_eq_conjTranspose, Matrix.mul_assoc (U * D), Matrix.trace_mul_comm]
    dsimp only [Y]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [htr_eq]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  have hsq : (star (Y j i) * Y j i).re = (Y j i).re ^ 2 + (Y j i).im ^ 2 := by simp [sq]
  rw [hsq]
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

/-! ## Section 1: Explicit Pentad `pentadF`, Subfamilies, and `thm:pentad` (i)–(iii) -/

def pentadF : Fin 5 → Albert
  | 0 => diagAtom 0
  | 1 => (1 / 2 : ℝ) • octDyad ![octOne, octOne, 0]
  | 2 => (1 / 3 : ℝ) • octDyad ![octOne, octI, octOne]
  | 3 => (1 / 2 : ℝ) • octDyad ![octOne, octJ, 0]
  | 4 => (1 / 2 : ℝ) • octDyad ![octOne, octL, 0]

def pentadDrop (k : Fin 5) : Fin 4 → Albert :=
  fun j => pentadF (k.succAbove j)

private theorem pentadF_0_eq : pentadF 0 = diagAtom 0 := rfl

private theorem pentadF_1_eq :
    pentadF 1 = mkAlbert ![1 / 2, 1 / 2, 0] ![octonionScalar (1 / 2), 0, 0] := by
  apply albert_ext
  · simp [pentadF, albert_smul_fst, octDyad_fst, octNormSq_one]
  · simp [pentadF, albert_smul_fst, octDyad_fst, octNormSq_one]
  · simp [pentadF, albert_smul_fst, octDyad_fst, octNormSq_zero]
  · apply oct_ext <;>
      simp only [pentadF, mkAlbert_snd, Matrix.cons_val_zero, albert_smul_snd, octDyad_snd_0,
        oct_smul_fst, oct_smul_snd, Matrix.cons_val_one] <;>
      (simp [octOne, octonionScalar, octonionConj, octonionMul]; try norm_num)
  · simp [pentadF, albert_smul_snd, octDyad_snd_1, octonionConj_zero, octonionMul_zero_right]
  · simp [pentadF, albert_smul_snd, octDyad_snd_2, octonionConj_zero, octonionMul_zero_right]

private theorem pentadF_2_eq :
    pentadF 2 = mkAlbert ![1 / 3, 1 / 3, 1 / 3] ![(-1 / 3 : ℝ) • octI, (1 / 3 : ℝ) • octOne, (1 / 3 : ℝ) • octI] := by
  apply albert_ext
  · simp [pentadF, albert_smul_fst, octDyad_fst, octNormSq_one]
  · simp [pentadF, albert_smul_fst, octDyad_fst, octNormSq_I]
  · simp [pentadF, albert_smul_fst, octDyad_fst, octNormSq_one]
  · apply oct_ext <;>
      simp only [pentadF, mkAlbert_snd, Matrix.cons_val_zero, albert_smul_snd, octDyad_snd_0,
        oct_smul_fst, oct_smul_snd, Matrix.cons_val_one] <;>
      (simp [octOne, octonionScalar, octI, octonionConj, octonionMul]; try norm_num)
  · apply oct_ext <;>
      simp only [pentadF, mkAlbert_snd, Matrix.cons_val_one, Matrix.cons_val_zero, albert_smul_snd,
        octDyad_snd_1, oct_smul_fst, oct_smul_snd] <;>
      (simp [octOne, octonionScalar, octonionConj, octonionMul]; try norm_num)
  · apply oct_ext <;>
      simp only [pentadF, mkAlbert_snd, Matrix.cons_val_one, Matrix.cons_val_zero,
        Matrix.cons_val, Fin.isValue, albert_smul_snd, octDyad_snd_2, oct_smul_fst,
        oct_smul_snd] <;>
      (simp [octOne, octonionScalar, octI, octonionConj, octonionMul]; try norm_num)

private theorem pentadF_3_eq :
    pentadF 3 = mkAlbert ![1 / 2, 1 / 2, 0] ![(-1 / 2 : ℝ) • octJ, 0, 0] := by
  apply albert_ext
  · simp [pentadF, albert_smul_fst, octDyad_fst, octNormSq_one]
  · simp [pentadF, albert_smul_fst, octDyad_fst, octNormSq_J]
  · simp [pentadF, albert_smul_fst, octDyad_fst, octNormSq_zero]
  · apply oct_ext <;>
      simp only [pentadF, mkAlbert_snd, Matrix.cons_val_zero, Matrix.cons_val_one, albert_smul_snd,
        octDyad_snd_0, oct_smul_fst, oct_smul_snd] <;>
      (simp [octOne, octonionScalar, octJ, octonionConj, octonionMul]; try norm_num)
  · simp [pentadF, albert_smul_snd, octDyad_snd_1, octonionConj_zero, octonionMul_zero_right]
  · simp [pentadF, albert_smul_snd, octDyad_snd_2, octonionConj_zero, octonionMul_zero_right]

private theorem pentadF_4_eq :
    pentadF 4 = mkAlbert ![1 / 2, 1 / 2, 0] ![(-1 / 2 : ℝ) • octL, 0, 0] := by
  apply albert_ext
  · simp [pentadF, albert_smul_fst, octDyad_fst, octNormSq_one]
  · simp [pentadF, albert_smul_fst, octDyad_fst, octNormSq_L]
  · simp [pentadF, albert_smul_fst, octDyad_fst, octNormSq_zero]
  · apply oct_ext <;>
      simp only [pentadF, mkAlbert_snd, Matrix.cons_val_zero, Matrix.cons_val_one, albert_smul_snd,
        octDyad_snd_0, oct_smul_fst, oct_smul_snd] <;>
      (simp [octOne, octonionScalar, octL, octonionConj, octonionMul]; try norm_num)
  · simp [pentadF, albert_smul_snd, octDyad_snd_1, octonionConj_zero, octonionMul_zero_right]
  · simp [pentadF, albert_smul_snd, octDyad_snd_2, octonionConj_zero, octonionMul_zero_right]

theorem pentadF_isAtom (i : Fin 5) : IsAtom (pentadF i) := by
  fin_cases i <;> dsimp
  · exact diagAtom_isAtom 0
  · simp only [pentadF, one_div]
    refine isAtom_scaled_octDyad quatEmbed1 quatEmbed1_isQuatEmbedding 2 (by norm_num) _ ?_ ?_
    · intro k; fin_cases k
      · exact octOne_mem_range_quat quatEmbed1 quatEmbed1_isQuatEmbedding
      · exact octOne_mem_range_quat quatEmbed1 quatEmbed1_isQuatEmbedding
      · exact ⟨0, map_zero _⟩
    · simp [Fin.sum_univ_three, octNormSq_one, octNormSq_zero]; norm_num
  · simp only [pentadF, one_div]
    refine isAtom_scaled_octDyad quatEmbed1 quatEmbed1_isQuatEmbedding 3 (by norm_num) _ ?_ ?_
    · intro k; fin_cases k
      · exact octOne_mem_range_quat quatEmbed1 quatEmbed1_isQuatEmbedding
      · exact quatEmbed1_mem_of_snd_zero octI rfl
      · exact octOne_mem_range_quat quatEmbed1 quatEmbed1_isQuatEmbedding
    · simp [Fin.sum_univ_three, octNormSq_one, octNormSq_I]; norm_num
  · simp only [pentadF, one_div]
    refine isAtom_scaled_octDyad quatEmbed1 quatEmbed1_isQuatEmbedding 2 (by norm_num) _ ?_ ?_
    · intro k; fin_cases k
      · exact octOne_mem_range_quat quatEmbed1 quatEmbed1_isQuatEmbedding
      · exact quatEmbed1_mem_of_snd_zero octJ rfl
      · exact ⟨0, map_zero _⟩
    · simp [Fin.sum_univ_three, octNormSq_one, octNormSq_J, octNormSq_zero]; norm_num
  · obtain ⟨φ, hφ, h1, hL⟩ := exists_quatEmbedding_containing_pair octOne octL
    simp only [pentadF, one_div]
    refine isAtom_scaled_octDyad φ hφ 2 (by norm_num) _ ?_ ?_
    · intro k; fin_cases k
      · exact h1
      · exact hL
      · exact ⟨0, map_zero _⟩
    · simp [Fin.sum_univ_three, octNormSq_one, octNormSq_L, octNormSq_zero]; norm_num

theorem pentadF_overlaps_two (k : Fin 5) (hk : k ≠ 2) :
    tracePairing (pentadF 2) (pentadF k) = 1 / 3 := by
  fin_cases k <;> dsimp
  · rw [tracePairing_eq_coords, pentadF_2_eq, pentadF_0_eq]
    simp [diagAtom_fst, diagAtom_snd, octDot_zero_right]
  · rw [tracePairing_eq_coords, pentadF_2_eq, pentadF_1_eq]
    rw [octonionScalar_eq_smul (1 / 2), ← octOne_eq_scalar]
    simp [octDot_smul_left, octDot_smul_right, octDot_zero_right,
      octDot_symm octI octOne, octDot_unit_basis.1]; norm_num
  · exact absurd rfl hk
  · rw [tracePairing_eq_coords, pentadF_2_eq, pentadF_3_eq]
    simp [octDot_smul_left, octDot_smul_right, octDot_zero_right, octDot_unit_basis.2.2.2.2.1]
    norm_num
  · rw [tracePairing_eq_coords, pentadF_2_eq, pentadF_4_eq]
    simp [octDot_smul_left, octDot_smul_right, octDot_zero_right, octDot_unit_basis.2.2.2.2.2.2.1]
    norm_num

private theorem pentadF_overlaps_other_aux :
    tracePairing (pentadF 0) (pentadF 1) = 1 / 2 ∧
    tracePairing (pentadF 0) (pentadF 3) = 1 / 2 ∧
    tracePairing (pentadF 0) (pentadF 4) = 1 / 2 ∧
    tracePairing (pentadF 1) (pentadF 3) = 1 / 2 ∧
    tracePairing (pentadF 1) (pentadF 4) = 1 / 2 ∧
    tracePairing (pentadF 3) (pentadF 4) = 1 / 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [tracePairing_eq_coords, pentadF_0_eq, pentadF_1_eq]
    simp [diagAtom_fst, diagAtom_snd, octDot_zero_left]
  · rw [tracePairing_eq_coords, pentadF_0_eq, pentadF_3_eq]
    simp [diagAtom_fst, diagAtom_snd, octDot_zero_left]
  · rw [tracePairing_eq_coords, pentadF_0_eq, pentadF_4_eq]
    simp [diagAtom_fst, diagAtom_snd, octDot_zero_left]
  · rw [tracePairing_eq_coords, pentadF_1_eq, pentadF_3_eq]
    rw [octonionScalar_eq_smul (1 / 2), ← octOne_eq_scalar]
    simp [octDot_smul_left, octDot_smul_right, octDot_zero_left, octDot_unit_basis.2.1]; norm_num
  · rw [tracePairing_eq_coords, pentadF_1_eq, pentadF_4_eq]
    rw [octonionScalar_eq_smul (1 / 2), ← octOne_eq_scalar]
    simp [octDot_smul_left, octDot_smul_right, octDot_zero_left, octDot_unit_basis.2.2.2.1]; norm_num
  · rw [tracePairing_eq_coords, pentadF_3_eq, pentadF_4_eq]
    simp [octDot_smul_left, octDot_smul_right, octDot_zero_left,
      octDot_unit_basis.2.2.2.2.2.2.2.2.1]; norm_num

theorem pentadF_overlaps_other {i j : Fin 5} (hij : i ≠ j) (hi : i ≠ 2) (hj : j ≠ 2) :
    tracePairing (pentadF i) (pentadF j) = 1 / 2 := by
  have h := pentadF_overlaps_other_aux
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact h.1
  · exact absurd rfl hj
  · exact h.2.1
  · exact h.2.2.1
  · rw [tracePairing_comm]; exact h.1
  · exact absurd rfl hij
  · exact absurd rfl hj
  · exact h.2.2.2.1
  · exact h.2.2.2.2.1
  · exact absurd rfl hi
  · exact absurd rfl hi
  · exact absurd rfl hi
  · exact absurd rfl hi
  · exact absurd rfl hi
  · rw [tracePairing_comm]; exact h.2.1
  · rw [tracePairing_comm]; exact h.2.2.2.1
  · exact absurd rfl hj
  · exact absurd rfl hij
  · exact h.2.2.2.2.2
  · rw [tracePairing_comm]; exact h.2.2.1
  · rw [tracePairing_comm]; exact h.2.2.2.2.1
  · exact absurd rfl hj
  · rw [tracePairing_comm]; exact h.2.2.2.2.2
  · exact absurd rfl hij

theorem pentadF_generatesAlbert : GeneratesAlbert pentadF := by
  rw [generatesAlbert_iff_generatedSubalgebra_eq_top]
  let B := generatedSubalgebra (Set.range pentadF)
  have hp : ∀ i : Fin 5, pentadF i ∈ B.carrier := fun i =>
    subset_generatedSubalgebra _ ⟨i, rfl⟩
  have hd0 : diagAtom 0 ∈ B.carrier := hp 0
  have hd1_half : (1 / 2 : ℝ) • diagAtom 1 ∈ B.carrier := by
    have hmem : quadraticMap (albertUnit - diagAtom 0) (pentadF 1) ∈ B.carrier :=
      (peirce_components_mem_subalgebra B hd0 (hp 1)).2.2
    have heq : quadraticMap (albertUnit - diagAtom 0) (pentadF 1) = (1 / 2 : ℝ) • diagAtom 1 := by
      rw [quadraticMap_compl_diagAtom0_eq, pentadF_1_eq]
      apply albert_ext <;> simp [albert_smul_fst, albert_smul_snd, diagAtom_fst, diagAtom_snd]
    rwa [heq] at hmem
  have hd1 : diagAtom 1 ∈ B.carrier := by
    have h2 : (2 : ℝ) * (1 / 2 : ℝ) = 1 := by norm_num
    have hs := B.carrier.smul_mem (2 : ℝ) hd1_half
    rwa [smul_smul, h2, one_smul] at hs
  have hd2 : diagAtom 2 ∈ B.carrier := by
    have heq : diagAtom 2 = albertUnit - diagAtom 0 - diagAtom 1 := by
      apply albert_ext <;> simp [albert_sub_fst, albert_sub_snd, albertUnit_fst, albertUnit_snd,
        diagAtom_fst, diagAtom_snd]
    rw [heq]
    exact B.carrier.sub_mem (B.carrier.sub_mem B.unit_mem hd0) hd1
  have hs01 : slotElem01 octOne ∈ B.carrier := by
    have heq : slotElem01 octOne = (2 : ℝ) • pentadF 1 - diagAtom 0 - diagAtom 1 := by
      rw [pentadF_1_eq]
      apply albert_ext
      · simp [albert_sub_fst, albert_smul_fst, slotElem01_fst, diagAtom_fst]
      · simp [albert_sub_fst, albert_smul_fst, slotElem01_fst, diagAtom_fst]
      · simp [albert_sub_fst, albert_smul_fst, slotElem01_fst, diagAtom_fst]
      · apply oct_ext <;>
          simp only [albert_sub_snd, albert_smul_snd, slotElem01_snd_0, diagAtom_snd, mkAlbert_snd,
            Matrix.cons_val_zero, oct_sub_fst, oct_sub_snd, oct_smul_fst, oct_smul_snd] <;>
          simp [octOne, octonionScalar]
      · simp [albert_sub_snd, albert_smul_snd, slotElem01_snd_1, diagAtom_snd]
      · simp [albert_sub_snd, albert_smul_snd, slotElem01_snd_2, diagAtom_snd]
    rw [heq]
    exact B.carrier.sub_mem (B.carrier.sub_mem (B.carrier.smul_mem (2 : ℝ) (hp 1)) hd0) hd1
  have hs02 : slotElem02 octOne ∈ B.carrier := by
    have hex : (4 : ℝ) • jordanMul (diagAtom 0) (jordanMul (diagAtom 2) (pentadF 2)) ∈ B.carrier :=
      B.carrier.smul_mem (4 : ℝ) (B.product_mem _ hd0 _ (B.product_mem _ hd2 _ (hp 2)))
    rw [peirce02_extract, pentadF_2_eq] at hex
    simp only [mkAlbert_snd, Matrix.cons_val_one, Matrix.cons_val_zero] at hex
    have hsm := B.carrier.smul_mem (3 : ℝ) hex
    rw [← map_smul, smul_smul, show (3 : ℝ) * (1 / 3 : ℝ) = 1 by norm_num, one_smul] at hsm
    exact hsm
  obtain ⟨F, hFset, hBeq, _⟩ := lem_five_coord B hd0 hd1 hd2 (.inl ⟨hs01, hs02⟩)
  have hI : octI ∈ F.carrier := by
    have hex : (4 : ℝ) • jordanMul (diagAtom 0) (jordanMul (diagAtom 1) (pentadF 2)) ∈ B.carrier :=
      B.carrier.smul_mem (4 : ℝ) (B.product_mem _ hd0 _ (B.product_mem _ hd1 _ (hp 2)))
    rw [peirce01_extract, pentadF_2_eq] at hex
    simp only [mkAlbert_snd, Matrix.cons_val_zero] at hex
    have hneg : slotElem01 octI ∈ B.carrier := by
      have hs := B.carrier.smul_mem (-3 : ℝ) hex
      rw [← map_smul, smul_smul, show (-3 : ℝ) * (-1 / 3 : ℝ) = 1 by norm_num, one_smul] at hs
      exact hs
    have hmem : octI ∈ (F.carrier : Set Octonion) := by rw [hFset]; exact hneg
    exact hmem
  have hJ : octJ ∈ F.carrier := by
    have hex : (4 : ℝ) • jordanMul (diagAtom 0) (jordanMul (diagAtom 1) (pentadF 3)) ∈ B.carrier :=
      B.carrier.smul_mem (4 : ℝ) (B.product_mem _ hd0 _ (B.product_mem _ hd1 _ (hp 3)))
    rw [peirce01_extract, pentadF_3_eq] at hex
    simp only [mkAlbert_snd, Matrix.cons_val_zero] at hex
    have hs : slotElem01 octJ ∈ B.carrier := by
      have hsm := B.carrier.smul_mem (-2 : ℝ) hex
      rw [← map_smul, smul_smul, show (-2 : ℝ) * (-1 / 2 : ℝ) = 1 by norm_num, one_smul] at hsm
      exact hsm
    have hm : octJ ∈ (F.carrier : Set Octonion) := by rw [hFset]; exact hs
    exact hm
  have hL : octL ∈ F.carrier := by
    have hex : (4 : ℝ) • jordanMul (diagAtom 0) (jordanMul (diagAtom 1) (pentadF 4)) ∈ B.carrier :=
      B.carrier.smul_mem (4 : ℝ) (B.product_mem _ hd0 _ (B.product_mem _ hd1 _ (hp 4)))
    rw [peirce01_extract, pentadF_4_eq] at hex
    simp only [mkAlbert_snd, Matrix.cons_val_zero] at hex
    have hs : slotElem01 octL ∈ B.carrier := by
      have hsm := B.carrier.smul_mem (-2 : ℝ) hex
      rw [← map_smul, smul_smul, show (-2 : ℝ) * (-1 / 2 : ℝ) = 1 by norm_num, one_smul] at hsm
      exact hsm
    have hm : octL ∈ (F.carrier : Set Octonion) := by rw [hFset]; exact hs
    exact hm
  have hFtop : F.carrier = ⊤ := by
    rw [eq_top_iff, ← octSubalgebra_generated_IJL_eq_top]
    apply OctSubalgebra.generated_le
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact F.one_mem
    · exact hI
    · exact hJ
    · exact hL
  change B = ⊤
  rw [hBeq]
  apply nativeJordanSubalgebra_ext
  ext x
  rw [mem_jordanSubalgebraH3_iff, hFtop]
  simp [mem_top_nativeJordanSubalgebra]

private def cornerSubmodule (f : Albert) (B : NativeJordanSubalgebra) : Submodule ℝ Albert where
  carrier := {y ∈ B.carrier | jordanMul f y = y}
  add_mem' := fun {a b} ⟨haB, haf⟩ ⟨hbB, hbf⟩ =>
    ⟨B.carrier.add_mem haB hbB, by rw [jordanMul_add_right, haf, hbf]⟩
  zero_mem' := ⟨B.carrier.zero_mem, jordanMul_zero_right f⟩
  smul_mem' := fun r {a} ⟨haB, haf⟩ =>
    ⟨B.carrier.smul_mem r haB, by rw [jordanMul_smul_right, haf]⟩

private theorem mem_H3O (y : Albert) : y ∈ (H3Subalgebra .O).carrier :=
  H3Subalgebra_O_eq_top.symm ▸ mem_top_nativeJordanSubalgebra y

private theorem pentadDrop_0_or_1_finrank (k : Fin 5) (hk : k = 0 ∨ k = 1) :
    Module.finrank ℝ (generatedSubalgebra (Set.range (pentadDrop k))).carrier = 15 := by
  have : Module.Finite ℝ Octonion :=
    inferInstanceAs (FiniteDimensional ℝ (Quaternion ℝ × Quaternion ℝ))
  let q := diagAtom 2
  have hq : IsAtom q := diagAtom_isAtom 2
  have hqK : q ∈ (H3Subalgebra .O).carrier := diagAtom_mem_H3Subalgebra .O 2
  let p := pentadF 2
  have hp : IsAtom p := pentadF_isAtom 2
  have hpK : p ∈ (H3Subalgebra .O).carrier := mem_H3O p
  have hp_off : p ∉ (lineSubalgebra q hq).carrier := by
    intro hmem
    rw [mem_lineSubalgebra_iff] at hmem
    have h1 := congrArg (fun a : Albert => a.2 1) hmem
    dsimp only [p] at h1
    rw [show q = diagAtom 2 from rfl, jordanMul_diagAtom2, pentadF_2_eq,
      albert_smul_snd, diagAtom_snd, smul_zero] at h1
    have hc := congrArg (fun u : Octonion => (6 : ℝ) • u) h1
    simp only [mkAlbert_snd, Matrix.cons_val_one, Matrix.cons_val_zero, smul_smul] at hc
    norm_num at hc
    have hre := congrArg (fun u : Octonion => u.1.re) hc
    simp [octOne, octonionScalar] at hre
  let s : Fin 3 → Albert := if k = 0 then ![pentadF 1, pentadF 3, pentadF 4]
    else ![pentadF 0, pentadF 3, pentadF 4]
  have hs_inj : Function.Injective s := by
    intro i j hij
    rcases hk with rfl | rfl <;> fin_cases i <;> fin_cases j <;> try rfl
    all_goals
      simp only [s, Fin.isValue, Fin.reduceEq, ↓reduceIte] at hij
      dsimp at hij
    · have h0 := congrArg (fun a : Albert => (a.2 0).1.re) hij
      rw [pentadF_1_eq, pentadF_3_eq] at h0
      simp only [mkAlbert_snd, Matrix.cons_val_zero, oct_smul_fst] at h0
      simp [octonionScalar, octJ] at h0
    · have h0 := congrArg (fun a : Albert => (a.2 0).1.re) hij
      rw [pentadF_1_eq, pentadF_4_eq] at h0
      simp only [mkAlbert_snd, Matrix.cons_val_zero, oct_smul_fst] at h0
      simp [octonionScalar, octL] at h0
    · have h0 := congrArg (fun a : Albert => (a.2 0).1.re) hij
      rw [pentadF_3_eq, pentadF_1_eq] at h0
      simp only [mkAlbert_snd, Matrix.cons_val_zero, oct_smul_fst] at h0
      simp [octonionScalar, octJ] at h0
    · have h0 := congrArg (fun a : Albert => (a.2 0).1.imJ) hij
      rw [pentadF_3_eq, pentadF_4_eq] at h0
      simp only [mkAlbert_snd, Matrix.cons_val_zero, oct_smul_fst] at h0
      simp [octJ, octL] at h0
    · have h0 := congrArg (fun a : Albert => (a.2 0).1.re) hij
      rw [pentadF_4_eq, pentadF_1_eq] at h0
      simp only [mkAlbert_snd, Matrix.cons_val_zero, oct_smul_fst] at h0
      simp [octonionScalar, octL] at h0
    · have h0 := congrArg (fun a : Albert => (a.2 0).1.imJ) hij
      rw [pentadF_4_eq, pentadF_3_eq] at h0
      simp only [mkAlbert_snd, Matrix.cons_val_zero, oct_smul_fst] at h0
      simp [octJ, octL] at h0
      norm_num at h0
    · have h0 := congrArg (fun a : Albert => a.1 0) hij
      rw [pentadF_0_eq, pentadF_3_eq] at h0
      simp [diagAtom_fst] at h0
    · have h0 := congrArg (fun a : Albert => a.1 0) hij
      rw [pentadF_0_eq, pentadF_4_eq] at h0
      simp [diagAtom_fst] at h0
    · have h0 := congrArg (fun a : Albert => a.1 0) hij
      rw [pentadF_3_eq, pentadF_0_eq] at h0
      simp [diagAtom_fst] at h0
    · have h0 := congrArg (fun a : Albert => (a.2 0).1.imJ) hij
      rw [pentadF_3_eq, pentadF_4_eq] at h0
      simp only [mkAlbert_snd, Matrix.cons_val_zero, oct_smul_fst] at h0
      simp [octJ, octL] at h0
    · have h0 := congrArg (fun a : Albert => a.1 0) hij
      rw [pentadF_4_eq, pentadF_0_eq] at h0
      simp [diagAtom_fst] at h0
    · have h0 := congrArg (fun a : Albert => (a.2 0).1.imJ) hij
      rw [pentadF_4_eq, pentadF_3_eq] at h0
      simp only [mkAlbert_snd, Matrix.cons_val_zero, oct_smul_fst] at h0
      simp [octJ, octL] at h0
      norm_num at h0
  have hs_atom : ∀ m, IsAtom (s m) := fun m => by
    rcases hk with rfl | rfl <;> fin_cases m <;> dsimp [s] <;> exact pentadF_isAtom _
  have hs_mem : ∀ m, s m ∈ (H3Subalgebra .O).carrier := fun m => mem_H3O _
  have hs_line : ∀ m, jordanMul q (s m) = 0 := fun m => by
    rcases hk with rfl | rfl <;> fin_cases m <;> dsimp [s] <;>
      simp only [q, jordanMul_diagAtom2]
    · rw [pentadF_1_eq]; apply albert_ext <;> simp [albert_zero_fst, albert_zero_snd]
    · rw [pentadF_3_eq]; apply albert_ext <;> simp [albert_zero_fst, albert_zero_snd]
    · rw [pentadF_4_eq]; apply albert_ext <;> simp [albert_zero_fst, albert_zero_snd]
    · rw [pentadF_0_eq]; apply albert_ext <;> simp [diagAtom_fst, diagAtom_snd, albert_zero_fst, albert_zero_snd]
    · rw [pentadF_3_eq]; apply albert_ext <;> simp [albert_zero_fst, albert_zero_snd]
    · rw [pentadF_4_eq]; apply albert_ext <;> simp [albert_zero_fst, albert_zero_snd]
  have hcomp_p : quadraticMap (albertUnit - q) p =
      mkAlbert ![1 / 3, 1 / 3, 0] ![(-1 / 3 : ℝ) • octI, 0, 0] := by
    have halg : albertUnit - diagAtom 2 = swap02AlbertAuto.linearEquiv (albertUnit - diagAtom 0) := by
      rw [map_sub, swap02AlbertAuto.preserves_unit, swap02AlbertAuto_diagAtom]; rfl
    have hp_swap : swap02AlbertAuto.linearEquiv
        (quadraticMap (albertUnit - diagAtom 0) (swap02AlbertAuto.linearEquiv p)) =
        quadraticMap (albertUnit - diagAtom 2) p := by
      have hinv : swap02AlbertAuto.linearEquiv (swap02AlbertAuto.linearEquiv p) = p := by
        rw [swap02AlbertAuto_apply, swap02AlbertAuto_apply]
        apply albert_ext <;> simp [octonionConj_conj]
      calc
        swap02AlbertAuto.linearEquiv
            (quadraticMap (albertUnit - diagAtom 0) (swap02AlbertAuto.linearEquiv p))
          = quadraticMap (swap02AlbertAuto.linearEquiv (albertUnit - diagAtom 0))
              (swap02AlbertAuto.linearEquiv (swap02AlbertAuto.linearEquiv p)) := by
            simp only [quadraticMap, two_nsmul, map_sub, map_add, swap02AlbertAuto.preserves_product]
        _ = quadraticMap (albertUnit - diagAtom 2) p := by rw [← halg, hinv]
    have hp2_swap : swap02AlbertAuto.linearEquiv (pentadF 2) = pentadF 2 := by
      rw [pentadF_2_eq, swap02AlbertAuto_apply]
      apply albert_ext <;> simp [octonionConj_smul, octonionConj_I, octonionConj_one]
      · rw [← neg_smul]; congr 1; norm_num
      · rw [← neg_smul]; congr 1; norm_num
    dsimp only [p] at hp_swap ⊢
    rw [← hp_swap, hp2_swap, pentadF_2_eq, quadraticMap_compl_diagAtom0_eq, swap02AlbertAuto_apply]
    apply albert_ext <;> simp [octonionConj_smul, octonionConj_I, octonionConj_zero]
    rw [← neg_smul]; congr 1; norm_num
  have htr_comp : albertTrace (quadraticMap (albertUnit - q) p) = 2 / 3 := by
    rw [hcomp_p]; simp [albertTrace, Fin.sum_univ_three]; norm_num
  have hr_eq : (albertTrace (quadraticMap (albertUnit - q) p))⁻¹ • quadraticMap (albertUnit - q) p =
      mkAlbert ![1 / 2, 1 / 2, 0] ![(-1 / 2 : ℝ) • octI, 0, 0] := by
    rw [htr_comp, hcomp_p]
    apply albert_ext
    · simp [albert_smul_fst]; norm_num
    · simp [albert_smul_fst]; norm_num
    · simp [albert_smul_fst]
    · simp [albert_smul_snd, smul_smul]
    · simp [albert_smul_snd]
    · simp [albert_smul_snd]
  have hfr_eq : (albertUnit - q) -
      (albertTrace (quadraticMap (albertUnit - q) p))⁻¹ • quadraticMap (albertUnit - q) p =
      mkAlbert ![1 / 2, 1 / 2, 0] ![(1 / 2 : ℝ) • octI, 0, 0] := by
    rw [hr_eq]
    apply albert_ext
    · simp [q, albert_sub_fst, albertUnit_fst, diagAtom_fst]; norm_num
    · simp [q, albert_sub_fst, albertUnit_fst, diagAtom_fst]; norm_num
    · simp [q, albert_sub_fst, albertUnit_fst, diagAtom_fst]
    · simp [q, albert_sub_snd, albertUnit_snd, diagAtom_snd]; module
    · simp [q, albert_sub_snd, albertUnit_snd, diagAtom_snd]
    · simp [q, albert_sub_snd, albertUnit_snd, diagAtom_snd]
  have hr_ne : ∀ m, s m ≠ (albertTrace (quadraticMap (albertUnit - q) p))⁻¹ • quadraticMap (albertUnit - q) p ∧
      s m ≠ (albertUnit - q) - (albertTrace (quadraticMap (albertUnit - q) p))⁻¹ • quadraticMap (albertUnit - q) p := by
    intro m
    rw [hfr_eq, hr_eq]
    constructor <;> intro heq
    · have h0 := congrArg (fun a : Albert => a.2 0) heq
      rcases hk with rfl | rfl <;> fin_cases m <;>
        (simp only [s, Fin.isValue, Fin.reduceEq, ↓reduceIte] at h0; dsimp at h0)
      all_goals
        first
        | rw [pentadF_0_eq] at h0
        | rw [pentadF_1_eq] at h0
        | rw [pentadF_3_eq] at h0
        | rw [pentadF_4_eq] at h0
        have him := congrArg (fun u : Octonion => u.1.imI) h0
        simp only [mkAlbert_snd, Matrix.cons_val_zero, oct_smul_fst] at him
        simp [octonionScalar, octI, octJ, octL, diagAtom_snd] at him
        try linarith
    · have h0 := congrArg (fun a : Albert => a.2 0) heq
      rcases hk with rfl | rfl <;> fin_cases m <;>
        (simp only [s, Fin.isValue, Fin.reduceEq, ↓reduceIte] at h0; dsimp at h0)
      all_goals
        first
        | rw [pentadF_0_eq] at h0
        | rw [pentadF_1_eq] at h0
        | rw [pentadF_3_eq] at h0
        | rw [pentadF_4_eq] at h0
        have him := congrArg (fun u : Octonion => u.1.imI) h0
        simp only [mkAlbert_snd, Matrix.cons_val_zero, oct_smul_fst] at him
        simp [octonionScalar, octI, octJ, octL, diagAtom_snd] at him
        try linarith
  obtain ⟨α, _, _, x, _, _, _, _, hαq, _, _, _, F, _, hFx, hFmin, hgen_iff⟩ :=
    lem_five_line .O (by omega : 2 ≤ 3) q hq hqK p hp hpK hp_off s hs_inj hs_atom hs_mem hs_line hr_ne
  let B := generatedSubalgebra (Set.range (pentadDrop k))
  have hrange_eq : insert p (Set.range s) = Set.range (pentadDrop k) := by
    ext z
    rcases hk with rfl | rfl
    · simp only [Set.mem_insert_iff, Set.mem_range]
      constructor
      · rintro (rfl | ⟨m, rfl⟩)
        · exact ⟨1, rfl⟩
        · fin_cases m
          · exact ⟨0, rfl⟩
          · exact ⟨2, rfl⟩
          · exact ⟨3, rfl⟩
      · rintro ⟨j, rfl⟩
        fin_cases j
        · exact Or.inr ⟨0, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨1, rfl⟩
        · exact Or.inr ⟨2, rfl⟩
    · simp only [Set.mem_insert_iff, Set.mem_range]
      constructor
      · rintro (rfl | ⟨m, rfl⟩)
        · exact ⟨1, rfl⟩
        · fin_cases m
          · exact ⟨0, rfl⟩
          · exact ⟨2, rfl⟩
          · exact ⟨3, rfl⟩
      · rintro ⟨j, rfl⟩
        fin_cases j
        · exact Or.inr ⟨0, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨1, rfl⟩
        · exact Or.inr ⟨2, rfl⟩
  have hB_eq : ∀ y : Albert, y ∈ B.carrier ↔
      (α.toLinearEquiv ⟨y, mem_H3O y⟩).1 ∈ (jordanSubalgebraH3 F).carrier := by
    intro y
    change y ∈ (generatedSubalgebra (Set.range (pentadDrop k))).carrier ↔ _
    rw [← hrange_eq, hgen_iff y]
    constructor
    · rintro ⟨yK, rfl, hyK⟩; exact hyK
    · intro hy; exact ⟨⟨y, mem_H3O y⟩, rfl, hy⟩
  let eqvBF : B.carrier ≃ₗ[ℝ] (jordanSubalgebraH3 F).carrier :=
    { toFun := fun y => ⟨(α.toLinearEquiv ⟨y.1, mem_H3O y.1⟩).1,
        (hB_eq y.1).mp y.2⟩
      invFun := fun z =>
        let y0 := α.toLinearEquiv.symm ⟨z.1, mem_H3O z.1⟩
        ⟨y0.1, (hB_eq y0.1).mpr (by
          have hsub : (⟨y0.1, mem_H3O y0.1⟩ : (H3Subalgebra .O).carrier) = y0 := rfl
          rw [hsub, LinearEquiv.apply_symm_apply]
          exact z.2)⟩
      left_inv := fun y => Subtype.ext (by
        change (α.toLinearEquiv.symm ⟨(α.toLinearEquiv ⟨y.1, mem_H3O y.1⟩).1, mem_H3O _⟩).1 = y.1
        have hsub : (⟨(α.toLinearEquiv ⟨y.1, mem_H3O y.1⟩).1, mem_H3O _⟩ :
            (H3Subalgebra .O).carrier) = α.toLinearEquiv ⟨y.1, mem_H3O y.1⟩ := rfl
        rw [hsub, LinearEquiv.symm_apply_apply])
      right_inv := fun z => Subtype.ext (by
        change (α.toLinearEquiv ⟨(α.toLinearEquiv.symm ⟨z.1, mem_H3O z.1⟩).1, mem_H3O _⟩).1 = z.1
        have hsub : (⟨(α.toLinearEquiv.symm ⟨z.1, mem_H3O z.1⟩).1, mem_H3O _⟩ :
            (H3Subalgebra .O).carrier) = α.toLinearEquiv.symm ⟨z.1, mem_H3O z.1⟩ := rfl
        rw [hsub, LinearEquiv.apply_symm_apply])
      map_add' := fun a b => Subtype.ext (by
        have hsub : (⟨(a + b).1, mem_H3O (a + b).1⟩ : (H3Subalgebra .O).carrier) =
            ⟨a.1, mem_H3O a.1⟩ + ⟨b.1, mem_H3O b.1⟩ := rfl
        change (α.toLinearEquiv ⟨(a + b).1, mem_H3O (a + b).1⟩).1 =
          (α.toLinearEquiv ⟨a.1, mem_H3O a.1⟩).1 + (α.toLinearEquiv ⟨b.1, mem_H3O b.1⟩).1
        rw [hsub, map_add, Submodule.coe_add])
      map_smul' := fun c a => Subtype.ext (by
        have hsub : (⟨(c • a).1, mem_H3O (c • a).1⟩ : (H3Subalgebra .O).carrier) =
            c • ⟨a.1, mem_H3O a.1⟩ := rfl
        change (α.toLinearEquiv ⟨(c • a).1, mem_H3O (c • a).1⟩).1 =
          c • (α.toLinearEquiv ⟨a.1, mem_H3O a.1⟩).1
        rw [hsub, map_smul, Submodule.coe_smul]) }
  have hfinB : Module.finrank ℝ B.carrier = 3 + 3 * Module.finrank ℝ F.carrier := by
    rw [eqvBF.finrank_eq, finrank_jordanSubalgebraH3]
  obtain ⟨φ, hφ, hx1, hx2⟩ := exists_quatEmbedding_containing_pair (x 1) (x 2)
  let Fφ : OctSubalgebra :=
    { carrier := LinearMap.range φ
      one_mem := ⟨1, by rw [hφ.map_one]; rfl⟩
      mul_mem := by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact ⟨a * b, hφ.map_mul a b⟩
      conj_mem := by rintro _ ⟨a, rfl⟩; exact ⟨star a, hφ.map_star a⟩ }
  have hF_le : F.carrier ≤ Fφ.carrier := hFmin Fφ fun m hm => by
    fin_cases m
    · exact absurd rfl hm
    · exact hx1
    · exact hx2
  have hF_fin_in : Module.finrank ℝ F.carrier ∈ ({1, 2, 4} : Set ℕ) :=
    octSubalgebra_le_quatEmbedding_finrank F φ hφ hF_le
  -- Corner lower bound: dim(corner f B) ≥ 5
  let f := albertUnit - q
  have hsB : ∀ m : Fin 3, s m ∈ B.carrier := fun m =>
    subset_generatedSubalgebra _ (by rw [← hrange_eq]; exact Or.inr ⟨m, rfl⟩)
  have hpB : p ∈ B.carrier :=
    subset_generatedSubalgebra _ (by rw [← hrange_eq]; exact Or.inl rfl)
  have hfB : f ∈ B.carrier := by
    obtain ⟨_, hsup⟩ := eq_fiv_support q (s 0) (s 1) hq (hs_atom 0) (hs_atom 1)
      (hs_line 0) (hs_line 1) (fun h => by have := hs_inj h; cases this)
    dsimp only [f]
    rw [hsup]
    exact B.carrier.smul_mem _ (B.carrier.sub_mem (B.carrier.add_mem (hsB 0) (hsB 1))
      (B.carrier.smul_mem _ (B.product_mem _ (hsB 0) _ (hsB 1))))
  have hqB : q ∈ B.carrier := by
    have hqe : q = albertUnit - f := by dsimp only [f]; abel
    rw [hqe]; exact B.carrier.sub_mem B.unit_mem hfB
  have hrB : (albertTrace (quadraticMap f p))⁻¹ • quadraticMap f p ∈ B.carrier :=
    B.carrier.smul_mem _ (peirce_components_mem_subalgebra B hfB hpB).1
  let v : Fin 5 → Albert :=
    fun m => match m with
    | 0 => f
    | 1 => (2 : ℝ) • ((albertTrace (quadraticMap f p))⁻¹ • quadraticMap f p) - f
    | 2 => (2 : ℝ) • s 0 - f
    | 3 => (2 : ℝ) • s 1 - f
    | 4 => (2 : ℝ) • s 2 - f
  have hv_mem : ∀ m : Fin 5, v m ∈ cornerSubmodule f B := fun m => by
    refine ⟨?_, ?_⟩
    · fin_cases m
      · exact hfB
      · exact B.carrier.sub_mem (B.carrier.smul_mem (2 : ℝ) hrB) hfB
      · exact B.carrier.sub_mem (B.carrier.smul_mem (2 : ℝ) (hsB 0)) hfB
      · exact B.carrier.sub_mem (B.carrier.smul_mem (2 : ℝ) (hsB 1)) hfB
      · exact B.carrier.sub_mem (B.carrier.smul_mem (2 : ℝ) (hsB 2)) hfB
    · have hff : jordanMul f f = f := by
        dsimp only [f]
        simp only [jordanMul_sub_left, jordanMul_sub_right, jordanMul_albertUnit_left,
          jordanMul_albertUnit_right, hq.1]
        abel
      have hfz : ∀ y : Albert, jordanMul q y = 0 → jordanMul f y = y := fun y hy => by
        dsimp only [f]
        rw [jordanMul_sub_left, jordanMul_albertUnit_left, hy, sub_zero]
      fin_cases m
      · exact hff
      · rw [jordanMul_sub_right, jordanMul_smul_right, jordanMul_smul_right, hff,
          hfz _ (by
            dsimp only [f]
            rw [hcomp_p]
            apply albert_ext <;> simp [q, jordanMul_diagAtom2, albert_zero_fst, albert_zero_snd])]
      · rw [jordanMul_sub_right, jordanMul_smul_right, hff, hfz _ (hs_line 0)]
      · rw [jordanMul_sub_right, jordanMul_smul_right, hff, hfz _ (hs_line 1)]
      · rw [jordanMul_sub_right, jordanMul_smul_right, hff, hfz _ (hs_line 2)]
  have hv_indep : LinearIndependent ℝ (fun m : Fin 5 => (⟨v m, hv_mem m⟩ : cornerSubmodule f B)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc m
    have hc' : ∑ i : Fin 5, c i • v i = 0 := congrArg Subtype.val hc
    have hsum_val : (∑ i : Fin 5, c i • v i) =
        c 0 • f + c 1 • v 1 + c 2 • v 2 + c 3 • v 3 + c 4 • v 4 := by
      rw [Fin.sum_univ_five]
    rw [hsum_val] at hc'
    have hdiag_f : f = diagAtom 0 + diagAtom 1 := by
      apply albert_ext <;> simp [f, q, albert_sub_fst, albert_sub_snd, albert_add_fst,
        albert_add_snd, albertUnit_fst, albertUnit_snd, diagAtom_fst, diagAtom_snd]
    have hv1 : v 1 = slotElem01 (-octI) := by
      dsimp only [v]
      rw [hr_eq, hdiag_f]
      apply albert_ext
      · simp [albert_sub_fst, albert_smul_fst, albert_add_fst, diagAtom_fst, albert_neg_fst,
          slotElem01_fst]
      · simp [albert_sub_fst, albert_smul_fst, albert_add_fst, diagAtom_fst, albert_neg_fst,
          slotElem01_fst]
      · simp [albert_sub_fst, albert_smul_fst, albert_add_fst, diagAtom_fst, albert_neg_fst,
          slotElem01_fst]
      · simp only [albert_sub_snd, albert_smul_snd, albert_add_snd, diagAtom_snd, slotElem01_snd_0,
          mkAlbert_snd, Matrix.cons_val_zero, smul_smul, add_zero, sub_zero]
        rw [show (2 : ℝ) * (-1 / 2 : ℝ) = -1 by norm_num, neg_one_smul]
      · simp [albert_sub_snd, albert_smul_snd, albert_add_snd, diagAtom_snd, map_neg,
          albert_neg_snd, slotElem01_snd_1]
      · simp [albert_sub_snd, albert_smul_snd, albert_add_snd, diagAtom_snd, map_neg,
          albert_neg_snd, slotElem01_snd_2]
    have hv3 : v 3 = slotElem01 (-octJ) := by
      dsimp only [v]
      have hs1 : s 1 = pentadF 3 := by rcases hk with rfl | rfl <;> rfl
      rw [hs1, pentadF_3_eq, hdiag_f]
      apply albert_ext
      · simp [albert_sub_fst, albert_smul_fst, albert_add_fst, diagAtom_fst, albert_neg_fst,
          slotElem01_fst]
      · simp [albert_sub_fst, albert_smul_fst, albert_add_fst, diagAtom_fst, albert_neg_fst,
          slotElem01_fst]
      · simp [albert_sub_fst, albert_smul_fst, albert_add_fst, diagAtom_fst, albert_neg_fst,
          slotElem01_fst]
      · simp only [albert_sub_snd, albert_smul_snd, albert_add_snd, diagAtom_snd, slotElem01_snd_0,
          mkAlbert_snd, Matrix.cons_val_zero, smul_smul, add_zero, sub_zero]
        rw [show (2 : ℝ) * (-1 / 2 : ℝ) = -1 by norm_num, neg_one_smul]
      · simp [albert_sub_snd, albert_smul_snd, albert_add_snd, diagAtom_snd, map_neg,
          albert_neg_snd, slotElem01_snd_1]
      · simp [albert_sub_snd, albert_smul_snd, albert_add_snd, diagAtom_snd, map_neg,
          albert_neg_snd, slotElem01_snd_2]
    have hv4 : v 4 = slotElem01 (-octL) := by
      dsimp only [v]
      have hs2 : s 2 = pentadF 4 := by rcases hk with rfl | rfl <;> rfl
      rw [hs2, pentadF_4_eq, hdiag_f]
      apply albert_ext
      · simp [albert_sub_fst, albert_smul_fst, albert_add_fst, diagAtom_fst, albert_neg_fst,
          slotElem01_fst]
      · simp [albert_sub_fst, albert_smul_fst, albert_add_fst, diagAtom_fst, albert_neg_fst,
          slotElem01_fst]
      · simp [albert_sub_fst, albert_smul_fst, albert_add_fst, diagAtom_fst, albert_neg_fst,
          slotElem01_fst]
      · simp only [albert_sub_snd, albert_smul_snd, albert_add_snd, diagAtom_snd, slotElem01_snd_0,
          mkAlbert_snd, Matrix.cons_val_zero, smul_smul, add_zero, sub_zero]
        rw [show (2 : ℝ) * (-1 / 2 : ℝ) = -1 by norm_num, neg_one_smul]
      · simp [albert_sub_snd, albert_smul_snd, albert_add_snd, diagAtom_snd, map_neg,
          albert_neg_snd, slotElem01_snd_1]
      · simp [albert_sub_snd, albert_smul_snd, albert_add_snd, diagAtom_snd, map_neg,
          albert_neg_snd, slotElem01_snd_2]
    have hc_tr : c 0 = 0 := by
      have ht := congrArg albertTrace hc'
      have htf : albertTrace f = 2 := by
        rw [hdiag_f]; simp [albertTrace, Fin.sum_univ_three, albert_add_fst, diagAtom_fst]; norm_num
      have htv1 : albertTrace (v 1) = 0 := by
        rw [hv1, map_neg]; simp [albertTrace, albert_neg_fst, slotElem01_fst]
      have htv3 : albertTrace (v 3) = 0 := by
        rw [hv3, map_neg]; simp [albertTrace, albert_neg_fst, slotElem01_fst]
      have htv4 : albertTrace (v 4) = 0 := by
        rw [hv4, map_neg]; simp [albertTrace, albert_neg_fst, slotElem01_fst]
      have htv2 : albertTrace (v 2) = 0 := by
        dsimp only [v]
        have hst : albertTrace (s 0) = 1 := (hs_atom 0).2
        rw [albertTrace_sub, albertTrace_smul, hst, htf]; norm_num
      simp only [albertTrace_add, albertTrace_smul, htf, htv1, htv2, htv3, htv4,
        albertTrace_zero_local, mul_zero, add_zero] at ht
      linarith
    rw [hc_tr, zero_smul, zero_add] at hc'
    have hci : c 1 = 0 := by
      have hi := congrArg (fun a : Albert => (a.2 0).1.imI) hc'
      have hv2i : ((v 2).2 0).1.imI = 0 := by
        rcases hk with rfl | rfl
        · have hs0 : s 0 = pentadF 1 := rfl
          dsimp only [v]; rw [hs0, pentadF_1_eq, hdiag_f]
          simp only [albert_sub_snd, albert_smul_snd, albert_add_snd, diagAtom_snd, mkAlbert_snd,
            Matrix.cons_val_zero, oct_sub_fst, oct_smul_fst, oct_add_fst]
          simp [octonionScalar]
        · have hs0 : s 0 = pentadF 0 := rfl
          dsimp only [v]; rw [hs0, pentadF_0_eq, hdiag_f]
          simp [albert_sub_snd, albert_smul_snd, albert_add_snd, diagAtom_snd]
      rw [hv1, hv3, hv4] at hi
      simp only [albert_add_snd, albert_smul_snd, albert_zero_snd, oct_zero_fst,
        oct_add_fst, oct_smul_fst, slotElem01_snd_0,
        oct_neg_fst, q_add_imI, q_smul_imI, q_neg_imI, hv2i] at hi
      simp [octI, octJ, octL] at hi
      linarith
    have hcj : c 3 = 0 := by
      have hj := congrArg (fun a : Albert => (a.2 0).1.imJ) hc'
      have hv2j : ((v 2).2 0).1.imJ = 0 := by
        rcases hk with rfl | rfl
        · have hs0 : s 0 = pentadF 1 := rfl
          dsimp only [v]; rw [hs0, pentadF_1_eq, hdiag_f]
          simp only [albert_sub_snd, albert_smul_snd, albert_add_snd, diagAtom_snd, mkAlbert_snd,
            Matrix.cons_val_zero, oct_sub_fst, oct_smul_fst, oct_add_fst]
          simp [octonionScalar]
        · have hs0 : s 0 = pentadF 0 := rfl
          dsimp only [v]; rw [hs0, pentadF_0_eq, hdiag_f]
          simp [albert_sub_snd, albert_smul_snd, albert_add_snd, diagAtom_snd]
      rw [hv1, hv3, hv4] at hj
      simp only [albert_add_snd, albert_smul_snd, albert_zero_snd, oct_zero_fst,
        oct_add_fst, oct_smul_fst, slotElem01_snd_0,
        oct_neg_fst, q_add_imJ, q_smul_imJ, q_neg_imJ, hv2j] at hj
      simp [octI, octJ, octL] at hj
      linarith
    have hcl : c 4 = 0 := by
      have hl := congrArg (fun a : Albert => (a.2 0).2.re) hc'
      have hv2l : ((v 2).2 0).2.re = 0 := by
        rcases hk with rfl | rfl
        · have hs0 : s 0 = pentadF 1 := rfl
          dsimp only [v]; rw [hs0, pentadF_1_eq, hdiag_f]
          simp only [albert_sub_snd, albert_smul_snd, albert_add_snd, diagAtom_snd, mkAlbert_snd,
            Matrix.cons_val_zero, oct_sub_snd, oct_smul_snd, oct_add_snd]
          simp [octonionScalar]
        · have hs0 : s 0 = pentadF 0 := rfl
          dsimp only [v]; rw [hs0, pentadF_0_eq, hdiag_f]
          simp [albert_sub_snd, albert_smul_snd, albert_add_snd, diagAtom_snd]
      rw [hv1, hv3, hv4] at hl
      simp only [albert_add_snd, albert_smul_snd, albert_zero_snd, oct_zero_snd,
        oct_add_snd, oct_smul_snd, slotElem01_snd_0,
        oct_neg_snd, q_add_re, q_smul_re, q_neg_re, hv2l] at hl
      simp [octI, octJ, octL] at hl
      linarith
    have hc2 : c 2 = 0 := by
      rw [hci, hcj, hcl, zero_smul, zero_smul, zero_smul, zero_add, add_zero, add_zero] at hc'
      rcases hk with rfl | rfl
      · have hr := congrArg (fun a : Albert => (a.2 0).1.re) hc'
        have hs0 : s 0 = pentadF 1 := rfl
        dsimp only [v] at hr; rw [hs0, pentadF_1_eq, hdiag_f] at hr
        simp only [albert_smul_snd, albert_sub_snd, albert_add_snd, albert_zero_snd, oct_zero_fst,
          oct_smul_fst, oct_sub_fst, oct_add_fst, mkAlbert_snd, Matrix.cons_val_zero, diagAtom_snd,
          q_smul_re] at hr
        simp [octonionScalar] at hr
        linarith
      · have hd := congrArg (fun a : Albert => a.1 0) hc'
        have hs0 : s 0 = pentadF 0 := rfl
        dsimp only [v] at hd; rw [hs0, pentadF_0_eq, hdiag_f] at hd
        simp [albert_smul_fst, albert_sub_fst, albert_add_fst, albert_zero_fst, diagAtom_fst] at hd
        norm_num at hd
        exact hd
    fin_cases m <;> assumption
  have h5_le : 5 ≤ Module.finrank ℝ (cornerSubmodule f B) := by
    have : Module.Finite ℝ Albert :=
      inferInstanceAs (FiniteDimensional ℝ ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
    have hle := Submodule.finrank_le (Submodule.span ℝ
      (Set.range (fun m : Fin 5 => (⟨v m, hv_mem m⟩ : cornerSubmodule f B))))
    rw [finrank_span_eq_card hv_indep, Fintype.card_fin] at hle
    exact hle
  -- Corner upper bound via α: cornerSubmodule (diagAtom 0 + diagAtom 2) (jordanSubalgebraH3 F) ≃ ℝ × ℝ × F.carrier
  let f' := diagAtom 0 + diagAtom 2
  have hf'_eq : (α.toLinearEquiv ⟨f, mem_H3O f⟩).1 = f' := by
    have hf1 : (⟨f, mem_H3O f⟩ : (H3Subalgebra .O).carrier) =
        ⟨albertUnit, (H3Subalgebra .O).unit_mem⟩ - ⟨q, hqK⟩ := rfl
    rw [hf1, map_sub, Submodule.coe_sub, α.map_unit, hαq]
    apply albert_ext <;> simp [f', albert_sub_fst, albert_sub_snd, albert_add_fst, albert_add_snd,
      albertUnit_fst, albertUnit_snd, diagAtom_fst, diagAtom_snd]
  let eqvCorner : cornerSubmodule f B ≃ₗ[ℝ] cornerSubmodule f' (jordanSubalgebraH3 F) :=
    { toFun := fun y => ⟨(eqvBF ⟨y.1, y.2.1⟩).1, (eqvBF ⟨y.1, y.2.1⟩).2, by
        change jordanMul f' (α.toLinearEquiv ⟨y.1, mem_H3O y.1⟩).1 =
          (α.toLinearEquiv ⟨y.1, mem_H3O y.1⟩).1
        have hmul := congrArg Subtype.val
          (α.map_jordan ⟨f, mem_H3O f⟩ ⟨y.1, mem_H3O y.1⟩)
        have hfy := congrArg (fun z : (H3Subalgebra .O).carrier => (α.toLinearEquiv z).1)
          (Subtype.ext y.2.2 : (⟨jordanMul f y.1, mem_H3O _⟩ : (H3Subalgebra .O).carrier) =
            ⟨y.1, mem_H3O y.1⟩)
        rw [hf'_eq] at hmul
        exact hmul.symm.trans hfy⟩
      invFun := fun z => ⟨(eqvBF.symm ⟨z.1, z.2.1⟩).1, (eqvBF.symm ⟨z.1, z.2.1⟩).2, by
        let y0 := eqvBF.symm ⟨z.1, z.2.1⟩
        have hy0_map : (α.toLinearEquiv ⟨y0.1, mem_H3O y0.1⟩).1 = z.1 :=
          congrArg Subtype.val (eqvBF.apply_symm_apply ⟨z.1, z.2.1⟩)
        have hmul := congrArg Subtype.val
          (α.map_jordan ⟨f, mem_H3O f⟩ ⟨y0.1, mem_H3O y0.1⟩)
        have hEq : α.toLinearEquiv ⟨jordanMul f y0.1, mem_H3O (jordanMul f y0.1)⟩ =
            α.toLinearEquiv ⟨y0.1, mem_H3O y0.1⟩ := by
          apply Subtype.ext
          have hmul' : (α.toLinearEquiv ⟨jordanMul f y0.1, mem_H3O (jordanMul f y0.1)⟩).1 =
              jordanMul f' (α.toLinearEquiv ⟨y0.1, mem_H3O y0.1⟩).1 := by
            rw [← hf'_eq]; exact hmul
          rw [hmul', hy0_map, z.2.2]
        exact congrArg (fun w : (H3Subalgebra .O).carrier => w.1) (α.toLinearEquiv.injective hEq)⟩
      left_inv := fun y => Subtype.ext (by
        change (eqvBF.symm ⟨(eqvBF ⟨y.1, y.2.1⟩).1, (eqvBF ⟨y.1, y.2.1⟩).2⟩).1 = y.1
        have hsub : (⟨(eqvBF ⟨y.1, y.2.1⟩).1, (eqvBF ⟨y.1, y.2.1⟩).2⟩ :
            (jordanSubalgebraH3 F).carrier) = eqvBF ⟨y.1, y.2.1⟩ := rfl
        rw [hsub, LinearEquiv.symm_apply_apply])
      right_inv := fun z => Subtype.ext (by
        change (eqvBF ⟨(eqvBF.symm ⟨z.1, z.2.1⟩).1, (eqvBF.symm ⟨z.1, z.2.1⟩).2⟩).1 = z.1
        have hsub : (⟨(eqvBF.symm ⟨z.1, z.2.1⟩).1, (eqvBF.symm ⟨z.1, z.2.1⟩).2⟩ :
            B.carrier) = eqvBF.symm ⟨z.1, z.2.1⟩ := rfl
        rw [hsub, LinearEquiv.apply_symm_apply])
      map_add' := fun a b => Subtype.ext (by
        have ha : (⟨(a + b).1, (a + b).2.1⟩ : B.carrier) = ⟨a.1, a.2.1⟩ + ⟨b.1, b.2.1⟩ := rfl
        change (eqvBF ⟨(a + b).1, (a + b).2.1⟩).1 =
          (eqvBF ⟨a.1, a.2.1⟩).1 + (eqvBF ⟨b.1, b.2.1⟩).1
        rw [ha, map_add, Submodule.coe_add])
      map_smul' := fun r a => Subtype.ext (by
        have ha : (⟨(r • a).1, (r • a).2.1⟩ : B.carrier) = r • ⟨a.1, a.2.1⟩ := rfl
        change (eqvBF ⟨(r • a).1, (r • a).2.1⟩).1 =
          r • (eqvBF ⟨a.1, a.2.1⟩).1
        rw [ha, map_smul, Submodule.coe_smul]) }
  have hf'_mem : ∀ z : Albert, jordanMul f' z = z ↔ z.1 1 = 0 ∧ z.2 0 = 0 ∧ z.2 2 = 0 := fun z => by
    have hdiag02 : jordanMul (diagAtom 0 + diagAtom 2) z =
        mkAlbert ![z.1 0, 0, z.1 2] ![(1 / 2 : ℝ) • z.2 0, z.2 1, (1 / 2 : ℝ) • z.2 2] := by
      rw [jordanMul_add_left, jordanMul_diagAtom0_mk, jordanMul_diagAtom2_mk]
      apply albert_ext <;> (simp [albert_add_fst, albert_add_snd]; try module)
    constructor
    · intro h
      rw [show f' = diagAtom 0 + diagAtom 2 from rfl, hdiag02] at h
      refine ⟨?_, ?_, ?_⟩
      · exact (congrArg (fun a : Albert => a.1 1) h).symm
      · have h2 := congrArg (fun a : Albert => (2 : ℝ) • a.2 0) h
        simp only [mkAlbert_snd, Matrix.cons_val_zero] at h2
        rw [smul_smul] at h2; norm_num at h2
        have hsub : z.2 0 - z.2 0 = (2 : ℝ) • z.2 0 - z.2 0 := congrArg (· - z.2 0) h2
        rw [sub_self, two_smul, add_sub_cancel_right] at hsub
        exact hsub.symm
      · have h2 := congrArg (fun a : Albert => (2 : ℝ) • a.2 2) h
        simp only [mkAlbert_snd, Matrix.cons_val] at h2
        rw [smul_smul] at h2; norm_num at h2
        have hsub : z.2 2 - z.2 2 = (2 : ℝ) • z.2 2 - z.2 2 := congrArg (· - z.2 2) h2
        rw [sub_self, two_smul, add_sub_cancel_right] at hsub
        exact hsub.symm
    · intro ⟨h1, h0, h2⟩
      rw [show f' = diagAtom 0 + diagAtom 2 from rfl, hdiag02]
      apply albert_ext <;> simp [h1, h0, h2]
  let eqvCornerF : cornerSubmodule f' (jordanSubalgebraH3 F) ≃ₗ[ℝ] (ℝ × ℝ × F.carrier) :=
    { toFun := fun z => (z.1.1 0, z.1.1 2, ⟨z.1.2 1, z.2.1.2.1⟩)
      invFun := fun p => ⟨(![p.1, 0, p.2.1], ![0, p.2.2.1, 0]),
        ⟨⟨F.carrier.zero_mem, p.2.2.2, F.carrier.zero_mem⟩,
         (hf'_mem _).mpr ⟨rfl, rfl, rfl⟩⟩⟩
      left_inv := fun z => by
        have hm := (hf'_mem z.1).mp z.2.2
        apply Subtype.ext
        apply albert_ext <;> simp [hm.1, hm.2.1, hm.2.2]
      right_inv := fun p => by apply Prod.ext <;> [rfl; apply Prod.ext <;> rfl]
      map_add' := fun a b => by apply Prod.ext <;> [rfl; apply Prod.ext <;> rfl]
      map_smul' := fun r a => by apply Prod.ext <;> [rfl; apply Prod.ext <;> rfl] }
  have hfin_corner : Module.finrank ℝ (cornerSubmodule f B) = 2 + Module.finrank ℝ F.carrier := by
    rw [eqvCorner.finrank_eq, eqvCornerF.finrank_eq, Module.finrank_prod, Module.finrank_prod,
      Module.finrank_self]
    ring
  have hF_ge3 : 3 ≤ Module.finrank ℝ F.carrier := by omega
  have hF_eq4 : Module.finrank ℝ F.carrier = 4 := by
    rcases hF_fin_in with h1 | h2 | h4
    · omega
    · omega
    · exact h4
  rw [hfinB, hF_eq4]

private theorem pentadDrop_0_0 : pentadDrop 0 0 = pentadF 1 := rfl
private theorem pentadDrop_0_1 : pentadDrop 0 1 = pentadF 2 := rfl
private theorem pentadDrop_0_2 : pentadDrop 0 2 = pentadF 3 := rfl
private theorem pentadDrop_0_3 : pentadDrop 0 3 = pentadF 4 := rfl
private theorem pentadDrop_1_0 : pentadDrop 1 0 = pentadF 0 := rfl
private theorem pentadDrop_1_1 : pentadDrop 1 1 = pentadF 2 := rfl
private theorem pentadDrop_1_2 : pentadDrop 1 2 = pentadF 3 := rfl
private theorem pentadDrop_1_3 : pentadDrop 1 3 = pentadF 4 := rfl
private theorem pentadDrop_2_0 : pentadDrop 2 0 = pentadF 0 := rfl
private theorem pentadDrop_2_1 : pentadDrop 2 1 = pentadF 1 := rfl
private theorem pentadDrop_2_2 : pentadDrop 2 2 = pentadF 3 := rfl
private theorem pentadDrop_2_3 : pentadDrop 2 3 = pentadF 4 := rfl
private theorem pentadDrop_3_0 : pentadDrop 3 0 = pentadF 0 := rfl
private theorem pentadDrop_3_1 : pentadDrop 3 1 = pentadF 1 := rfl
private theorem pentadDrop_3_2 : pentadDrop 3 2 = pentadF 2 := rfl
private theorem pentadDrop_3_3 : pentadDrop 3 3 = pentadF 4 := rfl
private theorem pentadDrop_4_0 : pentadDrop 4 0 = pentadF 0 := rfl
private theorem pentadDrop_4_1 : pentadDrop 4 1 = pentadF 1 := rfl
private theorem pentadDrop_4_2 : pentadDrop 4 2 = pentadF 2 := rfl
private theorem pentadDrop_4_3 : pentadDrop 4 3 = pentadF 3 := rfl

theorem pentadDrop_generated_finrank (k : Fin 5) :
    Module.finrank ℝ (generatedSubalgebra (Set.range (pentadDrop k))).carrier =
      (![15, 15, 6, 15, 15] : Fin 5 → ℕ) k := by
  have : Module.Finite ℝ Octonion :=
    inferInstanceAs (FiniteDimensional ℝ (Quaternion ℝ × Quaternion ℝ))
  fin_cases k
  · exact pentadDrop_0_or_1_finrank 0 (Or.inl rfl)
  · exact pentadDrop_0_or_1_finrank 1 (Or.inr rfl)
  · -- k = 2: {p0, p1, p3, p4} generates 6-dimensional subalgebra {d, ![v, 0, 0]} with v ∈ span {1, j, l}
    let B := generatedSubalgebra (Set.range (pentadDrop 2))
    let V0 : Submodule ℝ Octonion := Submodule.span ℝ {octOne, octJ, octL}
    let S2 : NativeJordanSubalgebra :=
      { carrier :=
          { carrier := {x : Albert | x.2 1 = 0 ∧ x.2 2 = 0 ∧ x.2 0 ∈ V0}
            add_mem' := fun {a b} ha hb =>
              ⟨by rw [albert_add_snd, ha.1, hb.1, add_zero],
               by rw [albert_add_snd, ha.2.1, hb.2.1, add_zero],
               V0.add_mem ha.2.2 hb.2.2⟩
            zero_mem' := ⟨rfl, rfl, V0.zero_mem⟩
            smul_mem' := fun r {a} ha =>
              ⟨by rw [albert_smul_snd, ha.1, smul_zero],
               by rw [albert_smul_snd, ha.2.1, smul_zero],
               V0.smul_mem r ha.2.2⟩ }
        unit_mem := ⟨rfl, rfl, V0.zero_mem⟩
        product_mem := fun a ha b hb => by
          refine ⟨?_, ?_, ?_⟩
          · simp [jordanMul_off_1, ha.1, ha.2.1, hb.1, hb.2.1, octonionMul_zero_right]
          · simp [jordanMul_off_2, ha.1, ha.2.1, hb.1, hb.2.1, octonionMul_zero_right]
          · simp only [jordanMul_off_0, ha.1, ha.2.1, hb.1, hb.2.1, octonionConj_zero,
              octonionMul_zero_right, add_zero]
            exact V0.smul_mem (1 / 2 : ℝ) (V0.add_mem (V0.smul_mem _ hb.2.2) (V0.smul_mem _ ha.2.2)) }
    have hB_eq : B = S2 := by
      apply nativeJordanSubalgebra_ext
      apply le_antisymm
      · exact generatedSubalgebra_le (by
          rintro x ⟨j, rfl⟩
          fin_cases j <;> dsimp
          · rw [pentadDrop_2_0, pentadF_0_eq]; exact ⟨rfl, rfl, V0.zero_mem⟩
          · rw [pentadDrop_2_1, pentadF_1_eq]
            refine ⟨rfl, rfl, ?_⟩
            simp only [mkAlbert_snd, Matrix.cons_val_zero]
            rw [octonionScalar_eq_smul, ← octOne_eq_scalar]
            exact Submodule.smul_mem V0 (1 / 2 : ℝ) (Submodule.subset_span (by simp))
          · rw [pentadDrop_2_2, pentadF_3_eq]
            refine ⟨rfl, rfl, Submodule.smul_mem V0 (-1 / 2 : ℝ) (Submodule.subset_span (by simp))⟩
          · rw [pentadDrop_2_3, pentadF_4_eq]
            refine ⟨rfl, rfl, Submodule.smul_mem V0 (-1 / 2 : ℝ) (Submodule.subset_span (by simp))⟩)
      · have hp : ∀ j : Fin 4, pentadDrop 2 j ∈ B.carrier := fun j =>
          subset_generatedSubalgebra _ ⟨j, rfl⟩
        have hd0 : diagAtom 0 ∈ B.carrier := hp 0
        have hf : diagAtom 0 + diagAtom 1 ∈ B.carrier := by
          obtain ⟨_, hsup⟩ := eq_fiv_support (diagAtom 2) (pentadDrop 2 0) (pentadDrop 2 1)
            (diagAtom_isAtom 2) (pentadF_isAtom 0) (pentadF_isAtom 1)
            (by rw [pentadDrop_2_0, pentadF_0_eq]; apply albert_ext <;> simp [jordanMul_diagAtom2, diagAtom_fst, diagAtom_snd, albert_zero_fst, albert_zero_snd])
            (by rw [pentadDrop_2_1, pentadF_1_eq]; apply albert_ext <;> simp [jordanMul_diagAtom2, albert_zero_fst, albert_zero_snd])
            (fun h => by
              have h0 := congrArg (fun a : Albert => a.1 0) h
              rw [pentadDrop_2_0, pentadDrop_2_1, pentadF_0_eq, pentadF_1_eq] at h0
              simp [diagAtom_fst] at h0)
          have heq : diagAtom 0 + diagAtom 1 = albertUnit - diagAtom 2 := by
            apply albert_ext <;> simp [albert_add_fst, albert_add_snd, albert_sub_fst, albert_sub_snd,
              albertUnit_fst, albertUnit_snd, diagAtom_fst, diagAtom_snd]
          rw [heq, hsup]
          exact B.carrier.smul_mem _ (B.carrier.sub_mem (B.carrier.add_mem (hp 0) (hp 1))
            (B.carrier.smul_mem _ (B.product_mem _ (hp 0) _ (hp 1))))
        have hd1 : diagAtom 1 ∈ B.carrier := by
          have : diagAtom 1 = (diagAtom 0 + diagAtom 1) - diagAtom 0 := by abel
          rw [this]; exact B.carrier.sub_mem hf hd0
        have hd2 : diagAtom 2 ∈ B.carrier := by
          have : diagAtom 2 = albertUnit - (diagAtom 0 + diagAtom 1) := by
            apply albert_ext <;> simp [albert_sub_fst, albert_sub_snd, albert_add_fst, albert_add_snd,
              albertUnit_fst, albertUnit_snd, diagAtom_fst, diagAtom_snd]
          rw [this]; exact B.carrier.sub_mem B.unit_mem hf
        have h1 : slotElem01 octOne ∈ B.carrier := by
          have heq : slotElem01 octOne = (2 : ℝ) • pentadDrop 2 1 - (diagAtom 0 + diagAtom 1) := by
            rw [pentadDrop_2_1, pentadF_1_eq]
            apply albert_ext
            · simp [albert_sub_fst, albert_smul_fst, albert_add_fst, slotElem01_fst, diagAtom_fst]
            · simp [albert_sub_fst, albert_smul_fst, albert_add_fst, slotElem01_fst, diagAtom_fst]
            · simp [albert_sub_fst, albert_smul_fst, albert_add_fst, slotElem01_fst, diagAtom_fst]
            · apply oct_ext <;>
                simp only [albert_sub_snd, albert_smul_snd, albert_add_snd, slotElem01_snd_0,
                  diagAtom_snd, mkAlbert_snd, Matrix.cons_val_zero, oct_sub_fst, oct_sub_snd,
                  oct_smul_fst, oct_smul_snd, oct_add_fst, oct_add_snd] <;>
                simp [octOne, octonionScalar]
            · simp [albert_sub_snd, albert_smul_snd, albert_add_snd, slotElem01_snd_1, diagAtom_snd]
            · simp [albert_sub_snd, albert_smul_snd, albert_add_snd, slotElem01_snd_2, diagAtom_snd]
          rw [heq]; exact B.carrier.sub_mem (B.carrier.smul_mem (2 : ℝ) (hp 1)) hf
        have hJ : slotElem01 octJ ∈ B.carrier := by
          have heq : slotElem01 octJ = (diagAtom 0 + diagAtom 1) - (2 : ℝ) • pentadDrop 2 2 := by
            rw [pentadDrop_2_2, pentadF_3_eq]
            apply albert_ext
            · simp [albert_sub_fst, albert_smul_fst, albert_add_fst, slotElem01_fst, diagAtom_fst]
            · simp [albert_sub_fst, albert_smul_fst, albert_add_fst, slotElem01_fst, diagAtom_fst]
            · simp [albert_sub_fst, albert_smul_fst, albert_add_fst, slotElem01_fst, diagAtom_fst]
            · apply oct_ext <;>
                simp only [albert_sub_snd, albert_smul_snd, albert_add_snd, slotElem01_snd_0,
                  diagAtom_snd, mkAlbert_snd, Matrix.cons_val_zero, oct_sub_fst, oct_sub_snd,
                  oct_smul_fst, oct_smul_snd, oct_add_fst, oct_add_snd] <;>
                (simp [octJ]; try norm_num)
            · simp [albert_sub_snd, albert_smul_snd, albert_add_snd, slotElem01_snd_1, diagAtom_snd]
            · simp [albert_sub_snd, albert_smul_snd, albert_add_snd, slotElem01_snd_2, diagAtom_snd]
          rw [heq]; exact B.carrier.sub_mem hf (B.carrier.smul_mem (2 : ℝ) (hp 2))
        have hL : slotElem01 octL ∈ B.carrier := by
          have heq : slotElem01 octL = (diagAtom 0 + diagAtom 1) - (2 : ℝ) • pentadDrop 2 3 := by
            rw [pentadDrop_2_3, pentadF_4_eq]
            apply albert_ext
            · simp [albert_sub_fst, albert_smul_fst, albert_add_fst, slotElem01_fst, diagAtom_fst]
            · simp [albert_sub_fst, albert_smul_fst, albert_add_fst, slotElem01_fst, diagAtom_fst]
            · simp [albert_sub_fst, albert_smul_fst, albert_add_fst, slotElem01_fst, diagAtom_fst]
            · apply oct_ext <;>
                simp only [albert_sub_snd, albert_smul_snd, albert_add_snd, slotElem01_snd_0,
                  diagAtom_snd, mkAlbert_snd, Matrix.cons_val_zero, oct_sub_fst, oct_sub_snd,
                  oct_smul_fst, oct_smul_snd, oct_add_fst, oct_add_snd] <;>
                (simp [octL]; try norm_num)
            · simp [albert_sub_snd, albert_smul_snd, albert_add_snd, slotElem01_snd_1, diagAtom_snd]
            · simp [albert_sub_snd, albert_smul_snd, albert_add_snd, slotElem01_snd_2, diagAtom_snd]
          rw [heq]; exact B.carrier.sub_mem hf (B.carrier.smul_mem (2 : ℝ) (hp 3))
        have hV0 : ∀ v ∈ V0, slotElem01 v ∈ B.carrier := fun v hv => by
          refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
          · rintro u (rfl | rfl | rfl)
            · exact h1
            · exact hJ
            · exact hL
          · rw [map_zero]; exact B.carrier.zero_mem
          · intro a b _ _ ha hb; rw [map_add]; exact B.carrier.add_mem ha hb
          · intro r a _ ha; rw [map_smul]; exact B.carrier.smul_mem r ha
        intro x ⟨hx1, hx2, hx0⟩
        rw [albert_decompose_slots x, hx1, hx2, map_zero, map_zero, add_zero, add_zero]
        exact B.carrier.add_mem (B.carrier.add_mem (B.carrier.add_mem
          (B.carrier.smul_mem _ hd0) (B.carrier.smul_mem _ hd1))
          (B.carrier.smul_mem _ hd2)) (hV0 _ hx0)
    have hV0_indep : LinearIndependent ℝ ![octOne, octJ, octL] := by
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      have hc0 : (∑ m : Fin 3, c m • ![octOne, octJ, octL] m) = 0 := hc
      rw [Fin.sum_univ_three] at hc0
      have hr := congrArg (fun u : Octonion => u.1.re) hc0
      have hj := congrArg (fun u : Octonion => u.1.imJ) hc0
      have hl := congrArg (fun u : Octonion => u.2.re) hc0
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, oct_add_fst, oct_add_snd,
        oct_smul_fst, oct_smul_snd] at hr hj hl
      simp [octOne, octonionScalar, octJ, octL] at hr hj hl
      fin_cases i <;> dsimp <;> linarith
    have hfinV0 : Module.finrank ℝ V0 = 3 := by
      have heq : V0 = Submodule.span ℝ (Set.range ![octOne, octJ, octL]) := by
        dsimp only [V0]
        congr 1
        ext u
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
        constructor
        · rintro (rfl | rfl | rfl)
          · exact ⟨0, rfl⟩
          · exact ⟨1, rfl⟩
          · exact ⟨2, rfl⟩
        · rintro ⟨m, rfl⟩
          fin_cases m <;> simp
      rw [heq, finrank_span_eq_card hV0_indep, Fintype.card_fin]
    let eqvS2 : S2.carrier ≃ₗ[ℝ] ((Fin 3 → ℝ) × V0) :=
      { toFun := fun x => (x.1.1, ⟨x.1.2 0, x.2.2.2⟩)
        invFun := fun p => ⟨(p.1, ![p.2.1, 0, 0]), ⟨rfl, rfl, p.2.2⟩⟩
        left_inv := fun x => by
          apply Subtype.ext; apply albert_ext <;> simp [x.2.1, x.2.2.1]
        right_inv := fun p => by apply Prod.ext <;> rfl
        map_add' := fun a b => by apply Prod.ext <;> rfl
        map_smul' := fun r a => by apply Prod.ext <;> rfl }
    change Module.finrank ℝ B.carrier = 6
    rw [hB_eq, eqvS2.finrank_eq, Module.finrank_prod, Module.finrank_fin_fun, hfinV0]
  · -- k = 3: {p0, p1, p2, p4} generates H3(H_{i,l}), finrank 15
    let B := generatedSubalgebra (Set.range (pentadDrop 3))
    have hp : ∀ j : Fin 4, pentadDrop 3 j ∈ B.carrier := fun j =>
      subset_generatedSubalgebra _ ⟨j, rfl⟩
    have hd0 : diagAtom 0 ∈ B.carrier := hp 0
    have hd1_half : (1 / 2 : ℝ) • diagAtom 1 ∈ B.carrier := by
      have hmem := (peirce_components_mem_subalgebra B hd0 (hp 1)).2.2
      have heq : quadraticMap (albertUnit - diagAtom 0) (pentadDrop 3 1) = (1 / 2 : ℝ) • diagAtom 1 := by
        rw [pentadDrop_3_1, quadraticMap_compl_diagAtom0_eq, pentadF_1_eq]
        apply albert_ext <;> simp [albert_smul_fst, albert_smul_snd, diagAtom_fst, diagAtom_snd]
      rwa [heq] at hmem
    have hd1 : diagAtom 1 ∈ B.carrier := by
      have h2 : (2 : ℝ) * (1 / 2 : ℝ) = 1 := by norm_num
      have hs := B.carrier.smul_mem (2 : ℝ) hd1_half
      rwa [smul_smul, h2, one_smul] at hs
    have hd2 : diagAtom 2 ∈ B.carrier := by
      have heq : diagAtom 2 = albertUnit - diagAtom 0 - diagAtom 1 := by
        apply albert_ext <;> simp [albert_sub_fst, albert_sub_snd, albertUnit_fst, albertUnit_snd,
          diagAtom_fst, diagAtom_snd]
      rw [heq]; exact B.carrier.sub_mem (B.carrier.sub_mem B.unit_mem hd0) hd1
    have hs01 : slotElem01 octOne ∈ B.carrier := by
      have heq : slotElem01 octOne = (2 : ℝ) • pentadDrop 3 1 - diagAtom 0 - diagAtom 1 := by
        rw [pentadDrop_3_1, pentadF_1_eq]
        apply albert_ext
        · simp [albert_sub_fst, albert_smul_fst, slotElem01_fst, diagAtom_fst]
        · simp [albert_sub_fst, albert_smul_fst, slotElem01_fst, diagAtom_fst]
        · simp [albert_sub_fst, albert_smul_fst, slotElem01_fst, diagAtom_fst]
        · apply oct_ext <;>
            simp only [albert_sub_snd, albert_smul_snd, slotElem01_snd_0, diagAtom_snd,
              mkAlbert_snd, Matrix.cons_val_zero, oct_sub_fst, oct_sub_snd, oct_smul_fst,
              oct_smul_snd] <;>
            simp [octOne, octonionScalar]
        · simp [albert_sub_snd, albert_smul_snd, slotElem01_snd_1, diagAtom_snd]
        · simp [albert_sub_snd, albert_smul_snd, slotElem01_snd_2, diagAtom_snd]
      rw [heq]; exact B.carrier.sub_mem (B.carrier.sub_mem (B.carrier.smul_mem (2 : ℝ) (hp 1)) hd0) hd1
    have hs02 : slotElem02 octOne ∈ B.carrier := by
      have hex : (4 : ℝ) • jordanMul (diagAtom 0) (jordanMul (diagAtom 2) (pentadDrop 3 2)) ∈ B.carrier :=
        B.carrier.smul_mem (4 : ℝ) (B.product_mem _ hd0 _ (B.product_mem _ hd2 _ (hp 2)))
      rw [peirce02_extract, pentadDrop_3_2, pentadF_2_eq] at hex
      simp only [mkAlbert_snd, Matrix.cons_val_one, Matrix.cons_val_zero] at hex
      have hsm := B.carrier.smul_mem (3 : ℝ) hex
      rw [← map_smul, smul_smul, show (3 : ℝ) * (1 / 3 : ℝ) = 1 by norm_num, one_smul] at hsm
      exact hsm
    obtain ⟨F, hFset, hBeq, _⟩ := lem_five_coord B hd0 hd1 hd2 (.inl ⟨hs01, hs02⟩)
    have hI : octI ∈ F.carrier := by
      have hex : (4 : ℝ) • jordanMul (diagAtom 0) (jordanMul (diagAtom 1) (pentadDrop 3 2)) ∈ B.carrier :=
        B.carrier.smul_mem (4 : ℝ) (B.product_mem _ hd0 _ (B.product_mem _ hd1 _ (hp 2)))
      rw [peirce01_extract, pentadDrop_3_2, pentadF_2_eq] at hex
      simp only [mkAlbert_snd, Matrix.cons_val_zero] at hex
      have hs : slotElem01 octI ∈ B.carrier := by
        have hsm := B.carrier.smul_mem (-3 : ℝ) hex
        rw [← map_smul, smul_smul, show (-3 : ℝ) * (-1 / 3 : ℝ) = 1 by norm_num, one_smul] at hsm
        exact hsm
      have hm : octI ∈ (F.carrier : Set Octonion) := by rw [hFset]; exact hs
      exact hm
    have hL : octL ∈ F.carrier := by
      have hex : (4 : ℝ) • jordanMul (diagAtom 0) (jordanMul (diagAtom 1) (pentadDrop 3 3)) ∈ B.carrier :=
        B.carrier.smul_mem (4 : ℝ) (B.product_mem _ hd0 _ (B.product_mem _ hd1 _ (hp 3)))
      rw [peirce01_extract, pentadDrop_3_3, pentadF_4_eq] at hex
      simp only [mkAlbert_snd, Matrix.cons_val_zero] at hex
      have hs : slotElem01 octL ∈ B.carrier := by
        have hsm := B.carrier.smul_mem (-2 : ℝ) hex
        rw [← map_smul, smul_smul, show (-2 : ℝ) * (-1 / 2 : ℝ) = 1 by norm_num, one_smul] at hsm
        exact hsm
      have hm : octL ∈ (F.carrier : Set Octonion) := by rw [hFset]; exact hs
      exact hm
    obtain ⟨φ, hφ, hφI, hφL⟩ := exists_quatEmbedding_containing_pair octI octL
    let Fφ : OctSubalgebra :=
      { carrier := LinearMap.range φ
        one_mem := ⟨1, by rw [hφ.map_one]; rfl⟩
        mul_mem := by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact ⟨a * b, hφ.map_mul a b⟩
        conj_mem := by rintro _ ⟨a, rfl⟩; exact ⟨star a, hφ.map_star a⟩ }
    have hF_le : F.carrier ≤ LinearMap.range φ := by
      have hB_le : B ≤ jordanSubalgebraH3 Fφ := generatedSubalgebra_le (by
        rintro x ⟨j, rfl⟩
        fin_cases j <;> dsimp
        · rw [pentadDrop_3_0, pentadF_0_eq]
          exact ⟨Fφ.carrier.zero_mem, Fφ.carrier.zero_mem, Fφ.carrier.zero_mem⟩
        · rw [pentadDrop_3_1, pentadF_1_eq]
          refine ⟨?_, Fφ.carrier.zero_mem, Fφ.carrier.zero_mem⟩
          simp only [mkAlbert_snd, Matrix.cons_val_zero]
          rw [octonionScalar_eq_smul, ← octOne_eq_scalar]
          exact Fφ.carrier.smul_mem _ Fφ.one_mem
        · rw [pentadDrop_3_2, pentadF_2_eq]
          exact ⟨Fφ.carrier.smul_mem _ hφI, Fφ.carrier.smul_mem _ Fφ.one_mem,
            Fφ.carrier.smul_mem _ hφI⟩
        · rw [pentadDrop_3_3, pentadF_4_eq]
          exact ⟨Fφ.carrier.smul_mem _ hφL, Fφ.carrier.zero_mem, Fφ.carrier.zero_mem⟩)
      intro a ha
      have ha' : a ∈ (F.carrier : Set Octonion) := ha
      have ha01 : slotElem01 a ∈ B.carrier := by rw [hFset] at ha'; exact ha'
      exact (hB_le ha01).1
    have hF_fin := octSubalgebra_le_quatEmbedding_finrank F φ hφ hF_le
    have hS : octS ∈ F.carrier := by rw [← octS_eq_mul]; exact F.mul_mem _ hI _ hL
    have h4_indep : LinearIndependent ℝ ![octOne, octI, octL, octS] := by
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      have hc0 : (∑ m : Fin 4, c m • ![octOne, octI, octL, octS] m) = 0 := hc
      rw [Fin.sum_univ_four] at hc0
      have h0 := congrArg (fun u : Octonion => u.1.re) hc0
      have h1 := congrArg (fun u : Octonion => u.1.imI) hc0
      have h2 := congrArg (fun u : Octonion => u.2.re) hc0
      have h3 := congrArg (fun u : Octonion => u.2.imI) hc0
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, oct_add_fst, oct_add_snd,
        oct_smul_fst, oct_smul_snd] at h0 h1 h2 h3
      simp [octOne, octonionScalar, octI, octL, octS] at h0 h1 h2 h3
      fin_cases i <;> dsimp <;> linarith
    have h4_le : 4 ≤ Module.finrank ℝ F.carrier := by
      have hle : Module.finrank ℝ (Submodule.span ℝ (Set.range ![octOne, octI, octL, octS])) ≤
          Module.finrank ℝ F.carrier := Submodule.finrank_mono (by
        rw [Submodule.span_le]
        rintro u ⟨m, rfl⟩
        fin_cases m <;> dsimp
        · exact F.one_mem
        · exact hI
        · exact hL
        · exact hS)
      rw [finrank_span_eq_card h4_indep, Fintype.card_fin] at hle
      exact hle
    have hFeq4 : Module.finrank ℝ F.carrier = 4 := by
      rcases hF_fin with h1 | h2 | h4
      · omega
      · omega
      · exact h4
    change Module.finrank ℝ B.carrier = 15
    rw [hBeq, finrank_jordanSubalgebraH3, hFeq4]
  · -- k = 4: {p0, p1, p2, p3} generates H3Subalgebra .H, finrank 15
    let B := generatedSubalgebra (Set.range (pentadDrop 4))
    have hp : ∀ j : Fin 4, pentadDrop 4 j ∈ B.carrier := fun j =>
      subset_generatedSubalgebra _ ⟨j, rfl⟩
    have hd0 : diagAtom 0 ∈ B.carrier := hp 0
    have hd1_half : (1 / 2 : ℝ) • diagAtom 1 ∈ B.carrier := by
      have hmem := (peirce_components_mem_subalgebra B hd0 (hp 1)).2.2
      have heq : quadraticMap (albertUnit - diagAtom 0) (pentadDrop 4 1) = (1 / 2 : ℝ) • diagAtom 1 := by
        rw [pentadDrop_4_1, quadraticMap_compl_diagAtom0_eq, pentadF_1_eq]
        apply albert_ext <;> simp [albert_smul_fst, albert_smul_snd, diagAtom_fst, diagAtom_snd]
      rwa [heq] at hmem
    have hd1 : diagAtom 1 ∈ B.carrier := by
      have h2 : (2 : ℝ) * (1 / 2 : ℝ) = 1 := by norm_num
      have hs := B.carrier.smul_mem (2 : ℝ) hd1_half
      rwa [smul_smul, h2, one_smul] at hs
    have hd2 : diagAtom 2 ∈ B.carrier := by
      have heq : diagAtom 2 = albertUnit - diagAtom 0 - diagAtom 1 := by
        apply albert_ext <;> simp [albert_sub_fst, albert_sub_snd, albertUnit_fst, albertUnit_snd,
          diagAtom_fst, diagAtom_snd]
      rw [heq]; exact B.carrier.sub_mem (B.carrier.sub_mem B.unit_mem hd0) hd1
    have hs01 : slotElem01 octOne ∈ B.carrier := by
      have heq : slotElem01 octOne = (2 : ℝ) • pentadDrop 4 1 - diagAtom 0 - diagAtom 1 := by
        rw [pentadDrop_4_1, pentadF_1_eq]
        apply albert_ext
        · simp [albert_sub_fst, albert_smul_fst, slotElem01_fst, diagAtom_fst]
        · simp [albert_sub_fst, albert_smul_fst, slotElem01_fst, diagAtom_fst]
        · simp [albert_sub_fst, albert_smul_fst, slotElem01_fst, diagAtom_fst]
        · apply oct_ext <;>
            simp only [albert_sub_snd, albert_smul_snd, slotElem01_snd_0, diagAtom_snd,
              mkAlbert_snd, Matrix.cons_val_zero, oct_sub_fst, oct_sub_snd, oct_smul_fst,
              oct_smul_snd] <;>
            simp [octOne, octonionScalar]
        · simp [albert_sub_snd, albert_smul_snd, slotElem01_snd_1, diagAtom_snd]
        · simp [albert_sub_snd, albert_smul_snd, slotElem01_snd_2, diagAtom_snd]
      rw [heq]; exact B.carrier.sub_mem (B.carrier.sub_mem (B.carrier.smul_mem (2 : ℝ) (hp 1)) hd0) hd1
    have hs02 : slotElem02 octOne ∈ B.carrier := by
      have hex : (4 : ℝ) • jordanMul (diagAtom 0) (jordanMul (diagAtom 2) (pentadDrop 4 2)) ∈ B.carrier :=
        B.carrier.smul_mem (4 : ℝ) (B.product_mem _ hd0 _ (B.product_mem _ hd2 _ (hp 2)))
      rw [peirce02_extract, pentadDrop_4_2, pentadF_2_eq] at hex
      simp only [mkAlbert_snd, Matrix.cons_val_one, Matrix.cons_val_zero] at hex
      have hsm := B.carrier.smul_mem (3 : ℝ) hex
      rw [← map_smul, smul_smul, show (3 : ℝ) * (1 / 3 : ℝ) = 1 by norm_num, one_smul] at hsm
      exact hsm
    obtain ⟨F, hFset, hBeq, _⟩ := lem_five_coord B hd0 hd1 hd2 (.inl ⟨hs01, hs02⟩)
    have hI : octI ∈ F.carrier := by
      have hex : (4 : ℝ) • jordanMul (diagAtom 0) (jordanMul (diagAtom 1) (pentadDrop 4 2)) ∈ B.carrier :=
        B.carrier.smul_mem (4 : ℝ) (B.product_mem _ hd0 _ (B.product_mem _ hd1 _ (hp 2)))
      rw [peirce01_extract, pentadDrop_4_2, pentadF_2_eq] at hex
      simp only [mkAlbert_snd, Matrix.cons_val_zero] at hex
      have hs : slotElem01 octI ∈ B.carrier := by
        have hsm := B.carrier.smul_mem (-3 : ℝ) hex
        rw [← map_smul, smul_smul, show (-3 : ℝ) * (-1 / 3 : ℝ) = 1 by norm_num, one_smul] at hsm
        exact hsm
      have hm : octI ∈ (F.carrier : Set Octonion) := by rw [hFset]; exact hs
      exact hm
    have hJ : octJ ∈ F.carrier := by
      have hex : (4 : ℝ) • jordanMul (diagAtom 0) (jordanMul (diagAtom 1) (pentadDrop 4 3)) ∈ B.carrier :=
        B.carrier.smul_mem (4 : ℝ) (B.product_mem _ hd0 _ (B.product_mem _ hd1 _ (hp 3)))
      rw [peirce01_extract, pentadDrop_4_3, pentadF_3_eq] at hex
      simp only [mkAlbert_snd, Matrix.cons_val_zero] at hex
      have hs : slotElem01 octJ ∈ B.carrier := by
        have hsm := B.carrier.smul_mem (-2 : ℝ) hex
        rw [← map_smul, smul_smul, show (-2 : ℝ) * (-1 / 2 : ℝ) = 1 by norm_num, one_smul] at hsm
        exact hsm
      have hm : octJ ∈ (F.carrier : Set Octonion) := by rw [hFset]; exact hs
      exact hm
    have hK : octK ∈ F.carrier := by rw [← octK_eq_mul]; exact F.mul_mem _ hI _ hJ
    have hFeqH : F = octQuatStandardSubalgebra := by
      cases F with
      | mk Fcar F1 Fmul Fconj =>
        simp only [octQuatStandardSubalgebra]
        congr 1
        apply le_antisymm
        · have hB_le : B ≤ H3Subalgebra .H := generatedSubalgebra_le (by
            rintro x ⟨j, rfl⟩
            fin_cases j <;> dsimp
            · rw [pentadDrop_4_0, pentadF_0_eq]; exact ⟨rfl, rfl, rfl⟩
            · rw [pentadDrop_4_1, pentadF_1_eq]; exact ⟨rfl, rfl, rfl⟩
            · rw [pentadDrop_4_2, pentadF_2_eq]
              refine ⟨?_, ?_, ?_⟩
              · change ((-1 / 3 : ℝ) • octI).2 = 0; rw [oct_smul_snd]; simp [octI]
              · change ((1 / 3 : ℝ) • octOne).2 = 0; rw [oct_smul_snd]; simp [octOne, octonionScalar]
              · change ((1 / 3 : ℝ) • octI).2 = 0; rw [oct_smul_snd]; simp [octI]
            · rw [pentadDrop_4_3, pentadF_3_eq]
              refine ⟨?_, rfl, rfl⟩
              change ((-1 / 2 : ℝ) • octJ).2 = 0; rw [oct_smul_snd]; simp [octJ])
          intro a ha
          have ha' : a ∈ (Fcar : Set Octonion) := ha
          have ha01 : slotElem01 a ∈ B.carrier := by rw [hFset] at ha'; exact ha'
          exact (hB_le ha01).1
        · intro a ha
          have ha2 : a.2 = 0 := ha
          have hexp : a = a.1.re • octOne + a.1.imI • octI + a.1.imJ • octJ + a.1.imK • octK := by
            apply oct_ext
            · simp only [oct_add_fst, oct_smul_fst]; simp [octOne, octonionScalar, octI, octJ, octK]
            · simp only [oct_add_fst, oct_smul_fst]; simp [octOne, octonionScalar, octI, octJ, octK]
            · simp only [oct_add_fst, oct_smul_fst]; simp [octOne, octonionScalar, octI, octJ, octK]
            · simp only [oct_add_fst, oct_smul_fst]; simp [octOne, octonionScalar, octI, octJ, octK]
            · simp only [oct_add_snd, oct_smul_snd]
              simp [octOne, octonionScalar, octI, octJ, octK, ha2]
            · simp only [oct_add_snd, oct_smul_snd]
              simp [octOne, octonionScalar, octI, octJ, octK, ha2]
            · simp only [oct_add_snd, oct_smul_snd]
              simp [octOne, octonionScalar, octI, octJ, octK, ha2]
            · simp only [oct_add_snd, oct_smul_snd]
              simp [octOne, octonionScalar, octI, octJ, octK, ha2]
          change a ∈ Fcar
          rw [hexp]
          exact Fcar.add_mem (Fcar.add_mem (Fcar.add_mem
            (Fcar.smul_mem _ F1) (Fcar.smul_mem _ hI))
            (Fcar.smul_mem _ hJ)) (Fcar.smul_mem _ hK)
    change Module.finrank ℝ B.carrier = 15
    rw [hBeq, hFeqH]
    exact finrank_H3Subalgebra .H

theorem pentadDrop_in_quaternionicWindow (k : Fin 5) :
    ∃ Q : QuaternionicWindow, ∀ j : Fin 4, pentadDrop k j ∈ Q.subalgebra.carrier := by
  have : Module.Finite ℝ Octonion :=
    inferInstanceAs (FiniteDimensional ℝ (Quaternion ℝ × Quaternion ℝ))
  have : Module.Finite ℝ Albert :=
    inferInstanceAs (FiniteDimensional ℝ ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
  by_cases hk2 : k = 2
  · subst hk2
    obtain ⟨φ, hφ, hφJ, hφL⟩ := exists_quatEmbedding_containing_pair octJ octL
    let Q := quaternionicWindowOfQuatEmbedding φ hφ
    refine ⟨Q, fun j => ?_⟩
    have hmem : ∀ x : Albert,
        x.2 0 ∈ Set.range φ → x.2 1 ∈ Set.range φ → x.2 2 ∈ Set.range φ →
        x ∈ Q.subalgebra.carrier := fun x ⟨q0, hq0⟩ ⟨q1, hq1⟩ ⟨q2, hq2⟩ => by
      let M : QuatMatrix3 := ![![⟨x.1 0, 0, 0, 0⟩, q0, q1],
        ![star q0, ⟨x.1 1, 0, 0, 0⟩, q2], ![star q1, star q2, ⟨x.1 2, 0, 0, 0⟩]]
      have hM : M ∈ QuatHermitian3 := by
        rw [selfAdjoint.mem_iff]
        funext a b
        fin_cases a <;> fin_cases b <;> (dsimp; simp [M])
      refine ⟨⟨M, hM⟩, ?_⟩
      change (quaternionicWindowOfQuatEmbedding φ hφ).embedding ⟨M, hM⟩ = x
      rw [quaternionicWindowOfQuatEmbedding_apply]
      apply albert_ext
      · rfl
      · rfl
      · rfl
      · exact hq0
      · exact hq1
      · exact hq2
    have h0 : (0 : Octonion) ∈ Set.range φ := ⟨0, map_zero _⟩
    have h1 : octOne ∈ Set.range φ := octOne_mem_range_quat φ hφ
    fin_cases j <;> dsimp
    · rw [pentadDrop_2_0, pentadF_0_eq]
      exact hmem _ h0 h0 h0
    · rw [pentadDrop_2_1, pentadF_1_eq]
      refine hmem _ ?_ h0 h0
      simp only [mkAlbert_snd, Matrix.cons_val_zero]
      rw [octonionScalar_eq_smul, ← octOne_eq_scalar]
      rcases h1 with ⟨q, hq⟩
      exact ⟨(1 / 2 : ℝ) • q, by rw [map_smul, hq]⟩
    · rw [pentadDrop_2_2, pentadF_3_eq]
      refine hmem _ ?_ h0 h0
      simp only [mkAlbert_snd, Matrix.cons_val_zero]
      rcases hφJ with ⟨q, hq⟩
      exact ⟨(-1 / 2 : ℝ) • q, by rw [map_smul, hq]⟩
    · rw [pentadDrop_2_3, pentadF_4_eq]
      refine hmem _ ?_ h0 h0
      simp only [mkAlbert_snd, Matrix.cons_val_zero]
      rcases hφL with ⟨q, hq⟩
      exact ⟨(-1 / 2 : ℝ) • q, by rw [map_smul, hq]⟩
  · let B := generatedSubalgebra (Set.range (pentadDrop k))
    have hfin15 : Module.finrank ℝ B.carrier = 15 := by
      rw [pentadDrop_generated_finrank k]
      fin_cases k <;> simp_all
    have hlt : B.carrier < (H3Subalgebra .O).carrier := by
      rw [H3Subalgebra_O_eq_top]
      refine lt_of_le_of_ne le_top fun heq => ?_
      have h15 : Module.finrank ℝ B.carrier = Module.finrank ℝ (⊤ : Submodule ℝ Albert) :=
        congrArg (fun S : Submodule ℝ Albert => Module.finrank ℝ S) heq
      have h27 : Module.finrank ℝ (⊤ : Submodule ℝ Albert) = 27 := by
        have hcar : (⊤ : Submodule ℝ Albert) = (H3Subalgebra .O).carrier :=
          (congrArg NativeJordanSubalgebra.carrier H3Subalgebra_O_eq_top).symm
        rw [hcar]
        exact finrank_H3Subalgebra .O
      omega
    rcases lem_five_sub .O B hlt with ⟨q, hq, _, hline⟩ | ⟨Q, hQ⟩
    · exfalso
      have hle : Module.finrank ℝ B.carrier ≤ Module.finrank ℝ (lineSubalgebra q hq).carrier :=
        Submodule.finrank_mono hline
      rw [hfin15, lineSubalgebra_finrank q hq] at hle
      omega
    · exact ⟨Q, fun j => hQ (subset_generatedSubalgebra _ ⟨j, rfl⟩)⟩

private theorem jordanMul_pentad_01 :
    jordanMul (pentadF 0) (pentadF 1) = mkAlbert ![1 / 2, 0, 0] ![octonionScalar (1 / 4), 0, 0] := by
  rw [pentadF_0_eq, pentadF_1_eq, jordanMul_diagAtom0]
  apply albert_ext
  · simp
  · simp
  · simp
  · simp only [mkAlbert_snd, Matrix.cons_val_zero]
    rw [octonionScalar_eq_smul (1 / 2), octonionScalar_eq_smul (1 / 4), smul_smul]
    congr 1; norm_num
  · simp
  · simp

private theorem jordanMul_pentad_02 :
    jordanMul (pentadF 0) (pentadF 2) =
      mkAlbert ![1 / 3, 0, 0] ![(-1 / 6 : ℝ) • octI, (1 / 6 : ℝ) • octOne, 0] := by
  rw [pentadF_0_eq, pentadF_2_eq, jordanMul_diagAtom0]
  apply albert_ext
  · simp
  · simp
  · simp
  · simp [smul_smul]; norm_num
  · simp [smul_smul]; norm_num
  · simp

private theorem jordanMul_pentad_03 :
    jordanMul (pentadF 0) (pentadF 3) = mkAlbert ![1 / 2, 0, 0] ![(-1 / 4 : ℝ) • octJ, 0, 0] := by
  rw [pentadF_0_eq, pentadF_3_eq, jordanMul_diagAtom0]
  apply albert_ext
  · simp
  · simp
  · simp
  · simp [smul_smul]; norm_num
  · simp
  · simp

private theorem jordanMul_pentad_04 :
    jordanMul (pentadF 0) (pentadF 4) = mkAlbert ![1 / 2, 0, 0] ![(-1 / 4 : ℝ) • octL, 0, 0] := by
  rw [pentadF_0_eq, pentadF_4_eq, jordanMul_diagAtom0]
  apply albert_ext
  · simp
  · simp
  · simp
  · simp [smul_smul]; norm_num
  · simp
  · simp

private theorem jordanMul_pentad_12 :
    jordanMul (pentadF 1) (pentadF 2) =
      mkAlbert ![1 / 6, 1 / 6, 0]
        ![(-1 / 6 : ℝ) • octI + (1 / 6 : ℝ) • octOne,
          (1 / 12 : ℝ) • octOne + (1 / 12 : ℝ) • octI,
          (1 / 12 : ℝ) • octI + (1 / 12 : ℝ) • octOne] := by
  rw [pentadF_1_eq, pentadF_2_eq]
  apply albert_ext
  · rw [jordanMul_diag_0, octonionScalar_eq_smul (1 / 2), ← octOne_eq_scalar]
    simp [octDot_smul_left, octDot_smul_right, octDot_zero_left, octDot_unit_basis.1]; norm_num
  · rw [jordanMul_diag_1, octonionScalar_eq_smul (1 / 2), ← octOne_eq_scalar]
    simp [octDot_smul_left, octDot_smul_right, octDot_zero_left, octDot_unit_basis.1]; norm_num
  · rw [jordanMul_diag_2]
    simp [octDot_zero_left]
  · rw [jordanMul_off_0, octonionScalar_eq_smul (1 / 2), ← octOne_eq_scalar]
    simp only [mkAlbert_fst, mkAlbert_snd, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Fin.isValue, octonionConj_zero, octonionMul_zero_left,
      octonionMul_zero_right, add_zero, smul_add, smul_smul]
    norm_num
  · rw [jordanMul_off_1, octonionScalar_eq_smul (1 / 2), ← octOne_eq_scalar]
    simp only [mkAlbert_fst, mkAlbert_snd, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Fin.isValue, octonionMul_zero_right, octonionMul_smul_left,
      octonionMul_smul_right, octonionMul_one_left, smul_zero, add_zero, smul_add, smul_smul]
    norm_num
  · rw [jordanMul_off_2, octonionScalar_eq_smul (1 / 2), ← octOne_eq_scalar]
    simp only [mkAlbert_fst, mkAlbert_snd, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Fin.isValue, octonionMul_zero_right, octonionConj_smul, octonionConj_one,
      octonionMul_smul_left, octonionMul_smul_right, octonionMul_one_left, smul_zero, add_zero,
      smul_add, smul_smul]
    norm_num

private theorem jordanMul_pentad_13 :
    jordanMul (pentadF 1) (pentadF 3) =
      mkAlbert ![1 / 4, 1 / 4, 0] ![(1 / 4 : ℝ) • octOne - (1 / 4 : ℝ) • octJ, 0, 0] := by
  rw [pentadF_1_eq, pentadF_3_eq]
  apply albert_ext
  · rw [jordanMul_diag_0, octonionScalar_eq_smul (1 / 2), ← octOne_eq_scalar]
    simp [octDot_smul_left, octDot_smul_right, octDot_zero_left, octDot_unit_basis.2.1]; norm_num
  · rw [jordanMul_diag_1, octonionScalar_eq_smul (1 / 2), ← octOne_eq_scalar]
    simp [octDot_smul_left, octDot_smul_right, octDot_zero_left, octDot_unit_basis.2.1]; norm_num
  · rw [jordanMul_diag_2]
    simp [octDot_zero_left]
  · rw [jordanMul_off_0, octonionScalar_eq_smul (1 / 2), ← octOne_eq_scalar]
    simp only [mkAlbert_fst, mkAlbert_snd, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Fin.isValue, octonionConj_zero, octonionMul_zero_right, add_zero,
      smul_add, smul_smul, sub_eq_add_neg]
    norm_num; abel
  · simp [jordanMul_off_1, octonionMul_zero_right]
  · simp [jordanMul_off_2, octonionMul_zero_right]

private theorem jordanMul_pentad_14 :
    jordanMul (pentadF 1) (pentadF 4) =
      mkAlbert ![1 / 4, 1 / 4, 0] ![(1 / 4 : ℝ) • octOne - (1 / 4 : ℝ) • octL, 0, 0] := by
  rw [pentadF_1_eq, pentadF_4_eq]
  apply albert_ext
  · rw [jordanMul_diag_0, octonionScalar_eq_smul (1 / 2), ← octOne_eq_scalar]
    simp [octDot_smul_left, octDot_smul_right, octDot_zero_left, octDot_unit_basis.2.2.2.1]; norm_num
  · rw [jordanMul_diag_1, octonionScalar_eq_smul (1 / 2), ← octOne_eq_scalar]
    simp [octDot_smul_left, octDot_smul_right, octDot_zero_left, octDot_unit_basis.2.2.2.1]; norm_num
  · rw [jordanMul_diag_2]
    simp [octDot_zero_left]
  · rw [jordanMul_off_0, octonionScalar_eq_smul (1 / 2), ← octOne_eq_scalar]
    simp only [mkAlbert_fst, mkAlbert_snd, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Fin.isValue, octonionConj_zero, octonionMul_zero_right, add_zero,
      smul_add, smul_smul, sub_eq_add_neg]
    norm_num; abel
  · simp [jordanMul_off_1, octonionMul_zero_right]
  · simp [jordanMul_off_2, octonionMul_zero_right]

private theorem jordanMul_pentad_23 :
    jordanMul (pentadF 2) (pentadF 3) =
      mkAlbert ![1 / 6, 1 / 6, 0]
        ![(-1 / 6 : ℝ) • octJ - (1 / 6 : ℝ) • octI,
          (1 / 12 : ℝ) • octOne + (1 / 12 : ℝ) • octK,
          (1 / 12 : ℝ) • octI + (1 / 12 : ℝ) • octJ] := by
  rw [pentadF_2_eq, pentadF_3_eq]
  apply albert_ext
  · rw [jordanMul_diag_0]
    simp [octDot_smul_left, octDot_smul_right, octDot_zero_right, octDot_unit_basis.2.2.2.2.1]
    norm_num
  · rw [jordanMul_diag_1]
    simp [octDot_smul_left, octDot_smul_right, octDot_zero_right, octDot_unit_basis.2.2.2.2.1]
    norm_num
  · rw [jordanMul_diag_2]
    simp [octDot_zero_right]
  · rw [jordanMul_off_0]
    simp only [mkAlbert_fst, mkAlbert_snd, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Fin.isValue, octonionConj_zero, octonionMul_zero_left,
      octonionMul_zero_right, add_zero, smul_add, smul_smul, sub_eq_add_neg]
    norm_num
  · rw [jordanMul_off_1]
    simp only [mkAlbert_fst, mkAlbert_snd, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Fin.isValue, octonionMul_zero_right, octonionMul_smul_left,
      octonionMul_smul_right, octMul_J_I, smul_zero, add_zero, zero_add, smul_add, smul_neg,
      smul_smul]
    norm_num
  · rw [jordanMul_off_2]
    simp only [mkAlbert_fst, mkAlbert_snd, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Fin.isValue, octonionMul_zero_right, octonionConj_smul, octonionConj_J,
      octonionMul_smul_right, octonionMul_one_right, smul_zero, add_zero, smul_add, smul_neg,
      smul_smul]
    norm_num

private theorem jordanMul_pentad_24 :
    jordanMul (pentadF 2) (pentadF 4) =
      mkAlbert ![1 / 6, 1 / 6, 0]
        ![(-1 / 6 : ℝ) • octL - (1 / 6 : ℝ) • octI,
          (1 / 12 : ℝ) • octOne + (1 / 12 : ℝ) • octS,
          (1 / 12 : ℝ) • octI + (1 / 12 : ℝ) • octL] := by
  rw [pentadF_2_eq, pentadF_4_eq]
  apply albert_ext
  · rw [jordanMul_diag_0]
    simp [octDot_smul_left, octDot_smul_right, octDot_zero_right, octDot_unit_basis.2.2.2.2.2.2.1]
    norm_num
  · rw [jordanMul_diag_1]
    simp [octDot_smul_left, octDot_smul_right, octDot_zero_right, octDot_unit_basis.2.2.2.2.2.2.1]
    norm_num
  · rw [jordanMul_diag_2]
    simp [octDot_zero_right]
  · rw [jordanMul_off_0]
    simp only [mkAlbert_fst, mkAlbert_snd, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Fin.isValue, octonionConj_zero, octonionMul_zero_left,
      octonionMul_zero_right, add_zero, smul_add, smul_smul, sub_eq_add_neg]
    norm_num
  · rw [jordanMul_off_1]
    simp only [mkAlbert_fst, mkAlbert_snd, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Fin.isValue, octonionMul_zero_right, octonionMul_smul_left,
      octonionMul_smul_right, octMul_L_I, smul_zero, add_zero, zero_add, smul_add, smul_neg,
      smul_smul]
    norm_num
  · rw [jordanMul_off_2]
    simp only [mkAlbert_fst, mkAlbert_snd, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Fin.isValue, octonionMul_zero_right, octonionConj_smul, octonionConj_L,
      octonionMul_smul_right, octonionMul_one_right, smul_zero, add_zero, smul_add, smul_neg,
      smul_smul]
    norm_num

private theorem jordanMul_pentad_34 :
    jordanMul (pentadF 3) (pentadF 4) =
      mkAlbert ![1 / 4, 1 / 4, 0] ![(-1 / 4 : ℝ) • octJ - (1 / 4 : ℝ) • octL, 0, 0] := by
  rw [pentadF_3_eq, pentadF_4_eq]
  apply albert_ext
  · rw [jordanMul_diag_0]
    simp [octDot_smul_left, octDot_smul_right, octDot_zero_left,
      octDot_unit_basis.2.2.2.2.2.2.2.2.1]; norm_num
  · rw [jordanMul_diag_1]
    simp [octDot_smul_left, octDot_smul_right, octDot_zero_left,
      octDot_unit_basis.2.2.2.2.2.2.2.2.1]; norm_num
  · rw [jordanMul_diag_2]
    simp [octDot_zero_left]
  · rw [jordanMul_off_0]
    simp only [mkAlbert_fst, mkAlbert_snd, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Fin.isValue, octonionConj_zero, octonionMul_zero_right, add_zero,
      smul_add, smul_smul, sub_eq_add_neg]
    norm_num; abel
  · simp [jordanMul_off_1, octonionMul_zero_right]
  · simp [jordanMul_off_2, octonionMul_zero_right]

theorem pentadDrop_fourPointInvariant_eq_zero (k : Fin 5) :
    fourPointInvariant (pentadDrop k) = 0 := by
  unfold fourPointInvariant fpOverlap fpTriangle fpOmega1 fpOmega2 fpOmega3
    fpDoublePair1 fpDoublePair2 fpDoublePair3 fourPointOmegaPoly
  fin_cases k <;>
    (dsimp
     try rw [pentadDrop_0_0, pentadDrop_0_1, pentadDrop_0_2, pentadDrop_0_3]
     try rw [pentadDrop_1_0, pentadDrop_1_1, pentadDrop_1_2, pentadDrop_1_3]
     try rw [pentadDrop_2_0, pentadDrop_2_1, pentadDrop_2_2, pentadDrop_2_3]
     try rw [pentadDrop_3_0, pentadDrop_3_1, pentadDrop_3_2, pentadDrop_3_3]
     try rw [pentadDrop_4_0, pentadDrop_4_1, pentadDrop_4_2, pentadDrop_4_3]
     try rw [jordanMul_pentad_01]
     try rw [jordanMul_pentad_02]
     try rw [jordanMul_pentad_03]
     try rw [jordanMul_pentad_04]
     try rw [jordanMul_pentad_12]
     try rw [jordanMul_pentad_13]
     try rw [jordanMul_pentad_14]
     try rw [jordanMul_pentad_23]
     try rw [jordanMul_pentad_24]
     try rw [jordanMul_pentad_34]
     try rw [pentadF_0_eq]
     try rw [pentadF_1_eq]
     try rw [pentadF_2_eq]
     try rw [pentadF_3_eq]
     try rw [pentadF_4_eq]
     simp only [tracePairing_eq_coords, diagAtom_fst, diagAtom_snd, mkAlbert_fst, mkAlbert_snd,
       Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue,
       octDot_add_left, octDot_add_right,
       octDot_sub_left, octDot_sub_right, octDot_smul_left, octDot_smul_right, octDot_zero_left,
       octDot_zero_right, octDot_self, octNormSq_zero]
     simp only [octDot_eq_coords]
     simp [octOne, octonionScalar, octI, octJ, octL]
     norm_num)

theorem pentadDrop_not_generatesAlbert (k : Fin 5) :
    ¬ GeneratesAlbert (pentadDrop k) := by
  intro hgen
  rw [generatesAlbert_iff_generatedSubalgebra_eq_top] at hgen
  have hfin := congrArg (fun B : NativeJordanSubalgebra => Module.finrank ℝ B.carrier) hgen
  rw [pentadDrop_generated_finrank k, ← H3Subalgebra_O_eq_top, finrank_H3Subalgebra .O] at hfin
  fin_cases k <;> simp at hfin

/-! ## Section 2: `thm:pentad` (a)–(b) and `quaternionic_c6_representation` -/

def IsComplexRankTwoProjection6 (P : HermitianEmbeddingMatrix 6) : Prop :=
  P.IsHermitian ∧ P * P = P ∧ Matrix.trace P = 2 ∧
  ∃ c₀ c₁ : Fin 6 → ℂ,
    (∑ a, star (c₀ a) * c₀ a = 1) ∧ (∑ a, star (c₁ a) * c₁ a = 1) ∧
    (∑ a, star (c₀ a) * c₁ a = 0) ∧
    ∀ a b, P a b = c₀ a * star (c₀ b) + c₁ a * star (c₁ b)

theorem quaternionic_c6_representation {n : ℕ} (Q : QuaternionicWindow)
    (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i)) (hpQ : ∀ i, p i ∈ Q.subalgebra.carrier)
    (ρ : Albert) (hρ : IsDensity ρ) :
    ∃ (M : AlgebraicProjectiveData (Fin n) (HermitianEmbeddingMatrix 6))
      (σ : HermitianEmbeddingMatrix 6),
      AlgebraicMomentBinding M ∧
      IsEmbeddingDensity 6 σ ∧
      (∀ X, M.state X = (Matrix.trace (σ * X)).re) ∧
      (∀ i, IsComplexRankTwoProjection6 (M.projection i)) ∧
      M.Matches p ρ := by
  obtain ⟨σ, hσ_dens, hstats⟩ :=
    suppliedEmbedding_scaled_state_transport Q.subalgebra 6 (symplecticQuatEmbed Q) 2 (by norm_num)
      (symplecticQuatEmbed_tracePairing Q) ρ hρ
  let P : Fin n → HermitianEmbeddingMatrix 6 := fun i =>
    (symplecticQuatEmbed Q).map ⟨p i, hpQ i⟩
  have hP_herm : ∀ i, (P i).IsHermitian := fun i => (symplecticQuatEmbed Q).hermitian ⟨p i, hpQ i⟩
  have hP_id : ∀ i, P i * P i = P i := fun i => by
    have hj := (symplecticQuatEmbed Q).jordan ⟨p i, hpQ i⟩ ⟨p i, hpQ i⟩
    have hp1 : (⟨jordanMul (p i) (p i), Q.subalgebra.product_mem _ (hpQ i) _ (hpQ i)⟩ :
        Q.subalgebra.carrier) = ⟨p i, hpQ i⟩ := Subtype.ext (hp i).1
    rw [hp1] at hj
    have h2 : (1 / 2 : ℝ) • (P i * P i + P i * P i) = P i * P i := by module
    change P i = (1 / 2 : ℝ) • (P i * P i + P i * P i) at hj
    rw [h2] at hj
    exact hj.symm
  have hP_tr : ∀ i, Matrix.trace (P i) = 2 := fun i => by
    have hre : (Matrix.trace (P i)).re = 2 := by
      have h1 := symplecticQuatEmbed_tracePairing Q ⟨p i, hpQ i⟩ ⟨albertUnit, Q.subalgebra.unit_mem⟩
      rw [(symplecticQuatEmbed Q).unit, Matrix.mul_one, tracePairing_unit_right_local,
        (hp i).2, mul_one] at h1
      exact h1
    have him : (Matrix.trace (P i)).im = 0 := by
      rw [Matrix.trace]
      have him_sum : ∀ s : Finset (Fin 6),
          (∑ k ∈ s, (P i).diag k).im = ∑ k ∈ s, (P i k k).im := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp
        | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Complex.add_im, ih]; rfl
      rw [him_sum Finset.univ]
      refine Finset.sum_eq_zero fun k _ => ?_
      have hk := congrArg Complex.im (congrFun (congrFun (hP_herm i).eq k) k)
      simp [Matrix.conjTranspose_apply] at hk
      linarith
    exact Complex.ext hre him
  let st : HermitianEmbeddingMatrix 6 →ₗ[ℝ] ℝ :=
    { toFun := fun X => (Matrix.trace (σ * X)).re
      map_add' := fun X Y => by rw [mul_add, Matrix.trace_add, Complex.add_re]
      map_smul' := fun r X => by
        rw [Algebra.mul_smul_comm, Matrix.trace_smul, Complex.real_smul, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, RingHom.id_apply, smul_eq_mul] }
  let M : AlgebraicProjectiveData (Fin n) (HermitianEmbeddingMatrix 6) :=
    { projection := P
      idempotent := hP_id
      selfAdjoint := fun i => (hP_herm i).eq
      state := st
      state_unit := by
        change (Matrix.trace (σ * 1)).re = 1
        rw [Matrix.mul_one, hσ_dens.2, Complex.one_re]
      state_star := fun X => by
        change (Matrix.trace (σ * star X)).re = (Matrix.trace (σ * X)).re
        have h1 : Matrix.trace (σ * star X) = star (Matrix.trace (σ * X)) := by
          rw [Matrix.star_eq_conjTranspose, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
            hσ_dens.1.isHermitian.eq, Matrix.trace_mul_comm]
        rw [h1, Complex.star_def, Complex.conj_re]
      state_positive := fun X => trace_psd_mul_sq_nonneg hσ_dens.1 X }
  refine ⟨M, σ, algebraicMomentBinding M, hσ_dens, fun _ => rfl, fun i => ?_, fun w => ?_⟩
  · obtain ⟨cols, hnorm, horth, hsum⟩ :=
      hermitian_idempotent_spectral_rank (P i) (hP_herm i) (hP_id i) (hP_tr i)
    refine ⟨hP_herm i, hP_id i, hP_tr i, cols 0, cols 1, hnorm 0, hnorm 1,
      horth 0 1 (by decide), fun a b => ?_⟩
    dsimp only [M]
    rw [hsum a b, Fin.sum_univ_two]
  · exact hstats n p hpQ w

theorem thm_pentad_a (k : Fin 5) (ρ : Albert) (hρ : IsDensity ρ) :
    ∃ (P : Fin 4 → HermitianEmbeddingMatrix 6) (σ : HermitianEmbeddingMatrix 6)
      (M : AlgebraicProjectiveData (Fin 4) (HermitianEmbeddingMatrix 6)),
      (∀ j, IsComplexRankTwoProjection6 (P j)) ∧
      IsEmbeddingDensity 6 σ ∧
      M.projection = P ∧
      (∀ X, M.state X = (Matrix.trace (σ * X)).re) ∧
      AlgebraicMomentBinding M ∧
      M.Matches (pentadDrop k) ρ := by
  obtain ⟨Q, hQ⟩ := pentadDrop_in_quaternionicWindow k
  obtain ⟨M, σ, hM, hσ, hst, hproj, hmatch⟩ :=
    quaternionic_c6_representation Q (pentadDrop k) (fun j => pentadF_isAtom _) hQ ρ hρ
  exact ⟨M.projection, σ, M, hproj, hσ, rfl, hst, hM, hmatch⟩

theorem thm_pentad_b_separator (hsep : AlbertUniformSeparationContract 5) :
    UniformMomentSeparator pentadF nativeDensitySet :=
  hsep.all_states pentadF pentadF_isAtom pentadF_generatesAlbert

theorem thm_pentad_b_no_match (hsep : AlbertUniformSeparationContract 5)
    {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData (Fin 5) A) (hM : AlgebraicMomentBinding M)
    (ρ : Albert) (hρ : IsDensity ρ) :
    ¬ M.Matches pentadF ρ := by
  intro hmatch
  obtain ⟨_L, c, γ, hγ, _hL, hpos, hneg⟩ := thm_pentad_b_separator hsep
  have hm_nonneg := hpos (momentsOfProjectiveData M) hM.admissible
  have hm_eq : c.evaluate (momentWordProbability (momentsOfProjectiveData M)) =
      c.evaluate (nativeWordProbability pentadF ρ) := by
    unfold FiniteRealWordFunctional.evaluate
    congr 1
    refine List.map_congr_left fun t _ => ?_
    rw [(hM.probabilities t.2).trans (hmatch t.2)]
  have hρ_neg := hneg ρ hρ
  linarith

/-! ## Section 3: Irredundant Generating Sets and `prop:arity` -/

section Section3
open Classical

private theorem jordanSubalgebraIso_symm_maps_atom {k : CDLevel} {B : NativeJordanSubalgebra}
    (ψ : JordanSubalgebraIso (H3Subalgebra k) B) (y : B.carrier) (hy : IsAtom y.1) :
    IsAtom (ψ.toLinearEquiv.symm y).1 := by
  let xsub := ψ.toLinearEquiv.symm y
  let x := xsub.1
  have hx_val : (ψ.toLinearEquiv xsub).1 = y.1 :=
    congrArg Subtype.val (ψ.toLinearEquiv.apply_symm_apply y)
  have hx_id : jordanMul x x = x := by
    have hmul : ψ.toLinearEquiv ⟨jordanMul x x, (H3Subalgebra k).product_mem x xsub.2 x xsub.2⟩ = y := by
      rw [ψ.map_jordan xsub xsub]
      apply Subtype.ext
      change jordanMul (ψ.toLinearEquiv xsub).1 (ψ.toLinearEquiv xsub).1 = y.1
      rw [hx_val, hy.1]
    have h := congrArg (fun z => (ψ.toLinearEquiv.symm z).1) hmul
    simpa [xsub, x] using h
  have hx_ne0 : x ≠ 0 := by
    intro h0
    have hxsub0 : xsub = 0 := Subtype.ext h0
    have hy0 : y = 0 := by
      have h := congrArg ψ.toLinearEquiv hxsub0
      rw [map_zero, ψ.toLinearEquiv.apply_symm_apply] at h
      exact h
    have hytr := hy.2
    have htr0 : albertTrace 0 = 0 := by simp [albertTrace, albert_zero_fst]
    rw [congrArg Subtype.val hy0, Submodule.coe_zero, htr0] at hytr
    norm_num at hytr
  have hx_ne1 : x ≠ albertUnit := by
    intro h1
    have hxsub1 : xsub = ⟨albertUnit, (H3Subalgebra k).unit_mem⟩ := Subtype.ext h1
    have hy1 : y = ⟨albertUnit, B.unit_mem⟩ := by
      have h := congrArg ψ.toLinearEquiv hxsub1
      rw [ψ.map_unit, ψ.toLinearEquiv.apply_symm_apply] at h
      exact h
    have hytr := hy.2
    have hau : albertTrace albertUnit = 3 := by simp [albertTrace, albertUnit]
    rw [congrArg Subtype.val hy1, hau] at hytr
    norm_num at hytr
  let t : ℝ := albertTrace x
  have htr2 : tracePairing x x = t := by
    unfold tracePairing
    rw [hx_id]
  have hsharp : albertSharp x =
      (1 - t) • x + ((1 / 2 : ℝ) * (t ^ 2 - t)) • albertUnit := by
    rw [albertSharp_eq_jordanMul, hx_id, htr2]
    change x - t • x + ((1 / 2 : ℝ) * (t ^ 2 - t)) • albertUnit = _
    simp only [sub_eq_add_neg, add_smul, one_smul, neg_smul]
  have hjmul : jordanMul x (albertSharp x) = ((1 / 2 : ℝ) * (t - 1) * (t - 2)) • x := by
    rw [hsharp, jordanMul_add_right, jordanMul_smul_right, jordanMul_smul_right,
      hx_id, jordanMul_albertUnit_right, ← add_smul]
    congr 1
    ring
  have hcub : ((1 / 2 : ℝ) * (t - 1) * (t - 2)) • x = albertCubicNorm x • albertUnit := by
    rw [← hjmul, jordanMul_albertSharp]
  have h00 : jordanMul (albertUnit - x) (((1 / 2 : ℝ) * (t - 1) * (t - 2)) • x) = 0 := by
    rw [jordanMul_smul_right, jordanMul_sub_left, jordanMul_albertUnit_left, hx_id, sub_self, smul_zero]
  have h01 : jordanMul (albertUnit - x) (albertCubicNorm x • albertUnit) =
      albertCubicNorm x • (albertUnit - x) := by
    rw [jordanMul_smul_right, jordanMul_albertUnit_right]
  rw [hcub, h01] at h00
  have hcub0 : albertCubicNorm x = 0 := (smul_eq_zero.mp h00).resolve_right (sub_ne_zero.mpr hx_ne1.symm)
  rw [hcub0, zero_smul] at hcub
  have ht_fac : (1 / 2 : ℝ) * (t - 1) * (t - 2) = 0 := (smul_eq_zero.mp hcub).resolve_right hx_ne0
  have ht12 : t = 1 ∨ t = 2 := by
    have hmul0 : (t - 1) * (t - 2) = 0 := by linarith
    rcases mul_eq_zero.mp hmul0 with h1 | h2
    · exact Or.inl (sub_eq_zero.mp h1)
    · exact Or.inr (sub_eq_zero.mp h2)
  rcases ht12 with ht1 | ht2
  · exact ⟨hx_id, ht1⟩
  · exfalso
    let x' : (H3Subalgebra k).carrier :=
      ⟨albertUnit - x, (H3Subalgebra k).carrier.sub_mem (H3Subalgebra k).unit_mem xsub.2⟩
    have hx' : IsAtom x'.1 := by
      constructor
      · change jordanMul (albertUnit - x) (albertUnit - x) = albertUnit - x
        rw [jordanMul_sub_left, jordanMul_sub_right, jordanMul_sub_right,
          jordanMul_albertUnit_left, jordanMul_albertUnit_right,
          jordanMul_albertUnit_left, hx_id]
        abel
      · change albertTrace (albertUnit - x) = 1
        have htr_sub : ∀ u v : Albert, albertTrace (u - v) = albertTrace u - albertTrace v := fun u v => by
          simp [albertTrace, albert_sub_fst, Fin.sum_univ_three]; try ring
        have hau : albertTrace albertUnit = 3 := by simp [albertTrace, albertUnit]
        rw [htr_sub, hau]
        change 3 - t = 1
        linarith
    have hy' : IsAtom (ψ.toLinearEquiv x').1 := iso_maps_atom ψ x' hx'
    have hy'_val : (ψ.toLinearEquiv x').1 = albertUnit - y.1 := by
      have hx'_sub : x' = ⟨albertUnit, (H3Subalgebra k).unit_mem⟩ - xsub := rfl
      rw [hx'_sub, map_sub, Submodule.coe_sub, ψ.map_unit, hx_val]
    have htr' := hy'.2
    rw [hy'_val] at htr'
    have htr_sub : ∀ u v : Albert, albertTrace (u - v) = albertTrace u - albertTrace v := fun u v => by
      simp [albertTrace, albert_sub_fst, Fin.sum_univ_three]; try ring
    have hau : albertTrace albertUnit = 3 := by simp [albertTrace, albertUnit]
    rw [htr_sub, hau, hy.2] at htr'
    norm_num at htr'

private def pullFinset {B₁ B₂ : NativeJordanSubalgebra} (ψ : JordanSubalgebraIso B₁ B₂)
    (T : Finset Albert) (hT : (T : Set Albert) ⊆ B₂.carrier) : Finset Albert :=
  T.attach.image fun p => (ψ.toLinearEquiv.symm ⟨p.1, hT p.2⟩).1

private theorem mem_pullFinset_iff {B₁ B₂ : NativeJordanSubalgebra} (ψ : JordanSubalgebraIso B₁ B₂)
    (T : Finset Albert) (hT : (T : Set Albert) ⊆ B₂.carrier) (x : Albert) :
    x ∈ pullFinset ψ T hT ↔ ∃ y ∈ T, ∃ hy : y ∈ B₂.carrier, (ψ.toLinearEquiv.symm ⟨y, hy⟩).1 = x := by
  simp only [pullFinset, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
  constructor
  · rintro ⟨y, hyT, rfl⟩
    exact ⟨y, hyT, hT hyT, rfl⟩
  · rintro ⟨y, hyT, _hyB, rfl⟩
    exact ⟨y, hyT, rfl⟩

private theorem pullFinset_card {B₁ B₂ : NativeJordanSubalgebra} (ψ : JordanSubalgebraIso B₁ B₂)
    (T : Finset Albert) (hT : (T : Set Albert) ⊆ B₂.carrier) :
    (pullFinset ψ T hT).card = T.card := by
  unfold pullFinset
  rw [Finset.card_image_of_injective _ fun a b hab => by
    have h1 := ψ.toLinearEquiv.symm.injective (Subtype.ext hab)
    exact Subtype.ext (congrArg (fun z : B₂.carrier => (z : Albert)) h1)]
  exact Finset.card_attach

private theorem pullFinset_mem_subalgebra {B₁ B₂ : NativeJordanSubalgebra} (ψ : JordanSubalgebraIso B₁ B₂)
    (T : Finset Albert) (hT : (T : Set Albert) ⊆ B₂.carrier) :
    (pullFinset ψ T hT : Set Albert) ⊆ B₁.carrier := by
  intro x hx
  rw [Finset.mem_coe, mem_pullFinset_iff] at hx
  rcases hx with ⟨y, _hyT, hyB, rfl⟩
  exact (ψ.toLinearEquiv.symm ⟨y, hyB⟩).2

private theorem generatedSubalgebra_iso_pull {B₁ B₂ : NativeJordanSubalgebra}
    (ψ : JordanSubalgebraIso B₁ B₂) (T : Finset Albert) (hT : (T : Set Albert) ⊆ B₂.carrier)
    (y : Albert) (hy : y ∈ B₂.carrier) :
    y ∈ (generatedSubalgebra (T : Set Albert)).carrier ↔
      (ψ.toLinearEquiv.symm ⟨y, hy⟩).1 ∈ (generatedSubalgebra (pullFinset ψ T hT : Set Albert)).carrier := by
  let T' := pullFinset ψ T hT
  let C₂ : NativeJordanSubalgebra :=
    { carrier :=
        { carrier := {z : Albert | ∃ hz : z ∈ B₂.carrier,
            (ψ.toLinearEquiv.symm ⟨z, hz⟩).1 ∈ (generatedSubalgebra (T' : Set Albert)).carrier}
          add_mem' := fun {a b} ⟨ha, ha'⟩ ⟨hb, hb'⟩ =>
            ⟨B₂.carrier.add_mem ha hb, by
              have heq : (⟨a + b, B₂.carrier.add_mem ha hb⟩ : B₂.carrier) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
              rw [heq, map_add, Submodule.coe_add]
              exact (generatedSubalgebra (T' : Set Albert)).carrier.add_mem ha' hb'⟩
          zero_mem' := ⟨B₂.carrier.zero_mem, by
            have heq : (⟨0, B₂.carrier.zero_mem⟩ : B₂.carrier) = 0 := rfl
            rw [heq, map_zero, Submodule.coe_zero]
            exact (generatedSubalgebra (T' : Set Albert)).carrier.zero_mem⟩
          smul_mem' := fun r {a} ⟨ha, ha'⟩ =>
            ⟨B₂.carrier.smul_mem r ha, by
              have heq : (⟨r • a, B₂.carrier.smul_mem r ha⟩ : B₂.carrier) = r • ⟨a, ha⟩ := rfl
              rw [heq, map_smul, Submodule.coe_smul]
              exact (generatedSubalgebra (T' : Set Albert)).carrier.smul_mem r ha'⟩ }
      unit_mem := ⟨B₂.unit_mem, by
        have h := congrArg Subtype.val ψ.symm.map_unit
        exact h ▸ (generatedSubalgebra (T' : Set Albert)).unit_mem⟩
      product_mem := fun a ⟨ha, ha'⟩ b ⟨hb, hb'⟩ =>
        ⟨B₂.product_mem a ha b hb, by
          have h := congrArg Subtype.val (ψ.symm.map_jordan ⟨a, ha⟩ ⟨b, hb⟩)
          exact h ▸ (generatedSubalgebra (T' : Set Albert)).product_mem _ ha' _ hb'⟩ }
  let C₁ : NativeJordanSubalgebra :=
    { carrier :=
        { carrier := {x : Albert | ∃ hx : x ∈ B₁.carrier,
            (ψ.toLinearEquiv ⟨x, hx⟩).1 ∈ (generatedSubalgebra (T : Set Albert)).carrier}
          add_mem' := fun {a b} ⟨ha, ha'⟩ ⟨hb, hb'⟩ =>
            ⟨B₁.carrier.add_mem ha hb, by
              have heq : (⟨a + b, B₁.carrier.add_mem ha hb⟩ : B₁.carrier) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
              rw [heq, map_add, Submodule.coe_add]
              exact (generatedSubalgebra (T : Set Albert)).carrier.add_mem ha' hb'⟩
          zero_mem' := ⟨B₁.carrier.zero_mem, by
            have heq : (⟨0, B₁.carrier.zero_mem⟩ : B₁.carrier) = 0 := rfl
            rw [heq, map_zero, Submodule.coe_zero]
            exact (generatedSubalgebra (T : Set Albert)).carrier.zero_mem⟩
          smul_mem' := fun r {a} ⟨ha, ha'⟩ =>
            ⟨B₁.carrier.smul_mem r ha, by
              have heq : (⟨r • a, B₁.carrier.smul_mem r ha⟩ : B₁.carrier) = r • ⟨a, ha⟩ := rfl
              rw [heq, map_smul, Submodule.coe_smul]
              exact (generatedSubalgebra (T : Set Albert)).carrier.smul_mem r ha'⟩ }
      unit_mem := ⟨B₁.unit_mem, by
        rw [ψ.map_unit]
        exact (generatedSubalgebra (T : Set Albert)).unit_mem⟩
      product_mem := fun a ⟨ha, ha'⟩ b ⟨hb, hb'⟩ =>
        ⟨B₁.product_mem a ha b hb, by
          have h := congrArg Subtype.val (ψ.map_jordan ⟨a, ha⟩ ⟨b, hb⟩)
          exact h ▸ (generatedSubalgebra (T : Set Albert)).product_mem _ ha' _ hb'⟩ }
  have hle2 : (generatedSubalgebra (T : Set Albert)).carrier ≤ C₂.carrier := by
    refine generatedSubalgebra_le (B := C₂) fun z hz => ⟨hT hz, subset_generatedSubalgebra T' ?_⟩
    rw [Finset.mem_coe, mem_pullFinset_iff]
    exact ⟨z, hz, hT hz, rfl⟩
  have hle1 : (generatedSubalgebra (T' : Set Albert)).carrier ≤ C₁.carrier := by
    refine generatedSubalgebra_le (B := C₁) fun x hx => ?_
    rw [Finset.mem_coe, mem_pullFinset_iff] at hx
    rcases hx with ⟨z, hzT, hzB, rfl⟩
    refine ⟨(ψ.toLinearEquiv.symm ⟨z, hzB⟩).2, ?_⟩
    have hsub : (⟨(ψ.toLinearEquiv.symm ⟨z, hzB⟩).1, (ψ.toLinearEquiv.symm ⟨z, hzB⟩).2⟩ : B₁.carrier) =
        ψ.toLinearEquiv.symm ⟨z, hzB⟩ := rfl
    rw [hsub, ψ.toLinearEquiv.apply_symm_apply]
    exact subset_generatedSubalgebra T hzT
  constructor
  · intro hyG
    obtain ⟨hyB, hy'⟩ := hle2 hyG
    have heq : (⟨y, hy⟩ : B₂.carrier) = ⟨y, hyB⟩ := rfl
    rw [heq]
    exact hy'
  · intro hxG
    obtain ⟨hxB, hyG⟩ := hle1 hxG
    have heq : (⟨(ψ.toLinearEquiv.symm ⟨y, hy⟩).1, hxB⟩ : B₁.carrier) = ψ.toLinearEquiv.symm ⟨y, hy⟩ := rfl
    rw [heq, ψ.toLinearEquiv.apply_symm_apply] at hyG
    exact hyG

private theorem pullFinset_isIrredundant {k : CDLevel} {B : NativeJordanSubalgebra}
    (ψ : JordanSubalgebraIso (H3Subalgebra k) B) (T : Finset Albert)
    (hT_sub : (T : Set Albert) ⊆ B.carrier) (hT_irr : IsIrredundant T) :
    IsIrredundant (pullFinset ψ T hT_sub) := by
  constructor
  · intro x hx
    rw [mem_pullFinset_iff] at hx
    rcases hx with ⟨y, hyT, hyB, rfl⟩
    exact jordanSubalgebraIso_symm_maps_atom ψ ⟨y, hyB⟩ (hT_irr.1 y hyT)
  · intro x hx hxgen
    rw [mem_pullFinset_iff] at hx
    rcases hx with ⟨y, hyT, hyB, rfl⟩
    have h_er_sub : (T.erase y : Set Albert) ⊆ B.carrier := fun z hz => hT_sub (Finset.mem_of_mem_erase hz)
    have h_erase : (pullFinset ψ (T.erase y) h_er_sub : Set Albert) =
        ((pullFinset ψ T hT_sub).erase ((ψ.toLinearEquiv.symm ⟨y, hyB⟩).1) : Set Albert) := by
      ext w
      rw [Finset.mem_coe, Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff,
        mem_pullFinset_iff, mem_pullFinset_iff]
      constructor
      · rintro ⟨z, hz_er, hzB, rfl⟩
        obtain ⟨hzy, hzT⟩ := Finset.mem_erase.mp hz_er
        refine ⟨⟨z, hzT, hzB, rfl⟩, fun heq => hzy ?_⟩
        have hsub := ψ.toLinearEquiv.symm.injective (Subtype.ext heq)
        exact congrArg Subtype.val hsub
      · rintro ⟨⟨z, hzT, hzB, rfl⟩, hw_ne⟩
        refine ⟨z, Finset.mem_erase.mpr ⟨fun hzy => hw_ne ?_, hzT⟩, hzB, rfl⟩
        subst hzy; rfl
    rw [← h_erase] at hxgen
    rw [← generatedSubalgebra_iso_pull ψ (T.erase y) h_er_sub y hyB] at hxgen
    exact hT_irr.2 y hyT hxgen

private theorem pullFinset_nonline {k k₀ : CDLevel} {B : NativeJordanSubalgebra}
    (hBk : B.carrier ≤ (H3Subalgebra k₀).carrier)
    (ψ : JordanSubalgebraIso (H3Subalgebra k) B) (T : Finset Albert)
    (hT_sub : (T : Set Albert) ⊆ B.carrier)
    (hnonline : ¬ ∃ q : Albert, ∃ hq : IsAtom q, q ∈ (H3Subalgebra k₀).carrier ∧
      (T : Set Albert) ⊆ (lineSubalgebra q hq).carrier) :
    ¬ ∃ q' : Albert, ∃ hq' : IsAtom q', q' ∈ (H3Subalgebra k).carrier ∧
      (pullFinset ψ T hT_sub : Set Albert) ⊆ (lineSubalgebra q' hq').carrier := by
  rintro ⟨q', hq', hq'K, hline'⟩
  apply hnonline
  let q := (ψ.toLinearEquiv ⟨q', hq'K⟩).1
  have hq : IsAtom q := iso_maps_atom ψ ⟨q', hq'K⟩ hq'
  have hqB : q ∈ (H3Subalgebra k₀).carrier := hBk (ψ.toLinearEquiv ⟨q', hq'K⟩).2
  refine ⟨q, hq, hqB, fun y hyT => ?_⟩
  change y ∈ (lineSubalgebra q hq).carrier
  rw [mem_lineSubalgebra_iff_idem]
  let x := ψ.toLinearEquiv.symm ⟨y, hT_sub hyT⟩
  have hx_mem : x.1 ∈ (pullFinset ψ T hT_sub : Set Albert) := by
    rw [Finset.mem_coe, mem_pullFinset_iff]
    exact ⟨y, hyT, hT_sub hyT, rfl⟩
  have hline_x : jordanMul q' (jordanMul q' x.1) = jordanMul q' x.1 :=
    (mem_lineSubalgebra_iff_idem q' hq' x.1).mp (hline' hx_mem)
  have hxy : (ψ.toLinearEquiv x).1 = y :=
    congrArg (fun z : B.carrier => z.1) (ψ.toLinearEquiv.apply_symm_apply ⟨y, hT_sub hyT⟩)
  have hm1 : (ψ.toLinearEquiv ⟨jordanMul q' x.1,
      (H3Subalgebra k).product_mem _ hq'K _ x.2⟩).1 = jordanMul q (ψ.toLinearEquiv x).1 :=
    congrArg (fun z : B.carrier => z.1) (ψ.map_jordan ⟨q', hq'K⟩ x)
  have h1 : (ψ.toLinearEquiv ⟨jordanMul q' x.1,
      (H3Subalgebra k).product_mem _ hq'K _ x.2⟩).1 = jordanMul q y := by
    rw [hm1, hxy]
  have hm2 : (ψ.toLinearEquiv ⟨jordanMul q' (jordanMul q' x.1),
      (H3Subalgebra k).product_mem _ hq'K _ ((H3Subalgebra k).product_mem _ hq'K _ x.2)⟩).1 =
      jordanMul q (ψ.toLinearEquiv ⟨jordanMul q' x.1,
        (H3Subalgebra k).product_mem _ hq'K _ x.2⟩).1 :=
    congrArg (fun z : B.carrier => z.1)
      (ψ.map_jordan ⟨q', hq'K⟩ ⟨jordanMul q' x.1, (H3Subalgebra k).product_mem _ hq'K _ x.2⟩)
  have heq : (ψ.toLinearEquiv ⟨jordanMul q' (jordanMul q' x.1),
      (H3Subalgebra k).product_mem _ hq'K _ ((H3Subalgebra k).product_mem _ hq'K _ x.2)⟩).1 =
      (ψ.toLinearEquiv ⟨jordanMul q' x.1, (H3Subalgebra k).product_mem _ hq'K _ x.2⟩).1 :=
    congrArg (fun z : (H3Subalgebra k).carrier => (ψ.toLinearEquiv z).1) (Subtype.ext hline_x)
  calc jordanMul q (jordanMul q y)
      = jordanMul q (ψ.toLinearEquiv ⟨jordanMul q' x.1,
          (H3Subalgebra k).product_mem _ hq'K _ x.2⟩).1 := by rw [h1]
    _ = (ψ.toLinearEquiv ⟨jordanMul q' (jordanMul q' x.1),
          (H3Subalgebra k).product_mem _ hq'K _ ((H3Subalgebra k).product_mem _ hq'K _ x.2)⟩).1 :=
        hm2.symm
    _ = (ψ.toLinearEquiv ⟨jordanMul q' x.1, (H3Subalgebra k).product_mem _ hq'K _ x.2⟩).1 := heq
    _ = jordanMul q y := h1

def arityBound : CDLevel → ℕ
  | .R => 3
  | .C => 4
  | .H => 4
  | .O => 5

/-! ### `prop:arity` lower bound witnesses (`3, 4, 4, 5`) -/

private theorem mem_unitaryConjSubalgebraC_H3R_of_matrix
    (U : Matrix.unitaryGroup (Fin 3) ℂ) (M : selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ))
    (hreal : ∀ i j : Fin 3, ((star U.1 * M.1 * U.1) i j).im = 0) :
    (assocHermEquiv assocCD_C M).1 ∈ (unitaryConjSubalgebraC U (H3Subalgebra .R)).carrier := by
  have hxC : (assocHermEquiv assocCD_C M).1 ∈ (H3Subalgebra .C).carrier :=
    (assocHermEquiv assocCD_C M).2
  refine ⟨hxC, ?_⟩
  let h1 : star U.1 * U.1 = 1 := Matrix.mem_unitaryGroup_iff'.mp U.prop
  let h2 : U.1 * star U.1 = 1 := Matrix.mem_unitaryGroup_iff.mp U.prop
  let ψ := assocCD_unitaryIso assocCD_C U.1 h1 h2
  change (ψ.toLinearEquiv (assocHermEquiv assocCD_C M)).1 ∈ (H3Subalgebra .R).carrier
  have heq : (ψ.toLinearEquiv (assocHermEquiv assocCD_C M)).1 =
      assocMatToAlbert assocCD_C (star U.1 * M.1 * U.1) := by
    have hN := (assocHermEquiv assocCD_C).symm_apply_apply M
    exact congrArg (fun X : selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ) =>
      assocMatToAlbert assocCD_C (star U.1 * X.1 * U.1)) hN
  rw [heq]
  have him0 : ∀ a b : Fin 3,
      complexToOctonion ((star U.1 * M.1 * U.1) a b) ∈ (octSubalgebraOfLevel .R).carrier := by
    intro a b
    have hre : (star U.1 * M.1 * U.1) a b = (((star U.1 * M.1 * U.1) a b).re : ℂ) :=
      Complex.ext rfl (by simp [hreal a b])
    rw [hre]
    change octonionScalar (((star U.1 * M.1 * U.1) a b).re) ∈ octRealSubalgebra.carrier
    rw [octonionScalar_eq_smul, ← octOne_eq_scalar]
    exact octRealSubalgebra.carrier.smul_mem _ octRealSubalgebra.one_mem
  exact ⟨him0 0 1, him0 0 2, him0 1 2⟩

private theorem unitaryConjSubalgebraC_H3R_finrank (U : Matrix.unitaryGroup (Fin 3) ℂ) :
    Module.finrank ℝ (unitaryConjSubalgebraC U (H3Subalgebra .R)).carrier = 6 := by
  let h1 : star U.1 * U.1 = 1 := Matrix.mem_unitaryGroup_iff'.mp U.prop
  let h2 : U.1 * star U.1 = 1 := Matrix.mem_unitaryGroup_iff.mp U.prop
  let ψ := assocCD_unitaryIso assocCD_C U.1 h1 h2
  have hRC : (H3Subalgebra .R).carrier ≤ (H3Subalgebra .C).carrier :=
    H3Subalgebra_mono (by decide)
  let eqv : (unitaryConjSubalgebraC U (H3Subalgebra .R)).carrier ≃ₗ[ℝ] (H3Subalgebra .R).carrier :=
    { toFun := fun x =>
        let z : (jordanSubalgebraH3 assocCD_C.subalgebra).carrier := ⟨x.1, x.2.1⟩
        ⟨(ψ.toLinearEquiv z).1, x.2.2⟩
      invFun := fun b =>
        let y := ψ.toLinearEquiv.symm ⟨b.1, hRC b.2⟩
        ⟨y.1, y.2, by
          change (ψ.toLinearEquiv y).1 ∈ (H3Subalgebra .R).carrier
          rw [ψ.toLinearEquiv.apply_symm_apply]
          exact b.2⟩
      left_inv := fun x => Subtype.ext (by
        let z : (jordanSubalgebraH3 assocCD_C.subalgebra).carrier := ⟨x.1, x.2.1⟩
        exact congrArg (fun u : (jordanSubalgebraH3 assocCD_C.subalgebra).carrier => u.1)
          (ψ.toLinearEquiv.symm_apply_apply z))
      right_inv := fun b => Subtype.ext (by
        change (ψ.toLinearEquiv (ψ.toLinearEquiv.symm ⟨b.1, hRC b.2⟩)).1 = b.1
        rw [ψ.toLinearEquiv.apply_symm_apply])
      map_add' := fun x y => Subtype.ext (by
        let zx : (jordanSubalgebraH3 assocCD_C.subalgebra).carrier := ⟨x.1, x.2.1⟩
        let zy : (jordanSubalgebraH3 assocCD_C.subalgebra).carrier := ⟨y.1, y.2.1⟩
        have hsum : (⟨(x + y).1, (x + y).2.1⟩ : (jordanSubalgebraH3 assocCD_C.subalgebra).carrier) =
            zx + zy := rfl
        change (ψ.toLinearEquiv ⟨(x + y).1, (x + y).2.1⟩).1 = _
        rw [hsum, map_add]; rfl)
      map_smul' := fun r x => Subtype.ext (by
        let zx : (jordanSubalgebraH3 assocCD_C.subalgebra).carrier := ⟨x.1, x.2.1⟩
        have hsm : (⟨(r • x).1, (r • x).2.1⟩ : (jordanSubalgebraH3 assocCD_C.subalgebra).carrier) =
            r • zx := rfl
        change (ψ.toLinearEquiv ⟨(r • x).1, (r • x).2.1⟩).1 = _
        rw [hsm, map_smul]; rfl) }
  rw [eqv.finrank_eq, finrank_H3Subalgebra .R]

private theorem not_mem_of_erase_le_lt_finrank {k : CDLevel}
    (T : Finset Albert) (hgen : generatedSubalgebra (T : Set Albert) = H3Subalgebra k)
    (p : Albert) (B : NativeJordanSubalgebra)
    (hB : (T.erase p : Set Albert) ⊆ B.carrier)
    (hfin : Module.finrank ℝ B.carrier < Module.finrank ℝ (H3Subalgebra k).carrier) :
    p ∉ (generatedSubalgebra (T.erase p : Set Albert)).carrier := by
  have : Module.Finite ℝ Octonion :=
    inferInstanceAs (FiniteDimensional ℝ (Quaternion ℝ × Quaternion ℝ))
  have : Module.Finite ℝ Albert :=
    inferInstanceAs (FiniteDimensional ℝ ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
  intro hp
  have hTB : (T : Set Albert) ⊆ B.carrier := by
    intro x hx
    by_cases hxp : x = p
    · subst hxp; exact generatedSubalgebra_le (B := B) hB hp
    · exact hB (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hxp, hx⟩))
  have hle : (H3Subalgebra k).carrier ≤ B.carrier := by
    rw [← hgen]
    exact generatedSubalgebra_le (B := B) hTB
  have hle_fin := Submodule.finrank_mono hle
  omega

private theorem oct_conj_fst (x : Octonion) : (octonionConj x).1 = star x.1 := rfl
private theorem oct_conj_snd (x : Octonion) : (octonionConj x).2 = -x.2 := rfl

private def octComplexJSubalgebra : OctSubalgebra where
  carrier :=
    { carrier := {x : Octonion | x.1.imI = 0 ∧ x.1.imK = 0 ∧ x.2 = 0}
      add_mem' := fun {a b} ha hb => by
        refine ⟨?_, ?_, ?_⟩ <;> simp [oct_add_fst, oct_add_snd, ha.1, ha.2.1, ha.2.2, hb.1, hb.2.1, hb.2.2]
      zero_mem' := by simp [oct_zero_fst, oct_zero_snd]
      smul_mem' := fun r {a} ha => by
        refine ⟨?_, ?_, ?_⟩ <;> simp [oct_smul_fst, oct_smul_snd, ha.1, ha.2.1, ha.2.2] }
  one_mem := ⟨rfl, rfl, rfl⟩
  conj_mem := fun a ha =>
    ⟨by rw [oct_conj_fst, Quaternion.imI_star, ha.1, neg_zero],
     by rw [oct_conj_fst, Quaternion.imK_star, ha.2.1, neg_zero],
     by rw [oct_conj_snd, ha.2.2, neg_zero]⟩
  mul_mem := fun a ha b hb => by
    have he1 : a.1.imI = 0 := ha.1; have he2 : a.1.imK = 0 := ha.2.1; have he3 : a.2 = 0 := ha.2.2
    have hf1 : b.1.imI = 0 := hb.1; have hf2 : b.1.imK = 0 := hb.2.1; have hf3 : b.2 = 0 := hb.2.2
    change (octonionMul a b).1.imI = 0 ∧ (octonionMul a b).1.imK = 0 ∧ (octonionMul a b).2 = 0
    have hmul1 : (octonionMul a b).1 = a.1 * b.1 := by
      change a.1 * b.1 - star b.2 * a.2 = a.1 * b.1
      rw [he3, hf3, mul_zero, sub_zero]
    have hmul2 : (octonionMul a b).2 = 0 := by
      change b.2 * a.1 + a.2 * star b.1 = 0
      rw [he3, hf3, zero_mul, zero_mul, add_zero]
    rw [hmul1, hmul2]
    exact ⟨by simp [he1, he2, hf1, hf2],
      by simp [he1, he2, hf1, hf2], rfl⟩

private theorem finrank_octComplexJSubalgebra :
    Module.finrank ℝ octComplexJSubalgebra.carrier = 2 := by
  let eqv : octComplexJSubalgebra.carrier ≃ₗ[ℝ] (Fin 2 → ℝ) :=
    { toFun := fun x => ![x.1.1.re, x.1.1.imJ]
      invFun := fun v => ⟨(⟨v 0, 0, v 1, 0⟩, 0), rfl, rfl, rfl⟩
      left_inv := fun ⟨⟨p, q⟩, hp1, hp2, hq⟩ => Subtype.ext (by
        apply Prod.ext
        · apply Quaternion.ext
          · rfl
          · exact hp1.symm
          · rfl
          · exact hp2.symm
        · exact hq.symm)
      right_inv := fun v => by funext i; fin_cases i <;> rfl
      map_add' := fun x y => by funext i; fin_cases i <;> simp [oct_add_fst]
      map_smul' := fun r x => by funext i; fin_cases i <;> simp [oct_smul_fst] }
  rw [eqv.finrank_eq, Module.finrank_fin_fun]

private def octComplexKSubalgebra : OctSubalgebra where
  carrier :=
    { carrier := {x : Octonion | x.1.imI = 0 ∧ x.1.imJ = 0 ∧ x.2 = 0}
      add_mem' := fun {a b} ha hb => by
        refine ⟨?_, ?_, ?_⟩ <;> simp [oct_add_fst, oct_add_snd, ha.1, ha.2.1, ha.2.2, hb.1, hb.2.1, hb.2.2]
      zero_mem' := by simp [oct_zero_fst, oct_zero_snd]
      smul_mem' := fun r {a} ha => by
        refine ⟨?_, ?_, ?_⟩ <;> simp [oct_smul_fst, oct_smul_snd, ha.1, ha.2.1, ha.2.2] }
  one_mem := ⟨rfl, rfl, rfl⟩
  conj_mem := fun a ha =>
    ⟨by rw [oct_conj_fst, Quaternion.imI_star, ha.1, neg_zero],
     by rw [oct_conj_fst, Quaternion.imJ_star, ha.2.1, neg_zero],
     by rw [oct_conj_snd, ha.2.2, neg_zero]⟩
  mul_mem := fun a ha b hb => by
    have he1 : a.1.imI = 0 := ha.1; have he2 : a.1.imJ = 0 := ha.2.1; have he3 : a.2 = 0 := ha.2.2
    have hf1 : b.1.imI = 0 := hb.1; have hf2 : b.1.imJ = 0 := hb.2.1; have hf3 : b.2 = 0 := hb.2.2
    change (octonionMul a b).1.imI = 0 ∧ (octonionMul a b).1.imJ = 0 ∧ (octonionMul a b).2 = 0
    have hmul1 : (octonionMul a b).1 = a.1 * b.1 := by
      change a.1 * b.1 - star b.2 * a.2 = a.1 * b.1
      rw [he3, hf3, mul_zero, sub_zero]
    have hmul2 : (octonionMul a b).2 = 0 := by
      change b.2 * a.1 + a.2 * star b.1 = 0
      rw [he3, hf3, zero_mul, zero_mul, add_zero]
    rw [hmul1, hmul2]
    exact ⟨by simp [he1, he2, hf1, hf2],
      by simp [he1, he2, hf1, hf2], rfl⟩

private theorem finrank_octComplexKSubalgebra :
    Module.finrank ℝ octComplexKSubalgebra.carrier = 2 := by
  let eqv : octComplexKSubalgebra.carrier ≃ₗ[ℝ] (Fin 2 → ℝ) :=
    { toFun := fun x => ![x.1.1.re, x.1.1.imK]
      invFun := fun v => ⟨(⟨v 0, 0, 0, v 1⟩, 0), rfl, rfl, rfl⟩
      left_inv := fun ⟨⟨p, q⟩, hp1, hp2, hq⟩ => Subtype.ext (by
        apply Prod.ext
        · apply Quaternion.ext
          · rfl
          · exact hp1.symm
          · exact hp2.symm
          · rfl
        · exact hq.symm)
      right_inv := fun v => by funext i; fin_cases i <;> rfl
      map_add' := fun x y => by funext i; fin_cases i <;> simp [oct_add_fst]
      map_smul' := fun r x => by funext i; fin_cases i <;> simp [oct_smul_fst] }
  rw [eqv.finrank_eq, Module.finrank_fin_fun]

private def unitaryConjSubalgebraH (U : QuatMatrix3)
    (h1 : star U * U = 1) (h2 : U * star U = 1)
    (B : NativeJordanSubalgebra) : NativeJordanSubalgebra :=
  let ψ : JordanSubalgebraIso (H3Subalgebra .H) (H3Subalgebra .H) :=
    assocCD_unitaryIso assocCD_H U h1 h2
  { carrier :=
      { carrier := {x : Albert | ∃ hx : x ∈ (H3Subalgebra .H).carrier,
          (ψ.toLinearEquiv ⟨x, hx⟩).1 ∈ B.carrier}
        add_mem' := fun {a b} ⟨ha, ha'⟩ ⟨hb, hb'⟩ =>
          ⟨(H3Subalgebra .H).carrier.add_mem ha hb, by
            have heq : (⟨a + b, (H3Subalgebra .H).carrier.add_mem ha hb⟩ : (H3Subalgebra .H).carrier) =
                ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
            rw [heq, map_add, Submodule.coe_add]
            exact B.carrier.add_mem ha' hb'⟩
        zero_mem' := ⟨(H3Subalgebra .H).carrier.zero_mem, by
          have heq : (⟨0, (H3Subalgebra .H).carrier.zero_mem⟩ : (H3Subalgebra .H).carrier) = 0 := rfl
          rw [heq, map_zero, Submodule.coe_zero]
          exact B.carrier.zero_mem⟩
        smul_mem' := fun r {a} ⟨ha, ha'⟩ =>
          ⟨(H3Subalgebra .H).carrier.smul_mem r ha, by
            have heq : (⟨r • a, (H3Subalgebra .H).carrier.smul_mem r ha⟩ : (H3Subalgebra .H).carrier) =
                r • ⟨a, ha⟩ := rfl
            rw [heq, map_smul, Submodule.coe_smul]
            exact B.carrier.smul_mem r ha'⟩ }
    unit_mem := ⟨(H3Subalgebra .H).unit_mem, by
      rw [ψ.map_unit]
      exact B.unit_mem⟩
    product_mem := fun a ⟨ha, ha'⟩ b ⟨hb, hb'⟩ =>
      ⟨(H3Subalgebra .H).product_mem a ha b hb, by
        rw [ψ.map_jordan ⟨a, ha⟩ ⟨b, hb⟩]
        exact B.product_mem _ ha' _ hb'⟩ }

private theorem unitaryConjSubalgebraH_finrank (U : QuatMatrix3)
    (h1 : star U * U = 1) (h2 : U * star U = 1)
    (B : NativeJordanSubalgebra) (hBH : B.carrier ≤ (H3Subalgebra .H).carrier) :
    Module.finrank ℝ (unitaryConjSubalgebraH U h1 h2 B).carrier = Module.finrank ℝ B.carrier := by
  let ψ := assocCD_unitaryIso assocCD_H U h1 h2
  let eqv : (unitaryConjSubalgebraH U h1 h2 B).carrier ≃ₗ[ℝ] B.carrier :=
    { toFun := fun x =>
        let z : (jordanSubalgebraH3 assocCD_H.subalgebra).carrier := ⟨x.1, x.2.1⟩
        ⟨(ψ.toLinearEquiv z).1, x.2.2⟩
      invFun := fun b =>
        let y := ψ.toLinearEquiv.symm ⟨b.1, hBH b.2⟩
        ⟨y.1, y.2, by
          change (ψ.toLinearEquiv y).1 ∈ B.carrier
          rw [ψ.toLinearEquiv.apply_symm_apply]
          exact b.2⟩
      left_inv := fun x => Subtype.ext (by
        let z : (jordanSubalgebraH3 assocCD_H.subalgebra).carrier := ⟨x.1, x.2.1⟩
        exact congrArg (fun u : (jordanSubalgebraH3 assocCD_H.subalgebra).carrier => u.1)
          (ψ.toLinearEquiv.symm_apply_apply z))
      right_inv := fun b => Subtype.ext (by
        change (ψ.toLinearEquiv (ψ.toLinearEquiv.symm ⟨b.1, hBH b.2⟩)).1 = b.1
        rw [ψ.toLinearEquiv.apply_symm_apply])
      map_add' := fun x y => Subtype.ext (by
        let zx : (jordanSubalgebraH3 assocCD_H.subalgebra).carrier := ⟨x.1, x.2.1⟩
        let zy : (jordanSubalgebraH3 assocCD_H.subalgebra).carrier := ⟨y.1, y.2.1⟩
        have hsum : (⟨(x + y).1, (x + y).2.1⟩ : (jordanSubalgebraH3 assocCD_H.subalgebra).carrier) =
            zx + zy := rfl
        change (ψ.toLinearEquiv ⟨(x + y).1, (x + y).2.1⟩).1 = _
        rw [hsum, map_add]; rfl)
      map_smul' := fun r x => Subtype.ext (by
        let zx : (jordanSubalgebraH3 assocCD_H.subalgebra).carrier := ⟨x.1, x.2.1⟩
        have hsm : (⟨(r • x).1, (r • x).2.1⟩ : (jordanSubalgebraH3 assocCD_H.subalgebra).carrier) =
            r • zx := rfl
        change (ψ.toLinearEquiv ⟨(r • x).1, (r • x).2.1⟩).1 = _
        rw [hsm, map_smul]; rfl) }
  exact eqv.finrank_eq

private theorem mem_unitaryConjSubalgebraH_K_of_matrix (U : QuatMatrix3)
    (h1 : star U * U = 1) (h2 : U * star U = 1)
    (M : selfAdjoint QuatMatrix3)
    (hK : ∀ i j : Fin 3, ((star U * M.1 * U) i j).imI = 0 ∧ ((star U * M.1 * U) i j).imJ = 0) :
    (assocHermEquiv assocCD_H M).1 ∈
      (unitaryConjSubalgebraH U h1 h2 (jordanSubalgebraH3 octComplexKSubalgebra)).carrier := by
  refine ⟨(assocHermEquiv assocCD_H M).2, ?_⟩
  let ψ := assocCD_unitaryIso assocCD_H U h1 h2
  change (ψ.toLinearEquiv (assocHermEquiv assocCD_H M)).1 ∈
    (jordanSubalgebraH3 octComplexKSubalgebra).carrier
  have heq : (ψ.toLinearEquiv (assocHermEquiv assocCD_H M)).1 =
      assocMatToAlbert assocCD_H (star U * M.1 * U) := by
    have hN := (assocHermEquiv assocCD_H).symm_apply_apply M
    exact congrArg (fun X : selfAdjoint QuatMatrix3 =>
      assocMatToAlbert assocCD_H (star U * X.1 * U)) hN
  rw [heq]
  have hmem : ∀ a b : Fin 3, quatEmbed1 ((star U * M.1 * U) a b) ∈ octComplexKSubalgebra.carrier := by
    intro a b
    refine ⟨(hK a b).1, (hK a b).2, rfl⟩
  exact ⟨hmem 0 1, hmem 0 2, hmem 1 2⟩

private theorem prop_arity_lower_R :
    ∃ T : Finset Albert, T.card = 3 ∧
      (∀ p ∈ T, IsAtom p ∧ p ∈ (H3Subalgebra .R).carrier) ∧
      IsIrredundant T ∧ generatedSubalgebra (T : Set Albert) = H3Subalgebra .R := by
  let r0 : Albert := diagAtom 0
  let r1 : Albert := (1 / 2 : ℝ) • octDyad ![octOne, octOne, 0]
  let r2 : Albert := (1 / 2 : ℝ) • octDyad ![octOne, 0, octOne]
  have hr1_eq : r1 = mkAlbert ![1 / 2, 1 / 2, 0] ![(1 / 2 : ℝ) • octOne, 0, 0] := by
    apply albert_ext
    · simp [r1, albert_smul_fst, octDyad_fst, octNormSq_one]
    · simp [r1, albert_smul_fst, octDyad_fst, octNormSq_one]
    · simp [r1, albert_smul_fst, octDyad_fst, octNormSq_zero]
    · simp [r1, albert_smul_snd, octDyad_snd_0, octonionConj_one, octonionMul_one_left]
    · simp [r1, albert_smul_snd, octDyad_snd_1, octonionConj_zero, octonionMul_zero_right]
    · simp [r1, albert_smul_snd, octDyad_snd_2, octonionConj_zero, octonionMul_zero_right]
  have hr2_eq : r2 = mkAlbert ![1 / 2, 0, 1 / 2] ![0, (1 / 2 : ℝ) • octOne, 0] := by
    apply albert_ext
    · simp [r2, albert_smul_fst, octDyad_fst, octNormSq_one]
    · simp [r2, albert_smul_fst, octDyad_fst, octNormSq_zero]
    · simp [r2, albert_smul_fst, octDyad_fst, octNormSq_one]
    · simp [r2, albert_smul_snd, octDyad_snd_0, octonionConj_zero, octonionMul_zero_right]
    · simp [r2, albert_smul_snd, octDyad_snd_1, octonionConj_one, octonionMul_one_left]
    · simp [r2, albert_smul_snd, octDyad_snd_2, octonionConj_one, octonionMul_zero_left]
  have hr0_atom : IsAtom r0 := diagAtom_isAtom 0
  have hr1_atom : IsAtom r1 := by
    dsimp only [r1]
    rw [one_div]
    refine isAtom_scaled_octDyad quatEmbed1 quatEmbed1_isQuatEmbedding 2 (by norm_num)
      ![octOne, octOne, 0] ?_ ?_
    · intro k; fin_cases k
      · exact octOne_mem_range_quat quatEmbed1 quatEmbed1_isQuatEmbedding
      · exact octOne_mem_range_quat quatEmbed1 quatEmbed1_isQuatEmbedding
      · exact ⟨0, map_zero _⟩
    · rw [Fin.sum_univ_three]
      change octNormSq octOne + octNormSq octOne + octNormSq 0 = 2
      rw [octNormSq_one, octNormSq_zero]; norm_num
  have hr2_atom : IsAtom r2 := by
    dsimp only [r2]
    rw [one_div]
    refine isAtom_scaled_octDyad quatEmbed1 quatEmbed1_isQuatEmbedding 2 (by norm_num)
      ![octOne, 0, octOne] ?_ ?_
    · intro k; fin_cases k
      · exact octOne_mem_range_quat quatEmbed1 quatEmbed1_isQuatEmbedding
      · exact ⟨0, map_zero _⟩
      · exact octOne_mem_range_quat quatEmbed1 quatEmbed1_isQuatEmbedding
    · rw [Fin.sum_univ_three]
      change octNormSq octOne + octNormSq 0 + octNormSq octOne = 2
      rw [octNormSq_one, octNormSq_zero]; norm_num
  have h1R : octOne ∈ (octSubalgebraOfLevel .R).carrier := (octSubalgebraOfLevel .R).one_mem
  have hr0_mem : r0 ∈ (H3Subalgebra .R).carrier := diagAtom_mem_H3Subalgebra .R 0
  have hr1_mem : r1 ∈ (H3Subalgebra .R).carrier := by
    rw [hr1_eq]
    exact ⟨(octSubalgebraOfLevel .R).carrier.smul_mem _ h1R,
      (octSubalgebraOfLevel .R).carrier.zero_mem, (octSubalgebraOfLevel .R).carrier.zero_mem⟩
  have hr2_mem : r2 ∈ (H3Subalgebra .R).carrier := by
    rw [hr2_eq]
    exact ⟨(octSubalgebraOfLevel .R).carrier.zero_mem,
      (octSubalgebraOfLevel .R).carrier.smul_mem _ h1R, (octSubalgebraOfLevel .R).carrier.zero_mem⟩
  have h01_ne : r0 ≠ r1 := fun h => by
    have hv := congrArg (fun x : Albert => x.1 0) h
    rw [diagAtom_fst, hr1_eq] at hv; norm_num at hv
  have h02_ne : r0 ≠ r2 := fun h => by
    have hv := congrArg (fun x : Albert => x.1 0) h
    rw [diagAtom_fst, hr2_eq] at hv; norm_num at hv
  have h12_ne : r1 ≠ r2 := fun h => by
    have hv := congrArg (fun x : Albert => x.1 1) h
    rw [hr1_eq, hr2_eq] at hv; norm_num at hv
  let T : Finset Albert := {r0, r1, r2}
  have hcard : T.card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair h12_ne]
    simp [h01_ne, h02_ne]
  have hT_atoms : ∀ p ∈ T, IsAtom p ∧ p ∈ (H3Subalgebra .R).carrier := by
    intro p hp
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨hr0_atom, hr0_mem⟩
    · exact ⟨hr1_atom, hr1_mem⟩
    · exact ⟨hr2_atom, hr2_mem⟩
  have hgen : generatedSubalgebra (T : Set Albert) = H3Subalgebra .R := by
    refine le_antisymm (generatedSubalgebra_le (B := H3Subalgebra .R) fun p hp =>
        (hT_atoms p (Finset.mem_coe.mp hp)).2) ?_
    let B := generatedSubalgebra (T : Set Albert)
    have hr0B : r0 ∈ B.carrier := subset_generatedSubalgebra _ (by simp [T])
    have hr1B : r1 ∈ B.carrier := subset_generatedSubalgebra _ (by simp [T])
    have hr2B : r2 ∈ B.carrier := subset_generatedSubalgebra _ (by simp [T])
    have hs01_eq : slotElem01 octOne = (4 : ℝ) • jordanMul r0 r1 - (2 : ℝ) • r0 := by
      rw [hr1_eq]; dsimp only [r0]; rw [jordanMul_diagAtom0_mk]
      apply albert_ext <;> simp [diagAtom_fst, diagAtom_snd, slotElem01_fst, slotElem01_snd_0,
        slotElem01_snd_1, slotElem01_snd_2, albert_sub_fst, albert_sub_snd, albert_smul_fst,
        albert_smul_snd, smul_smul] <;> norm_num
    have hs01B : slotElem01 octOne ∈ B.carrier := by
      rw [hs01_eq]
      exact B.carrier.sub_mem (B.carrier.smul_mem _ (B.product_mem _ hr0B _ hr1B))
        (B.carrier.smul_mem _ hr0B)
    have hd1_eq : diagAtom 1 = (2 : ℝ) • r1 - r0 - slotElem01 octOne := by
      rw [hr1_eq]
      apply albert_ext <;> simp [r0, diagAtom_fst, diagAtom_snd, slotElem01_fst, slotElem01_snd_0,
        slotElem01_snd_1, slotElem01_snd_2, albert_sub_fst, albert_sub_snd, albert_smul_fst,
        albert_smul_snd, smul_smul]
    have hd1B : diagAtom 1 ∈ B.carrier := by
      rw [hd1_eq]
      exact B.carrier.sub_mem (B.carrier.sub_mem (B.carrier.smul_mem _ hr1B) hr0B) hs01B
    have hs02_eq : slotElem02 octOne = (4 : ℝ) • jordanMul r0 r2 - (2 : ℝ) • r0 := by
      rw [hr2_eq]; dsimp only [r0]; rw [jordanMul_diagAtom0_mk]
      apply albert_ext <;> simp [diagAtom_fst, diagAtom_snd, slotElem02_fst, slotElem02_snd_0,
        slotElem02_snd_1, slotElem02_snd_2, albert_sub_fst, albert_sub_snd, albert_smul_fst,
        albert_smul_snd, smul_smul] <;> norm_num
    have hs02B : slotElem02 octOne ∈ B.carrier := by
      rw [hs02_eq]
      exact B.carrier.sub_mem (B.carrier.smul_mem _ (B.product_mem _ hr0B _ hr2B))
        (B.carrier.smul_mem _ hr0B)
    have hd2_eq : diagAtom 2 = (2 : ℝ) • r2 - r0 - slotElem02 octOne := by
      rw [hr2_eq]
      apply albert_ext <;> simp [r0, diagAtom_fst, diagAtom_snd, slotElem02_fst, slotElem02_snd_0,
        slotElem02_snd_1, slotElem02_snd_2, albert_sub_fst, albert_sub_snd, albert_smul_fst,
        albert_smul_snd, smul_smul]
    have hd2B : diagAtom 2 ∈ B.carrier := by
      rw [hd2_eq]
      exact B.carrier.sub_mem (B.carrier.sub_mem (B.carrier.smul_mem _ hr2B) hr0B) hs02B
    have hs12B : slotElem12 octOne ∈ B.carrier := slotElem02_mem_12_of_mem hs01B hs02B
    obtain ⟨F, _, hF_eq, _⟩ := lem_five_coord B hr0B hd1B hd2B
      (Or.inl ⟨by simpa [octOne_eq_scalar] using hs01B,
        by simpa [octOne_eq_scalar] using hs02B⟩)
    have hR_le_F : (octSubalgebraOfLevel .R).carrier ≤ F.carrier := by
      intro x hx
      rcases hx with ⟨hI, hJ, hK, h2⟩
      have hx_eq : x = x.1.re • octOne := by
        apply Prod.ext
        · apply Quaternion.ext
          · rw [oct_smul_fst]; simp [octOne, octonionScalar]
          · rw [oct_smul_fst]; simp [octOne, octonionScalar, hI]
          · rw [oct_smul_fst]; simp [octOne, octonionScalar, hJ]
          · rw [oct_smul_fst]; simp [octOne, octonionScalar, hK]
        · rw [oct_smul_snd]; simp [octOne, octonionScalar, h2]
      rw [hx_eq]
      exact F.carrier.smul_mem _ F.one_mem
    have hH3_le : (H3Subalgebra .R).carrier ≤ B.carrier := by
      intro x hx
      rw [hF_eq]
      exact ⟨hR_le_F hx.1, hR_le_F hx.2.1, hR_le_F hx.2.2⟩
    exact hH3_le
  have hIrr : IsIrredundant T := by
    refine ⟨fun p hp => (hT_atoms p hp).1, fun p hp => ?_⟩
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · let q₀ : Albert := (3 : ℝ)⁻¹ • octDyad ![octOne, -octOne, -octOne]
      have hq₀ : IsAtom q₀ := by
        refine isAtom_scaled_octDyad quatEmbed1 quatEmbed1_isQuatEmbedding 3 (by norm_num)
          ![octOne, -octOne, -octOne] ?_ ?_
        · intro k; fin_cases k
          · exact octOne_mem_range_quat quatEmbed1 quatEmbed1_isQuatEmbedding
          · exact ⟨-1, by rw [map_neg, quatEmbed1_isQuatEmbedding.map_one]; rfl⟩
          · exact ⟨-1, by rw [map_neg, quatEmbed1_isQuatEmbedding.map_one]; rfl⟩
        · rw [Fin.sum_univ_three]
          change octNormSq octOne + octNormSq (-octOne) + octNormSq (-octOne) = 3
          rw [octNormSq_neg, octNormSq_one]; norm_num
      have hq₀_eq : q₀ = mkAlbert ![1 / 3, 1 / 3, 1 / 3]
          ![(-1 / 3 : ℝ) • octOne, (-1 / 3 : ℝ) • octOne, (1 / 3 : ℝ) • octOne] := by
        apply albert_ext
        · simp [q₀, albert_smul_fst, octDyad_fst, octNormSq_one]; try norm_num
        · simp [q₀, albert_smul_fst, octDyad_fst, octNormSq_neg, octNormSq_one]; try norm_num
        · simp [q₀, albert_smul_fst, octDyad_fst, octNormSq_neg, octNormSq_one]; try norm_num
        · simp [q₀, albert_smul_snd, octDyad_snd_0, octonionConj_neg, octonionConj_one,
            octonionMul_neg_right, octonionMul_one_left, smul_neg, ← neg_smul]; try norm_num
        · simp [q₀, albert_smul_snd, octDyad_snd_1, octonionConj_neg, octonionConj_one,
            octonionMul_neg_right, octonionMul_one_left, smul_neg, ← neg_smul]; try norm_num
        · simp [q₀, albert_smul_snd, octDyad_snd_2, octonionConj_neg, octonionConj_one,
            octonionMul_neg_left, octonionMul_neg_right, octonionMul_one_left]; try norm_num
      have hsub : (T.erase r0 : Set Albert) ⊆ (lineSubalgebra q₀ hq₀).carrier := by
        intro x hx
        simp only [T, Finset.mem_coe, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hx
        change x ∈ (lineSubalgebra q₀ hq₀).carrier
        rcases hx with ⟨hne, rfl | rfl | rfl⟩
        · exact absurd rfl hne
        · rw [mem_lineSubalgebra_iff, hr1_eq, hq₀_eq]
          have htp : tracePairing (mkAlbert ![1 / 3, 1 / 3, 1 / 3]
              ![(-1 / 3 : ℝ) • octOne, (-1 / 3 : ℝ) • octOne, (1 / 3 : ℝ) • octOne])
              (mkAlbert ![1 / 2, 1 / 2, 0] ![(1 / 2 : ℝ) • octOne, 0, 0]) = 0 := by
            simp [tracePairing_eq_coords, octDot_smul_left, octDot_smul_right, octDot_self,
              octNormSq_one, octDot_zero_right]
            norm_num
          rw [htp, zero_smul]
          apply albert_ext
          · rw [jordanMul_diag_0]
            simp [octDot_smul_left, octDot_smul_right, octDot_self, octNormSq_one,
              octDot_zero_right, albert_zero_fst]
            try norm_num
          · rw [jordanMul_diag_1]
            simp [octDot_smul_left, octDot_smul_right, octDot_self, octNormSq_one,
              octDot_zero_right, albert_zero_fst]
            try norm_num
          · rw [jordanMul_diag_2]; simp [octDot_zero_right, albert_zero_fst]
          · rw [jordanMul_off_0]
            simp [octonionMul_smul_right, octonionConj_smul, octonionConj_one,
              octonionMul_zero_left, octonionMul_zero_right, octonionConj_zero,
              smul_smul, albert_zero_snd]
            module
          · rw [jordanMul_off_1]
            simp [octonionMul_smul_left, octonionMul_smul_right,
              octonionMul_one_left, octonionMul_zero_right,
              smul_smul, albert_zero_snd]
            module
          · rw [jordanMul_off_2]
            simp [octonionMul_smul_left, octonionMul_smul_right, octonionConj_smul, octonionConj_one,
              octonionMul_one_left, octonionMul_zero_right,
              smul_smul, albert_zero_snd]
            module
        · rw [mem_lineSubalgebra_iff, hr2_eq, hq₀_eq]
          have htp : tracePairing (mkAlbert ![1 / 3, 1 / 3, 1 / 3]
              ![(-1 / 3 : ℝ) • octOne, (-1 / 3 : ℝ) • octOne, (1 / 3 : ℝ) • octOne])
              (mkAlbert ![1 / 2, 0, 1 / 2] ![0, (1 / 2 : ℝ) • octOne, 0]) = 0 := by
            simp [tracePairing_eq_coords, octDot_smul_left, octDot_smul_right, octDot_self,
              octNormSq_one, octDot_zero_right]
            norm_num
          rw [htp, zero_smul]
          apply albert_ext
          · rw [jordanMul_diag_0]
            simp [octDot_smul_left, octDot_smul_right, octDot_self, octNormSq_one,
              octDot_zero_right, albert_zero_fst]
            try norm_num
          · rw [jordanMul_diag_1]; simp [octDot_zero_right, albert_zero_fst]
          · rw [jordanMul_diag_2]
            simp [octDot_smul_left, octDot_smul_right, octDot_self, octNormSq_one,
              octDot_zero_right, albert_zero_fst]
            try norm_num
          · rw [jordanMul_off_0]
            simp [octonionMul_smul_left, octonionMul_smul_right, octonionConj_smul, octonionConj_one,
              octonionMul_one_left, octonionMul_zero_right, octonionConj_zero,
              smul_smul, albert_zero_snd]
            module
          · rw [jordanMul_off_1]
            simp [octonionMul_smul_right,
              octonionMul_zero_left, octonionMul_zero_right,
              smul_smul, albert_zero_snd]
            module
          · rw [jordanMul_off_2]
            simp [octonionMul_smul_left, octonionMul_smul_right, octonionConj_smul, octonionConj_one,
              octonionMul_one_left, octonionMul_zero_left, octonionConj_zero,
              smul_smul, albert_zero_snd]
            module
      intro hr0_in
      have h0_line : r0 ∈ (lineSubalgebra q₀ hq₀).carrier :=
        generatedSubalgebra_le (B := lineSubalgebra q₀ hq₀) hsub hr0_in
      rw [mem_lineSubalgebra_iff, hq₀_eq] at h0_line
      have htp : tracePairing (mkAlbert ![1 / 3, 1 / 3, 1 / 3]
          ![(-1 / 3 : ℝ) • octOne, (-1 / 3 : ℝ) • octOne, (1 / 3 : ℝ) • octOne]) r0 = 1 / 3 := by
        simp [r0, tracePairing_eq_coords, diagAtom_fst, diagAtom_snd, octDot_zero_right]; try norm_num
      rw [htp] at h0_line
      have h01 := congrArg (fun a : Albert => (a.2 0).1.re) h0_line
      dsimp only [r0] at h01
      rw [jordanMul_comm, jordanMul_diagAtom0] at h01
      simp only [albert_smul_snd, mkAlbert_snd, Matrix.cons_val_zero,
        oct_smul_fst, Quaternion.re_smul, smul_eq_mul] at h01
      simp [octOne, octonionScalar] at h01
      try norm_num at h01
    · have hsub : (T.erase r1 : Set Albert) ⊆ (lineSubalgebra (diagAtom 1) (diagAtom_isAtom 1)).carrier := by
        intro x hx
        simp only [T, Finset.mem_coe, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hx
        change x ∈ (lineSubalgebra (diagAtom 1) (diagAtom_isAtom 1)).carrier
        rw [mem_lineSubalgebra_iff]
        rcases hx with ⟨hne, rfl | rfl | rfl⟩
        · have htp : tracePairing (diagAtom 1) r0 = 0 := by
            simp [r0, tracePairing_eq_coords, diagAtom_fst, diagAtom_snd, octDot_zero_right]
          rw [htp, zero_smul]
          dsimp only [r0]; rw [jordanMul_diagAtom1]
          apply albert_ext <;> simp [diagAtom_fst, diagAtom_snd, albert_zero_fst, albert_zero_snd]
        · exact absurd rfl hne
        · have htp : tracePairing (diagAtom 1) r2 = 0 := by
            rw [hr2_eq]; simp [tracePairing_eq_coords, diagAtom_fst, diagAtom_snd, octDot_zero_left]
          rw [htp, zero_smul, hr2_eq, jordanMul_diagAtom1]
          apply albert_ext <;> simp [albert_zero_fst, albert_zero_snd]
      intro hr1_in
      have h1_line := generatedSubalgebra_le (B := lineSubalgebra (diagAtom 1) (diagAtom_isAtom 1)) hsub hr1_in
      change r1 ∈ (lineSubalgebra (diagAtom 1) (diagAtom_isAtom 1)).carrier at h1_line
      rw [mem_lineSubalgebra_iff, hr1_eq] at h1_line
      have h20 := congrArg (fun a : Albert => (a.2 0).1.re) h1_line
      rw [jordanMul_diagAtom1] at h20
      simp only [tracePairing_eq_coords, diagAtom_fst, diagAtom_snd, octDot_zero_left,
        albert_smul_snd, mkAlbert_snd, Matrix.cons_val_zero, oct_smul_fst, Quaternion.re_smul,
        smul_eq_mul] at h20
      simp [octOne, octonionScalar] at h20
      try norm_num at h20
    · have hsub : (T.erase r2 : Set Albert) ⊆ (lineSubalgebra (diagAtom 2) (diagAtom_isAtom 2)).carrier := by
        intro x hx
        simp only [T, Finset.mem_coe, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hx
        change x ∈ (lineSubalgebra (diagAtom 2) (diagAtom_isAtom 2)).carrier
        rw [mem_lineSubalgebra_iff]
        rcases hx with ⟨hne, rfl | rfl | rfl⟩
        · have htp : tracePairing (diagAtom 2) r0 = 0 := by
            simp [r0, tracePairing_eq_coords, diagAtom_fst, diagAtom_snd, octDot_zero_right]
          rw [htp, zero_smul]
          dsimp only [r0]; rw [jordanMul_diagAtom2]
          apply albert_ext <;> simp [diagAtom_fst, diagAtom_snd, albert_zero_fst, albert_zero_snd]
        · have htp : tracePairing (diagAtom 2) r1 = 0 := by
            rw [hr1_eq]; simp [tracePairing_eq_coords, diagAtom_fst, diagAtom_snd, octDot_zero_left]
          rw [htp, zero_smul, hr1_eq, jordanMul_diagAtom2]
          apply albert_ext <;> simp [albert_zero_fst, albert_zero_snd]
        · exact absurd rfl hne
      intro hr2_in
      have h2_line := generatedSubalgebra_le (B := lineSubalgebra (diagAtom 2) (diagAtom_isAtom 2)) hsub hr2_in
      change r2 ∈ (lineSubalgebra (diagAtom 2) (diagAtom_isAtom 2)).carrier at h2_line
      rw [mem_lineSubalgebra_iff, hr2_eq] at h2_line
      have h21 := congrArg (fun a : Albert => (a.2 1).1.re) h2_line
      rw [jordanMul_diagAtom2] at h21
      dsimp only at h21
      simp only [tracePairing_eq_coords, diagAtom_fst, diagAtom_snd, octDot_zero_left,
        albert_smul_snd, mkAlbert_snd, Matrix.cons_val_one, Matrix.cons_val_zero,
        oct_smul_fst, Quaternion.re_smul, smul_eq_mul] at h21
      simp [octOne, octonionScalar] at h21
      try norm_num at h21
  exact ⟨T, hcard, hT_atoms, hIrr, hgen⟩

private theorem hrank1_real_aux (U : Matrix.unitaryGroup (Fin 3) ℂ)
    (M : selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ)) (c : ℝ) (v : Fin 3 → ℂ)
    (hM : ∀ a b, M.1 a b = (c : ℂ) * (v a * star (v b)))
    (hcond : (∀ j, (∑ a : Fin 3, star (U.1 a j) * v a).im = 0) ∨
      (∀ j, (∑ a : Fin 3, star (U.1 a j) * v a).re = 0))
    (i j : Fin 3) : ((star U.1 * M.1 * U.1) i j).im = 0 := by
  let w : Fin 3 → ℂ := fun k => ∑ a : Fin 3, star (U.1 a k) * v a
  have hprod : (star U.1 * M.1 * U.1) i j = (c : ℂ) * (w i * star (w j)) := by
    simp only [Matrix.mul_apply, Matrix.star_apply, hM]
    calc
      ∑ b : Fin 3, (∑ a : Fin 3, star (U.1 a i) * ((c : ℂ) * (v a * star (v b)))) * U.1 b j
        = ∑ b : Fin 3, ∑ a : Fin 3, (c : ℂ) * (star (U.1 a i) * v a) * (star (v b) * U.1 b j) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => by ring
      _ = ∑ a : Fin 3, ∑ b : Fin 3, (c : ℂ) * (star (U.1 a i) * v a) * (star (v b) * U.1 b j) :=
          Finset.sum_comm
      _ = (c : ℂ) * ((∑ a : Fin 3, star (U.1 a i) * v a) *
            (∑ b : Fin 3, star (v b) * U.1 b j)) := by
          rw [Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => by ring
      _ = (c : ℂ) * (w i * star (w j)) := by
          dsimp only [w]
          rw [star_sum]
          congr 2
          refine Finset.sum_congr rfl fun b _ => by rw [star_mul, star_star, mul_comm]
  rw [hprod, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  rcases hcond with him | hre
  · have hi : (w i).im = 0 := him i
    have hj : (w j).im = 0 := him j
    rw [hi, hj]; ring
  · have hi : (w i).re = 0 := hre i
    have hj : (w j).re = 0 := hre j
    rw [hi, hj]; ring

private theorem oct_smul_one_eq (r : ℝ) :
    r • octOne = ((⟨r, 0, 0, 0⟩, (0 : Quaternion ℝ)) : Octonion) := by
  apply Prod.ext <;> apply Quaternion.ext <;>
    first | exact mul_one r | exact mul_zero r

private theorem oct_smul_I_eq (r : ℝ) :
    r • octI = ((⟨0, r, 0, 0⟩, (0 : Quaternion ℝ)) : Octonion) := by
  apply Prod.ext <;> apply Quaternion.ext <;>
    first | exact mul_one r | exact mul_zero r

private theorem oct_smul_J_eq (r : ℝ) :
    r • octJ = ((⟨0, 0, r, 0⟩, (0 : Quaternion ℝ)) : Octonion) := by
  apply Prod.ext <;> apply Quaternion.ext <;>
    first | exact mul_one r | exact mul_zero r

private theorem oct_smul_sub1I_eq (r : ℝ) :
    r • (octOne - octI) = ((⟨r, -r, 0, 0⟩, (0 : Quaternion ℝ)) : Octonion) := by
  rw [smul_sub, oct_smul_one_eq, oct_smul_I_eq]
  apply Prod.ext <;> apply Quaternion.ext <;>
    first | exact sub_zero r | exact zero_sub r | exact sub_zero 0

private theorem oct_smul_add1I_eq (r : ℝ) :
    r • (octOne + octI) = ((⟨r, r, 0, 0⟩, (0 : Quaternion ℝ)) : Octonion) := by
  rw [smul_add, oct_smul_one_eq, oct_smul_I_eq]
  apply Prod.ext <;> apply Quaternion.ext <;>
    first | exact add_zero r | exact zero_add r | exact add_zero 0

private noncomputable def cM0 : selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ) :=
  ⟨Matrix.of ![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], by
    rw [selfAdjoint.mem_iff]; funext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.star_apply]⟩

private noncomputable def cM1 : selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ) :=
  ⟨Matrix.of ![![0, 0, 0], ![0, 1, 0], ![0, 0, 0]], by
    rw [selfAdjoint.mem_iff]; funext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.star_apply]⟩

private noncomputable def cM2 : selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ) :=
  let inv3 : ℂ := ((1 / 3 : ℝ) : ℂ)
  ⟨Matrix.of ![![inv3, inv3, inv3], ![inv3, inv3, inv3], ![inv3, inv3, inv3]], by
    rw [selfAdjoint.mem_iff]; funext i j; fin_cases i <;> fin_cases j <;>
      apply Complex.ext <;> simp [inv3, Matrix.star_apply]⟩

private noncomputable def cM3 : selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ) :=
  let q4 : ℂ := ((1 / 4 : ℝ) : ℂ)
  let q2 : ℂ := ((1 / 2 : ℝ) : ℂ)
  ⟨Matrix.of ![![q4, -q4 * Complex.I, -q4 + q4 * Complex.I],
     ![q4 * Complex.I, q4, -q4 - q4 * Complex.I],
     ![-q4 - q4 * Complex.I, -q4 + q4 * Complex.I, q2]], by
    rw [selfAdjoint.mem_iff]; funext i j; fin_cases i <;> fin_cases j <;>
      apply Complex.ext <;> simp [q4, q2, Matrix.star_apply]⟩

private theorem prop_arity_lower_C_U0 :
    ∃ U0 : Matrix.unitaryGroup (Fin 3) ℂ,
      (assocHermEquiv assocCD_C cM1).1 ∈ (unitaryConjSubalgebraC U0 (H3Subalgebra .R)).carrier ∧
      (assocHermEquiv assocCD_C cM2).1 ∈ (unitaryConjSubalgebraC U0 (H3Subalgebra .R)).carrier ∧
      (assocHermEquiv assocCD_C cM3).1 ∈ (unitaryConjSubalgebraC U0 (H3Subalgebra .R)).carrier := by
  have hsq2 : (Real.sqrt 2)⁻¹ ^ 2 = (1 / 2 : ℝ) := by
    rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hsq10 : (Real.sqrt 10)⁻¹ ^ 2 = (1 / 10 : ℝ) := by
    rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hmul2 : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by rw [← sq, hsq2]
  have hmul10 : (Real.sqrt 10)⁻¹ * (Real.sqrt 10)⁻¹ = (1 / 10 : ℝ) := by rw [← sq, hsq10]
  have hrt2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hrt10 : Real.sqrt 10 ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  have hrt2m : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hrt10m : Real.sqrt 10 * Real.sqrt 10 = 10 := Real.mul_self_sqrt (by norm_num)
  let r10 : ℝ := Real.sqrt 10
  let r2 : ℝ := Real.sqrt 2
  let U0_mat : Matrix (Fin 3) (Fin 3) ℂ :=
    Matrix.of ![![0, (r2⁻¹ : ℝ), (1 - 2 * Complex.I) * (r10⁻¹ : ℝ)],
      ![1, 0, 0],
      ![0, (r2⁻¹ : ℝ), (-1 + 2 * Complex.I) * (r10⁻¹ : ℝ)]]
  have hU0_mem : U0_mat ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    funext i j
    fin_cases i <;> fin_cases j <;>
      (dsimp only [U0_mat];
       apply Complex.ext <;>
         simp [Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_three, r2, r10] <;>
         try ring_nf <;>
         simp only [hrt2, hrt10] <;>
         try norm_num)
  let U0 : Matrix.unitaryGroup (Fin 3) ℂ := ⟨U0_mat, hU0_mem⟩
  refine ⟨U0, ?_, ?_, ?_⟩
  · refine mem_unitaryConjSubalgebraC_H3R_of_matrix U0 cM1
      (hrank1_real_aux U0 cM1 1 ![0, 1, 0]
        (fun a b => by fin_cases a <;> fin_cases b <;> simp [cM1])
        (Or.inl fun j => by
          fin_cases j <;> simp [U0, U0_mat, Fin.sum_univ_three, r2, r10]))
  · refine mem_unitaryConjSubalgebraC_H3R_of_matrix U0 cM2
      (hrank1_real_aux U0 cM2 (1 / 3) ![1, 1, 1]
        (fun a b => by fin_cases a <;> fin_cases b <;> simp [cM2]; try norm_num)
        (Or.inl fun j => by
          fin_cases j <;>
            simp [U0, U0_mat, Fin.sum_univ_three, r2, r10]))
  · refine mem_unitaryConjSubalgebraC_H3R_of_matrix U0 cM3
      (hrank1_real_aux U0 cM3 1 ![((2⁻¹ : ℝ) : ℂ), (2⁻¹ : ℝ) * Complex.I,
          ((-2⁻¹ : ℝ) : ℂ) - (2⁻¹ : ℝ) * Complex.I]
        (fun a b => by
          fin_cases a <;> fin_cases b <;> apply Complex.ext <;>
            simp [cM3] <;> try norm_num)
        (Or.inr fun j => by
          fin_cases j <;>
            (dsimp only [U0, U0_mat];
             simp [Fin.sum_univ_three, r2, r10] <;> try ring)))

private theorem prop_arity_lower_C_U1 :
    ∃ U1 : Matrix.unitaryGroup (Fin 3) ℂ,
      (assocHermEquiv assocCD_C cM0).1 ∈ (unitaryConjSubalgebraC U1 (H3Subalgebra .R)).carrier ∧
      (assocHermEquiv assocCD_C cM2).1 ∈ (unitaryConjSubalgebraC U1 (H3Subalgebra .R)).carrier ∧
      (assocHermEquiv assocCD_C cM3).1 ∈ (unitaryConjSubalgebraC U1 (H3Subalgebra .R)).carrier := by
  have hsq2 : (Real.sqrt 2)⁻¹ ^ 2 = (1 / 2 : ℝ) := by
    rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hsq10 : (Real.sqrt 10)⁻¹ ^ 2 = (1 / 10 : ℝ) := by
    rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hmul2 : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by rw [← sq, hsq2]
  have hmul10 : (Real.sqrt 10)⁻¹ * (Real.sqrt 10)⁻¹ = (1 / 10 : ℝ) := by rw [← sq, hsq10]
  have hrt2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hrt10 : Real.sqrt 10 ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  have hrt2m : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hrt10m : Real.sqrt 10 * Real.sqrt 10 = 10 := Real.mul_self_sqrt (by norm_num)
  let r10 : ℝ := Real.sqrt 10
  let r2 : ℝ := Real.sqrt 2
  let U1_mat : Matrix (Fin 3) (Fin 3) ℂ :=
    Matrix.of ![![1, 0, 0],
      ![0, (r2⁻¹ : ℝ), (1 + 2 * Complex.I) * (r10⁻¹ : ℝ)],
      ![0, (r2⁻¹ : ℝ), (-1 - 2 * Complex.I) * (r10⁻¹ : ℝ)]]
  have hU1_mem : U1_mat ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    funext i j
    fin_cases i <;> fin_cases j <;>
      (dsimp only [U1_mat];
       apply Complex.ext <;>
         simp [Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_three, r2, r10] <;>
         try ring_nf <;>
         simp only [hrt2, hrt10] <;>
         try norm_num)
  let U1 : Matrix.unitaryGroup (Fin 3) ℂ := ⟨U1_mat, hU1_mem⟩
  refine ⟨U1, ?_, ?_, ?_⟩
  · refine mem_unitaryConjSubalgebraC_H3R_of_matrix U1 cM0
      (hrank1_real_aux U1 cM0 1 ![1, 0, 0]
        (fun a b => by fin_cases a <;> fin_cases b <;> simp [cM0])
        (Or.inl fun j => by
          fin_cases j <;> simp [U1, U1_mat, Fin.sum_univ_three, r2, r10]))
  · refine mem_unitaryConjSubalgebraC_H3R_of_matrix U1 cM2
      (hrank1_real_aux U1 cM2 (1 / 3) ![1, 1, 1]
        (fun a b => by fin_cases a <;> fin_cases b <;> simp [cM2]; try norm_num)
        (Or.inl fun j => by
          fin_cases j <;>
            simp [U1, U1_mat, Fin.sum_univ_three, r2, r10]))
  · refine mem_unitaryConjSubalgebraC_H3R_of_matrix U1 cM3
      (hrank1_real_aux U1 cM3 1 ![((2⁻¹ : ℝ) : ℂ), (2⁻¹ : ℝ) * Complex.I,
          ((-2⁻¹ : ℝ) : ℂ) - (2⁻¹ : ℝ) * Complex.I]
        (fun a b => by
          fin_cases a <;> fin_cases b <;> apply Complex.ext <;>
            simp [cM3] <;> try norm_num)
        (Or.inl fun j => by
          fin_cases j <;>
            (dsimp only [U1, U1_mat];
             simp [Fin.sum_univ_three, r2, r10] <;> try ring)))

private theorem prop_arity_lower_C_U2 :
    ∃ U2 : Matrix.unitaryGroup (Fin 3) ℂ,
      (assocHermEquiv assocCD_C cM0).1 ∈ (unitaryConjSubalgebraC U2 (H3Subalgebra .R)).carrier ∧
      (assocHermEquiv assocCD_C cM1).1 ∈ (unitaryConjSubalgebraC U2 (H3Subalgebra .R)).carrier ∧
      (assocHermEquiv assocCD_C cM3).1 ∈ (unitaryConjSubalgebraC U2 (H3Subalgebra .R)).carrier := by
  have hsq2 : (Real.sqrt 2)⁻¹ ^ 2 = (1 / 2 : ℝ) := by
    rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hmul2 : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by rw [← sq, hsq2]
  have hrt2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hrt2m : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  let r2 : ℝ := Real.sqrt 2
  let U2_mat : Matrix (Fin 3) (Fin 3) ℂ :=
    Matrix.diagonal ![1, Complex.I, (-1 - Complex.I) * (r2⁻¹ : ℝ)]
  have hU2_mem : U2_mat ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    funext a b
    dsimp only [U2_mat]
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · by_cases hab : a = b
      · subst hab
        fin_cases a <;> apply Complex.ext <;> simp [Matrix.star_apply, r2]
        all_goals (ring_nf; simp only [hrt2]; norm_num)
      · simp [Matrix.star_apply, hab]
    · intro c _ hca; simp [Matrix.star_apply, Matrix.diagonal_apply, hca]
    · intro ha; exact absurd (Finset.mem_univ a) ha
  let U2 : Matrix.unitaryGroup (Fin 3) ℂ := ⟨U2_mat, hU2_mem⟩
  refine ⟨U2, ?_, ?_, ?_⟩
  · refine mem_unitaryConjSubalgebraC_H3R_of_matrix U2 cM0
      (hrank1_real_aux U2 cM0 1 ![1, 0, 0]
        (fun a b => by fin_cases a <;> fin_cases b <;> simp [cM0])
        (Or.inl fun j => by
          fin_cases j <;> simp [U2, U2_mat, Fin.sum_univ_three, r2]))
  · refine mem_unitaryConjSubalgebraC_H3R_of_matrix U2 cM1
      (hrank1_real_aux U2 cM1 1 ![0, 1, 0]
        (fun a b => by fin_cases a <;> fin_cases b <;> simp [cM1])
        (Or.inr fun j => by
          fin_cases j <;> simp [U2, U2_mat, Fin.sum_univ_three, r2]))
  · refine mem_unitaryConjSubalgebraC_H3R_of_matrix U2 cM3
      (hrank1_real_aux U2 cM3 1 ![((2⁻¹ : ℝ) : ℂ), (2⁻¹ : ℝ) * Complex.I,
          ((-2⁻¹ : ℝ) : ℂ) - (2⁻¹ : ℝ) * Complex.I]
        (fun a b => by
          fin_cases a <;> fin_cases b <;> apply Complex.ext <;>
            simp [cM3] <;> try norm_num)
        (Or.inl fun j => by
          fin_cases j <;>
            (dsimp only [U2, U2_mat];
             simp [Fin.sum_univ_three, r2])))

private theorem prop_arity_lower_C :
    ∃ T : Finset Albert, T.card = 4 ∧
      (∀ p ∈ T, IsAtom p ∧ p ∈ (H3Subalgebra .C).carrier) ∧
      IsIrredundant T ∧ generatedSubalgebra (T : Set Albert) = H3Subalgebra .C := by
  let c0 : Albert := diagAtom 0
  let c1 : Albert := diagAtom 1
  let c2 : Albert := (1 / 3 : ℝ) • octDyad ![octOne, octOne, octOne]
  let c3 : Albert := (1 / 4 : ℝ) • octDyad ![octOne, octI, -(octOne + octI)]
  have hc2_eq : c2 = mkAlbert ![1 / 3, 1 / 3, 1 / 3]
      ![(1 / 3 : ℝ) • octOne, (1 / 3 : ℝ) • octOne, (1 / 3 : ℝ) • octOne] := by
    apply albert_ext
    · simp [c2, albert_smul_fst, octDyad_fst, octNormSq_one]
    · simp [c2, albert_smul_fst, octDyad_fst, octNormSq_one]
    · simp [c2, albert_smul_fst, octDyad_fst, octNormSq_one]
    · simp [c2, albert_smul_snd, octDyad_snd_0, octonionConj_one, octonionMul_one_left]
    · simp [c2, albert_smul_snd, octDyad_snd_1, octonionConj_one, octonionMul_one_left]
    · simp [c2, albert_smul_snd, octDyad_snd_2, octonionConj_one, octonionMul_one_left]
  have hsum1I : -(octOne + octI) = ((⟨-1, -1, 0, 0⟩, (0 : Quaternion ℝ)) : Octonion) := by
    apply Prod.ext
    · rw [oct_neg_fst, oct_add_fst]
      apply Quaternion.ext <;> simp [octOne, octonionScalar, octI]
    · rw [oct_neg_snd, oct_add_snd]; simp [octOne, octonionScalar, octI]
  have hsub1I : -(octOne - octI) = ((⟨-1, 1, 0, 0⟩, (0 : Quaternion ℝ)) : Octonion) := by
    apply Prod.ext
    · rw [oct_neg_fst, oct_sub_fst]
      apply Quaternion.ext <;> simp [octOne, octonionScalar, octI]
    · rw [oct_neg_snd, oct_sub_snd]; simp [octOne, octonionScalar, octI]
  have h1c_mul : octonionMul octI (octonionConj (-(octOne + octI))) = -(octOne + octI) := by
    rw [hsum1I]
    apply Prod.ext <;> apply Quaternion.ext <;> simp [octonionMul, octonionConj, octI]
  have h0c_mul : octonionMul octOne (octonionConj (-(octOne + octI))) = -(octOne - octI) := by
    rw [hsum1I, hsub1I]
    apply Prod.ext <;> apply Quaternion.ext <;>
      simp [octonionMul, octonionConj, octOne, octonionScalar]
  have hnorm1I : octNormSq (-(octOne + octI)) = 2 := by
    rw [octNormSq_eq_coords, hsum1I]
    norm_num
  have hc3_eq : c3 = mkAlbert ![1 / 4, 1 / 4, 1 / 2]
      ![(-1 / 4 : ℝ) • octI, (-1 / 4 : ℝ) • (octOne - octI), (-1 / 4 : ℝ) • (octOne + octI)] := by
    apply albert_ext
    · simp [c3, albert_smul_fst, octDyad_fst, octNormSq_one]
    · simp [c3, albert_smul_fst, octDyad_fst, octNormSq_I]
    · dsimp only [c3]; rw [albert_smul_fst, octDyad_fst]
      change (1 / 4 : ℝ) * octNormSq (-(octOne + octI)) = 1 / 2
      rw [hnorm1I]; norm_num
    · dsimp only [c3]; rw [albert_smul_snd, octDyad_snd_0]
      change (1 / 4 : ℝ) • octonionMul octOne (octonionConj octI) = (-1 / 4 : ℝ) • octI
      rw [octonionMul_one_left, octonionConj_I, smul_neg, ← neg_smul]; norm_num
    · dsimp only [c3]; rw [albert_smul_snd, octDyad_snd_1]
      change (1 / 4 : ℝ) • octonionMul octOne (octonionConj (-(octOne + octI))) =
        (-1 / 4 : ℝ) • (octOne - octI)
      rw [h0c_mul, smul_neg, ← neg_smul]; norm_num
    · dsimp only [c3]; rw [albert_smul_snd, octDyad_snd_2]
      change (1 / 4 : ℝ) • octonionMul octI (octonionConj (-(octOne + octI))) =
        (-1 / 4 : ℝ) • (octOne + octI)
      rw [h1c_mul, smul_neg, ← neg_smul]; norm_num
  have hc0_atom : IsAtom c0 := diagAtom_isAtom 0
  have hc1_atom : IsAtom c1 := diagAtom_isAtom 1
  have hc2_atom : IsAtom c2 := by
    dsimp only [c2]
    rw [one_div]
    refine isAtom_scaled_octDyad quatEmbed1 quatEmbed1_isQuatEmbedding 3 (by norm_num)
      ![octOne, octOne, octOne] ?_ ?_
    · intro k; fin_cases k <;> exact octOne_mem_range_quat quatEmbed1 quatEmbed1_isQuatEmbedding
    · rw [Fin.sum_univ_three]
      change octNormSq octOne + octNormSq octOne + octNormSq octOne = 3
      rw [octNormSq_one]; norm_num
  have hc3_atom : IsAtom c3 := by
    dsimp only [c3]
    rw [one_div]
    refine isAtom_scaled_octDyad quatEmbed1 quatEmbed1_isQuatEmbedding 4 (by norm_num)
      ![octOne, octI, -(octOne + octI)] ?_ ?_
    · intro k; fin_cases k
      · exact octOne_mem_range_quat quatEmbed1 quatEmbed1_isQuatEmbedding
      · exact ⟨⟨0, 1, 0, 0⟩, rfl⟩
      · refine ⟨-(1 + ⟨0, 1, 0, 0⟩), ?_⟩
        rw [map_neg, map_add]
        rfl
    · rw [Fin.sum_univ_three]
      change octNormSq octOne + octNormSq octI + octNormSq (-(octOne + octI)) = 4
      rw [octNormSq_one, octNormSq_I, hnorm1I]; norm_num
  have h1C : octOne ∈ (octSubalgebraOfLevel .C).carrier := (octSubalgebraOfLevel .C).one_mem
  have hIC : octI ∈ (octSubalgebraOfLevel .C).carrier := ⟨rfl, rfl, rfl⟩
  have hc0_mem : c0 ∈ (H3Subalgebra .C).carrier := diagAtom_mem_H3Subalgebra .C 0
  have hc1_mem : c1 ∈ (H3Subalgebra .C).carrier := diagAtom_mem_H3Subalgebra .C 1
  have hc2_mem : c2 ∈ (H3Subalgebra .C).carrier := by
    rw [hc2_eq]
    exact ⟨(octSubalgebraOfLevel .C).carrier.smul_mem _ h1C,
      (octSubalgebraOfLevel .C).carrier.smul_mem _ h1C,
      (octSubalgebraOfLevel .C).carrier.smul_mem _ h1C⟩
  have hc3_mem : c3 ∈ (H3Subalgebra .C).carrier := by
    rw [hc3_eq]
    exact ⟨(octSubalgebraOfLevel .C).carrier.smul_mem _ hIC,
      (octSubalgebraOfLevel .C).carrier.smul_mem _ ((octSubalgebraOfLevel .C).carrier.sub_mem h1C hIC),
      (octSubalgebraOfLevel .C).carrier.smul_mem _ ((octSubalgebraOfLevel .C).carrier.add_mem h1C hIC)⟩
  have h01_ne : c0 ≠ c1 := fun h => by
    have hv := congrArg (fun x : Albert => x.1 0) h; simp [c0, c1, diagAtom_fst] at hv
  have h02_ne : c0 ≠ c2 := fun h => by
    have hv := congrArg (fun x : Albert => x.1 0) h; rw [hc2_eq] at hv; simp [c0, diagAtom_fst] at hv; try norm_num at hv
  have h03_ne : c0 ≠ c3 := fun h => by
    have hv := congrArg (fun x : Albert => x.1 0) h; rw [hc3_eq] at hv; simp [c0, diagAtom_fst] at hv; try norm_num at hv
  have h12_ne : c1 ≠ c2 := fun h => by
    have hv := congrArg (fun x : Albert => x.1 1) h; rw [hc2_eq] at hv; simp [c1, diagAtom_fst] at hv; try norm_num at hv
  have h13_ne : c1 ≠ c3 := fun h => by
    have hv := congrArg (fun x : Albert => x.1 1) h; rw [hc3_eq] at hv; simp [c1, diagAtom_fst] at hv; try norm_num at hv
  have h23_ne : c2 ≠ c3 := fun h => by
    have hv := congrArg (fun x : Albert => x.1 0) h
    rw [hc2_eq, hc3_eq, mkAlbert_fst, mkAlbert_fst] at hv
    simp at hv; try norm_num at hv
  let T : Finset Albert := {c0, c1, c2, c3}
  have hcard : T.card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h01_ne, h02_ne, h03_ne]),
      Finset.card_insert_of_notMem (by simp [h12_ne, h13_ne]),
      Finset.card_pair h23_ne]
  have hT_atoms : ∀ p ∈ T, IsAtom p ∧ p ∈ (H3Subalgebra .C).carrier := by
    intro p hp
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact ⟨hc0_atom, hc0_mem⟩
    · exact ⟨hc1_atom, hc1_mem⟩
    · exact ⟨hc2_atom, hc2_mem⟩
    · exact ⟨hc3_atom, hc3_mem⟩
  have hgen : generatedSubalgebra (T : Set Albert) = H3Subalgebra .C := by
    refine le_antisymm (generatedSubalgebra_le (B := H3Subalgebra .C) fun p hp =>
        (hT_atoms p (Finset.mem_coe.mp hp)).2) ?_
    let B := generatedSubalgebra (T : Set Albert)
    have hc0B : c0 ∈ B.carrier := subset_generatedSubalgebra _ (by simp [T])
    have hc1B : c1 ∈ B.carrier := subset_generatedSubalgebra _ (by simp [T])
    have hc2B : c2 ∈ B.carrier := subset_generatedSubalgebra _ (by simp [T])
    have hc3B : c3 ∈ B.carrier := subset_generatedSubalgebra _ (by simp [T])
    have hd2B : diagAtom 2 ∈ B.carrier := by
      have hd : diagAtom 2 = albertUnit - c0 - c1 := by
        have hs := diagAtom_sum_eq_unit
        rw [Fin.sum_univ_three] at hs
        rw [← hs]; change diagAtom 2 = _ - diagAtom 0 - diagAtom 1; abel
      rw [hd]
      exact B.carrier.sub_mem (B.carrier.sub_mem B.unit_mem hc0B) hc1B
    have hs01B : slotElem01 octOne ∈ B.carrier := by
      have hp := peirce01_extract c2
      have heq : slotElem01 octOne = (3 : ℝ) • ((4 : ℝ) • jordanMul (diagAtom 0) (jordanMul (diagAtom 1) c2)) := by
        rw [hp, hc2_eq, mkAlbert_snd]
        change slotElem01 octOne = (3 : ℝ) • slotElem01 ((1 / 3 : ℝ) • octOne)
        rw [slotElem01.map_smul, smul_smul]; norm_num
      rw [heq]
      exact B.carrier.smul_mem _ (B.carrier.smul_mem _ (B.product_mem _ hc0B _ (B.product_mem _ hc1B _ hc2B)))
    have hs12B : slotElem12 octOne ∈ B.carrier := by
      have hp := peirce12_extract c2
      have heq : slotElem12 octOne = (3 : ℝ) • ((4 : ℝ) • jordanMul (diagAtom 1) (jordanMul (diagAtom 2) c2)) := by
        rw [hp, hc2_eq, mkAlbert_snd]
        change slotElem12 octOne = (3 : ℝ) • slotElem12 ((1 / 3 : ℝ) • octOne)
        rw [slotElem12.map_smul, smul_smul]; norm_num
      rw [heq]
      exact B.carrier.smul_mem _ (B.carrier.smul_mem _ (B.product_mem _ hc1B _ (B.product_mem _ hd2B _ hc2B)))
    have hs01_I : slotElem01 octI ∈ B.carrier := by
      have hp := peirce01_extract c3
      have heq : slotElem01 octI = (-4 : ℝ) • ((4 : ℝ) • jordanMul (diagAtom 0) (jordanMul (diagAtom 1) c3)) := by
        rw [hp, hc3_eq, mkAlbert_snd]
        change slotElem01 octI = (-4 : ℝ) • slotElem01 ((-1 / 4 : ℝ) • octI)
        rw [slotElem01.map_smul, smul_smul]; norm_num
      rw [heq]
      exact B.carrier.smul_mem _ (B.carrier.smul_mem _ (B.product_mem _ hc0B _ (B.product_mem _ hc1B _ hc3B)))
    obtain ⟨F, hFC, hF_eq, _⟩ := lem_five_coord B hc0B hc1B hd2B
      (Or.inr (Or.inl ⟨by simpa [octOne_eq_scalar] using hs01B,
        by simpa [octOne_eq_scalar] using hs12B⟩))
    have hIF : octI ∈ F.carrier := by
      change octI ∈ (F.carrier : Set Octonion)
      rw [hFC]
      exact hs01_I
    have hC_le_F : (octSubalgebraOfLevel .C).carrier ≤ F.carrier := by
      intro z hz
      have hz_exp : z = z.1.re • octOne + z.1.imI • octI := by
        rcases hz with ⟨hJ, hK, h2⟩
        apply Prod.ext
        · apply Quaternion.ext
          · rw [oct_add_fst, oct_smul_fst, oct_smul_fst]; simp [octOne, octI, octonionScalar]
          · rw [oct_add_fst, oct_smul_fst, oct_smul_fst]; simp [octOne, octI, octonionScalar]
          · rw [oct_add_fst, oct_smul_fst, oct_smul_fst]; simp [octOne, octI, octonionScalar, hJ]
          · rw [oct_add_fst, oct_smul_fst, oct_smul_fst]; simp [octOne, octI, octonionScalar, hK]
        · rw [oct_add_snd, oct_smul_snd, oct_smul_snd]; simp [octOne, octI, octonionScalar, h2]
      rw [hz_exp]
      exact F.carrier.add_mem (F.carrier.smul_mem _ F.one_mem) (F.carrier.smul_mem _ hIF)
    intro x hx
    dsimp only [B] at hF_eq ⊢
    rw [hF_eq]
    exact ⟨hC_le_F hx.1, hC_le_F hx.2.1, hC_le_F hx.2.2⟩
  have hM0 : (assocHermEquiv assocCD_C cM0).1 = c0 := by
    rw [assocHermEquiv_apply]
    apply albert_ext
    · rw [assocMatToAlbert_fst]; simp [c0, diagAtom_fst, cM0, assocCD_C]
    · rw [assocMatToAlbert_fst]; simp [c0, diagAtom_fst, cM0, assocCD_C]
    · rw [assocMatToAlbert_fst]; simp [c0, diagAtom_fst, cM0, assocCD_C]
    · rw [assocMatToAlbert_snd_0]
      apply oct_ext <;> simp [c0, diagAtom_snd, cM0, assocCD_C, complexToOctonion]
    · rw [assocMatToAlbert_snd_1]
      apply oct_ext <;> simp [c0, diagAtom_snd, cM0, assocCD_C, complexToOctonion]
    · rw [assocMatToAlbert_snd_2]
      apply oct_ext <;> simp [c0, diagAtom_snd, cM0, assocCD_C, complexToOctonion]
  have hM1 : (assocHermEquiv assocCD_C cM1).1 = c1 := by
    rw [assocHermEquiv_apply]
    apply albert_ext
    · rw [assocMatToAlbert_fst]; simp [c1, diagAtom_fst, cM1, assocCD_C]
    · rw [assocMatToAlbert_fst]; simp [c1, diagAtom_fst, cM1, assocCD_C]
    · rw [assocMatToAlbert_fst]; simp [c1, diagAtom_fst, cM1, assocCD_C]
    · rw [assocMatToAlbert_snd_0]
      apply oct_ext <;> simp [c1, diagAtom_snd, cM1, assocCD_C, complexToOctonion]
    · rw [assocMatToAlbert_snd_1]
      apply oct_ext <;> simp [c1, diagAtom_snd, cM1, assocCD_C, complexToOctonion]
    · rw [assocMatToAlbert_snd_2]
      apply oct_ext <;> simp [c1, diagAtom_snd, cM1, assocCD_C, complexToOctonion]
  have hM2 : (assocHermEquiv assocCD_C cM2).1 = c2 := by
    rw [assocHermEquiv_apply, hc2_eq]
    apply albert_ext
    · rw [assocMatToAlbert_fst]; simp [cM2, assocCD_C]; try norm_num
    · rw [assocMatToAlbert_fst]; simp [cM2, assocCD_C]; try norm_num
    · rw [assocMatToAlbert_fst]; simp [cM2, assocCD_C]; try norm_num
    · rw [assocMatToAlbert_snd_0, oct_smul_one_eq]
      dsimp only [cM2, assocCD_C]
      rw [complexToOctonion_apply]
      apply Prod.ext <;> apply Quaternion.ext <;> simp
    · rw [assocMatToAlbert_snd_1, oct_smul_one_eq]
      dsimp only [cM2, assocCD_C]
      rw [complexToOctonion_apply]
      apply Prod.ext <;> apply Quaternion.ext <;> simp
    · rw [assocMatToAlbert_snd_2, oct_smul_one_eq]
      dsimp only [cM2, assocCD_C]
      rw [complexToOctonion_apply]
      apply Prod.ext <;> apply Quaternion.ext <;> simp
  have hM3 : (assocHermEquiv assocCD_C cM3).1 = c3 := by
    rw [assocHermEquiv_apply, hc3_eq]
    apply albert_ext
    · rw [assocMatToAlbert_fst]; simp [cM3, assocCD_C]; try norm_num
    · rw [assocMatToAlbert_fst]; simp [cM3, assocCD_C]; try norm_num
    · rw [assocMatToAlbert_fst]; simp [cM3, assocCD_C]; try norm_num
    · rw [assocMatToAlbert_snd_0, oct_smul_I_eq]
      dsimp only [cM3, assocCD_C]
      rw [complexToOctonion_apply]
      (apply Prod.ext <;> apply Quaternion.ext <;> simp)
      try norm_num
    · rw [assocMatToAlbert_snd_1, oct_smul_sub1I_eq]
      dsimp only [cM3, assocCD_C]
      rw [complexToOctonion_apply]
      apply Prod.ext <;> apply Quaternion.ext <;> simp <;> try norm_num
    · rw [assocMatToAlbert_snd_2, oct_smul_add1I_eq]
      dsimp only [cM3, assocCD_C]
      rw [complexToOctonion_apply]
      apply Prod.ext <;> apply Quaternion.ext <;> simp <;> try norm_num
  have hIrr : IsIrredundant T := by
    refine ⟨fun p hp => (hT_atoms p hp).1, fun p hp => ?_⟩
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · obtain ⟨U0, h1m, h2m, h3m⟩ := prop_arity_lower_C_U0
      refine not_mem_of_erase_le_lt_finrank T hgen c0 (unitaryConjSubalgebraC U0 (H3Subalgebra .R)) ?_
        (by rw [unitaryConjSubalgebraC_H3R_finrank, finrank_H3Subalgebra]; norm_num)
      intro x hx
      simp only [T, Finset.mem_coe, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with ⟨hne, rfl | rfl | rfl | rfl⟩
      · exact absurd rfl hne
      · rw [← hM1]; exact h1m
      · rw [← hM2]; exact h2m
      · rw [← hM3]; exact h3m
    · obtain ⟨U1, h0m, h2m, h3m⟩ := prop_arity_lower_C_U1
      refine not_mem_of_erase_le_lt_finrank T hgen c1 (unitaryConjSubalgebraC U1 (H3Subalgebra .R)) ?_
        (by rw [unitaryConjSubalgebraC_H3R_finrank, finrank_H3Subalgebra]; norm_num)
      intro x hx
      simp only [T, Finset.mem_coe, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with ⟨hne, rfl | rfl | rfl | rfl⟩
      · rw [← hM0]; exact h0m
      · exact absurd rfl hne
      · rw [← hM2]; exact h2m
      · rw [← hM3]; exact h3m
    · obtain ⟨U2, h0m, h1m, h3m⟩ := prop_arity_lower_C_U2
      refine not_mem_of_erase_le_lt_finrank T hgen c2 (unitaryConjSubalgebraC U2 (H3Subalgebra .R)) ?_
        (by rw [unitaryConjSubalgebraC_H3R_finrank, finrank_H3Subalgebra]; norm_num)
      intro x hx
      simp only [T, Finset.mem_coe, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with ⟨hne, rfl | rfl | rfl | rfl⟩
      · rw [← hM0]; exact h0m
      · rw [← hM1]; exact h1m
      · exact absurd rfl hne
      · rw [← hM3]; exact h3m
    · refine not_mem_of_erase_le_lt_finrank T hgen c3 (H3Subalgebra .R) ?_
        (by rw [finrank_H3Subalgebra, finrank_H3Subalgebra]; norm_num)
      intro x hx
      simp only [T, Finset.mem_coe, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hx
      have h1R : octOne ∈ (octSubalgebraOfLevel .R).carrier := (octSubalgebraOfLevel .R).one_mem
      rcases hx with ⟨hne, rfl | rfl | rfl | rfl⟩
      · exact diagAtom_mem_H3Subalgebra .R 0
      · exact diagAtom_mem_H3Subalgebra .R 1
      · rw [hc2_eq]
        exact ⟨(octSubalgebraOfLevel .R).carrier.smul_mem _ h1R,
          (octSubalgebraOfLevel .R).carrier.smul_mem _ h1R,
          (octSubalgebraOfLevel .R).carrier.smul_mem _ h1R⟩
      · exact absurd rfl hne
  exact ⟨T, hcard, hT_atoms, hIrr, hgen⟩

private noncomputable def omit0_s2 : ℝ := 1 / Real.sqrt 2

private noncomputable def omit0_Ua : QuatMatrix3 :=
  Matrix.of ![![⟨omit0_s2, 0, 0, 0⟩, -⟨omit0_s2, 0, 0, 0⟩, 0],
    ![⟨omit0_s2, 0, 0, 0⟩, ⟨omit0_s2, 0, 0, 0⟩, 0], ![0, 0, 1]]

private noncomputable def omit0_Ub : QuatMatrix3 :=
  Matrix.of ![![1, 0, 0],
    ![0, ⟨0, -omit0_s2, 0, 0⟩, ⟨1 / 2, 1 / 2, 0, 0⟩],
    ![0, ⟨1 / 2, -1 / 2, 0, 0⟩, ⟨0, -omit0_s2, 0, 0⟩]]

private noncomputable def omit0_Uc : QuatMatrix3 :=
  Matrix.diagonal ![1, 1, ⟨0, 0, -omit0_s2, omit0_s2⟩]

private theorem omit0_unitary :
    star (omit0_Ua * omit0_Ub * omit0_Uc) * (omit0_Ua * omit0_Ub * omit0_Uc) = 1 ∧
    (omit0_Ua * omit0_Ub * omit0_Uc) * star (omit0_Ua * omit0_Ub * omit0_Uc) = 1 := by
  have hs2_sq : omit0_s2 ^ 2 = 1 / 2 := by
    dsimp only [omit0_s2]; rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)]
  have hs2_mul : omit0_s2 * omit0_s2 = 1 / 2 := by rw [← sq, hs2_sq]
  have hUa : star omit0_Ua * omit0_Ua = 1 ∧ omit0_Ua * star omit0_Ua = 1 := by
    constructor <;> (funext a b; fin_cases a <;> fin_cases b <;>
      apply Quaternion.ext <;>
      simp [omit0_Ua, Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_three, hs2_mul] <;>
      norm_num)
  have hUb : star omit0_Ub * omit0_Ub = 1 ∧ omit0_Ub * star omit0_Ub = 1 := by
    constructor <;> (funext a b; fin_cases a <;> fin_cases b <;>
      apply Quaternion.ext <;>
      simp [omit0_Ub, Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_three, hs2_mul] <;>
      (try ring_nf))
  have hUc : star omit0_Uc * omit0_Uc = 1 ∧ omit0_Uc * star omit0_Uc = 1 := by
    constructor <;> (funext a b; fin_cases a <;> fin_cases b <;>
      apply Quaternion.ext <;>
      simp [omit0_Uc, Matrix.mul_apply, Matrix.star_apply, Matrix.diagonal_apply, hs2_mul])
    all_goals norm_num
  refine ⟨?_, ?_⟩
  · rw [star_mul, star_mul]
    calc
      star omit0_Uc * (star omit0_Ub * star omit0_Ua) * (omit0_Ua * omit0_Ub * omit0_Uc)
        = star omit0_Uc * (star omit0_Ub * (star omit0_Ua * omit0_Ua) * omit0_Ub) * omit0_Uc := by simp only [mul_assoc]
      _ = star omit0_Uc * (star omit0_Ub * omit0_Ub) * omit0_Uc := by rw [hUa.1, mul_one]
      _ = star omit0_Uc * omit0_Uc := by rw [hUb.1, mul_one]
      _ = 1 := hUc.1
  · rw [star_mul, star_mul]
    calc
      omit0_Ua * omit0_Ub * omit0_Uc * (star omit0_Uc * (star omit0_Ub * star omit0_Ua))
        = omit0_Ua * (omit0_Ub * (omit0_Uc * star omit0_Uc) * star omit0_Ub) * star omit0_Ua := by simp only [mul_assoc]
      _ = omit0_Ua * (omit0_Ub * star omit0_Ub) * star omit0_Ua := by rw [hUc.2, mul_one]
      _ = omit0_Ua * star omit0_Ua := by rw [hUb.2, mul_one]
      _ = 1 := hUa.2

private theorem pentadDrop4_omit0_M1_conj (M1 : selfAdjoint QuatMatrix3)
    (hM1_eq : M1.1 = Matrix.of ![![(1 / 2 : ℝ) • (1 : Quaternion ℝ), (1 / 2 : ℝ) • (1 : Quaternion ℝ), 0],
        ![(1 / 2 : ℝ) • (1 : Quaternion ℝ), (1 / 2 : ℝ) • (1 : Quaternion ℝ), 0], ![0, 0, 0]]) :
    ∀ a b, ((star (omit0_Ua * omit0_Ub * omit0_Uc) * M1.1 * (omit0_Ua * omit0_Ub * omit0_Uc)) a b).imI = 0 ∧
           ((star (omit0_Ua * omit0_Ub * omit0_Uc) * M1.1 * (omit0_Ua * omit0_Ub * omit0_Uc)) a b).imJ = 0 := by
  have hs2_sq : omit0_s2 ^ 2 = 1 / 2 := by
    dsimp only [omit0_s2]; rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)]
  have hs2_mul : omit0_s2 * omit0_s2 = 1 / 2 := by rw [← sq, hs2_sq]
  have hconj : star (omit0_Ua * omit0_Ub * omit0_Uc) * M1.1 * (omit0_Ua * omit0_Ub * omit0_Uc) =
      star omit0_Uc * (star omit0_Ub * (star omit0_Ua * M1.1 * omit0_Ua) * omit0_Ub) * omit0_Uc := by
    rw [star_mul, star_mul]; simp only [mul_assoc]
  rw [hconj, hM1_eq]
  have hUaM1 : star omit0_Ua *
      Matrix.of ![![(1 / 2 : ℝ) • (1 : Quaternion ℝ), (1 / 2 : ℝ) • (1 : Quaternion ℝ), 0],
        ![(1 / 2 : ℝ) • (1 : Quaternion ℝ), (1 / 2 : ℝ) • (1 : Quaternion ℝ), 0], ![0, 0, 0]] * omit0_Ua =
      Matrix.of ![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]] := by
    funext r c; fin_cases r <;> fin_cases c <;> apply Quaternion.ext <;>
      (simp [omit0_Ua, Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_three] <;>
       (try ring_nf) <;> (try simp only [hs2_sq]) <;> norm_num)
  have hUbM1 : star omit0_Ub * Matrix.of ![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]] * omit0_Ub =
      Matrix.of ![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]] := by
    funext r c; fin_cases r <;> fin_cases c <;>
      simp [omit0_Ub, Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_three]
  have hUcM1 : star omit0_Uc * Matrix.of ![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]] * omit0_Uc =
      Matrix.of ![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]] := by
    funext r c; fin_cases r <;> fin_cases c <;>
      simp [omit0_Uc, Matrix.mul_apply, Matrix.star_apply, Matrix.diagonal_apply, Fin.sum_univ_three]
  rw [hUaM1, hUbM1, hUcM1]
  intro a b; fin_cases a <;> fin_cases b <;> simp

private theorem pentadDrop4_omit0_M2_conj (M2 : selfAdjoint QuatMatrix3)
    (hM2_eq : M2.1 = Matrix.of ![![(1 / 3 : ℝ) • (1 : Quaternion ℝ), (-1 / 3 : ℝ) • ⟨0, 1, 0, 0⟩, (1 / 3 : ℝ) • (1 : Quaternion ℝ)],
       ![(1 / 3 : ℝ) • ⟨0, 1, 0, 0⟩, (1 / 3 : ℝ) • (1 : Quaternion ℝ), (1 / 3 : ℝ) • ⟨0, 1, 0, 0⟩],
       ![(1 / 3 : ℝ) • (1 : Quaternion ℝ), (-1 / 3 : ℝ) • ⟨0, 1, 0, 0⟩, (1 / 3 : ℝ) • (1 : Quaternion ℝ)]]) :
    ∀ a b, ((star (omit0_Ua * omit0_Ub * omit0_Uc) * M2.1 * (omit0_Ua * omit0_Ub * omit0_Uc)) a b).imI = 0 ∧
           ((star (omit0_Ua * omit0_Ub * omit0_Uc) * M2.1 * (omit0_Ua * omit0_Ub * omit0_Uc)) a b).imJ = 0 := by
  have hs2_sq : omit0_s2 ^ 2 = 1 / 2 := by
    dsimp only [omit0_s2]; rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)]
  have hs2_mul : omit0_s2 * omit0_s2 = 1 / 2 := by rw [← sq, hs2_sq]
  have hs2_cu : omit0_s2 ^ 3 = omit0_s2 / 2 := by rw [pow_succ, hs2_sq]; ring
  have hconj : star (omit0_Ua * omit0_Ub * omit0_Uc) * M2.1 * (omit0_Ua * omit0_Ub * omit0_Uc) =
      star omit0_Uc * (star omit0_Ub * (star omit0_Ua * M2.1 * omit0_Ua) * omit0_Ub) * omit0_Uc := by
    rw [star_mul, star_mul]; simp only [mul_assoc]
  rw [hconj, hM2_eq]
  have hUaM2 : star omit0_Ua *
      Matrix.of ![![(1 / 3 : ℝ) • (1 : Quaternion ℝ), (-1 / 3 : ℝ) • ⟨0, 1, 0, 0⟩, (1 / 3 : ℝ) • (1 : Quaternion ℝ)],
       ![(1 / 3 : ℝ) • ⟨0, 1, 0, 0⟩, (1 / 3 : ℝ) • (1 : Quaternion ℝ), (1 / 3 : ℝ) • ⟨0, 1, 0, 0⟩],
       ![(1 / 3 : ℝ) • (1 : Quaternion ℝ), (-1 / 3 : ℝ) • ⟨0, 1, 0, 0⟩, (1 / 3 : ℝ) • (1 : Quaternion ℝ)]] * omit0_Ua =
      Matrix.of ![![⟨1 / 3, 0, 0, 0⟩, ⟨0, -1 / 3, 0, 0⟩, ⟨omit0_s2 / 3, omit0_s2 / 3, 0, 0⟩],
        ![⟨0, 1 / 3, 0, 0⟩, ⟨1 / 3, 0, 0, 0⟩, ⟨-omit0_s2 / 3, omit0_s2 / 3, 0, 0⟩],
        ![⟨omit0_s2 / 3, -omit0_s2 / 3, 0, 0⟩, ⟨-omit0_s2 / 3, -omit0_s2 / 3, 0, 0⟩, ⟨1 / 3, 0, 0, 0⟩]] := by
    funext r c; fin_cases r <;> fin_cases c <;> apply Quaternion.ext <;>
      (simp [omit0_Ua, Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_three] <;>
       (try ring_nf) <;> (try simp only [hs2_sq]) <;> (try ring))
  rw [hUaM2]
  have hUbM2 : star omit0_Ub *
      Matrix.of ![![⟨1 / 3, 0, 0, 0⟩, ⟨0, -1 / 3, 0, 0⟩, ⟨omit0_s2 / 3, omit0_s2 / 3, 0, 0⟩],
        ![⟨0, 1 / 3, 0, 0⟩, ⟨1 / 3, 0, 0, 0⟩, ⟨-omit0_s2 / 3, omit0_s2 / 3, 0, 0⟩],
        ![⟨omit0_s2 / 3, -omit0_s2 / 3, 0, 0⟩, ⟨-omit0_s2 / 3, -omit0_s2 / 3, 0, 0⟩, ⟨1 / 3, 0, 0, 0⟩]] * omit0_Ub =
      Matrix.of ![![⟨1 / 3, 0, 0, 0⟩, 0, ⟨1 / 3, -1 / 3, 0, 0⟩],
        ![0, 0, 0],
        ![⟨1 / 3, 1 / 3, 0, 0⟩, 0, ⟨2 / 3, 0, 0, 0⟩]] := by
    funext r c; fin_cases r <;> fin_cases c <;> apply Quaternion.ext <;>
      (simp [omit0_Ub, Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_three] <;>
       (try ring_nf) <;> (try simp only [hs2_sq, hs2_cu]) <;> (try ring))
  rw [hUbM2]
  have hUc_conj : ∀ (A : QuatMatrix3) (a b : Fin 3), (star omit0_Uc * A * omit0_Uc) a b =
      star ((![1, 1, ⟨0, 0, -omit0_s2, omit0_s2⟩] : Fin 3 → Quaternion ℝ) a) * A a b *
        (![1, 1, ⟨0, 0, -omit0_s2, omit0_s2⟩] : Fin 3 → Quaternion ℝ) b := fun A a b => by
    rw [Matrix.mul_apply, Finset.sum_eq_single b]
    · rw [Matrix.mul_apply, Finset.sum_eq_single a]
      · simp [omit0_Uc, Matrix.star_apply]
      · intro c _ hca; simp [omit0_Uc, Matrix.star_apply, hca]
      · intro ha; exact absurd (Finset.mem_univ a) ha
    · intro c _ hcb; simp [omit0_Uc, hcb]
    · intro hb; exact absurd (Finset.mem_univ b) hb
  have hUcM2 : star omit0_Uc *
      Matrix.of ![![⟨1 / 3, 0, 0, 0⟩, 0, ⟨1 / 3, -1 / 3, 0, 0⟩],
        ![0, 0, 0],
        ![⟨1 / 3, 1 / 3, 0, 0⟩, 0, ⟨2 / 3, 0, 0, 0⟩]] * omit0_Uc =
      Matrix.of ![![⟨1 / 3, 0, 0, 0⟩, 0, ⟨0, 0, 0, 2 * omit0_s2 / 3⟩],
        ![0, 0, 0],
        ![⟨0, 0, 0, -2 * omit0_s2 / 3⟩, 0, ⟨2 / 3, 0, 0, 0⟩]] := by
    funext r c; rw [hUc_conj]; fin_cases r <;> fin_cases c <;> apply Quaternion.ext <;>
      (simp <;> (try ring_nf) <;> (try simp only [hs2_sq]) <;> (try ring))
  rw [hUcM2]
  intro a b; fin_cases a <;> fin_cases b <;> simp

private theorem pentadDrop4_omit0_M3_conj (M3 : selfAdjoint QuatMatrix3)
    (hM3_eq : M3.1 = Matrix.of ![![(1 / 2 : ℝ) • (1 : Quaternion ℝ), (-1 / 2 : ℝ) • ⟨0, 0, 1, 0⟩, 0],
       ![(1 / 2 : ℝ) • ⟨0, 0, 1, 0⟩, (1 / 2 : ℝ) • (1 : Quaternion ℝ), 0],
       ![0, 0, 0]]) :
    ∀ a b, ((star (omit0_Ua * omit0_Ub * omit0_Uc) * M3.1 * (omit0_Ua * omit0_Ub * omit0_Uc)) a b).imI = 0 ∧
           ((star (omit0_Ua * omit0_Ub * omit0_Uc) * M3.1 * (omit0_Ua * omit0_Ub * omit0_Uc)) a b).imJ = 0 := by
  have hs2_sq : omit0_s2 ^ 2 = 1 / 2 := by
    dsimp only [omit0_s2]; rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)]
  have hs2_mul : omit0_s2 * omit0_s2 = 1 / 2 := by rw [← sq, hs2_sq]
  have hconj : star (omit0_Ua * omit0_Ub * omit0_Uc) * M3.1 * (omit0_Ua * omit0_Ub * omit0_Uc) =
      star omit0_Uc * (star omit0_Ub * (star omit0_Ua * M3.1 * omit0_Ua) * omit0_Ub) * omit0_Uc := by
    rw [star_mul, star_mul]; simp only [mul_assoc]
  rw [hconj, hM3_eq]
  have hUaM3 : star omit0_Ua *
      Matrix.of ![![(1 / 2 : ℝ) • (1 : Quaternion ℝ), (-1 / 2 : ℝ) • ⟨0, 0, 1, 0⟩, 0],
       ![(1 / 2 : ℝ) • ⟨0, 0, 1, 0⟩, (1 / 2 : ℝ) • (1 : Quaternion ℝ), 0],
       ![0, 0, 0]] * omit0_Ua =
      Matrix.of ![![⟨1 / 2, 0, 0, 0⟩, ⟨0, 0, -1 / 2, 0⟩, 0],
        ![⟨0, 0, 1 / 2, 0⟩, ⟨1 / 2, 0, 0, 0⟩, 0],
        ![0, 0, 0]] := by
    funext r c; fin_cases r <;> fin_cases c <;> apply Quaternion.ext <;>
      (simp [omit0_Ua, Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_three] <;>
       (try ring_nf) <;> (try simp only [hs2_sq]) <;> (try ring))
  rw [hUaM3]
  have hUbM3 : star omit0_Ub *
      Matrix.of ![![⟨1 / 2, 0, 0, 0⟩, ⟨0, 0, -1 / 2, 0⟩, 0],
        ![⟨0, 0, 1 / 2, 0⟩, ⟨1 / 2, 0, 0, 0⟩, 0],
        ![0, 0, 0]] * omit0_Ub =
      Matrix.of ![![⟨1 / 2, 0, 0, 0⟩, ⟨0, 0, 0, -omit0_s2 / 2⟩, ⟨0, 0, -1 / 4, 1 / 4⟩],
        ![⟨0, 0, 0, omit0_s2 / 2⟩, ⟨1 / 4, 0, 0, 0⟩, ⟨-omit0_s2 / 4, omit0_s2 / 4, 0, 0⟩],
        ![⟨0, 0, 1 / 4, -1 / 4⟩, ⟨-omit0_s2 / 4, -omit0_s2 / 4, 0, 0⟩, ⟨1 / 4, 0, 0, 0⟩]] := by
    funext r c; fin_cases r <;> fin_cases c <;> apply Quaternion.ext <;>
      (simp [omit0_Ub, Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_three] <;>
       (try ring_nf) <;> (try simp only [hs2_sq]) <;> (try ring))
  rw [hUbM3]
  have hUc_conj : ∀ (A : QuatMatrix3) (a b : Fin 3), (star omit0_Uc * A * omit0_Uc) a b =
      star ((![1, 1, ⟨0, 0, -omit0_s2, omit0_s2⟩] : Fin 3 → Quaternion ℝ) a) * A a b *
        (![1, 1, ⟨0, 0, -omit0_s2, omit0_s2⟩] : Fin 3 → Quaternion ℝ) b := fun A a b => by
    rw [Matrix.mul_apply, Finset.sum_eq_single b]
    · rw [Matrix.mul_apply, Finset.sum_eq_single a]
      · simp [omit0_Uc, Matrix.star_apply]
      · intro c _ hca; simp [omit0_Uc, Matrix.star_apply, hca]
      · intro ha; exact absurd (Finset.mem_univ a) ha
    · intro c _ hcb; simp [omit0_Uc, hcb]
    · intro hb; exact absurd (Finset.mem_univ b) hb
  have hUcM3 : star omit0_Uc *
      Matrix.of ![![⟨1 / 2, 0, 0, 0⟩, ⟨0, 0, 0, -omit0_s2 / 2⟩, ⟨0, 0, -1 / 4, 1 / 4⟩],
        ![⟨0, 0, 0, omit0_s2 / 2⟩, ⟨1 / 4, 0, 0, 0⟩, ⟨-omit0_s2 / 4, omit0_s2 / 4, 0, 0⟩],
        ![⟨0, 0, 1 / 4, -1 / 4⟩, ⟨-omit0_s2 / 4, -omit0_s2 / 4, 0, 0⟩, ⟨1 / 4, 0, 0, 0⟩]] * omit0_Uc =
      Matrix.of ![![⟨1 / 2, 0, 0, 0⟩, ⟨0, 0, 0, -omit0_s2 / 2⟩, ⟨-omit0_s2 / 2, 0, 0, 0⟩],
        ![⟨0, 0, 0, omit0_s2 / 2⟩, ⟨1 / 4, 0, 0, 0⟩, ⟨0, 0, 0, -1 / 4⟩],
        ![⟨-omit0_s2 / 2, 0, 0, 0⟩, ⟨0, 0, 0, 1 / 4⟩, ⟨1 / 4, 0, 0, 0⟩]] := by
    funext r c; rw [hUc_conj]; fin_cases r <;> fin_cases c <;> apply Quaternion.ext <;>
      (simp <;> (try ring_nf) <;> (try simp only [hs2_sq]) <;> (try ring))
  rw [hUcM3]
  intro a b; fin_cases a <;> fin_cases b <;> simp

private theorem pentadDrop4_omit0_in_conjH3K :
    ∃ (U : QuatMatrix3) (h1 : star U * U = 1) (h2 : U * star U = 1),
      ∀ m : Fin 4, m ≠ 0 →
        pentadDrop 4 m ∈ (unitaryConjSubalgebraH U h1 h2 (jordanSubalgebraH3 octComplexKSubalgebra)).carrier := by
  let qi : Quaternion ℝ := ⟨0, 1, 0, 0⟩
  let qj : Quaternion ℝ := ⟨0, 0, 1, 0⟩
  let U : QuatMatrix3 := omit0_Ua * omit0_Ub * omit0_Uc
  have h1 : star U * U = 1 := omit0_unitary.1
  have h2 : U * star U = 1 := omit0_unitary.2
  let M1 : selfAdjoint QuatMatrix3 :=
    ⟨Matrix.of ![![(1 / 2 : ℝ) • (1 : Quaternion ℝ), (1 / 2 : ℝ) • (1 : Quaternion ℝ), 0],
        ![(1 / 2 : ℝ) • (1 : Quaternion ℝ), (1 / 2 : ℝ) • (1 : Quaternion ℝ), 0], ![0, 0, 0]], by
      rw [selfAdjoint.mem_iff]; funext a b; fin_cases a <;> fin_cases b <;>
        apply Quaternion.ext <;> simp [Matrix.star_apply]⟩
  let M2 : selfAdjoint QuatMatrix3 :=
    ⟨Matrix.of ![![(1 / 3 : ℝ) • (1 : Quaternion ℝ), (-1 / 3 : ℝ) • qi, (1 / 3 : ℝ) • (1 : Quaternion ℝ)],
       ![(1 / 3 : ℝ) • qi, (1 / 3 : ℝ) • (1 : Quaternion ℝ), (1 / 3 : ℝ) • qi],
       ![(1 / 3 : ℝ) • (1 : Quaternion ℝ), (-1 / 3 : ℝ) • qi, (1 / 3 : ℝ) • (1 : Quaternion ℝ)]], by
      rw [selfAdjoint.mem_iff]; funext a b; fin_cases a <;> fin_cases b <;>
        apply Quaternion.ext <;> simp [Matrix.star_apply, qi] <;> norm_num⟩
  let M3 : selfAdjoint QuatMatrix3 :=
    ⟨Matrix.of ![![(1 / 2 : ℝ) • (1 : Quaternion ℝ), (-1 / 2 : ℝ) • qj, 0],
       ![(1 / 2 : ℝ) • qj, (1 / 2 : ℝ) • (1 : Quaternion ℝ), 0],
       ![0, 0, 0]], by
      rw [selfAdjoint.mem_iff]; funext a b; fin_cases a <;> fin_cases b <;>
        apply Quaternion.ext <;> simp [Matrix.star_apply, qj] <;> norm_num⟩
  have hM1 : (assocHermEquiv assocCD_H M1).1 = pentadDrop 4 1 := by
    rw [assocHermEquiv_apply, pentadDrop_4_1, pentadF_1_eq]
    apply albert_ext
    · rw [assocMatToAlbert_fst]; dsimp only [M1, assocCD_H]; simp; try norm_num
    · rw [assocMatToAlbert_fst]; dsimp only [M1, assocCD_H]; simp; try norm_num
    · rw [assocMatToAlbert_fst]; dsimp only [M1, assocCD_H]; simp
    · rw [assocMatToAlbert_snd_0]
      change quatEmbed1 ((1 / 2 : ℝ) • (1 : Quaternion ℝ)) = octonionScalar (1 / 2)
      rw [quatEmbed1_apply]
      apply oct_ext <;> simp [octonionScalar]
    · rw [assocMatToAlbert_snd_1]
      change quatEmbed1 0 = 0
      rw [map_zero]
    · rw [assocMatToAlbert_snd_2]
      change quatEmbed1 0 = 0
      rw [map_zero]
  have hM2 : (assocHermEquiv assocCD_H M2).1 = pentadDrop 4 2 := by
    rw [assocHermEquiv_apply, pentadDrop_4_2, pentadF_2_eq]
    apply albert_ext
    · rw [assocMatToAlbert_fst]; dsimp only [M2, assocCD_H]; simp; try norm_num
    · rw [assocMatToAlbert_fst]; dsimp only [M2, assocCD_H]; simp; try norm_num
    · rw [assocMatToAlbert_fst]; dsimp only [M2, assocCD_H]; simp; try norm_num
    · rw [assocMatToAlbert_snd_0]
      change quatEmbed1 ((-1 / 3 : ℝ) • qi) = (-1 / 3 : ℝ) • octI
      rw [quatEmbed1.map_smul, quatEmbed1_apply]; rfl
    · rw [assocMatToAlbert_snd_1]
      change quatEmbed1 ((1 / 3 : ℝ) • (1 : Quaternion ℝ)) = (1 / 3 : ℝ) • octOne
      rw [quatEmbed1.map_smul, quatEmbed1_apply]; rfl
    · rw [assocMatToAlbert_snd_2]
      change quatEmbed1 ((1 / 3 : ℝ) • qi) = (1 / 3 : ℝ) • octI
      rw [quatEmbed1.map_smul, quatEmbed1_apply]; rfl
  have hM3 : (assocHermEquiv assocCD_H M3).1 = pentadDrop 4 3 := by
    rw [assocHermEquiv_apply, pentadDrop_4_3, pentadF_3_eq]
    apply albert_ext
    · rw [assocMatToAlbert_fst]; dsimp only [M3, assocCD_H]; simp; try norm_num
    · rw [assocMatToAlbert_fst]; dsimp only [M3, assocCD_H]; simp; try norm_num
    · rw [assocMatToAlbert_fst]; dsimp only [M3, assocCD_H]; simp
    · rw [assocMatToAlbert_snd_0]
      change quatEmbed1 ((-1 / 2 : ℝ) • qj) = (-1 / 2 : ℝ) • octJ
      rw [quatEmbed1.map_smul, quatEmbed1_apply]; rfl
    · rw [assocMatToAlbert_snd_1]
      change quatEmbed1 0 = 0
      rw [map_zero]
    · rw [assocMatToAlbert_snd_2]
      change quatEmbed1 0 = 0
      rw [map_zero]
  refine ⟨U, h1, h2, fun m hm => ?_⟩
  fin_cases m
  · exact absurd rfl hm
  · change pentadDrop 4 1 ∈ _
    rw [← hM1]
    exact mem_unitaryConjSubalgebraH_K_of_matrix U h1 h2 M1 (pentadDrop4_omit0_M1_conj M1 rfl)
  · change pentadDrop 4 2 ∈ _
    rw [← hM2]
    exact mem_unitaryConjSubalgebraH_K_of_matrix U h1 h2 M2 (pentadDrop4_omit0_M2_conj M2 rfl)
  · change pentadDrop 4 3 ∈ _
    rw [← hM3]
    exact mem_unitaryConjSubalgebraH_K_of_matrix U h1 h2 M3 (pentadDrop4_omit0_M3_conj M3 rfl)

private theorem pentadDrop4_omit1_M2_conj (M2 : selfAdjoint QuatMatrix3)
    (hM2_eq : M2.1 = Matrix.of ![![(1 / 3 : ℝ) • (1 : Quaternion ℝ), (-1 / 3 : ℝ) • ⟨0, 1, 0, 0⟩, (1 / 3 : ℝ) • (1 : Quaternion ℝ)],
       ![(1 / 3 : ℝ) • ⟨0, 1, 0, 0⟩, (1 / 3 : ℝ) • (1 : Quaternion ℝ), (1 / 3 : ℝ) • ⟨0, 1, 0, 0⟩],
       ![(1 / 3 : ℝ) • (1 : Quaternion ℝ), (-1 / 3 : ℝ) • ⟨0, 1, 0, 0⟩, (1 / 3 : ℝ) • (1 : Quaternion ℝ)]]) :
    ∀ a b, ((star (Matrix.diagonal ![1, (⟨0, 1, 0, 0⟩ : Quaternion ℝ), 1]) * M2.1 *
        Matrix.diagonal ![1, (⟨0, 1, 0, 0⟩ : Quaternion ℝ), 1]) a b).imI = 0 ∧
      ((star (Matrix.diagonal ![1, (⟨0, 1, 0, 0⟩ : Quaternion ℝ), 1]) * M2.1 *
        Matrix.diagonal ![1, (⟨0, 1, 0, 0⟩ : Quaternion ℝ), 1]) a b).imJ = 0 := by
  let qi : Quaternion ℝ := ⟨0, 1, 0, 0⟩
  let Ud : QuatMatrix3 := Matrix.diagonal ![1, qi, 1]
  have hUd_conj : ∀ a b, (star Ud * M2.1 * Ud) a b =
      star ((![1, qi, 1] : Fin 3 → Quaternion ℝ) a) * M2.1 a b *
        (![1, qi, 1] : Fin 3 → Quaternion ℝ) b := fun a b => by
    rw [Matrix.mul_apply, Finset.sum_eq_single b]
    · rw [Matrix.mul_apply, Finset.sum_eq_single a]
      · simp [Ud, Matrix.star_apply]
      · intro c _ hca; simp [Ud, Matrix.star_apply, hca]
      · intro ha; exact absurd (Finset.mem_univ a) ha
    · intro c _ hcb; simp [Ud, hcb]
    · intro hb; exact absurd (Finset.mem_univ b) hb
  intro a b
  rw [show star (Matrix.diagonal ![1, qi, 1]) * M2.1 * Matrix.diagonal ![1, qi, 1] =
    star Ud * M2.1 * Ud from rfl, hUd_conj a b, hM2_eq]
  fin_cases a <;> fin_cases b <;>
    simp [qi]

private theorem pentadDrop4_omit1_M3_conj (M3 : selfAdjoint QuatMatrix3)
    (hM3_eq : M3.1 = Matrix.of ![![(1 / 2 : ℝ) • (1 : Quaternion ℝ), (-1 / 2 : ℝ) • ⟨0, 0, 1, 0⟩, 0],
       ![(1 / 2 : ℝ) • ⟨0, 0, 1, 0⟩, (1 / 2 : ℝ) • (1 : Quaternion ℝ), 0],
       ![0, 0, 0]]) :
    ∀ a b, ((star (Matrix.diagonal ![1, (⟨0, 1, 0, 0⟩ : Quaternion ℝ), 1]) * M3.1 *
        Matrix.diagonal ![1, (⟨0, 1, 0, 0⟩ : Quaternion ℝ), 1]) a b).imI = 0 ∧
      ((star (Matrix.diagonal ![1, (⟨0, 1, 0, 0⟩ : Quaternion ℝ), 1]) * M3.1 *
        Matrix.diagonal ![1, (⟨0, 1, 0, 0⟩ : Quaternion ℝ), 1]) a b).imJ = 0 := by
  let qi : Quaternion ℝ := ⟨0, 1, 0, 0⟩
  let Ud : QuatMatrix3 := Matrix.diagonal ![1, qi, 1]
  have hUd_conj : ∀ a b, (star Ud * M3.1 * Ud) a b =
      star ((![1, qi, 1] : Fin 3 → Quaternion ℝ) a) * M3.1 a b *
        (![1, qi, 1] : Fin 3 → Quaternion ℝ) b := fun a b => by
    rw [Matrix.mul_apply, Finset.sum_eq_single b]
    · rw [Matrix.mul_apply, Finset.sum_eq_single a]
      · simp [Ud, Matrix.star_apply]
      · intro c _ hca; simp [Ud, Matrix.star_apply, hca]
      · intro ha; exact absurd (Finset.mem_univ a) ha
    · intro c _ hcb; simp [Ud, hcb]
    · intro hb; exact absurd (Finset.mem_univ b) hb
  intro a b
  rw [show star (Matrix.diagonal ![1, qi, 1]) * M3.1 * Matrix.diagonal ![1, qi, 1] =
    star Ud * M3.1 * Ud from rfl, hUd_conj a b, hM3_eq]
  fin_cases a <;> fin_cases b <;>
    simp [qi, smul_eq_mul]

private theorem pentadDrop4_omit1_in_conjH3K :
    ∃ (Ud : QuatMatrix3) (h1 : star Ud * Ud = 1) (h2 : Ud * star Ud = 1),
      ∀ m : Fin 4, m ≠ 1 →
        pentadDrop 4 m ∈ (unitaryConjSubalgebraH Ud h1 h2 (jordanSubalgebraH3 octComplexKSubalgebra)).carrier := by
  let qi : Quaternion ℝ := ⟨0, 1, 0, 0⟩
  let qj : Quaternion ℝ := ⟨0, 0, 1, 0⟩
  let Ud : Matrix (Fin 3) (Fin 3) (Quaternion ℝ) := Matrix.diagonal ![1, qi, 1]
  have hdiag_unitary : ∀ d : Fin 3 → Quaternion ℝ,
      (∀ i, star (d i) * d i = 1 ∧ d i * star (d i) = 1) →
      star (Matrix.diagonal d) * Matrix.diagonal d = 1 ∧
        Matrix.diagonal d * star (Matrix.diagonal d) = 1 := fun d hd => by
    constructor <;>
      (funext a b
       rw [Matrix.mul_apply, Finset.sum_eq_single a]
       · by_cases hab : a = b
         · subst hab; simp [Matrix.star_apply, hd]
         · simp [Matrix.star_apply, hab, Ne.symm hab]
       · intro c _ hca; simp [Matrix.star_apply, Matrix.diagonal_apply, hca, hca.symm]
       · intro ha; exact absurd (Finset.mem_univ a) ha)
  have hUd_u := hdiag_unitary ![1, qi, 1] fun i => by
    fin_cases i <;> constructor <;> apply Quaternion.ext <;> simp [qi]
  have h1 : star Ud * Ud = 1 := hUd_u.1
  have h2 : Ud * star Ud = 1 := hUd_u.2
  have hUd_conj_entry : ∀ (A : Matrix (Fin 3) (Fin 3) (Quaternion ℝ)) (a b : Fin 3),
      (star Ud * A * Ud) a b = star ((![1, qi, 1] : Fin 3 → Quaternion ℝ) a) * A a b *
        (![1, qi, 1] : Fin 3 → Quaternion ℝ) b := fun A a b => by
    rw [Matrix.mul_apply, Finset.sum_eq_single b]
    · rw [Matrix.mul_apply, Finset.sum_eq_single a]
      · simp [Ud, Matrix.star_apply]
      · intro c _ hca; simp [Ud, Matrix.star_apply, hca]
      · intro ha; exact absurd (Finset.mem_univ a) ha
    · intro c _ hcb; simp [Ud, hcb]
    · intro hb; exact absurd (Finset.mem_univ b) hb
  let M0 : selfAdjoint QuatMatrix3 :=
    ⟨Matrix.of ![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], by
      rw [selfAdjoint.mem_iff]; funext a b; fin_cases a <;> fin_cases b <;>
        apply Quaternion.ext <;> simp [Matrix.star_apply]⟩
  let M2 : selfAdjoint QuatMatrix3 :=
    ⟨Matrix.of ![![(1 / 3 : ℝ) • (1 : Quaternion ℝ), (-1 / 3 : ℝ) • qi, (1 / 3 : ℝ) • (1 : Quaternion ℝ)],
       ![(1 / 3 : ℝ) • qi, (1 / 3 : ℝ) • (1 : Quaternion ℝ), (1 / 3 : ℝ) • qi],
       ![(1 / 3 : ℝ) • (1 : Quaternion ℝ), (-1 / 3 : ℝ) • qi, (1 / 3 : ℝ) • (1 : Quaternion ℝ)]], by
      rw [selfAdjoint.mem_iff]; funext a b; fin_cases a <;> fin_cases b <;>
        apply Quaternion.ext <;> simp [Matrix.star_apply, qi] <;> norm_num⟩
  let M3 : selfAdjoint QuatMatrix3 :=
    ⟨Matrix.of ![![(1 / 2 : ℝ) • (1 : Quaternion ℝ), (-1 / 2 : ℝ) • qj, 0],
       ![(1 / 2 : ℝ) • qj, (1 / 2 : ℝ) • (1 : Quaternion ℝ), 0],
       ![0, 0, 0]], by
      rw [selfAdjoint.mem_iff]; funext a b; fin_cases a <;> fin_cases b <;>
        apply Quaternion.ext <;> simp [Matrix.star_apply, qj] <;> norm_num⟩
  have hM0 : (assocHermEquiv assocCD_H M0).1 = pentadDrop 4 0 := by
    rw [assocHermEquiv_apply, pentadDrop_4_0, pentadF_0_eq]
    apply albert_ext
    · rw [assocMatToAlbert_fst]; simp [M0, assocCD_H, diagAtom_fst]
    · rw [assocMatToAlbert_fst]; simp [M0, assocCD_H, diagAtom_fst]
    · rw [assocMatToAlbert_fst]; simp [M0, assocCD_H, diagAtom_fst]
    · rw [assocMatToAlbert_snd_0]; apply oct_ext <;> (dsimp only [M0, assocCD_H]; rw [quatEmbed1_apply]; simp [diagAtom_snd])
    · rw [assocMatToAlbert_snd_1]; apply oct_ext <;> (dsimp only [M0, assocCD_H]; rw [quatEmbed1_apply]; simp [diagAtom_snd])
    · rw [assocMatToAlbert_snd_2]; apply oct_ext <;> (dsimp only [M0, assocCD_H]; rw [quatEmbed1_apply]; simp [diagAtom_snd])
  have hM2 : (assocHermEquiv assocCD_H M2).1 = pentadDrop 4 2 := by
    rw [assocHermEquiv_apply, pentadDrop_4_2, pentadF_2_eq]
    apply albert_ext
    · rw [assocMatToAlbert_fst]; dsimp only [M2, assocCD_H]; simp; try norm_num
    · rw [assocMatToAlbert_fst]; dsimp only [M2, assocCD_H]; simp; try norm_num
    · rw [assocMatToAlbert_fst]; dsimp only [M2, assocCD_H]; simp; try norm_num
    · rw [assocMatToAlbert_snd_0]
      change quatEmbed1 ((-1 / 3 : ℝ) • qi) = (-1 / 3 : ℝ) • octI
      rw [quatEmbed1.map_smul, quatEmbed1_apply]; rfl
    · rw [assocMatToAlbert_snd_1]
      change quatEmbed1 ((1 / 3 : ℝ) • (1 : Quaternion ℝ)) = (1 / 3 : ℝ) • octOne
      rw [quatEmbed1.map_smul, quatEmbed1_apply]; rfl
    · rw [assocMatToAlbert_snd_2]
      change quatEmbed1 ((1 / 3 : ℝ) • qi) = (1 / 3 : ℝ) • octI
      rw [quatEmbed1.map_smul, quatEmbed1_apply]; rfl
  have hM3 : (assocHermEquiv assocCD_H M3).1 = pentadDrop 4 3 := by
    rw [assocHermEquiv_apply, pentadDrop_4_3, pentadF_3_eq]
    apply albert_ext
    · rw [assocMatToAlbert_fst]; dsimp only [M3, assocCD_H]; simp; try norm_num
    · rw [assocMatToAlbert_fst]; dsimp only [M3, assocCD_H]; simp; try norm_num
    · rw [assocMatToAlbert_fst]; dsimp only [M3, assocCD_H]; simp
    · rw [assocMatToAlbert_snd_0]
      change quatEmbed1 ((-1 / 2 : ℝ) • qj) = (-1 / 2 : ℝ) • octJ
      rw [quatEmbed1.map_smul, quatEmbed1_apply]; rfl
    · rw [assocMatToAlbert_snd_1]
      change quatEmbed1 0 = 0
      rw [map_zero]
    · rw [assocMatToAlbert_snd_2]
      change quatEmbed1 0 = 0
      rw [map_zero]
  refine ⟨Ud, h1, h2, fun m hm => ?_⟩
  fin_cases m
  · change pentadDrop 4 0 ∈ _; rw [← hM0]
    refine mem_unitaryConjSubalgebraH_K_of_matrix Ud h1 h2 M0 fun a b => ?_
    rw [hUd_conj_entry]
    fin_cases a <;> fin_cases b <;> simp [M0, qi]
  · exact absurd rfl hm
  · change pentadDrop 4 2 ∈ _; rw [← hM2]
    exact mem_unitaryConjSubalgebraH_K_of_matrix Ud h1 h2 M2 (pentadDrop4_omit1_M2_conj M2 rfl)
  · change pentadDrop 4 3 ∈ _; rw [← hM3]
    exact mem_unitaryConjSubalgebraH_K_of_matrix Ud h1 h2 M3 (pentadDrop4_omit1_M3_conj M3 rfl)

private theorem prop_arity_lower_H :
    ∃ T : Finset Albert, T.card = 4 ∧
      (∀ p ∈ T, IsAtom p ∧ p ∈ (H3Subalgebra .H).carrier) ∧
      IsIrredundant T ∧ generatedSubalgebra (T : Set Albert) = H3Subalgebra .H := by
  have : Module.Finite ℝ Octonion :=
    inferInstanceAs (FiniteDimensional ℝ (Quaternion ℝ × Quaternion ℝ))
  have : Module.Finite ℝ Albert :=
    inferInstanceAs (FiniteDimensional ℝ ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
  let T : Finset Albert := Finset.univ.image (pentadDrop 4)
  have hinj : Function.Injective (pentadDrop 4) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> dsimp only at hab
    · rfl
    · exfalso; have h := congrArg (fun x : Albert => x.1 0) hab
      change (pentadDrop 4 0).1 0 = (pentadDrop 4 1).1 0 at h
      rw [pentadDrop_4_0, pentadDrop_4_1, pentadF_0_eq, pentadF_1_eq] at h
      simp [diagAtom_fst, mkAlbert_fst] at h; try norm_num at h
    · exfalso; have h := congrArg (fun x : Albert => x.1 0) hab
      change (pentadDrop 4 0).1 0 = (pentadDrop 4 2).1 0 at h
      rw [pentadDrop_4_0, pentadDrop_4_2, pentadF_0_eq, pentadF_2_eq] at h
      simp [diagAtom_fst, mkAlbert_fst] at h; try norm_num at h
    · exfalso; have h := congrArg (fun x : Albert => x.1 0) hab
      change (pentadDrop 4 0).1 0 = (pentadDrop 4 3).1 0 at h
      rw [pentadDrop_4_0, pentadDrop_4_3, pentadF_0_eq, pentadF_3_eq] at h
      simp [diagAtom_fst, mkAlbert_fst] at h; try norm_num at h
    · exfalso; have h := congrArg (fun x : Albert => x.1 0) hab
      change (pentadDrop 4 1).1 0 = (pentadDrop 4 0).1 0 at h
      rw [pentadDrop_4_1, pentadDrop_4_0, pentadF_0_eq, pentadF_1_eq] at h
      simp [diagAtom_fst, mkAlbert_fst] at h; try norm_num at h
    · rfl
    · exfalso; have h := congrArg (fun x : Albert => x.1 0) hab
      change (pentadDrop 4 1).1 0 = (pentadDrop 4 2).1 0 at h
      rw [pentadDrop_4_1, pentadDrop_4_2, pentadF_1_eq, pentadF_2_eq] at h
      simp [mkAlbert_fst] at h; try norm_num at h
    · exfalso; have h := congrArg (fun x : Albert => (x.2 0).1.re) hab
      change ((pentadDrop 4 1).2 0).1.re = ((pentadDrop 4 3).2 0).1.re at h
      rw [pentadDrop_4_1, pentadDrop_4_3, pentadF_1_eq, pentadF_3_eq] at h
      simp only [mkAlbert_snd, Matrix.cons_val_zero, oct_smul_fst, Quaternion.re_smul,
        smul_eq_mul] at h
      simp [octonionScalar, octJ] at h
      try norm_num at h
    · exfalso; have h := congrArg (fun x : Albert => x.1 0) hab
      change (pentadDrop 4 2).1 0 = (pentadDrop 4 0).1 0 at h
      rw [pentadDrop_4_2, pentadDrop_4_0, pentadF_0_eq, pentadF_2_eq] at h
      simp [diagAtom_fst, mkAlbert_fst] at h; try norm_num at h
    · exfalso; have h := congrArg (fun x : Albert => x.1 0) hab
      change (pentadDrop 4 2).1 0 = (pentadDrop 4 1).1 0 at h
      rw [pentadDrop_4_2, pentadDrop_4_1, pentadF_1_eq, pentadF_2_eq] at h
      simp [mkAlbert_fst] at h; try norm_num at h
    · rfl
    · exfalso; have h := congrArg (fun x : Albert => x.1 0) hab
      change (pentadDrop 4 2).1 0 = (pentadDrop 4 3).1 0 at h
      rw [pentadDrop_4_2, pentadDrop_4_3, pentadF_2_eq, pentadF_3_eq] at h
      simp [mkAlbert_fst] at h; try norm_num at h
    · exfalso; have h := congrArg (fun x : Albert => x.1 0) hab
      change (pentadDrop 4 3).1 0 = (pentadDrop 4 0).1 0 at h
      rw [pentadDrop_4_3, pentadDrop_4_0, pentadF_0_eq, pentadF_3_eq] at h
      simp [diagAtom_fst, mkAlbert_fst] at h; try norm_num at h
    · exfalso; have h := congrArg (fun x : Albert => (x.2 0).1.re) hab
      change ((pentadDrop 4 3).2 0).1.re = ((pentadDrop 4 1).2 0).1.re at h
      rw [pentadDrop_4_3, pentadDrop_4_1, pentadF_1_eq, pentadF_3_eq] at h
      simp only [mkAlbert_snd, Matrix.cons_val_zero, oct_smul_fst, Quaternion.re_smul,
        smul_eq_mul] at h
      simp [octonionScalar, octJ] at h
      try norm_num at h
    · exfalso; have h := congrArg (fun x : Albert => x.1 0) hab
      change (pentadDrop 4 3).1 0 = (pentadDrop 4 2).1 0 at h
      rw [pentadDrop_4_3, pentadDrop_4_2, pentadF_2_eq, pentadF_3_eq] at h
      simp [mkAlbert_fst] at h; try norm_num at h
    · rfl
  have hcard : T.card = 4 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_fin]
  have hpH : ∀ j : Fin 4, pentadDrop 4 j ∈ (H3Subalgebra .H).carrier := fun j => by
    fin_cases j
    · change pentadDrop 4 0 ∈ _; rw [pentadDrop_4_0, pentadF_0_eq]; exact diagAtom_mem_H3Subalgebra .H 0
    · change pentadDrop 4 1 ∈ _; rw [pentadDrop_4_1, pentadF_1_eq]
      exact ⟨rfl, rfl, rfl⟩
    · change pentadDrop 4 2 ∈ _; rw [pentadDrop_4_2, pentadF_2_eq]
      refine ⟨(octSubalgebraOfLevel .H).carrier.smul_mem _ rfl,
        (octSubalgebraOfLevel .H).carrier.smul_mem _ rfl,
        (octSubalgebraOfLevel .H).carrier.smul_mem _ rfl⟩
    · change pentadDrop 4 3 ∈ _; rw [pentadDrop_4_3, pentadF_3_eq]
      exact ⟨(octSubalgebraOfLevel .H).carrier.smul_mem _ rfl, rfl, rfl⟩
  have hT_atoms : ∀ p ∈ T, IsAtom p ∧ p ∈ (H3Subalgebra .H).carrier := by
    rintro p hp
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨pentadF_isAtom _, hpH j⟩
  have hcoe : (T : Set Albert) = Set.range (pentadDrop 4) := by
    ext x; simp [T]
  have hgen : generatedSubalgebra (T : Set Albert) = H3Subalgebra .H := by
    have hle : (generatedSubalgebra (T : Set Albert)).carrier ≤ (H3Subalgebra .H).carrier :=
      generatedSubalgebra_le (B := H3Subalgebra .H) fun x hx => (hT_atoms x (Finset.mem_coe.mp hx)).2
    have hfin_eq : Module.finrank ℝ (generatedSubalgebra (T : Set Albert)).carrier =
        Module.finrank ℝ (H3Subalgebra .H).carrier := by
      rw [hcoe, pentadDrop_generated_finrank 4, finrank_H3Subalgebra .H]
      simp
    have heq : (generatedSubalgebra (T : Set Albert)).carrier = (H3Subalgebra .H).carrier :=
      Submodule.eq_of_le_of_finrank_eq hle hfin_eq
    ext x
    exact show x ∈ (generatedSubalgebra (T : Set Albert)).carrier ↔
      x ∈ (H3Subalgebra .H).carrier from by rw [heq]
  have hJK_fin : ∀ F : OctSubalgebra, Module.finrank ℝ F.carrier = 2 →
      Module.finrank ℝ (jordanSubalgebraH3 F).carrier = 9 := fun F hF => by
    rw [finrank_jordanSubalgebraH3, hF]
  have hmem_p0 : pentadF 0 ∈ (H3Subalgebra .C).carrier := by
    rw [pentadF_0_eq]; exact diagAtom_mem_H3Subalgebra .C 0
  have hmem_p1 : pentadF 1 ∈ (H3Subalgebra .C).carrier := by
    rw [pentadF_1_eq]
    refine ⟨?_, (octSubalgebraOfLevel .C).carrier.zero_mem, (octSubalgebraOfLevel .C).carrier.zero_mem⟩
    rw [octonionScalar_eq_smul, ← octOne_eq_scalar]
    exact (octSubalgebraOfLevel .C).carrier.smul_mem _ (octSubalgebraOfLevel .C).one_mem
  have hmem_p2 : pentadF 2 ∈ (H3Subalgebra .C).carrier := by
    rw [pentadF_2_eq]
    exact ⟨(octSubalgebraOfLevel .C).carrier.smul_mem _ ⟨rfl, rfl, rfl⟩,
      (octSubalgebraOfLevel .C).carrier.smul_mem _ (octSubalgebraOfLevel .C).one_mem,
      (octSubalgebraOfLevel .C).carrier.smul_mem _ ⟨rfl, rfl, rfl⟩⟩
  have hIrr : IsIrredundant T := by
    refine ⟨fun p hp => (hT_atoms p hp).1, fun p hp => ?_⟩
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp
    fin_cases j
    · obtain ⟨U, h1, h2, hmem⟩ := pentadDrop4_omit0_in_conjH3K
      let BK := jordanSubalgebraH3 octComplexKSubalgebra
      have hBK_le : BK.carrier ≤ (H3Subalgebra .H).carrier := fun x hx =>
        ⟨hx.1.2.2, hx.2.1.2.2, hx.2.2.2.2⟩
      let B0 := unitaryConjSubalgebraH U h1 h2 BK
      refine not_mem_of_erase_le_lt_finrank T hgen (pentadDrop 4 0) B0 ?_ ?_
      · intro x hx
        simp only [T, Finset.mem_coe, Finset.mem_erase, Finset.mem_image, Finset.mem_univ, true_and] at hx
        rcases hx with ⟨hne, m, rfl⟩
        exact hmem m fun hm => hne (by rw [hm])
      · rw [unitaryConjSubalgebraH_finrank U h1 h2 BK hBK_le,
          hJK_fin octComplexKSubalgebra finrank_octComplexKSubalgebra, finrank_H3Subalgebra]
        norm_num
    · obtain ⟨Ud, h1, h2, hmem⟩ := pentadDrop4_omit1_in_conjH3K
      let BK := jordanSubalgebraH3 octComplexKSubalgebra
      have hBK_le : BK.carrier ≤ (H3Subalgebra .H).carrier := fun x hx =>
        ⟨hx.1.2.2, hx.2.1.2.2, hx.2.2.2.2⟩
      let B1 := unitaryConjSubalgebraH Ud h1 h2 BK
      refine not_mem_of_erase_le_lt_finrank T hgen (pentadDrop 4 1) B1 ?_ ?_
      · intro x hx
        simp only [T, Finset.mem_coe, Finset.mem_erase, Finset.mem_image, Finset.mem_univ, true_and] at hx
        rcases hx with ⟨hne, m, rfl⟩
        exact hmem m fun hm => hne (by rw [hm])
      · rw [unitaryConjSubalgebraH_finrank Ud h1 h2 BK hBK_le,
          hJK_fin octComplexKSubalgebra finrank_octComplexKSubalgebra, finrank_H3Subalgebra]
        norm_num
    · -- Omit p₂: {p₀, p₁, p₃} lies in H₃(ℂ_j)
      refine not_mem_of_erase_le_lt_finrank T hgen (pentadDrop 4 2)
        (jordanSubalgebraH3 octComplexJSubalgebra) ?_ ?_
      · intro x hx
        simp only [T, Finset.mem_coe, Finset.mem_erase, Finset.mem_image, Finset.mem_univ, true_and] at hx
        rcases hx with ⟨hne, m, rfl⟩
        fin_cases m
        · change pentadDrop 4 0 ∈ _; rw [pentadDrop_4_0, pentadF_0_eq]
          exact ⟨octComplexJSubalgebra.carrier.zero_mem, octComplexJSubalgebra.carrier.zero_mem,
            octComplexJSubalgebra.carrier.zero_mem⟩
        · change pentadDrop 4 1 ∈ _; rw [pentadDrop_4_1, pentadF_1_eq]
          refine ⟨?_, octComplexJSubalgebra.carrier.zero_mem, octComplexJSubalgebra.carrier.zero_mem⟩
          rw [octonionScalar_eq_smul, ← octOne_eq_scalar]
          exact octComplexJSubalgebra.carrier.smul_mem _ octComplexJSubalgebra.one_mem
        · exact absurd rfl hne
        · change pentadDrop 4 3 ∈ _; rw [pentadDrop_4_3, pentadF_3_eq]
          exact ⟨octComplexJSubalgebra.carrier.smul_mem _ ⟨rfl, rfl, rfl⟩,
            octComplexJSubalgebra.carrier.zero_mem, octComplexJSubalgebra.carrier.zero_mem⟩
      · rw [hJK_fin octComplexJSubalgebra finrank_octComplexJSubalgebra, finrank_H3Subalgebra]
        norm_num
    · -- Omit p₃: {p₀, p₁, p₂} lies in H₃(ℂ_i) = H₃(ℂ)
      refine not_mem_of_erase_le_lt_finrank T hgen (pentadDrop 4 3) (H3Subalgebra .C) ?_
        (by rw [finrank_H3Subalgebra, finrank_H3Subalgebra]; norm_num)
      intro x hx
      simp only [T, Finset.mem_coe, Finset.mem_erase, Finset.mem_image, Finset.mem_univ, true_and] at hx
      rcases hx with ⟨hne, m, rfl⟩
      fin_cases m
      · change pentadDrop 4 0 ∈ _; rw [pentadDrop_4_0]; exact hmem_p0
      · change pentadDrop 4 1 ∈ _; rw [pentadDrop_4_1]; exact hmem_p1
      · change pentadDrop 4 2 ∈ _; rw [pentadDrop_4_2]; exact hmem_p2
      · exact absurd rfl hne
  exact ⟨T, hcard, hT_atoms, hIrr, hgen⟩

private theorem pentadF_injective : Function.Injective pentadF := by
  intro i j hij
  by_contra hne
  have hsucc : ∀ a b : Fin 5, a ≠ b → ∃ k : Fin 4, b.succAbove k = a := fun a b hab => by
    fin_cases a <;> fin_cases b <;>
      first | exact absurd rfl hab | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩
  have hsub : Set.range pentadF ⊆ (generatedSubalgebra (Set.range (pentadDrop i))).carrier := by
    rintro _ ⟨m, rfl⟩
    by_cases hmi : m = i
    · subst hmi
      rw [hij]
      obtain ⟨k, hk⟩ := hsucc j m (Ne.symm hne)
      rw [show pentadF j = pentadDrop m k from by simp [pentadDrop, hk]]
      exact subset_generatedSubalgebra _ ⟨k, rfl⟩
    · obtain ⟨k, hk⟩ := hsucc m i hmi
      rw [show pentadF m = pentadDrop i k from by simp [pentadDrop, hk]]
      exact subset_generatedSubalgebra _ ⟨k, rfl⟩
  have htop : generatedSubalgebra (Set.range (pentadDrop i)) = ⊤ := by
    have hge : (⊤ : NativeJordanSubalgebra).carrier ≤
        (generatedSubalgebra (Set.range (pentadDrop i))).carrier := by
      rw [← (generatesAlbert_iff_generatedSubalgebra_eq_top pentadF).mp pentadF_generatesAlbert]
      exact generatedSubalgebra_le hsub
    ext x
    exact ⟨fun _ => Submodule.mem_top, fun _ => hge Submodule.mem_top⟩
  exact pentadDrop_not_generatesAlbert i ((generatesAlbert_iff_generatedSubalgebra_eq_top (pentadDrop i)).mpr htop)

private theorem prop_arity_lower_O :
    ∃ T : Finset Albert, T.card = 5 ∧
      (∀ p ∈ T, IsAtom p ∧ p ∈ (H3Subalgebra .O).carrier) ∧
      IsIrredundant T ∧ generatedSubalgebra (T : Set Albert) = H3Subalgebra .O := by
  let T : Finset Albert := Finset.univ.image pentadF
  have hcard : T.card = 5 := by
    rw [Finset.card_image_of_injective _ pentadF_injective, Finset.card_fin]
  have hT_atoms : ∀ p ∈ T, IsAtom p ∧ p ∈ (H3Subalgebra .O).carrier := by
    rintro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨pentadF_isAtom i, mem_H3O _⟩
  have hcoe : (T : Set Albert) = Set.range pentadF := by
    ext x; simp [T]
  have hgen : generatedSubalgebra (T : Set Albert) = H3Subalgebra .O := by
    rw [hcoe, H3Subalgebra_O_eq_top]
    exact (generatesAlbert_iff_generatedSubalgebra_eq_top pentadF).mp pentadF_generatesAlbert
  have hIrr : IsIrredundant T := by
    refine ⟨fun p hp => (hT_atoms p hp).1, fun p hp hp_in => ?_⟩
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    have hsucc : ∀ a b : Fin 5, a ≠ b → ∃ k : Fin 4, b.succAbove k = a := fun a b hab => by
      fin_cases a <;> fin_cases b <;>
        first | exact absurd rfl hab | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩
    have h_er : (T.erase (pentadF i) : Set Albert) ⊆ Set.range (pentadDrop i) := by
      intro x hx
      rw [Finset.mem_coe, Finset.mem_erase, Finset.mem_image] at hx
      rcases hx with ⟨hxi, m, _, rfl⟩
      have hmi : m ≠ i := fun h => hxi (h ▸ rfl)
      obtain ⟨k, hk⟩ := hsucc m i hmi
      exact ⟨k, by simp [pentadDrop, hk]⟩
    have hle : (generatedSubalgebra (T : Set Albert)).carrier ≤
        (generatedSubalgebra (Set.range (pentadDrop i))).carrier := by
      refine generatedSubalgebra_le fun x hx => ?_
      by_cases hxp : x = pentadF i
      · subst hxp
        exact generatedSubalgebra_mono h_er hp_in
      · exact subset_generatedSubalgebra _ (h_er (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hxp, hx⟩)))
    have htop : generatedSubalgebra (Set.range (pentadDrop i)) = ⊤ := by
      rw [hgen, H3Subalgebra_O_eq_top] at hle
      ext x
      exact ⟨fun _ => Submodule.mem_top, fun _ => hle Submodule.mem_top⟩
    exact pentadDrop_not_generatesAlbert i
      ((generatesAlbert_iff_generatedSubalgebra_eq_top (pentadDrop i)).mpr htop)
  exact ⟨T, hcard, hT_atoms, hIrr, hgen⟩

theorem prop_arity_lower (k : CDLevel) :
    ∃ T : Finset Albert, T.card = arityBound k ∧
      (∀ p ∈ T, IsAtom p ∧ p ∈ (H3Subalgebra k).carrier) ∧
      IsIrredundant T ∧ generatedSubalgebra (T : Set Albert) = H3Subalgebra k := by
  cases k with
  | R => exact prop_arity_lower_R
  | C => exact prop_arity_lower_C
  | H => exact prop_arity_lower_H
  | O => exact prop_arity_lower_O

/-! ### `prop:arity` upper bound: OctSubalgebra dimension ladder, Line-erase, and Bargmann -/

private theorem octSubalgebra_finrank_mem (G : OctSubalgebra) :
    Module.finrank ℝ G.carrier ∈ ({1, 2, 4, 8} : Set ℕ) := by
  have : Module.Finite ℝ Octonion :=
    inferInstanceAs (FiniteDimensional ℝ (Quaternion ℝ × Quaternion ℝ))
  by_cases h1 : G.carrier ≤ Submodule.span ℝ ({octOne} : Set Octonion)
  · have h1_le : Submodule.span ℝ ({octOne} : Set Octonion) ≤ G.carrier :=
      Submodule.span_le.mpr (Set.singleton_subset_iff.mpr G.one_mem)
    have hfin1 : Module.finrank ℝ (Submodule.span ℝ ({octOne} : Set Octonion)) = 1 :=
      finrank_span_singleton (fun h => by
        have := congrArg (fun x : Octonion => x.1.re) h
        simp [octOne, octonionScalar, oct_zero_fst] at this)
    rw [le_antisymm h1 h1_le, hfin1]
    simp
  · obtain ⟨u, huG, hu_not⟩ := Set.not_subset.mp h1
    obtain ⟨φ, hφ, ⟨q1, hq1⟩, ⟨q2, hq2⟩⟩ := exists_quatEmbedding_containing_pair octOne u
    let H := OctSubalgebra.generated ({u} : Set Octonion)
    have hHG : H.carrier ≤ G.carrier :=
      OctSubalgebra.generated_le _ G (Set.singleton_subset_iff.mpr huG)
    have hH_le : H.carrier ≤ LinearMap.range φ := by
      refine OctSubalgebra.generated_le _
        { carrier := LinearMap.range φ
          one_mem := ⟨1, by rw [hφ.map_one]; rfl⟩
          mul_mem := by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact ⟨a * b, hφ.map_mul a b⟩
          conj_mem := by rintro _ ⟨a, rfl⟩; exact ⟨star a, hφ.map_star a⟩ }
        (Set.singleton_subset_iff.mpr ⟨q2, hq2⟩)
    have hH_mem := octSubalgebra_le_quatEmbedding_finrank H φ hφ hH_le
    have hH_ne1 : Module.finrank ℝ H.carrier ≠ 1 := fun h => by
      have hspan := (octSubalgebra_le_quatEmbedding_finrank_one_iff H φ hφ hH_le).mp h
      apply hu_not
      rw [← hspan]
      exact OctSubalgebra.subset_generated _ rfl
    have hH24 : Module.finrank ℝ H.carrier = 2 ∨ Module.finrank ℝ H.carrier = 4 := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hH_mem
      rcases hH_mem with h | h | h
      · exact absurd h hH_ne1
      · exact Or.inl h
      · exact Or.inr h
    by_cases hHG_eq : H.carrier = G.carrier
    · rw [← hHG_eq]
      rcases hH24 with h2 | h4
      · simp [h2]
      · simp [h4]
    · have hHG_lt : H.carrier < G.carrier := lt_of_le_of_ne hHG hHG_eq
      rcases hH24 with hH2 | hH4
      · obtain ⟨v, hvG, hvH⟩ := Set.not_subset.mp (fun h => hHG_eq (le_antisymm hHG h))
        obtain ⟨ψ, hψ, ⟨p1, hp1⟩, ⟨p2, hp2⟩⟩ := exists_quatEmbedding_containing_pair u v
        let K := OctSubalgebra.generated ({u, v} : Set Octonion)
        have hKG : K.carrier ≤ G.carrier := OctSubalgebra.generated_le _ G (fun z hz => by
          rcases hz with rfl | rfl <;> assumption)
        have hHK : H.carrier ≤ K.carrier :=
          OctSubalgebra.generated_le _ K (Set.singleton_subset_iff.mpr (OctSubalgebra.subset_generated _ (Or.inl rfl)))
        have hK_le : K.carrier ≤ LinearMap.range ψ := by
          refine OctSubalgebra.generated_le _
            { carrier := LinearMap.range ψ
              one_mem := ⟨1, by rw [hψ.map_one]; rfl⟩
              mul_mem := by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact ⟨a * b, hψ.map_mul a b⟩
              conj_mem := by rintro _ ⟨a, rfl⟩; exact ⟨star a, hψ.map_star a⟩ }
            (fun z hz => by rcases hz with rfl | rfl; exact ⟨p1, hp1⟩; exact ⟨p2, hp2⟩)
        have hHK_lt : H.carrier < K.carrier := lt_of_le_of_ne hHK fun h =>
          hvH (h ▸ OctSubalgebra.subset_generated _ (Or.inr rfl))
        have hK_gt2 : 2 < Module.finrank ℝ K.carrier := by
          rw [← hH2]; exact Submodule.finrank_lt_finrank_of_lt hHK_lt
        have hK_mem := octSubalgebra_le_quatEmbedding_finrank K ψ hψ hK_le
        have hK4 : Module.finrank ℝ K.carrier = 4 := by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hK_mem
          omega
        have hK_eq := (octSubalgebra_le_quatEmbedding_finrank_four_iff K ψ hψ hK_le).mp hK4
        by_cases hKG_eq : K.carrier = G.carrier
        · rw [← hKG_eq, hK4]; simp
        · have hG_top := octSubalgebra_strict_gt_quatEmbedding_eq_top G ψ hψ
            (hK_eq ▸ lt_of_le_of_ne hKG hKG_eq)
          have hfin8 : Module.finrank ℝ G.carrier = 8 := by
            rw [hG_top, finrank_top]
            let eqv : Octonion ≃ₗ[ℝ] (Fin 8 → ℝ) :=
              { toFun := fun x => ![x.1.re, x.1.imI, x.1.imJ, x.1.imK,
                    x.2.re, x.2.imI, x.2.imJ, x.2.imK]
                invFun := fun f => (⟨f 0, f 1, f 2, f 3⟩, ⟨f 4, f 5, f 6, f 7⟩)
                left_inv := fun ⟨p, q⟩ => by apply Prod.ext <;> apply Quaternion.ext <;> rfl
                right_inv := fun f => by funext i; fin_cases i <;> rfl
                map_add' := fun a b => by funext i; fin_cases i <;> rfl
                map_smul' := fun r a => by funext i; fin_cases i <;> rfl }
            rw [eqv.finrank_eq, Module.finrank_fin_fun]
          rw [hfin8]; simp
      · have hH_eq := (octSubalgebra_le_quatEmbedding_finrank_four_iff H φ hφ hH_le).mp hH4
        have hG_top := octSubalgebra_strict_gt_quatEmbedding_eq_top G φ hφ (hH_eq ▸ hHG_lt)
        have hfin8 : Module.finrank ℝ G.carrier = 8 := by
          rw [hG_top, finrank_top]
          let eqv : Octonion ≃ₗ[ℝ] (Fin 8 → ℝ) :=
            { toFun := fun x => ![x.1.re, x.1.imI, x.1.imJ, x.1.imK,
                  x.2.re, x.2.imI, x.2.imJ, x.2.imK]
              invFun := fun f => (⟨f 0, f 1, f 2, f 3⟩, ⟨f 4, f 5, f 6, f 7⟩)
              left_inv := fun ⟨p, q⟩ => by apply Prod.ext <;> apply Quaternion.ext <;> rfl
              right_inv := fun f => by funext i; fin_cases i <;> rfl
              map_add' := fun a b => by funext i; fin_cases i <;> rfl
              map_smul' := fun r a => by funext i; fin_cases i <;> rfl }
          rw [eqv.finrank_eq, Module.finrank_fin_fun]
        rw [hfin8]; simp

private theorem octSubalgebra_strict_chain_card_le {k : CDLevel} {r : ℕ}
    (x : Fin r → Octonion) (hxK : ∀ i, x i ∈ (octSubalgebraOfLevel k).carrier)
    (hx_irr : ∀ i, x i ∉ (OctSubalgebra.generated {z | ∃ j, j ≠ i ∧ z = x j}).carrier) :
    r ≤ match k with | .R => 0 | .C => 1 | .H => 2 | .O => 3 := by
  have : Module.Finite ℝ Octonion :=
    inferInstanceAs (FiniteDimensional ℝ (Quaternion ℝ × Quaternion ℝ))
  let G : Fin (r + 1) → OctSubalgebra := fun m =>
    OctSubalgebra.generated {z | ∃ j : Fin r, j.1 < m.1 ∧ z = x j}
  have hG_mono : ∀ m : Fin r, (G m.castSucc).carrier < (G m.succ).carrier := fun m => by
    refine lt_of_le_of_ne (OctSubalgebra.generated_le _ (G m.succ) fun z ⟨j, hjm, hz⟩ => by
      subst hz
      exact OctSubalgebra.subset_generated _ ⟨j, Nat.lt_succ_of_lt hjm, rfl⟩) fun heq => ?_
    have hxm : x m ∈ (G m.succ).carrier :=
      OctSubalgebra.subset_generated _ ⟨m, by simp, rfl⟩
    rw [← heq] at hxm
    apply hx_irr m
    have hle_irr : (G m.castSucc).carrier ≤
        (OctSubalgebra.generated {z | ∃ j, j ≠ m ∧ z = x j}).carrier :=
      OctSubalgebra.generated_le _ _ fun z ⟨j, hjm, hz⟩ => by
        subst hz
        exact OctSubalgebra.subset_generated _ ⟨j, fun hji => Nat.lt_irrefl m.1 (hji ▸ hjm), rfl⟩
    exact hle_irr hxm
  have hG_strict : ∀ m : Fin r,
      Module.finrank ℝ (G m.castSucc).carrier < Module.finrank ℝ (G m.succ).carrier := fun m =>
    Submodule.finrank_lt_finrank_of_lt (hG_mono m)
  have hG_leK : ∀ m, (G m).carrier ≤ (octSubalgebraOfLevel k).carrier := fun m =>
    OctSubalgebra.generated_le _ (octSubalgebraOfLevel k) fun z ⟨j, _, hz⟩ => hz ▸ hxK j
  have hG_mem : ∀ m, Module.finrank ℝ (G m).carrier ∈ ({1, 2, 4, 8} : Set ℕ) :=
    fun m => octSubalgebra_finrank_mem (G m)
  have h0_ge1 : 1 ≤ Module.finrank ℝ (G 0).carrier := by
    have := hG_mem 0
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    omega
  cases k with
  | R =>
    by_contra hgt
    dsimp only at hgt
    have hr1 : 1 ≤ r := by omega
    have hlt0 := hG_strict ⟨0, hr1⟩
    have htop : Module.finrank ℝ (G ⟨1, Nat.succ_le_succ hr1⟩).carrier ≤ 1 := calc
      Module.finrank ℝ (G ⟨1, Nat.succ_le_succ hr1⟩).carrier
        ≤ Module.finrank ℝ (octSubalgebraOfLevel .R).carrier := Submodule.finrank_mono (hG_leK _)
      _ = 1 := octSubalgebraOfLevel_finrank .R
    change Module.finrank ℝ (G 0).carrier < Module.finrank ℝ (G ⟨1, Nat.succ_le_succ hr1⟩).carrier at hlt0
    omega
  | C =>
    by_contra hgt
    dsimp only at hgt
    have hr2 : 2 ≤ r := by omega
    have hlt0 := hG_strict ⟨0, by omega⟩
    have hlt1 := hG_strict ⟨1, by omega⟩
    have htop : Module.finrank ℝ (G ⟨2, Nat.succ_le_succ hr2⟩).carrier ≤ 2 := calc
      Module.finrank ℝ (G ⟨2, Nat.succ_le_succ hr2⟩).carrier
        ≤ Module.finrank ℝ (octSubalgebraOfLevel .C).carrier := Submodule.finrank_mono (hG_leK _)
      _ = 2 := octSubalgebraOfLevel_finrank .C
    change Module.finrank ℝ (G 0).carrier < Module.finrank ℝ (G ⟨1, by omega⟩).carrier at hlt0
    change Module.finrank ℝ (G ⟨1, by omega⟩).carrier < Module.finrank ℝ (G ⟨2, by omega⟩).carrier at hlt1
    omega
  | H =>
    by_contra hgt
    dsimp only at hgt
    have hr3 : 3 ≤ r := by omega
    have hlt0 : Module.finrank ℝ (G 0).carrier < Module.finrank ℝ (G ⟨1, by omega⟩).carrier := hG_strict ⟨0, by omega⟩
    have hlt1 : Module.finrank ℝ (G ⟨1, by omega⟩).carrier < Module.finrank ℝ (G ⟨2, by omega⟩).carrier := hG_strict ⟨1, by omega⟩
    have hlt2 : Module.finrank ℝ (G ⟨2, by omega⟩).carrier < Module.finrank ℝ (G ⟨3, by omega⟩).carrier := hG_strict ⟨2, by omega⟩
    have hfinH : Module.finrank ℝ (octSubalgebraOfLevel .H).carrier = 4 := octSubalgebraOfLevel_finrank .H
    have htop : Module.finrank ℝ (G ⟨3, by omega⟩).carrier ≤ 4 := by
      rw [← hfinH]
      exact Submodule.finrank_mono (hG_leK _)
    have hm1 := hG_mem ⟨1, by omega⟩
    have hm2 := hG_mem ⟨2, by omega⟩
    have hm3 := hG_mem ⟨3, by omega⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm1 hm2 hm3
    rcases hm1 with h1 | h1 | h1 | h1 <;> rcases hm2 with h2 | h2 | h2 | h2 <;>
      rcases hm3 with h3 | h3 | h3 | h3 <;> omega
  | O =>
    by_contra hgt
    dsimp only at hgt
    have hr4 : 4 ≤ r := by omega
    have hlt0 : Module.finrank ℝ (G 0).carrier < Module.finrank ℝ (G ⟨1, by omega⟩).carrier := hG_strict ⟨0, by omega⟩
    have hlt1 : Module.finrank ℝ (G ⟨1, by omega⟩).carrier < Module.finrank ℝ (G ⟨2, by omega⟩).carrier := hG_strict ⟨1, by omega⟩
    have hlt2 : Module.finrank ℝ (G ⟨2, by omega⟩).carrier < Module.finrank ℝ (G ⟨3, by omega⟩).carrier := hG_strict ⟨2, by omega⟩
    have hlt3 : Module.finrank ℝ (G ⟨3, by omega⟩).carrier < Module.finrank ℝ (G ⟨4, by omega⟩).carrier := hG_strict ⟨3, by omega⟩
    have hfinO : Module.finrank ℝ (octSubalgebraOfLevel .O).carrier = 8 := octSubalgebraOfLevel_finrank .O
    have htop : Module.finrank ℝ (G ⟨4, by omega⟩).carrier ≤ 8 := by
      rw [← hfinO]
      exact Submodule.finrank_mono (hG_leK _)
    have hm1 := hG_mem ⟨1, by omega⟩
    have hm2 := hG_mem ⟨2, by omega⟩
    have hm3 := hG_mem ⟨3, by omega⟩
    have hm4 := hG_mem ⟨4, by omega⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm1 hm2 hm3 hm4
    rcases hm1 with h1 | h1 | h1 | h1 <;> rcases hm2 with h2 | h2 | h2 | h2 <;>
      rcases hm3 with h3 | h3 | h3 | h3 <;> rcases hm4 with h4 | h4 | h4 | h4 <;> omega

private theorem line_erase_upper_bound {k : CDLevel} (T : Finset Albert)
    (hT_atoms : ∀ p ∈ T, IsAtom p ∧ p ∈ (H3Subalgebra k).carrier)
    (hT_irr : IsIrredundant T)
    (hT_nonline : ¬ ∃ q : Albert, ∃ hq : IsAtom q, q ∈ (H3Subalgebra k).carrier ∧
      (T : Set Albert) ⊆ (lineSubalgebra q hq).carrier)
    (hcard4 : 4 ≤ T.card)
    (p : Albert) (hpT : p ∈ T)
    (q : Albert) (hq : IsAtom q) (hqK : q ∈ (H3Subalgebra k).carrier)
    (hsub : (T.erase p : Set Albert) ⊆ (lineSubalgebra q hq).carrier) :
    T.card ≤ match k with | .R => 2 | .C => 2 | .H => 4 | .O => 5 := by
  let S := T.erase p
  have hS_irr : IsIrredundant S := by
    refine ⟨fun a ha => hT_irr.1 a (Finset.mem_of_mem_erase ha), fun a ha ha_in => ?_⟩
    apply hT_irr.2 a (Finset.mem_of_mem_erase ha)
    exact generatedSubalgebra_mono (by
      intro z hz
      simp only [Finset.mem_coe, Finset.mem_erase] at hz ⊢
      exact ⟨hz.1, Finset.mem_of_mem_erase hz.2⟩) ha_in
  have hS_card : 3 ≤ S.card := by
    have := Finset.card_erase_add_one hpT
    dsimp only [S]
    omega
  have hS_orth := (lem_fiv_facts_b S hS_irr hS_card q hq hsub).2
  have hp_atom := (hT_atoms p hpT).1
  have hpK := (hT_atoms p hpT).2
  have hp_off : p ∉ (lineSubalgebra q hq).carrier := fun hp_in => by
    apply hT_nonline
    refine ⟨q, hq, hqK, fun z hz => ?_⟩
    by_cases hzp : z = p
    · exact hzp ▸ hp_in
    · exact hsub (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hzp, hz⟩))
  let n := S.card
  have hn : 2 ≤ n := by omega
  let eqv := (Fintype.equivFinOfCardEq (Fintype.card_coe S)).symm
  let s : Fin n → Albert := fun m => (eqv m).1
  have hs_inj : Function.Injective s := fun a b hab => eqv.injective (Subtype.ext hab)
  have hs_atom : ∀ m, IsAtom (s m) := fun m => (hT_atoms (s m) (Finset.mem_of_mem_erase (eqv m).2)).1
  have hs_mem : ∀ m, s m ∈ (H3Subalgebra k).carrier := fun m =>
    (hT_atoms (s m) (Finset.mem_of_mem_erase (eqv m).2)).2
  have hs_line : ∀ m, jordanMul q (s m) = 0 := fun m => hS_orth (s m) (eqv m).2
  let f := albertUnit - q
  let r := (albertTrace (quadraticMap f p))⁻¹ • quadraticMap f p
  have hr_ne : ∀ m, s m ≠ r ∧ s m ≠ f - r := fun m => by
    have hm_ne : ∀ w ∈ ({r, f - r} : Set Albert), s m = w → False := fun w hw heq => by
      let S' := S.erase (s m)
      have hS'_card : 2 ≤ S'.card := by
        have := Finset.card_erase_add_one (eqv m).2
        dsimp only [S', s]
        omega
      obtain ⟨s₁, hs₁, s₂, hs₂, hs₁₂⟩ := Finset.one_lt_card.mp (by omega : 1 < S'.card)
      have hs₁S : s₁ ∈ S := Finset.mem_of_mem_erase hs₁
      have hs₂S : s₂ ∈ S := Finset.mem_of_mem_erase hs₂
      have hsup := eq_fiv_support q s₁ s₂ hq
        (hT_atoms s₁ (Finset.mem_of_mem_erase hs₁S)).1
        (hT_atoms s₂ (Finset.mem_of_mem_erase hs₂S)).1
        (hS_orth s₁ hs₁S) (hS_orth s₂ hs₂S) hs₁₂
      let B := generatedSubalgebra (T.erase (s m) : Set Albert)
      have hS'_sub : (S' : Set Albert) ⊆ (T.erase (s m) : Set Albert) := fun z hz => by
        simp only [S', S, Finset.mem_coe, Finset.mem_erase] at hz ⊢
        exact ⟨hz.1, hz.2.2⟩
      have hp_ne_sm : p ≠ s m := Ne.symm (Finset.mem_erase.mp (eqv m).2).1
      have hpB : p ∈ B.carrier := subset_generatedSubalgebra _ (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hp_ne_sm, hpT⟩))
      have hs₁B : s₁ ∈ B.carrier := subset_generatedSubalgebra _ (hS'_sub hs₁)
      have hs₂B : s₂ ∈ B.carrier := subset_generatedSubalgebra _ (hS'_sub hs₂)
      have hfB : f ∈ B.carrier := by
        change albertUnit - q ∈ B.carrier
        rw [hsup.2]
        exact B.carrier.smul_mem _ (B.carrier.sub_mem (B.carrier.add_mem hs₁B hs₂B)
          (B.carrier.smul_mem _ (B.product_mem _ hs₁B _ hs₂B)))
      have hrB : r ∈ B.carrier := by
        change (albertTrace (quadraticMap f p))⁻¹ • quadraticMap f p ∈ B.carrier
        refine B.carrier.smul_mem _ ?_
        unfold quadraticMap; rw [two_nsmul]
        exact B.carrier.sub_mem
          (B.carrier.add_mem (B.product_mem _ hfB _ (B.product_mem _ hfB _ hpB))
            (B.product_mem _ hfB _ (B.product_mem _ hfB _ hpB)))
          (B.product_mem _ (B.product_mem _ hfB _ hfB) _ hpB)
      have hsmB : s m ∈ B.carrier := by
        rw [heq]
        rcases hw with rfl | rfl
        · exact hrB
        · exact B.carrier.sub_mem hfB hrB
      exact hT_irr.2 (s m) (Finset.mem_of_mem_erase (eqv m).2) hsmB
    exact ⟨fun h => hm_ne r (Or.inl rfl) h, fun h => hm_ne (f - r) (Or.inr rfl) h⟩
  obtain ⟨α, a, γ, x, ha0, ha1, hx_mem, hx0, hαq, _, hαp, hαs, _, _, _, _⟩ :=
    lem_five_line k hn q hq hqK p hp_atom hpK hp_off s hs_inj hs_atom hs_mem hs_line hr_ne
  obtain ⟨r₀, hr₀_pos, hx0_eq⟩ := hx0
  let m0 : Fin n := ⟨0, by omega⟩
  let eqv_rest := (Fintype.equivFinOfCardEq (α := ↥(Finset.univ.erase m0 : Finset (Fin n))) (n := n - 1)
    (by rw [Fintype.card_coe]; simp)).symm
  let x' : Fin (n - 1) → Octonion := fun j => x (eqv_rest j).1
  have hx'_mem : ∀ j, x' j ∈ (octSubalgebraOfLevel k).carrier := fun j => (hx_mem _).1
  have hx'_irr : ∀ j, x' j ∉ (OctSubalgebra.generated {z | ∃ j', j' ≠ j ∧ z = x' j'}).carrier := by
    intro j hj_in
    let m := (eqv_rest j).1
    have hm0 : m ≠ m0 := (Finset.mem_erase.mp (eqv_rest j).2).1
    let G_m := OctSubalgebra.generated {z | ∃ j', j' ≠ j ∧ z = x' j'}
    let B_m := generatedSubalgebra (T.erase (s m) : Set Albert)
    have hBm_le : B_m.carrier ≤ (H3Subalgebra k).carrier :=
      generatedSubalgebra_le (B := H3Subalgebra k) fun z hz =>
        (hT_atoms z (Finset.mem_of_mem_erase hz)).2
    let C_m : NativeJordanSubalgebra :=
      { carrier :=
          { carrier := {y : Albert | ∃ hy : y ∈ (H3Subalgebra k).carrier,
              (α.toLinearEquiv.symm ⟨y, hy⟩).1 ∈ B_m.carrier}
            add_mem' := fun {u v} ⟨hu, hu'⟩ ⟨hv, hv'⟩ =>
              ⟨(H3Subalgebra k).carrier.add_mem hu hv, by
                have heq : (⟨u + v, (H3Subalgebra k).carrier.add_mem hu hv⟩ : (H3Subalgebra k).carrier) =
                    ⟨u, hu⟩ + ⟨v, hv⟩ := rfl
                rw [heq, map_add, Submodule.coe_add]
                exact B_m.carrier.add_mem hu' hv'⟩
            zero_mem' := ⟨(H3Subalgebra k).carrier.zero_mem, by
              have heq : (⟨0, (H3Subalgebra k).carrier.zero_mem⟩ : (H3Subalgebra k).carrier) = 0 := rfl
              rw [heq, map_zero, Submodule.coe_zero]
              exact B_m.carrier.zero_mem⟩
            smul_mem' := fun c {u} ⟨hu, hu'⟩ =>
              ⟨(H3Subalgebra k).carrier.smul_mem c hu, by
                have heq : (⟨c • u, (H3Subalgebra k).carrier.smul_mem c hu⟩ : (H3Subalgebra k).carrier) =
                    c • ⟨u, hu⟩ := rfl
                rw [heq, map_smul, Submodule.coe_smul]
                exact B_m.carrier.smul_mem c hu'⟩ }
        unit_mem := ⟨(H3Subalgebra k).unit_mem, by
          change (α.symm.toLinearEquiv ⟨albertUnit, (H3Subalgebra k).unit_mem⟩).1 ∈ B_m.carrier
          rw [α.symm.map_unit]
          exact B_m.unit_mem⟩
        product_mem := fun u ⟨hu, hu'⟩ v ⟨hv, hv'⟩ =>
          ⟨(H3Subalgebra k).product_mem u hu v hv, by
            change (α.symm.toLinearEquiv ⟨jordanMul u v, (H3Subalgebra k).product_mem u hu v hv⟩).1 ∈ B_m.carrier
            rw [α.symm.map_jordan ⟨u, hu⟩ ⟨v, hv⟩]
            exact B_m.product_mem _ hu' _ hv'⟩ }
    have hα_in_Cm : ∀ z : Albert, ∀ hz : z ∈ B_m.carrier,
        (α.toLinearEquiv ⟨z, hBm_le hz⟩).1 ∈ C_m.carrier := fun z hz => by
      refine ⟨(α.toLinearEquiv ⟨z, hBm_le hz⟩).2, ?_⟩
      have hsub : (⟨(α.toLinearEquiv ⟨z, hBm_le hz⟩).1, (α.toLinearEquiv ⟨z, hBm_le hz⟩).2⟩ :
          (H3Subalgebra k).carrier) = α.toLinearEquiv ⟨z, hBm_le hz⟩ := rfl
      rw [hsub, α.toLinearEquiv.symm_apply_apply]
      exact hz
    have hp_ne_sm : p ≠ s m := Ne.symm (Finset.mem_erase.mp (eqv m).2).1
    have hp_Cm : (α.toLinearEquiv ⟨p, hpK⟩).1 ∈ C_m.carrier :=
      hα_in_Cm p (subset_generatedSubalgebra _ (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hp_ne_sm, hpT⟩)))
    have hs_Cm : ∀ m' : Fin n, m' ≠ m → (α.toLinearEquiv ⟨s m', hs_mem m'⟩).1 ∈ C_m.carrier :=
      fun m' hm' => hα_in_Cm (s m') (subset_generatedSubalgebra _ (Finset.mem_coe.mpr (Finset.mem_erase.mpr
        ⟨fun heq => hm' (hs_inj heq), Finset.mem_of_mem_erase (eqv m').2⟩)))
    obtain ⟨m₁, hm₁0, hm₁m⟩ : ∃ m₁ : Fin n, m₁ ≠ m0 ∧ m₁ ≠ m := by
      have hsub2 : ((Finset.univ.erase m0).erase m).Nonempty := by
        rw [← Finset.card_pos]
        have hc1 : (Finset.univ.erase m0).card = n - 1 := by simp [Finset.card_erase_of_mem]
        have hc2 : m ∈ Finset.univ.erase m0 := Finset.mem_erase.mpr ⟨hm0, Finset.mem_univ m⟩
        have := Finset.card_erase_add_one hc2
        omega
      obtain ⟨m₁, hm₁⟩ := hsub2
      exact ⟨m₁, (Finset.mem_erase.mp (Finset.mem_of_mem_erase hm₁)).1, (Finset.mem_erase.mp hm₁).1⟩
    have hd1_Cm : diagAtom 1 ∈ C_m.carrier := by
      have h0_Cm := hs_Cm m0 hm0.symm
      have h1_Cm := hs_Cm m₁ hm₁m
      have hq0 : jordanMul (diagAtom 1) (α.toLinearEquiv ⟨s m0, hs_mem m0⟩).1 = 0 := by
        have hm := congrArg (fun z : (H3Subalgebra k).carrier => z.1)
          (α.map_jordan ⟨q, hqK⟩ ⟨s m0, hs_mem m0⟩)
        have h0 : (⟨jordanMul q (s m0), (H3Subalgebra k).product_mem _ hqK _ (hs_mem m0)⟩ :
            (H3Subalgebra k).carrier) = 0 := Subtype.ext (hs_line m0)
        rw [h0, map_zero, Submodule.coe_zero] at hm
        dsimp only at hm
        rw [hαq] at hm
        exact hm.symm
      have hq1 : jordanMul (diagAtom 1) (α.toLinearEquiv ⟨s m₁, hs_mem m₁⟩).1 = 0 := by
        have hm := congrArg (fun z : (H3Subalgebra k).carrier => z.1)
          (α.map_jordan ⟨q, hqK⟩ ⟨s m₁, hs_mem m₁⟩)
        have h0 : (⟨jordanMul q (s m₁), (H3Subalgebra k).product_mem _ hqK _ (hs_mem m₁)⟩ :
            (H3Subalgebra k).carrier) = 0 := Subtype.ext (hs_line m₁)
        rw [h0, map_zero, Submodule.coe_zero] at hm
        dsimp only at hm
        rw [hαq] at hm
        exact hm.symm
      have hne01 : (α.toLinearEquiv ⟨s m0, hs_mem m0⟩).1 ≠ (α.toLinearEquiv ⟨s m₁, hs_mem m₁⟩).1 :=
        fun h => hm₁0.symm (hs_inj (congrArg (fun z : (H3Subalgebra k).carrier => z.1)
          (α.toLinearEquiv.injective (Subtype.ext h))))
      have hsupp := eq_fiv_support (diagAtom 1) (α.toLinearEquiv ⟨s m0, hs_mem m0⟩).1
        (α.toLinearEquiv ⟨s m₁, hs_mem m₁⟩).1 (diagAtom_isAtom 1)
        (iso_maps_atom α ⟨s m0, hs_mem m0⟩ (hs_atom m0))
        (iso_maps_atom α ⟨s m₁, hs_mem m₁⟩ (hs_atom m₁)) hq0 hq1 hne01
      have hcomp : albertUnit - diagAtom 1 ∈ C_m.carrier := by
        rw [hsupp.2]
        exact C_m.carrier.smul_mem _ (C_m.carrier.sub_mem (C_m.carrier.add_mem h0_Cm h1_Cm)
          (C_m.carrier.smul_mem _ (C_m.product_mem _ h0_Cm _ h1_Cm)))
      have heq : diagAtom 1 = albertUnit - (albertUnit - diagAtom 1) := by abel
      rw [heq]
      exact C_m.carrier.sub_mem C_m.unit_mem hcomp
    have hprod_p : jordanMul (diagAtom 1) (α.toLinearEquiv ⟨p, hpK⟩).1 =
        a • diagAtom 1 + (1 / 2 : ℝ) • slotElem12 (octonionScalar (Real.sqrt (a * (1 - a)))) := by
      have hj11 : jordanMul (diagAtom 1) (diagAtom 1) = diagAtom 1 := (diagAtom_isAtom 1).1
      have hj12 : jordanMul (diagAtom 1) (diagAtom 2) = 0 := by
        apply albert_ext <;> simp [jordanMul_diagAtom1, diagAtom_fst, diagAtom_snd,
          albert_zero_fst, albert_zero_snd]
      have hj1s : jordanMul (diagAtom 1) (slotElem12 (octonionScalar (Real.sqrt (a * (1 - a))))) =
          (1 / 2 : ℝ) • slotElem12 (octonionScalar (Real.sqrt (a * (1 - a)))) := by
        apply albert_ext <;>
          simp [jordanMul_diagAtom1, slotElem12_fst, slotElem12_snd_0, slotElem12_snd_1,
            slotElem12_snd_2, albert_smul_fst, albert_smul_snd]
      rw [hαp, jordanMul_add_right, jordanMul_add_right, jordanMul_smul_right, jordanMul_smul_right,
        hj11, hj12, hj1s, smul_zero, add_zero]
    have hs12_sqrt : slotElem12 (octonionScalar (Real.sqrt (a * (1 - a)))) ∈ C_m.carrier := by
      have hdiff : (2 : ℝ) • (jordanMul (diagAtom 1) (α.toLinearEquiv ⟨p, hpK⟩).1 - a • diagAtom 1) =
          slotElem12 (octonionScalar (Real.sqrt (a * (1 - a)))) := by
        rw [hprod_p]
        have : a • diagAtom 1 + (1 / 2 : ℝ) • slotElem12 (octonionScalar (Real.sqrt (a * (1 - a)))) -
            a • diagAtom 1 = (1 / 2 : ℝ) • slotElem12 (octonionScalar (Real.sqrt (a * (1 - a)))) := by abel
        rw [this, smul_smul]; norm_num
      rw [← hdiff]
      exact C_m.carrier.smul_mem _ (C_m.carrier.sub_mem (C_m.product_mem _ hd1_Cm _ hp_Cm)
        (C_m.carrier.smul_mem _ hd1_Cm))
    have hsqrt_pos : 0 < Real.sqrt (a * (1 - a)) := Real.sqrt_pos.mpr (mul_pos ha0 (sub_pos.mpr ha1))
    have hs12_Cm : slotElem12 octOne ∈ C_m.carrier := by
      have heq : slotElem12 octOne = (Real.sqrt (a * (1 - a)))⁻¹ •
          slotElem12 (octonionScalar (Real.sqrt (a * (1 - a)))) := by
        rw [← slotElem12.map_smul, octonionScalar_eq_smul, ← octOne_eq_scalar, smul_smul,
          inv_mul_cancel₀ hsqrt_pos.ne', one_smul]
      rw [heq]
      exact C_m.carrier.smul_mem _ hs12_sqrt
    have hd2_Cm : diagAtom 2 ∈ C_m.carrier := by
      have heq : diagAtom 2 = (1 - a)⁻¹ • ((α.toLinearEquiv ⟨p, hpK⟩).1 - a • diagAtom 1 -
          slotElem12 (octonionScalar (Real.sqrt (a * (1 - a))))) := by
        rw [hαp]
        have : a • diagAtom 1 + (1 - a) • diagAtom 2 +
            slotElem12 (octonionScalar (Real.sqrt (a * (1 - a)))) -
            a • diagAtom 1 - slotElem12 (octonionScalar (Real.sqrt (a * (1 - a)))) =
            (1 - a) • diagAtom 2 := by abel
        rw [this, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr ha1.ne'), one_smul]
      rw [heq]
      exact C_m.carrier.smul_mem _ (C_m.carrier.sub_mem (C_m.carrier.sub_mem hp_Cm
        (C_m.carrier.smul_mem _ hd1_Cm)) hs12_sqrt)
    have hd0_Cm : diagAtom 0 ∈ C_m.carrier := by
      have hs := diagAtom_sum_eq_unit
      rw [Fin.sum_univ_three] at hs
      have heq : diagAtom 0 = albertUnit - diagAtom 1 - diagAtom 2 := by rw [← hs]; abel
      rw [heq]
      exact C_m.carrier.sub_mem (C_m.carrier.sub_mem C_m.unit_mem hd1_Cm) hd2_Cm
    have hs02_of_s : ∀ m' : Fin n, m' ≠ m → slotElem02 (x m') ∈ C_m.carrier := fun m' hm' => by
      have hp := peirce02_extract (α.toLinearEquiv ⟨s m', hs_mem m'⟩).1
      have heq : slotElem02 (x m') = (4 : ℝ) • jordanMul (diagAtom 0)
          (jordanMul (diagAtom 2) (α.toLinearEquiv ⟨s m', hs_mem m'⟩).1) := by
        rw [hp, hαs m']
        simp [albert_add_snd, albert_smul_snd, diagAtom_snd, slotElem02_snd_1]
      rw [heq]
      exact C_m.carrier.smul_mem _ (C_m.product_mem _ hd0_Cm _
        (C_m.product_mem _ hd2_Cm _ (hs_Cm m' hm')))
    have hs02_Cm : slotElem02 octOne ∈ C_m.carrier := by
      have hs0 := hs02_of_s m0 hm0.symm
      rw [hx0_eq, octonionScalar_eq_smul, ← octOne_eq_scalar, slotElem02.map_smul] at hs0
      have heq : slotElem02 octOne = r₀⁻¹ • (r₀ • slotElem02 octOne) := by
        rw [smul_smul, inv_mul_cancel₀ hr₀_pos.ne', one_smul]
      rw [heq]
      exact C_m.carrier.smul_mem _ hs0
    have hs01_Cm : slotElem01 octOne ∈ C_m.carrier := by
      have hmul := C_m.product_mem _ hs02_Cm _ hs12_Cm
      rw [jordanMul_slotElem02_slotElem12, octonionConj_one, octonionMul_one_right] at hmul
      have heq : slotElem01 octOne = (2 : ℝ) • ((1 / 2 : ℝ) • slotElem01 octOne) := by
        rw [smul_smul]; norm_num
      rw [heq]
      exact C_m.carrier.smul_mem _ hmul
    obtain ⟨F_C, hFC_car, hF_C_eq, _⟩ := lem_five_coord C_m hd0_Cm hd1_Cm hd2_Cm
      (Or.inr (Or.inl ⟨by simpa [octOne_eq_scalar] using hs01_Cm,
        by simpa [octOne_eq_scalar] using hs12_Cm⟩))
    have hGm_le : G_m.carrier ≤ F_C.carrier := by
      refine OctSubalgebra.generated_le _ F_C fun z ⟨j', hj', hz⟩ => ?_
      subst hz
      have hm'_ne : (eqv_rest j').1 ≠ m := fun h => hj' (eqv_rest.injective (Subtype.ext h))
      have hs02_m' := hs02_of_s (eqv_rest j').1 hm'_ne
      have hmul := C_m.product_mem _ hs02_m' _ hs12_Cm
      rw [jordanMul_slotElem02_slotElem12, octonionConj_one, octonionMul_one_right] at hmul
      have heq : slotElem01 (x' j') = (2 : ℝ) • ((1 / 2 : ℝ) • slotElem01 (x' j')) := by
        rw [smul_smul]; norm_num
      change (x' j') ∈ (F_C.carrier : Set Octonion)
      rw [hFC_car]
      change slotElem01 (x' j') ∈ C_m.carrier
      rw [heq]
      exact C_m.carrier.smul_mem _ hmul
    have hxm_in_FC : x m ∈ F_C.carrier := hGm_le hj_in
    have hαsm_in : (α.toLinearEquiv ⟨s m, hs_mem m⟩).1 ∈ C_m.carrier := by
      rw [hF_C_eq, mem_jordanSubalgebraH3_iff, hαs m]
      simp only [albert_add_snd, albert_smul_snd,
        diagAtom_snd, slotElem02_snd_0, slotElem02_snd_1, slotElem02_snd_2,
        smul_zero, zero_add, add_zero]
      exact ⟨F_C.carrier.zero_mem, hxm_in_FC, F_C.carrier.zero_mem⟩
    rcases hαsm_in with ⟨hy', hsm_in_Bm⟩
    have hsub : (⟨(α.toLinearEquiv ⟨s m, hs_mem m⟩).1, hy'⟩ : (H3Subalgebra k).carrier) =
        α.toLinearEquiv ⟨s m, hs_mem m⟩ := rfl
    rw [hsub, α.toLinearEquiv.symm_apply_apply] at hsm_in_Bm
    exact hT_irr.2 (s m) (Finset.mem_of_mem_erase (eqv m).2) hsm_in_Bm
  have hchain := octSubalgebra_strict_chain_card_le x' hx'_mem hx'_irr
  have hS_eq : S.card = T.card - 1 := by
    have := Finset.card_erase_add_one hpT; dsimp only [S]; omega
  have hnm : n - 1 = T.card - 2 := by dsimp only [n]; omega
  cases k with
  | R => change T.card ≤ 2; change n - 1 ≤ 0 at hchain; omega
  | C => change T.card ≤ 2; change n - 1 ≤ 1 at hchain; omega
  | H => change T.card ≤ 4; change n - 1 ≤ 2 at hchain; omega
  | O => change T.card ≤ 5; change n - 1 ≤ 3 at hchain; omega

/-! ### Bargmann Invariant and Real Gram-Schmidt in `ℂ³` -/

private def vecIp3 (x y : Fin 3 → ℂ) : ℂ := ∑ a : Fin 3, star (x a) * y a

private theorem vecIp3_add_left (x₁ x₂ y : Fin 3 → ℂ) :
    vecIp3 (x₁ + x₂) y = vecIp3 x₁ y + vecIp3 x₂ y := by
  simp [vecIp3, add_mul, Finset.sum_add_distrib]

private theorem vecIp3_add_right (x y₁ y₂ : Fin 3 → ℂ) :
    vecIp3 x (y₁ + y₂) = vecIp3 x y₁ + vecIp3 x y₂ := by
  simp [vecIp3, mul_add, Finset.sum_add_distrib]

private theorem vecIp3_smul_right (c : ℂ) (x y : Fin 3 → ℂ) :
    vecIp3 x (c • y) = c * vecIp3 x y := by
  simp only [vecIp3, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => by ring

private theorem vecIp3_smul_left (c : ℂ) (x y : Fin 3 → ℂ) :
    vecIp3 (c • x) y = star c * vecIp3 x y := by
  simp only [vecIp3, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => by ring

private theorem vecIp3_conj_symm (x y : Fin 3 → ℂ) :
    star (vecIp3 x y) = vecIp3 y x := by
  simp [vecIp3, star_mul', mul_comm]

private theorem vecIp3_self_im (x : Fin 3 → ℂ) : (vecIp3 x x).im = 0 := by
  simp [vecIp3, Complex.im_sum, mul_comm]

private theorem vecIp3_self_re_nonneg (x : Fin 3 → ℂ) : 0 ≤ (vecIp3 x x).re := by
  simp only [vecIp3, Complex.re_sum, Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  refine Finset.sum_nonneg fun a _ => by ring_nf; nlinarith

private theorem vecIp3_self_eq_zero_iff (x : Fin 3 → ℂ) : vecIp3 x x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    simp only [vecIp3, Complex.re_sum, Complex.star_def, Complex.mul_re, Complex.conj_re,
      Complex.conj_im, Complex.zero_re] at hre
    have hsq : ∀ a : Fin 3, (x a).re * (x a).re - -(x a).im * (x a).im = 0 := fun a =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => by ring_nf; nlinarith)).mp hre a (Finset.mem_univ a)
    funext a
    have ha := hsq a
    apply Complex.ext <;> (simp; ring_nf at ha; nlinarith)
  · intro h; subst h; simp [vecIp3]

private noncomputable def projStep (x : Fin 3 → ℂ) (L : List (Fin 3 → ℂ)) : List (Fin 3 → ℂ) :=
  let z := x - ∑ u ∈ L.toFinset, (vecIp3 u x) • u
  if _hz : z = 0 then L
  else
    let r : ℂ := ((Real.sqrt (vecIp3 z z).re)⁻¹ : ℝ)
    L ++ [r • z]

private theorem projStep_preserves_orthonormal (x : Fin 3 → ℂ) (L : List (Fin 3 → ℂ))
    (hnodup : L.Nodup)
    (hnorm : ∀ u ∈ L, vecIp3 u u = 1)
    (horth : ∀ u ∈ L, ∀ v ∈ L, u ≠ v → vecIp3 u v = 0) :
    (projStep x L).Nodup ∧
    (∀ u ∈ projStep x L, vecIp3 u u = 1) ∧
    (∀ u ∈ projStep x L, ∀ v ∈ projStep x L, u ≠ v → vecIp3 u v = 0) ∧
    x ∈ Submodule.span ℂ (projStep x L).toFinset := by
  dsimp only [projStep]
  set z := x - ∑ u ∈ L.toFinset, (vecIp3 u x) • u
  have horth_z : ∀ w ∈ L, vecIp3 w z = 0 := fun w hw => by
    have hzw : vecIp3 w z = vecIp3 w x - vecIp3 w (∑ u ∈ L.toFinset, (vecIp3 u x) • u) := by
      simp [z, vecIp3_add_right, sub_eq_add_neg]
      have : vecIp3 w (- ∑ u ∈ L.toFinset, (vecIp3 u x) • u) =
          - vecIp3 w (∑ u ∈ L.toFinset, (vecIp3 u x) • u) := by
        simpa using vecIp3_smul_right (-1 : ℂ) w (∑ u ∈ L.toFinset, (vecIp3 u x) • u)
      rw [this]
    have hsum : vecIp3 w (∑ u ∈ L.toFinset, (vecIp3 u x) • u) =
        ∑ u ∈ L.toFinset, vecIp3 u x * vecIp3 w u := by
      clear hzw
      induction L.toFinset using Finset.induction_on with
      | empty => simp [vecIp3]
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, vecIp3_add_right, vecIp3_smul_right, ih]
    rw [hzw, hsum, Finset.sum_eq_single w]
    · rw [hnorm w hw, mul_one, sub_self]
    · intro u hu hne; rw [horth w hw u (List.mem_toFinset.mp hu) hne.symm, mul_zero]
    · intro hnw; exact absurd (List.mem_toFinset.mpr hw) hnw
  by_cases hz : z = 0
  · simp only [hz, ↓reduceDIte]
    refine ⟨hnodup, hnorm, horth, ?_⟩
    have hx_eq : x = ∑ u ∈ L.toFinset, (vecIp3 u x) • u := sub_eq_zero.mp hz
    rw [hx_eq]
    exact Submodule.sum_mem _ fun u hu =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.mpr hu))
  · simp only [hz, ↓reduceDIte]
    have hzz_pos : 0 < (vecIp3 z z).re := by
      refine lt_of_le_of_ne (vecIp3_self_re_nonneg z) (Ne.symm fun h0 => hz ?_)
      rw [← vecIp3_self_eq_zero_iff]
      exact Complex.ext h0 (by simpa using vecIp3_self_im z)
    let r : ℂ := ((Real.sqrt (vecIp3 z z).re)⁻¹ : ℝ)
    let w := r • z
    have hwnorm : vecIp3 w w = 1 := by
      rw [vecIp3_smul_left, vecIp3_smul_right]
      have hsr : star r = r := Complex.conj_ofReal _
      rw [hsr]
      have hzz_eq : vecIp3 z z = ((vecIp3 z z).re : ℂ) := Complex.ext rfl (vecIp3_self_im z)
      rw [hzz_eq, ← mul_assoc]
      dsimp only [r]
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt hzz_pos.le,
        inv_mul_cancel₀ hzz_pos.ne', Complex.ofReal_one]
    have hworth : ∀ u ∈ L, vecIp3 u w = 0 := fun u hu => by
      rw [vecIp3_smul_right, horth_z u hu, mul_zero]
    have hw_not_mem : w ∉ L := fun h => by
      have h0 := hworth w h
      rw [hwnorm] at h0
      norm_num at h0
    refine ⟨List.nodup_append.mpr ⟨hnodup, List.nodup_singleton w, fun a ha b hb => by
      simp only [List.mem_singleton] at hb; subst hb; exact fun h => by rw [h] at ha; exact hw_not_mem ha⟩,
      fun u hu => ?_, fun u hu v hv huv => ?_, ?_⟩
    · simp only [List.mem_append, List.mem_singleton] at hu
      rcases hu with huL | rfl
      · exact hnorm u huL
      · exact hwnorm
    · simp only [List.mem_append, List.mem_singleton] at hu hv
      rcases hu with huL | rfl <;> rcases hv with hvL | rfl
      · exact horth u huL v hvL huv
      · exact hworth u huL
      · rw [← vecIp3_conj_symm, hworth v hvL, star_zero]
      · exact absurd rfl huv
    · have hx_eq : x = (∑ u ∈ L.toFinset, (vecIp3 u x) • u) + (r⁻¹ • w) := by
        have hzw : r⁻¹ • w = z := by
          dsimp only [w]
          rw [smul_smul, inv_mul_cancel₀, one_smul]
          exact Complex.ofReal_ne_zero.mpr (inv_ne_zero (Real.sqrt_ne_zero'.mpr hzz_pos))
        rw [hzw]
        dsimp only [z]
        abel
      rw [hx_eq]
      refine Submodule.add_mem _ (Submodule.sum_mem _ fun u hu =>
        Submodule.smul_mem _ _ (Submodule.subset_span (by simp [List.mem_toFinset.mp hu]))) ?_
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.mpr (List.mem_toFinset.mpr
        (by simp only [List.mem_append, List.mem_singleton]; exact Or.inr rfl))))

private theorem list_orthonormal_length_le_three (L : List (Fin 3 → ℂ))
    (hnodup : L.Nodup) (hnorm : ∀ u ∈ L, vecIp3 u u = 1)
    (horth : ∀ u ∈ L, ∀ v ∈ L, u ≠ v → vecIp3 u v = 0) :
    L.length ≤ 3 := by
  have hli : LinearIndependent ℂ (fun i : Fin L.length => L[i]) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hip : vecIp3 L[i] (∑ j : Fin L.length, c j • L[j]) = 0 := by rw [hc]; simp [vecIp3]
    have hsum : vecIp3 L[i] (∑ j : Fin L.length, c j • L[j]) =
        ∑ j : Fin L.length, c j * vecIp3 L[i] L[j] := by
      have : ∀ s : Finset (Fin L.length),
          vecIp3 L[i] (∑ j ∈ s, c j • L[j]) = ∑ j ∈ s, c j * vecIp3 L[i] L[j] := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp [vecIp3]
        | insert a s ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha, vecIp3_add_right, vecIp3_smul_right, ih]
      exact this Finset.univ
    rw [hsum, Finset.sum_eq_single i] at hip
    · have hi1 : vecIp3 L[i] L[i] = 1 := hnorm _ (List.getElem_mem i.isLt)
      rw [hi1, mul_one] at hip; exact hip
    · intro j _ hji
      have hne : L[i] ≠ L[j] := fun h => hji (Fin.ext (hnodup.getElem_inj_iff.mp h)).symm
      have hij0 : vecIp3 L[i] L[j] = 0 := horth _ (List.getElem_mem i.isLt) _ (List.getElem_mem j.isLt) hne
      rw [hij0, mul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hle := hli.fintype_card_le_finrank
  simpa [Module.finrank_fin_fun] using hle

private theorem unitary_matrix_real_of_real_vecIp (v : Fin 4 → (Fin 3 → ℂ))
    (hreal : ∀ i j : Fin 4, (vecIp3 (v i) (v j)).im = 0) :
    ∃ U : Matrix.unitaryGroup (Fin 3) ℂ,
      ∀ (i : Fin 4) (a : Fin 3), (∑ b : Fin 3, star (U.1 b a) * v i b).im = 0 := by
  let L0 : List (Fin 3 → ℂ) := []
  let L1 := projStep (v 0) L0
  let L2 := projStep (v 1) L1
  let L3 := projStep (v 2) L2
  let L4 := projStep (v 3) L3
  let Rsub : Submodule ℝ (Fin 3 → ℂ) := Submodule.span ℝ (Set.range v)
  have hR_ip : ∀ x ∈ Rsub, ∀ y ∈ Rsub, (vecIp3 x y).im = 0 := by
    intro x hx y hy
    refine Submodule.span_induction (p := fun a _ => (vecIp3 a y).im = 0) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨i, rfl⟩
      refine Submodule.span_induction (p := fun b _ => (vecIp3 (v i) b).im = 0) ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨j, rfl⟩; exact hreal i j
      · simp [vecIp3]
      · intro a b _ _ ha hb; rw [vecIp3_add_right, Complex.add_im, ha, hb, add_zero]
      · intro r a _ ha
        change (vecIp3 (v i) ((r : ℂ) • a)).im = 0
        rw [vecIp3_smul_right, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, ha, mul_zero, add_zero]
    · simp [vecIp3]
    · intro a b _ _ ha hb; rw [vecIp3_add_left, Complex.add_im, ha, hb, add_zero]
    · intro r a _ ha
      change (vecIp3 ((r : ℂ) • a) y).im = 0
      rw [vecIp3_smul_left, Complex.star_def, Complex.conj_ofReal, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, ha, mul_zero, add_zero]
  have hstep_R : ∀ (x : Fin 3 → ℂ) (L : List (Fin 3 → ℂ)),
      x ∈ Rsub → (∀ u ∈ L, u ∈ Rsub) → ∀ u ∈ projStep x L, u ∈ Rsub := by
    intro x L hx hL u hu
    dsimp only [projStep] at hu
    set z := x - ∑ u ∈ L.toFinset, (vecIp3 u x) • u
    by_cases hz : z = 0
    · simp only [hz, ↓reduceDIte] at hu; exact hL u hu
    · simp only [hz, ↓reduceDIte] at hu
      simp only [List.mem_append, List.mem_singleton] at hu
      rcases hu with huL | rfl
      · exact hL u huL
      · have hzR : z ∈ Rsub := by
          refine Rsub.sub_mem hx (Submodule.sum_mem _ fun w hw => ?_)
          have hwR := hL w (List.mem_toFinset.mp hw)
          have him : (vecIp3 w x).im = 0 := hR_ip w hwR x hx
          have heq : (vecIp3 w x) • w = (vecIp3 w x).re • w := by
            funext a
            rw [Pi.smul_apply, Pi.smul_apply, Complex.real_smul, smul_eq_mul,
              ← (Complex.ext rfl him : vecIp3 w x = ((vecIp3 w x).re : ℂ))]
          rw [heq]
          exact Rsub.smul_mem _ hwR
        change (((Real.sqrt (vecIp3 z z).re)⁻¹ : ℝ) : ℂ) • z ∈ Rsub
        rw [show ((((Real.sqrt (vecIp3 z z).re)⁻¹ : ℝ) : ℂ) • z) =
            (Real.sqrt (vecIp3 z z).re)⁻¹ • z from by
          funext a; rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]]
        exact Rsub.smul_mem _ hzR
  have h1 := projStep_preserves_orthonormal (v 0) L0 List.nodup_nil (by simp [L0]) (by simp [L0])
  have h2 := projStep_preserves_orthonormal (v 1) L1 h1.1 h1.2.1 h1.2.2.1
  have h3 := projStep_preserves_orthonormal (v 2) L2 h2.1 h2.2.1 h2.2.2.1
  have h4 := projStep_preserves_orthonormal (v 3) L3 h3.1 h3.2.1 h3.2.2.1
  have hL4_R : ∀ u ∈ L4, u ∈ Rsub := by
    refine hstep_R (v 3) L3 (Submodule.subset_span ⟨3, rfl⟩) ?_
    refine hstep_R (v 2) L2 (Submodule.subset_span ⟨2, rfl⟩) ?_
    refine hstep_R (v 1) L1 (Submodule.subset_span ⟨1, rfl⟩) ?_
    refine hstep_R (v 0) L0 (Submodule.subset_span ⟨0, rfl⟩) (by simp [L0])
  have hprefix_sub : ∀ (a : Fin 3 → ℂ) (L : List (Fin 3 → ℂ)) (u : Fin 3 → ℂ),
      u ∈ L → u ∈ projStep a L := by
    intro a L u hu
    dsimp only [projStep]
    split_ifs <;> simp [hu]
  have hv_span_R : ∀ i : Fin 4, v i ∈ Submodule.span ℂ (L4.toFinset : Set (Fin 3 → ℂ)) := by
    have h12 : Submodule.span ℂ (L1.toFinset : Set (Fin 3 → ℂ)) ≤
        Submodule.span ℂ (L2.toFinset : Set (Fin 3 → ℂ)) :=
      Submodule.span_mono (fun u hu => Finset.mem_coe.mpr (List.mem_toFinset.mpr (hprefix_sub (v 1) L1 u (List.mem_toFinset.mp (Finset.mem_coe.mp hu)))))
    have h23 : Submodule.span ℂ (L2.toFinset : Set (Fin 3 → ℂ)) ≤
        Submodule.span ℂ (L3.toFinset : Set (Fin 3 → ℂ)) :=
      Submodule.span_mono (fun u hu => Finset.mem_coe.mpr (List.mem_toFinset.mpr (hprefix_sub (v 2) L2 u (List.mem_toFinset.mp (Finset.mem_coe.mp hu)))))
    have h34 : Submodule.span ℂ (L3.toFinset : Set (Fin 3 → ℂ)) ≤
        Submodule.span ℂ (L4.toFinset : Set (Fin 3 → ℂ)) :=
      Submodule.span_mono (fun u hu => Finset.mem_coe.mpr (List.mem_toFinset.mpr (hprefix_sub (v 3) L3 u (List.mem_toFinset.mp (Finset.mem_coe.mp hu)))))
    intro i; fin_cases i
    · exact h34 (h23 (h12 h1.2.2.2))
    · exact h34 (h23 h2.2.2.2)
    · exact h34 h3.2.2.2
    · exact h4.2.2.2
  let e0 : Fin 3 → ℂ := Pi.single 0 1
  let e1 : Fin 3 → ℂ := Pi.single 1 1
  let e2 : Fin 3 → ℂ := Pi.single 2 1
  let L5 := projStep e0 L4
  let L6 := projStep e1 L5
  let L7 := projStep e2 L6
  have h5 := projStep_preserves_orthonormal e0 L4 h4.1 h4.2.1 h4.2.2.1
  have h6 := projStep_preserves_orthonormal e1 L5 h5.1 h5.2.1 h5.2.2.1
  have h7 := projStep_preserves_orthonormal e2 L6 h6.1 h6.2.1 h6.2.2.1
  have hL4_in_L7 : ∀ u ∈ L4, u ∈ L7 := fun u hu =>
    hprefix_sub e2 L6 u (hprefix_sub e1 L5 u (hprefix_sub e0 L4 u hu))
  have he_span : ∀ k : Fin 3, Pi.single k (1 : ℂ) ∈ Submodule.span ℂ (L7.toFinset : Set (Fin 3 → ℂ)) := by
    have h56 : Submodule.span ℂ (L5.toFinset : Set (Fin 3 → ℂ)) ≤
        Submodule.span ℂ (L6.toFinset : Set (Fin 3 → ℂ)) :=
      Submodule.span_mono (fun u hu => Finset.mem_coe.mpr (List.mem_toFinset.mpr (hprefix_sub e1 L5 u (List.mem_toFinset.mp (Finset.mem_coe.mp hu)))))
    have h67 : Submodule.span ℂ (L6.toFinset : Set (Fin 3 → ℂ)) ≤
        Submodule.span ℂ (L7.toFinset : Set (Fin 3 → ℂ)) :=
      Submodule.span_mono (fun u hu => Finset.mem_coe.mpr (List.mem_toFinset.mpr (hprefix_sub e2 L6 u (List.mem_toFinset.mp (Finset.mem_coe.mp hu)))))
    intro k; fin_cases k
    · exact h67 (h56 h5.2.2.2)
    · exact h67 h6.2.2.2
    · exact h7.2.2.2
  have hL7_span_top : Submodule.span ℂ (L7.toFinset : Set (Fin 3 → ℂ)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx_eq : x = ∑ k : Fin 3, x k • Pi.single k (1 : ℂ) := by
      funext a; simp [Finset.sum_apply, Pi.single_apply]
    rw [hx_eq]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (he_span k)
  have hL7_len_le : L7.length ≤ 3 := list_orthonormal_length_le_three L7 h7.1 h7.2.1 h7.2.2.1
  have hL7_len_ge : 3 ≤ L7.length := by
    have hfin := finrank_span_le_card (R := ℂ) (L7.toFinset : Set (Fin 3 → ℂ))
    rw [hL7_span_top, finrank_top, Module.finrank_fin_fun] at hfin
    have hfin' : 3 ≤ L7.toFinset.card := by simpa using hfin
    have hcard_le : L7.toFinset.card ≤ L7.length := List.toFinset_card_le L7
    omega
  have hL7_len : L7.length = 3 := by omega
  let U_mat : Matrix (Fin 3) (Fin 3) ℂ := fun b a => L7[a.1] b
  have hU_mem : U_mat ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    funext a b
    simp only [U_mat]
    change vecIp3 L7[a.1] L7[b.1] = (1 : Matrix (Fin 3) (Fin 3) ℂ) a b
    by_cases hab : a = b
    · subst hab; rw [h7.2.1 _ (List.getElem_mem (by omega : a.1 < L7.length)), Matrix.one_apply_eq]
    · have hne : L7[a.1] ≠ L7[b.1] := fun h => hab (Fin.ext (h7.1.getElem_inj_iff.mp h))
      rw [h7.2.2.1 _ (List.getElem_mem (by omega : a.1 < L7.length)) _
        (List.getElem_mem (by omega : b.1 < L7.length)) hne, Matrix.one_apply_ne hab]
  refine ⟨⟨U_mat, hU_mem⟩, fun i a => ?_⟩
  change (vecIp3 L7[a.1] (v i)).im = 0
  let w := L7[a.1]
  by_cases hw_L4 : w ∈ L4
  · exact hR_ip w (hL4_R w hw_L4) (v i) (Submodule.subset_span ⟨i, rfl⟩)
  · have horth_w : ∀ u ∈ L4, vecIp3 w u = 0 := fun u hu =>
      h7.2.2.1 w (List.getElem_mem (by omega : a.1 < L7.length)) u (hL4_in_L7 u hu)
        fun h => hw_L4 (h ▸ hu)
    have hvw0 : vecIp3 w (v i) = 0 := by
      refine Submodule.span_induction (p := fun y _ => vecIp3 w y = 0) ?_ ?_ ?_ ?_ (hv_span_R i)
      · intro u hu; exact horth_w u (List.mem_toFinset.mp (Finset.mem_coe.mp hu))
      · simp [vecIp3]
      · intro x y _ _ hx hy; rw [vecIp3_add_right, hx, hy, add_zero]
      · intro c x _ hx; rw [vecIp3_smul_right, hx, mul_zero]
    rw [hvw0, Complex.zero_im]

private theorem bargmann_real_gram_pull_H3R (T : Finset Albert)
    (hT_atoms : ∀ p ∈ T, IsAtom p ∧ p ∈ (H3Subalgebra .C).carrier)
    (hT_card : T.card = 4)
    (hreal : ∀ U_sub : Finset Albert, U_sub ⊆ T → U_sub.card = 3 →
      ∃ U : Matrix.unitaryGroup (Fin 3) ℂ,
        (U_sub : Set Albert) ⊆ (unitaryConjSubalgebraC U (H3Subalgebra .R)).carrier)
    (_hnonline : ¬ ∃ q : Albert, ∃ hq : IsAtom q, q ∈ (H3Subalgebra .C).carrier ∧
      (T : Set Albert) ⊆ (lineSubalgebra q hq).carrier)
    (h_no_orth : ∃ a ∈ T, ∀ b ∈ T, b ≠ a → jordanMul a b ≠ 0) :
    ∃ U : Matrix.unitaryGroup (Fin 3) ℂ,
      (T : Set Albert) ⊆ (unitaryConjSubalgebraC U (H3Subalgebra .R)).carrier := by
  let eqv := (Fintype.equivFinOfCardEq (α := ↥T) (n := 4) (by rw [Fintype.card_coe]; exact hT_card)).symm
  let p : Fin 4 → Albert := fun i => (eqv i).1
  have hp_memT : ∀ i, p i ∈ T := fun i => (eqv i).2
  have hp_atom : ∀ i, IsAtom (p i) := fun i => (hT_atoms _ (hp_memT i)).1
  have hp_C : ∀ i, p i ∈ (H3Subalgebra .C).carrier := fun i => (hT_atoms _ (hp_memT i)).2
  let M : Fin 4 → selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ) := fun i =>
    (assocHermEquiv assocCD_C).symm ⟨p i, hp_C i⟩
  have hM_eq : ∀ i, (assocHermEquiv assocCD_C (M i)).1 = p i := fun i =>
    congrArg Subtype.val ((assocHermEquiv assocCD_C).apply_symm_apply ⟨p i, hp_C i⟩)
  have hM_herm : ∀ i, (M i).1.IsHermitian := fun i => (M i).prop
  have hM_id : ∀ i, (M i).1 * (M i).1 = (M i).1 := fun i => by
    have h12 : (M i).1 * (M i).1 = (1 / 2 : ℝ) • ((M i).1 * (M i).1 + (M i).1 * (M i).1) := by module
    have hj : (assocHermEquiv assocCD_C ⟨(M i).1 * (M i).1,
        by rw [selfAdjoint.mem_iff, star_mul, (M i).prop]⟩).1 = p i := by
      change assocMatToAlbert assocCD_C ((M i).1 * (M i).1) = p i
      rw [h12, jordanMul_assocMatToAlbert assocCD_C]
      change jordanMul (assocHermEquiv assocCD_C (M i)).1 (assocHermEquiv assocCD_C (M i)).1 = p i
      rw [hM_eq i, (hp_atom i).1]
    have hsub := congrArg Subtype.val ((assocHermEquiv assocCD_C).injective (Subtype.ext (hj.trans (hM_eq i).symm)))
    exact hsub
  have hM_tr : ∀ i, Matrix.trace (M i).1 = 1 := fun i => by
    have hdiag_re : ∀ a : Fin 3, ((M i).1 a a).re = (p i).1 a ∧ ((M i).1 a a).im = 0 := fun a => by
      have hm := congrArg (fun x : Albert => x.1 a) (hM_eq i)
      change Complex.re ((M i).1 a a) = (p i).1 a at hm
      have him := congrArg Complex.im (congrFun (congrFun (hM_herm i).eq a) a)
      simp [Matrix.conjTranspose_apply] at him
      exact ⟨hm, by linarith⟩
    apply Complex.ext
    · rw [Matrix.trace, Complex.re_sum, Fin.sum_univ_three]
      simp only [Matrix.diag_apply, (hdiag_re 0).1, (hdiag_re 1).1, (hdiag_re 2).1]
      simpa [albertTrace, Fin.sum_univ_three] using (hp_atom i).2
    · rw [Matrix.trace, Complex.im_sum, Fin.sum_univ_three]
      simp only [Matrix.diag_apply, (hdiag_re 0).2, (hdiag_re 1).2, (hdiag_re 2).2, add_zero, Complex.one_im]
  have hv_raw : ∀ i : Fin 4, ∃ v : Fin 3 → ℂ,
      vecIp3 v v = 1 ∧ ∀ a b, (M i).1 a b = v a * star (v b) := fun i => by
    obtain ⟨cols, hnorm, _, hsum⟩ :=
      hermitian_idempotent_spectral_rank (k := 1) (M i).1 (hM_herm i) (hM_id i) (by simpa using hM_tr i)
    refine ⟨cols 0, hnorm 0, fun a b => ?_⟩
    rw [hsum a b, Fin.sum_univ_one]
  choose v hv_norm hv_eq using hv_raw
  have htrace_pair : ∀ i j : Fin 4,
      tracePairing (p i) (p j) = Complex.normSq (vecIp3 (v i) (v j)) := fun i j => by
    have hmul := jordanMul_assocMatToAlbert assocCD_C (M := M i) (N := M j)
    have htr : tracePairing (p i) (p j) = (Matrix.trace ((M i).1 * (M j).1)).re := by
      have hsub : tracePairing (p i) (p j) = albertTrace (jordanMul (p i) (p j)) := rfl
      rw [hsub]
      conv_lhs => rw [← hM_eq i, ← hM_eq j]
      change albertTrace (jordanMul (assocMatToAlbert assocCD_C (M i).1)
        (assocMatToAlbert assocCD_C (M j).1)) = _
      rw [← hmul]
      simp only [albertTrace, assocMatToAlbert_fst, Matrix.smul_apply, Matrix.add_apply]
      have hre : ∀ A : Matrix (Fin 3) (Fin 3) ℂ,
          (∑ a : Fin 3, assocCD_C.re (A a a)) = (Matrix.trace A).re := fun A => by
        change (∑ a : Fin 3, (A a a).re) = (∑ a : Fin 3, A a a).re
        rw [Complex.re_sum]
      simp_rw [map_smul, map_add, smul_eq_mul, mul_add]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hre, hre,
        Matrix.trace_mul_comm (M j).1 (M i).1]
      ring
    rw [htr]
    have hmat_tr : Matrix.trace ((M i).1 * (M j).1) = vecIp3 (v i) (v j) * star (vecIp3 (v i) (v j)) := by
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, hv_eq, vecIp3]
      calc
        ∑ a : Fin 3, ∑ b : Fin 3, (v i a * star (v i b)) * (v j b * star (v j a))
          = ∑ a : Fin 3, (v i a * star (v j a)) * ∑ b : Fin 3, (star (v i b) * v j b) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun b _ => by ring
        _ = (∑ b : Fin 3, star (v i b) * v j b) * ∑ a : Fin 3, (v i a * star (v j a)) := by
            rw [← Finset.sum_mul, mul_comm]
        _ = vecIp3 (v i) (v j) * star (vecIp3 (v i) (v j)) := by
            congr 1
            simp only [vecIp3, star_sum, star_mul, star_star, mul_comm]
    rw [hmat_tr, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
  have htriple_im : ∀ i j l : Fin 4,
      (vecIp3 (v i) (v j) * vecIp3 (v j) (v l) * vecIp3 (v l) (v i)).im = 0 := fun i j l => by
    let S3 : Finset Albert := {p i, p j, p l}
    have hS3_sub : S3 ⊆ T := by
      intro x hx
      simp only [S3, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> exact hp_memT _
    have hS3_le : S3.card ≤ 3 :=
      le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ (Finset.card_le_two))
    obtain ⟨U_sub, hU_sub, hU_le, hU_card⟩ : ∃ U_sub : Finset Albert,
        S3 ⊆ U_sub ∧ U_sub ⊆ T ∧ U_sub.card = 3 := by
      have hdisj : Disjoint S3 (T \ S3) := disjoint_sdiff_self_right
      have hunion : S3 ∪ (T \ S3) = T := Finset.union_sdiff_of_subset hS3_sub
      have hcs : S3.card + (T \ S3).card = T.card := by
        rw [← Finset.card_union_of_disjoint hdisj, hunion]
      obtain ⟨B0, hB0_sub, hB0_card⟩ :=
        Finset.exists_subset_card_eq (by omega : 3 - S3.card ≤ (T \ S3).card)
      refine ⟨S3 ∪ B0, Finset.subset_union_left,
        Finset.union_subset hS3_sub (hB0_sub.trans Finset.sdiff_subset), ?_⟩
      rw [Finset.card_union_of_disjoint (hdisj.mono_right hB0_sub), hB0_card]
      omega
    obtain ⟨U, hU⟩ := hreal U_sub hU_le hU_card
    have hreal_mat : ∀ m : Fin 4, p m ∈ U_sub →
        ∀ a b : Fin 3, ((star U.1 * (M m).1 * U.1) a b).im = 0 := fun m hm a b => by
      obtain ⟨hxC, hxR⟩ := hU (Finset.mem_coe.mpr hm)
      let h1 : star U.1 * U.1 = 1 := Matrix.mem_unitaryGroup_iff'.mp U.prop
      let h2 : U.1 * star U.1 = 1 := Matrix.mem_unitaryGroup_iff.mp U.prop
      let ψ := assocCD_unitaryIso assocCD_C U.1 h1 h2
      have hψeq : (ψ.toLinearEquiv ⟨p m, hxC⟩).1 = assocMatToAlbert assocCD_C (star U.1 * (M m).1 * U.1) := by
        have hX : ((assocHermEquiv assocCD_C).symm ⟨p m, hxC⟩).1 = (M m).1 :=
          congrArg (fun Z : selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ) => Z.1) (rfl : (assocHermEquiv assocCD_C).symm ⟨p m, hxC⟩ = M m)
        change assocMatToAlbert assocCD_C (star U.1 * ((assocHermEquiv assocCD_C).symm ⟨p m, hxC⟩).1 * U.1) = _
        rw [hX]
      have hmemR : assocMatToAlbert assocCD_C (star U.1 * (M m).1 * U.1) ∈ (H3Subalgebra .R).carrier := by
        rw [← hψeq]; exact hxR
      let N := star U.1 * (M m).1 * U.1
      have hNherm : N.IsHermitian := by
        dsimp only [N]
        rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, (hM_herm m).eq]
        simp only [← Matrix.star_eq_conjTranspose, star_star, mul_assoc]
      have hreal_of_memR : ∀ {z : ℂ}, complexToOctonion z ∈ (octSubalgebraOfLevel .R).carrier → z.im = 0 := by
        rintro z hz
        have h1 := hz.1
        simp [complexToOctonion] at h1
        exact h1
      have h01 := hreal_of_memR hmemR.1
      have h02 := hreal_of_memR hmemR.2.1
      have h12 := hreal_of_memR hmemR.2.2
      have hdiag : ∀ c : Fin 3, (N c c).im = 0 := fun c => by
        have hc := congrArg Complex.im (congrFun (congrFun hNherm.eq c) c)
        simp [Matrix.conjTranspose_apply] at hc; linarith
      have hconj_im : ∀ x y : Fin 3, (N x y).im = 0 → (N y x).im = 0 := fun x y hxy => by
        have hc := congrArg Complex.im (congrFun (congrFun hNherm.eq y) x)
        simp [Matrix.conjTranspose_apply] at hc; linarith
      fin_cases a <;> fin_cases b
      · exact hdiag 0
      · exact h01
      · exact h02
      · exact hconj_im 0 1 h01
      · exact hdiag 1
      · exact h12
      · exact hconj_im 0 2 h02
      · exact hconj_im 1 2 h12
      · exact hdiag 2
    have hm1 := hreal_mat i (hU_sub (by simp [S3]))
    have hm2 := hreal_mat j (hU_sub (by simp [S3]))
    have hm3 := hreal_mat l (hU_sub (by simp [S3]))
    have htr_eq : Matrix.trace ((M i).1 * (M j).1 * (M l).1) =
        Matrix.trace ((star U.1 * (M i).1 * U.1) * (star U.1 * (M j).1 * U.1) * (star U.1 * (M l).1 * U.1)) := by
      have h1 : star U.1 * U.1 = 1 := Matrix.mem_unitaryGroup_iff'.mp U.prop
      have h2 : U.1 * star U.1 = 1 := Matrix.mem_unitaryGroup_iff.mp U.prop
      calc
        Matrix.trace ((M i).1 * (M j).1 * (M l).1)
          = Matrix.trace ((U.1 * star U.1) * (M i).1 * (U.1 * star U.1) * (M j).1 *
              (U.1 * star U.1) * (M l).1) := by
            simp only [h2, one_mul, mul_one]
        _ = Matrix.trace (U.1 * ((star U.1 * (M i).1 * U.1) * (star U.1 * (M j).1 * U.1) *
              (star U.1 * (M l).1))) := by
            simp only [mul_assoc]
        _ = Matrix.trace (((star U.1 * (M i).1 * U.1) * (star U.1 * (M j).1 * U.1) *
              (star U.1 * (M l).1)) * U.1) := by
            rw [Matrix.trace_mul_comm]
        _ = _ := by simp only [mul_assoc]
    have hreal_prod : ∀ A B : Matrix (Fin 3) (Fin 3) ℂ,
        (∀ a b, (A a b).im = 0) → (∀ a b, (B a b).im = 0) → ∀ a b, ((A * B) a b).im = 0 :=
      fun A B hA hB a b => by
        simp [Matrix.mul_apply, Complex.im_sum, Complex.mul_im, hA, hB]
    have htr_im0 : (Matrix.trace ((star U.1 * (M i).1 * U.1) * (star U.1 * (M j).1 * U.1) *
        (star U.1 * (M l).1 * U.1))).im = 0 := by
      rw [Matrix.trace, Complex.im_sum]
      exact Finset.sum_eq_zero fun a _ => hreal_prod _ _ (hreal_prod _ _ hm1 hm2) hm3 a a
    have htr_barg : Matrix.trace ((M i).1 * (M j).1 * (M l).1) =
        vecIp3 (v i) (v j) * vecIp3 (v j) (v l) * vecIp3 (v l) (v i) := by
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, hv_eq, vecIp3,
        Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
        Finset.sum_congr rfl fun c _ => by ring
    rw [← htr_barg, htr_eq, htr_im0]
  obtain ⟨a0, ha0T, ha0_no⟩ := h_no_orth
  let i0 := eqv.symm ⟨a0, ha0T⟩
  have hi0_eq : p i0 = a0 := congrArg Subtype.val (eqv.apply_symm_apply ⟨a0, ha0T⟩)
  have hne0 : ∀ j : Fin 4, vecIp3 (v i0) (v j) ≠ 0 := fun j h0 => by
    by_cases hji : j = i0
    · subst hji; rw [hv_norm] at h0; norm_num at h0
    · have htp0 : tracePairing (p i0) (p j) = 0 := by rw [htrace_pair, h0, Complex.normSq_zero]
      have hjmul0 : jordanMul (p i0) (p j) = 0 :=
        (tracePairing_eq_zero_iff_jordanMul_eq_zero_of_isPositive (p i0) (p j) (hp_atom i0)
          ⟨p j, (hp_atom j).1.symm⟩).mp htp0
      rw [hi0_eq] at hjmul0
      exact ha0_no (p j) (hp_memT j) (fun h => hji (eqv.injective (Subtype.ext (h.trans hi0_eq.symm)))) hjmul0
  let ph : Fin 4 → ℂ := fun j => star (vecIp3 (v i0) (v j)) / ((Real.sqrt (Complex.normSq (vecIp3 (v i0) (v j)))) : ℂ)
  have hph_norm : ∀ j : Fin 4, star (ph j) * ph j = 1 := fun j => by
    have hn_pos : 0 < Complex.normSq (vecIp3 (v i0) (v j)) := Complex.normSq_pos.mpr (hne0 j)
    dsimp only [ph]
    rw [star_div₀, star_star, Complex.star_def, Complex.conj_ofReal, div_mul_div_comm,
      Complex.mul_conj, ← Complex.ofReal_mul, Real.mul_self_sqrt hn_pos.le,
      div_self (Complex.ofReal_ne_zero.mpr hn_pos.ne')]
  let w : Fin 4 → (Fin 3 → ℂ) := fun j => ph j • v j
  have hw_i0_pos : ∀ j : Fin 4, (vecIp3 (w i0) (w j)).im = 0 ∧ 0 < (vecIp3 (w i0) (w j)).re := fun j => by
    have hn_i0 : vecIp3 (v i0) (v i0) = 1 := hv_norm i0
    have hph_i0 : ph i0 = 1 := by
      dsimp only [ph]; rw [hn_i0, Complex.normSq_one, Real.sqrt_one, Complex.ofReal_one, div_one, star_one]
    have hval : vecIp3 (w i0) (w j) = ((Real.sqrt (Complex.normSq (vecIp3 (v i0) (v j)))) : ℂ) := by
      dsimp only [w]
      rw [hph_i0, one_smul, vecIp3_smul_right]
      dsimp only [ph]
      have hn_pos : 0 < Complex.normSq (vecIp3 (v i0) (v j)) := Complex.normSq_pos.mpr (hne0 j)
      have hs_ne : ((Real.sqrt (Complex.normSq (vecIp3 (v i0) (v j)))) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hn_pos)
      rw [div_mul_eq_mul_div, mul_comm (star (vecIp3 (v i0) (v j))) (vecIp3 (v i0) (v j)),
        Complex.star_def, Complex.mul_conj, div_eq_iff hs_ne, ← Complex.ofReal_mul,
        Real.mul_self_sqrt hn_pos.le]
    rw [hval]
    exact ⟨Complex.ofReal_im _, by rw [Complex.ofReal_re]; exact Real.sqrt_pos.mpr (Complex.normSq_pos.mpr (hne0 j))⟩
  have hw_real : ∀ j l : Fin 4, (vecIp3 (w j) (w l)).im = 0 := fun j l => by
    have hb : (vecIp3 (w i0) (w j) * vecIp3 (w j) (w l) * vecIp3 (w l) (w i0)).im = 0 := by
      have hfactor : vecIp3 (w i0) (w j) * vecIp3 (w j) (w l) * vecIp3 (w l) (w i0) =
          (star (ph i0) * ph i0) * (star (ph j) * ph j) * (star (ph l) * ph l) *
          (vecIp3 (v i0) (v j) * vecIp3 (v j) (v l) * vecIp3 (v l) (v i0)) := by
        dsimp only [w]
        simp only [vecIp3_smul_left, vecIp3_smul_right]
        ring
      rw [hfactor, hph_norm i0, hph_norm j, hph_norm l, one_mul, one_mul, one_mul]
      exact htriple_im i0 j l
    have h1 := hw_i0_pos j
    have h2 : (vecIp3 (w l) (w i0)).im = 0 ∧ 0 < (vecIp3 (w l) (w i0)).re := by
      rw [← vecIp3_conj_symm]
      exact ⟨by simp [(hw_i0_pos l).1], by simp [(hw_i0_pos l).2]⟩
    have hre1 : vecIp3 (w i0) (w j) = ((vecIp3 (w i0) (w j)).re : ℂ) := Complex.ext rfl h1.1
    have hre2 : vecIp3 (w l) (w i0) = ((vecIp3 (w l) (w i0)).re : ℂ) := Complex.ext rfl h2.1
    rw [hre1, hre2] at hb
    have hmul_eq : ((vecIp3 (w i0) (w j)).re : ℂ) * vecIp3 (w j) (w l) *
        ((vecIp3 (w l) (w i0)).re : ℂ) =
        (((vecIp3 (w i0) (w j)).re * (vecIp3 (w l) (w i0)).re : ℝ) : ℂ) *
          vecIp3 (w j) (w l) := by push_cast; ring
    rw [hmul_eq] at hb
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at hb
    have hpos_prod : (vecIp3 (w i0) (w j)).re * (vecIp3 (w l) (w i0)).re ≠ 0 :=
      (mul_pos h1.2 h2.2).ne'
    exact (mul_eq_zero.mp hb).resolve_left hpos_prod
  obtain ⟨U, hU⟩ := unitary_matrix_real_of_real_vecIp w hw_real
  refine ⟨U, fun x hxT => ?_⟩
  let m := eqv.symm ⟨x, hxT⟩
  have hpm : p m = x := congrArg Subtype.val (eqv.apply_symm_apply ⟨x, hxT⟩)
  rw [← hpm, ← hM_eq m]
  refine mem_unitaryConjSubalgebraC_H3R_of_matrix U (M m) fun a b => ?_
  have hmat : (star U.1 * (M m).1 * U.1) a b =
      (∑ c : Fin 3, star (U.1 c a) * w m c) * star (∑ d : Fin 3, star (U.1 d b) * w m d) := by
    simp only [Matrix.mul_apply, Matrix.star_apply, hv_eq m]
    calc
      ∑ d : Fin 3, (∑ c : Fin 3, star (U.1 c a) * (v m c * star (v m d))) * U.1 d b
        = ∑ c : Fin 3, ∑ d : Fin 3,
            (star (U.1 c a) * v m c) * (star (v m d) * U.1 d b) := by
          trans ∑ d : Fin 3, ∑ c : Fin 3,
              (star (U.1 c a) * v m c) * (star (v m d) * U.1 d b)
          · refine Finset.sum_congr rfl fun d _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun c _ => by ring
          · exact Finset.sum_comm
      _ = ∑ c : Fin 3, ∑ d : Fin 3,
            (star (U.1 c a) * (ph m * v m c)) * (star (ph m * v m d) * U.1 d b) := by
          refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
          have hnorm := hph_norm m
          calc
            (star (U.1 c a) * v m c) * (star (v m d) * U.1 d b)
              = (star (ph m) * ph m) * ((star (U.1 c a) * v m c) * (star (v m d) * U.1 d b)) := by
                rw [hnorm, one_mul]
            _ = (star (U.1 c a) * (ph m * v m c)) * (star (ph m * v m d) * U.1 d b) := by
                rw [star_mul']; ring
      _ = (∑ c : Fin 3, star (U.1 c a) * w m c) *
            star (∑ d : Fin 3, star (U.1 d b) * w m d) := by
          rw [star_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun d _ => ?_
          simp only [w, Pi.smul_apply, smul_eq_mul, star_mul', star_star]
          ring
  rw [hmat]
  have ha := hU m a
  have hb := hU m b
  simp only [Complex.star_def] at ha hb
  simp only [Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im, ha, hb]
  ring

private theorem prop_arity_upper_R (T : Finset Albert)
    (hT_atoms : ∀ p ∈ T, IsAtom p ∧ p ∈ (H3Subalgebra .R).carrier)
    (hT_irr : IsIrredundant T)
    (hT_nonline : ¬ ∃ q : Albert, ∃ hq : IsAtom q, q ∈ (H3Subalgebra .R).carrier ∧
      (T : Set Albert) ⊆ (lineSubalgebra q hq).carrier) :
    T.card ≤ 3 := by
  by_contra hlt
  have h4 : 4 ≤ T.card := by omega
  obtain ⟨p, hpT⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
  let B := generatedSubalgebra (T.erase p : Set Albert)
  have hBk : B.carrier < (H3Subalgebra .R).carrier := by
    refine lt_of_le_of_ne (generatedSubalgebra_le (B := H3Subalgebra .R) fun z hz =>
        (hT_atoms z (Finset.mem_of_mem_erase hz)).2) fun heq => ?_
    apply hT_irr.2 p hpT
    change p ∈ B.carrier
    rw [heq]
    exact (hT_atoms p hpT).2
  rcases lem_five_sub .R B hBk with ⟨q, hq, hqK, hline⟩ | hfalse
  · have hle := line_erase_upper_bound T hT_atoms hT_irr hT_nonline h4 p hpT q hq hqK
      (subset_generatedSubalgebra _ |>.trans hline)
    dsimp only at hle
    omega
  · exact hfalse

private theorem prop_arity_upper_C (T : Finset Albert)
    (hT_atoms : ∀ p ∈ T, IsAtom p ∧ p ∈ (H3Subalgebra .C).carrier)
    (hT_irr : IsIrredundant T)
    (hT_nonline : ¬ ∃ q : Albert, ∃ hq : IsAtom q, q ∈ (H3Subalgebra .C).carrier ∧
      (T : Set Albert) ⊆ (lineSubalgebra q hq).carrier) :
    T.card ≤ 4 ∧
      (T.card = 4 → ∀ a ∈ T, ∃! b ∈ T, b ≠ a ∧ jordanMul a b = 0) := by
  have h_erase_U : 4 ≤ T.card → ∀ p ∈ T,
      ∃ U : Matrix.unitaryGroup (Fin 3) ℂ,
        (T.erase p : Set Albert) ⊆ (unitaryConjSubalgebraC U (H3Subalgebra .R)).carrier := by
    intro h4 p hpT
    let B := generatedSubalgebra (T.erase p : Set Albert)
    have hBk : B.carrier < (H3Subalgebra .C).carrier := by
      refine lt_of_le_of_ne (generatedSubalgebra_le (B := H3Subalgebra .C) fun z hz =>
          (hT_atoms z (Finset.mem_of_mem_erase hz)).2) fun heq => ?_
      apply hT_irr.2 p hpT
      change p ∈ B.carrier
      rw [heq]
      exact (hT_atoms p hpT).2
    rcases lem_five_sub .C B hBk with ⟨q, hq, hqK, hline⟩ | ⟨U, hU⟩
    · exfalso
      have hle := line_erase_upper_bound T hT_atoms hT_irr hT_nonline h4 p hpT q hq hqK
        (subset_generatedSubalgebra _ |>.trans hline)
      dsimp only at hle
      omega
    · exact ⟨U, (subset_generatedSubalgebra _).trans hU⟩
  have hle4 : T.card ≤ 4 := by
    by_contra hgt
    have h5 : 5 ≤ T.card := by omega
    obtain ⟨p, hpT⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
    obtain ⟨U, hU⟩ := h_erase_U (by omega) p hpT
    let h1 : star U.1 * U.1 = 1 := Matrix.mem_unitaryGroup_iff'.mp U.prop
    let h2 : U.1 * star U.1 = 1 := Matrix.mem_unitaryGroup_iff.mp U.prop
    let ψ : JordanSubalgebraIso (H3Subalgebra .C) (H3Subalgebra .C) :=
      assocCD_unitaryIso assocCD_C U.1 h1 h2
    let S := T.erase p
    have hS_subC : (S : Set Albert) ⊆ (H3Subalgebra .C).carrier := fun z hz =>
      (hT_atoms z (Finset.mem_of_mem_erase hz)).2
    let S' := pullFinset ψ.symm S hS_subC
    have hS'_R : (S' : Set Albert) ⊆ (H3Subalgebra .R).carrier := by
      intro x hx
      dsimp only [S'] at hx
      rw [Finset.mem_coe, mem_pullFinset_iff] at hx
      rcases hx with ⟨y, hyS, hyC, rfl⟩
      exact (hU hyS).2
    have hS_irr : IsIrredundant S := by
      refine ⟨fun a ha => hT_irr.1 a (Finset.mem_of_mem_erase ha), fun a ha ha_in => ?_⟩
      apply hT_irr.2 a (Finset.mem_of_mem_erase ha)
      exact generatedSubalgebra_mono (fun z hz => by
        simp only [Finset.mem_coe, Finset.mem_erase] at hz ⊢
        exact ⟨hz.1, Finset.mem_of_mem_erase hz.2⟩) ha_in
    have hS'_irr : IsIrredundant S' := pullFinset_isIrredundant ψ.symm S hS_subC hS_irr
    have hS'_atoms : ∀ a ∈ S', IsAtom a ∧ a ∈ (H3Subalgebra .R).carrier := fun a ha =>
      ⟨hS'_irr.1 a ha, hS'_R ha⟩
    have hS'_nonline : ¬ ∃ q' : Albert, ∃ hq' : IsAtom q', q' ∈ (H3Subalgebra .R).carrier ∧
        (S' : Set Albert) ⊆ (lineSubalgebra q' hq').carrier := by
      rintro ⟨q', hq', hq'R, hline'⟩
      have hq'C := H3Subalgebra_mono (k₁ := .R) (k₂ := .C) (by decide) hq'R
      refine pullFinset_nonline le_rfl ψ.symm S hS_subC ?_ ⟨q', hq', hq'C, hline'⟩
      rintro ⟨q, hq, hqC, hlineS⟩
      have hle := line_erase_upper_bound T hT_atoms hT_irr hT_nonline (by omega) p hpT q hq hqC hlineS
      dsimp only at hle
      omega
    have hS'_card : S'.card = S.card := pullFinset_card ψ.symm S hS_subC
    have hR := prop_arity_upper_R S' hS'_atoms hS'_irr hS'_nonline
    have hS_add : S.card + 1 = T.card := Finset.card_erase_add_one hpT
    omega
  refine ⟨hle4, fun h4 => ?_⟩
  have h_all_orth : ∀ a ∈ T, ∃ b ∈ T, b ≠ a ∧ jordanMul a b = 0 := by
    by_contra h_not
    push Not at h_not
    obtain ⟨U, hU⟩ := bargmann_real_gram_pull_H3R T hT_atoms h4
      (fun U_sub hU_sub hU_card => by
        obtain ⟨p, hpT, hpU⟩ : ∃ p ∈ T, p ∉ U_sub := by
          by_contra hall
          push Not at hall
          have : T ⊆ U_sub := fun x hx => hall x hx
          have := Finset.card_le_card this
          omega
        obtain ⟨U, hU⟩ := h_erase_U (by omega) p hpT
        refine ⟨U, fun x hx => hU (Finset.mem_erase.mpr ⟨fun hxp => hpU (hxp ▸ hx), hU_sub hx⟩)⟩)
      hT_nonline h_not
    let h1 : star U.1 * U.1 = 1 := Matrix.mem_unitaryGroup_iff'.mp U.prop
    let h2 : U.1 * star U.1 = 1 := Matrix.mem_unitaryGroup_iff.mp U.prop
    let ψ : JordanSubalgebraIso (H3Subalgebra .C) (H3Subalgebra .C) :=
      assocCD_unitaryIso assocCD_C U.1 h1 h2
    have hT_subC : (T : Set Albert) ⊆ (H3Subalgebra .C).carrier :=
      fun x hx => (hT_atoms x (Finset.mem_coe.mp hx)).2
    let T' := pullFinset ψ.symm T hT_subC
    have hT'_R : (T' : Set Albert) ⊆ (H3Subalgebra .R).carrier := by
      intro x hx
      dsimp only [T'] at hx
      rw [Finset.mem_coe, mem_pullFinset_iff] at hx
      rcases hx with ⟨y, hyT, hyC, rfl⟩
      exact (hU hyT).2
    have hT'_irr : IsIrredundant T' := pullFinset_isIrredundant ψ.symm T hT_subC hT_irr
    have hT'_atoms : ∀ a ∈ T', IsAtom a ∧ a ∈ (H3Subalgebra .R).carrier := fun a ha =>
      ⟨hT'_irr.1 a ha, hT'_R ha⟩
    have hT'_nonline : ¬ ∃ q' : Albert, ∃ hq' : IsAtom q', q' ∈ (H3Subalgebra .R).carrier ∧
        (T' : Set Albert) ⊆ (lineSubalgebra q' hq').carrier := by
      rintro ⟨q', hq', hq'R, hline'⟩
      let hq'C := H3Subalgebra_mono (k₁ := .R) (k₂ := .C) (by decide) hq'R
      let q := (ψ.toLinearEquiv.symm ⟨q', hq'C⟩).1
      have hq : IsAtom q := jordanSubalgebraIso_symm_maps_atom ψ ⟨q', hq'C⟩ hq'
      have hqC : q ∈ (H3Subalgebra .C).carrier := (ψ.toLinearEquiv.symm ⟨q', hq'C⟩).2
      apply hT_nonline
      refine ⟨q, hq, hqC, fun y hyT => ?_⟩
      change y ∈ (lineSubalgebra q hq).carrier
      rw [mem_lineSubalgebra_iff_idem]
      let x' := (ψ.toLinearEquiv ⟨y, (hT_atoms y hyT).2⟩).1
      have hx'_mem : x' ∈ (T' : Set Albert) := by
        rw [Finset.mem_coe, mem_pullFinset_iff]
        exact ⟨y, hyT, (hT_atoms y hyT).2, rfl⟩
      have hline_x' := (mem_lineSubalgebra_iff_idem q' hq' x').mp (hline' hx'_mem)
      have h1m : jordanMul q' x' ∈ (H3Subalgebra .C).carrier :=
        (H3Subalgebra .C).product_mem _ hq'C _ (ψ.toLinearEquiv ⟨y, (hT_atoms y hyT).2⟩).2
      have h2m : jordanMul q' (jordanMul q' x') ∈ (H3Subalgebra .C).carrier :=
        (H3Subalgebra .C).product_mem _ hq'C _ h1m
      have heq := congrArg (fun z => (ψ.symm.toLinearEquiv z).1)
        (Subtype.ext hline_x' : (⟨jordanMul q' (jordanMul q' x'), h2m⟩ : (H3Subalgebra .C).carrier) =
          ⟨jordanMul q' x', h1m⟩)
      rw [ψ.symm.map_jordan ⟨q', hq'C⟩ ⟨jordanMul q' x', h1m⟩,
        ψ.symm.map_jordan ⟨q', hq'C⟩ ⟨x', (ψ.toLinearEquiv ⟨y, (hT_atoms y hyT).2⟩).2⟩] at heq
      have hxy : (ψ.symm.toLinearEquiv ⟨x', (ψ.toLinearEquiv ⟨y, (hT_atoms y hyT).2⟩).2⟩).1 = y := by
        have hsub : (⟨x', (ψ.toLinearEquiv ⟨y, (hT_atoms y hyT).2⟩).2⟩ : (H3Subalgebra .C).carrier) =
            ψ.toLinearEquiv ⟨y, (hT_atoms y hyT).2⟩ := rfl
        change (ψ.toLinearEquiv.symm ⟨x', _⟩).1 = y
        rw [hsub, ψ.toLinearEquiv.symm_apply_apply]
      dsimp only at heq
      rw [hxy] at heq
      exact heq
    have hT'_card : T'.card = 4 := by rw [pullFinset_card, h4]
    have hR := prop_arity_upper_R T' hT'_atoms hT'_irr hT'_nonline
    omega
  intro a ha
  obtain ⟨b, hbT, hba, hab0⟩ := h_all_orth a ha
  refine ⟨b, ⟨hbT, hba, hab0⟩, ?_⟩
  rintro b' ⟨hb'T, hb'a, hab'0⟩
  by_contra hbb'
  exact lem_fiv_facts_a T hT_irr a b b' ha hbT hb'T (Ne.symm hbb') hab0 hab'0

private theorem prop_arity_upper_H (T : Finset Albert)
    (hT_atoms : ∀ p ∈ T, IsAtom p ∧ p ∈ (H3Subalgebra .H).carrier)
    (hT_irr : IsIrredundant T)
    (hT_nonline : ¬ ∃ q : Albert, ∃ hq : IsAtom q, q ∈ (H3Subalgebra .H).carrier ∧
      (T : Set Albert) ⊆ (lineSubalgebra q hq).carrier) :
    T.card ≤ 4 := by
  by_contra hgt
  have h5 : 5 ≤ T.card := by omega
  have h_erase_Q : ∀ p ∈ T, ∃ Q : NativeJordanSubalgebra,
      Q.carrier ≤ (H3Subalgebra .H).carrier ∧
      Nonempty (JordanSubalgebraIso (H3Subalgebra .C) Q) ∧
      (T.erase p : Set Albert) ⊆ Q.carrier := by
    intro p hpT
    let B := generatedSubalgebra (T.erase p : Set Albert)
    have hBk : B.carrier < (H3Subalgebra .H).carrier := by
      refine lt_of_le_of_ne (generatedSubalgebra_le (B := H3Subalgebra .H) fun z hz =>
          (hT_atoms z (Finset.mem_of_mem_erase hz)).2) fun heq => ?_
      apply hT_irr.2 p hpT
      change p ∈ B.carrier
      rw [heq]
      exact (hT_atoms p hpT).2
    rcases lem_five_sub .H B hBk with ⟨q, hq, hqK, hline⟩ | ⟨Q, hQH, hiso, hBQ⟩
    · exfalso
      have hle := line_erase_upper_bound T hT_atoms hT_irr hT_nonline (by omega) p hpT q hq hqK
        (subset_generatedSubalgebra _ |>.trans hline)
      dsimp only at hle
      omega
    · exact ⟨Q, hQH, hiso, (subset_generatedSubalgebra _).trans hBQ⟩
  by_cases h5eq : T.card = 5
  · -- Parity: in any 5-vertex graph with max degree ≤ 1, some vertex v₀ has degree 0.
    have h_v0 : ∃ v₀ ∈ T, ∀ b ∈ T, b ≠ v₀ → jordanMul v₀ b ≠ 0 := by
      by_contra hno
      push Not at hno
      have hall : ∀ a ∈ T, ∃! b ∈ T, b ≠ a ∧ jordanMul a b = 0 := fun a ha => by
        obtain ⟨b, hb, hba, hab⟩ := hno a ha
        refine ⟨b, ⟨hb, hba, hab⟩, fun b' ⟨hb', hb'a, hab'⟩ => ?_⟩
        by_contra hne
        exact lem_fiv_facts_a T hT_irr a b b' ha hb hb' (Ne.symm hne) hab hab'
      -- A fixed-point-free involution on a 5-element set is impossible!
      let f : T → T := fun a =>
        let b := Classical.choose (hall a.1 a.2)
        ⟨b, (Classical.choose_spec (hall a.1 a.2)).1.1⟩
      have hf_ne : ∀ a : T, f a ≠ a := fun a ha =>
        (Classical.choose_spec (hall a.1 a.2)).1.2.1 (congrArg Subtype.val ha)
      have hf_inv : Function.Involutive f := fun a => by
        apply Subtype.ext
        let b := f a
        have hb_spec := (Classical.choose_spec (hall a.1 a.2)).1
        have hba : a.1 ∈ T ∧ a.1 ≠ b.1 ∧ jordanMul b.1 a.1 = 0 :=
          ⟨a.2, hb_spec.2.1.symm, jordanMul_comm b.1 a.1 ▸ hb_spec.2.2⟩
        exact ((Classical.choose_spec (hall b.1 b.2)).2 a.1 hba).symm
      let eqv5 : T ≃ Fin 5 := Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact h5eq)
      let g : Fin 5 → Fin 5 := fun i => eqv5 (f (eqv5.symm i))
      have hg_ne : ∀ i : Fin 5, g i ≠ i := fun i hi =>
        hf_ne (eqv5.symm i) (by have h := congrArg eqv5.symm hi; simpa [g] using h)
      have hg_inv : Function.Involutive g := fun i => by
        dsimp only [g]
        rw [Equiv.symm_apply_apply, hf_inv, Equiv.apply_symm_apply]
      let i0 : Fin 5 := g 0
      have hi0 : i0 ≠ 0 := hg_ne 0
      let R2 : Finset (Fin 5) := (Finset.univ.erase 0).erase i0
      have hR2_card : R2.card = 3 := by
        have h0u : (0 : Fin 5) ∈ (Finset.univ : Finset (Fin 5)) := Finset.mem_univ 0
        have hiR : i0 ∈ (Finset.univ : Finset (Fin 5)).erase 0 := Finset.mem_erase.mpr ⟨hi0, Finset.mem_univ _⟩
        rw [Finset.card_erase_of_mem hiR, Finset.card_erase_of_mem h0u, Finset.card_fin]
      obtain ⟨j0, hj0⟩ := Finset.card_pos.mp (by omega : 0 < R2.card)
      have hj0_0 : j0 ≠ 0 := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hj0)).1
      have hj0_i0 : j0 ≠ i0 := (Finset.mem_erase.mp hj0).1
      let j1 : Fin 5 := g j0
      have hj1_ne : j1 ≠ j0 := hg_ne j0
      have hj1_0 : j1 ≠ 0 := fun h => hj0_i0 (by rw [← hg_inv j0]; change g j1 = i0; rw [h])
      have hj1_i0 : j1 ≠ i0 := fun h => hj0_0 (by rw [← hg_inv j0]; change g j1 = 0; rw [h, hg_inv 0])
      have hj1_R2 : j1 ∈ R2.erase j0 :=
        Finset.mem_erase.mpr ⟨hj1_ne, Finset.mem_erase.mpr ⟨hj1_i0, Finset.mem_erase.mpr ⟨hj1_0, Finset.mem_univ _⟩⟩⟩
      let R4 := (R2.erase j0).erase j1
      have hR4_card : R4.card = 1 := by
        rw [Finset.card_erase_of_mem hj1_R2, Finset.card_erase_of_mem hj0, hR2_card]
      obtain ⟨k0, hk0⟩ := Finset.card_pos.mp (by omega : 0 < R4.card)
      have hk0_j1 : k0 ≠ j1 := (Finset.mem_erase.mp hk0).1
      have hk0_j0 : k0 ≠ j0 := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hk0)).1
      have hk0_i0 : k0 ≠ i0 := (Finset.mem_erase.mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hk0))).1
      have hk0_0 : k0 ≠ 0 := (Finset.mem_erase.mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase
        (Finset.mem_of_mem_erase hk0)))).1
      have hS5 : ({0, i0, j0, j1, k0} : Finset (Fin 5)) = Finset.univ := by
        apply Finset.eq_univ_of_card
        rw [Finset.card_insert_of_notMem (by
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨hi0.symm, hj0_0.symm, hj1_0.symm, hk0_0.symm⟩),
          Finset.card_insert_of_notMem (by
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨hj0_i0.symm, hj1_i0.symm, hk0_i0.symm⟩),
          Finset.card_insert_of_notMem (by
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨hj1_ne.symm, hk0_j0.symm⟩),
          Finset.card_pair hk0_j1.symm]
        rfl
      have hgk := Finset.mem_univ (g k0)
      rw [← hS5] at hgk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hgk
      rcases hgk with h0 | h1 | h2 | h3 | h4
      · exact hk0_i0 (by rw [← hg_inv k0, h0])
      · exact hk0_0 (by rw [← hg_inv k0, h1, hg_inv 0])
      · exact hk0_j1 (by rw [← hg_inv k0, h2])
      · exact hk0_j0 (by rw [← hg_inv k0, h3, hg_inv j0])
      · exact hg_ne k0 h4
    obtain ⟨v₀, hv₀T, hv₀_no⟩ := h_v0
    obtain ⟨p, hpT, hpv₀⟩ : ∃ p ∈ T, p ≠ v₀ := by
      have := Finset.one_lt_card.mp (by omega : 1 < T.card)
      rcases this with ⟨a, ha, b, hb, hab⟩
      by_cases hav : a = v₀
      · exact ⟨b, hb, fun h => hab (hav.trans h.symm)⟩
      · exact ⟨a, ha, hav⟩
    obtain ⟨Q, hQH, ⟨ψ⟩, hQ⟩ := h_erase_Q p hpT
    let S := T.erase p
    have hS_sub : (S : Set Albert) ⊆ Q.carrier := hQ
    let S' := pullFinset ψ S hS_sub
    have hS_irr : IsIrredundant S := by
      refine ⟨fun a ha => hT_irr.1 a (Finset.mem_of_mem_erase ha), fun a ha ha_in => ?_⟩
      apply hT_irr.2 a (Finset.mem_of_mem_erase ha)
      exact generatedSubalgebra_mono (fun z hz => by
        simp only [Finset.mem_coe, Finset.mem_erase] at hz ⊢
        exact ⟨hz.1, Finset.mem_of_mem_erase hz.2⟩) ha_in
    have hS'_irr : IsIrredundant S' := pullFinset_isIrredundant ψ S hS_sub hS_irr
    have hS'_atoms : ∀ a ∈ S', IsAtom a ∧ a ∈ (H3Subalgebra .C).carrier := fun a ha =>
      ⟨hS'_irr.1 a ha, pullFinset_mem_subalgebra ψ S hS_sub ha⟩
    have hS'_nonline : ¬ ∃ q' : Albert, ∃ hq' : IsAtom q', q' ∈ (H3Subalgebra .C).carrier ∧
        (S' : Set Albert) ⊆ (lineSubalgebra q' hq').carrier :=
      pullFinset_nonline hQH ψ S hS_sub fun ⟨q, hq, hqH, hlineS⟩ => by
        have hle := line_erase_upper_bound T hT_atoms hT_irr hT_nonline (by omega) p hpT q hq hqH hlineS
        dsimp only at hle
        omega
    have hS_card : S.card = 4 := by
      have hS_add : S.card + 1 = T.card := Finset.card_erase_add_one hpT
      omega
    have hS'_card : S'.card = 4 := by rw [pullFinset_card, hS_card]
    have hmatch := (prop_arity_upper_C S' hS'_atoms hS'_irr hS'_nonline).2 hS'_card
    have hv₀S : v₀ ∈ S := Finset.mem_erase.mpr ⟨hpv₀.symm, hv₀T⟩
    let v₀' := (ψ.toLinearEquiv.symm ⟨v₀, hS_sub hv₀S⟩).1
    have hv₀'_mem : v₀' ∈ S' := by
      rw [mem_pullFinset_iff]; exact ⟨v₀, hv₀S, hS_sub hv₀S, rfl⟩
    obtain ⟨b', ⟨hb'S', hb'v₀', hv₀'b'⟩, _⟩ := hmatch v₀' hv₀'_mem
    rw [mem_pullFinset_iff] at hb'S'
    rcases hb'S' with ⟨b, hbS, hbQ, rfl⟩
    have hbv₀ : b ≠ v₀ := fun h => hb'v₀' (by simp [v₀', h])
    have hj0 : jordanMul v₀ b = 0 := by
      have hj0_mem : jordanMul v₀' (ψ.toLinearEquiv.symm ⟨b, hbQ⟩).1 ∈ (H3Subalgebra .C).carrier :=
        (H3Subalgebra .C).product_mem _ (pullFinset_mem_subalgebra ψ S hS_sub hv₀'_mem) _
          (ψ.toLinearEquiv.symm ⟨b, hbQ⟩).2
      have h1 := congrArg (fun z => (ψ.toLinearEquiv z).1)
        (Subtype.ext hv₀'b' : (⟨jordanMul v₀' (ψ.toLinearEquiv.symm ⟨b, hbQ⟩).1, hj0_mem⟩ :
          (H3Subalgebra .C).carrier) = 0)
      rw [ψ.map_jordan _ _, map_zero, Submodule.coe_zero] at h1
      rw [ψ.toLinearEquiv.apply_symm_apply, ψ.toLinearEquiv.apply_symm_apply] at h1
      exact h1
    exact hv₀_no b (Finset.mem_of_mem_erase hbS) hbv₀ hj0
  · have h6 : 6 ≤ T.card := by omega
    obtain ⟨p, hpT⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
    obtain ⟨Q, hQH, ⟨ψ⟩, hQ⟩ := h_erase_Q p hpT
    let S := T.erase p
    have hS_sub : (S : Set Albert) ⊆ Q.carrier := hQ
    let S' := pullFinset ψ S hS_sub
    have hS_irr : IsIrredundant S := by
      refine ⟨fun a ha => hT_irr.1 a (Finset.mem_of_mem_erase ha), fun a ha ha_in => ?_⟩
      apply hT_irr.2 a (Finset.mem_of_mem_erase ha)
      exact generatedSubalgebra_mono (fun z hz => by
        simp only [Finset.mem_coe, Finset.mem_erase] at hz ⊢
        exact ⟨hz.1, Finset.mem_of_mem_erase hz.2⟩) ha_in
    have hS'_irr : IsIrredundant S' := pullFinset_isIrredundant ψ S hS_sub hS_irr
    have hS'_atoms : ∀ a ∈ S', IsAtom a ∧ a ∈ (H3Subalgebra .C).carrier := fun a ha =>
      ⟨hS'_irr.1 a ha, pullFinset_mem_subalgebra ψ S hS_sub ha⟩
    have hS'_nonline : ¬ ∃ q' : Albert, ∃ hq' : IsAtom q', q' ∈ (H3Subalgebra .C).carrier ∧
        (S' : Set Albert) ⊆ (lineSubalgebra q' hq').carrier :=
      pullFinset_nonline hQH ψ S hS_sub fun ⟨q, hq, hqH, hlineS⟩ => by
        have hle := line_erase_upper_bound T hT_atoms hT_irr hT_nonline (by omega) p hpT q hq hqH hlineS
        dsimp only at hle
        omega
    have hC := (prop_arity_upper_C S' hS'_atoms hS'_irr hS'_nonline).1
    have hS'_card : S'.card = S.card := pullFinset_card ψ S hS_sub
    have hS_add : S.card + 1 = T.card := Finset.card_erase_add_one hpT
    omega

private def quatWindowIsoH3H (Q : QuaternionicWindow) :
    JordanSubalgebraIso (H3Subalgebra .H) Q.subalgebra where
  toLinearEquiv :=
    { toFun := fun x =>
        ⟨Q.embedding ((assocHermEquiv assocCD_H).symm x), Q.range_eq ▸ ⟨_, rfl⟩⟩
      invFun := fun y =>
        assocHermEquiv assocCD_H (quatWindowEquiv Q y)
      left_inv := fun x => by
        apply Subtype.ext
        have h1 : quatWindowEquiv Q ⟨Q.embedding ((assocHermEquiv assocCD_H).symm x),
            Q.range_eq ▸ ⟨_, rfl⟩⟩ = (assocHermEquiv assocCD_H).symm x :=
          Q.injective (quatWindowEquiv_apply_eq Q _)
        have h2 : (assocHermEquiv assocCD_H ((assocHermEquiv assocCD_H).symm x)).1 = x.1 :=
          congrArg Subtype.val ((assocHermEquiv assocCD_H).apply_symm_apply x)
        dsimp only
        rw [h1, h2]
      right_inv := fun y => Subtype.ext (by
        dsimp only
        rw [(assocHermEquiv assocCD_H).symm_apply_apply]
        exact quatWindowEquiv_apply_eq Q y)
      map_add' := fun x y => Subtype.ext (by
        have heq : (assocHermEquiv assocCD_H).symm (x + y) =
            (assocHermEquiv assocCD_H).symm x + (assocHermEquiv assocCD_H).symm y :=
          map_add _ x y
        change Q.embedding ((assocHermEquiv assocCD_H).symm (x + y)) =
          Q.embedding ((assocHermEquiv assocCD_H).symm x) + Q.embedding ((assocHermEquiv assocCD_H).symm y)
        rw [heq, map_add])
      map_smul' := fun r x => Subtype.ext (by
        have heq : (assocHermEquiv assocCD_H).symm (r • x) =
            r • (assocHermEquiv assocCD_H).symm x :=
          map_smul _ r x
        change Q.embedding ((assocHermEquiv assocCD_H).symm (r • x)) =
          r • Q.embedding ((assocHermEquiv assocCD_H).symm x)
        rw [heq, map_smul]) }
  map_unit := Subtype.ext (by
    have h1 : (assocHermEquiv assocCD_H).symm ⟨albertUnit, (H3Subalgebra .H).unit_mem⟩ = 1 :=
      (assocHermEquiv assocCD_H).symm_apply_eq.mpr (Subtype.ext (assocHermEquiv_one assocCD_H).symm)
    change Q.embedding ((assocHermEquiv assocCD_H).symm ⟨albertUnit, (H3Subalgebra .H).unit_mem⟩) = albertUnit
    rw [h1, Q.unit])
  map_jordan x y := Subtype.ext (by
    let M := (assocHermEquiv assocCD_H).symm x
    let N := (assocHermEquiv assocCD_H).symm y
    obtain ⟨P, hP⟩ := quatHermitian_product_closed M N
    have hP_val : (assocHermEquiv assocCD_H P).1 = jordanMul x.1 y.1 := by
      change assocMatToAlbert assocCD_H (P : QuatMatrix3) = jordanMul x.1 y.1
      rw [hP, jordanMul_assocMatToAlbert assocCD_H]
      have hx : assocMatToAlbert assocCD_H M.1 = x.1 :=
        congrArg Subtype.val ((assocHermEquiv assocCD_H).apply_symm_apply x)
      have hy : assocMatToAlbert assocCD_H N.1 = y.1 :=
        congrArg Subtype.val ((assocHermEquiv assocCD_H).apply_symm_apply y)
      rw [hx, hy]
    have hsymm : (assocHermEquiv assocCD_H).symm
        ⟨jordanMul x.1 y.1, (H3Subalgebra .H).product_mem _ x.2 _ y.2⟩ = P :=
      (assocHermEquiv assocCD_H).symm_apply_eq.mpr (Subtype.ext hP_val.symm)
    change Q.embedding ((assocHermEquiv assocCD_H).symm ⟨jordanMul x.1 y.1, _⟩) =
      jordanMul (Q.embedding M) (Q.embedding N)
    rw [hsymm, Q.preserves_product M N P hP])

private theorem prop_arity_upper_O (T : Finset Albert)
    (hT_atoms : ∀ p ∈ T, IsAtom p ∧ p ∈ (H3Subalgebra .O).carrier)
    (hT_irr : IsIrredundant T)
    (hT_nonline : ¬ ∃ q : Albert, ∃ hq : IsAtom q, q ∈ (H3Subalgebra .O).carrier ∧
      (T : Set Albert) ⊆ (lineSubalgebra q hq).carrier) :
    T.card ≤ 5 := by
  by_contra hgt
  have h6 : 6 ≤ T.card := by omega
  obtain ⟨p, hpT⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
  let B := generatedSubalgebra (T.erase p : Set Albert)
  have hBk : B.carrier < (H3Subalgebra .O).carrier := by
    refine lt_of_le_of_ne (generatedSubalgebra_le (B := H3Subalgebra .O) fun z hz =>
        (hT_atoms z (Finset.mem_of_mem_erase hz)).2) fun heq => ?_
    apply hT_irr.2 p hpT
    change p ∈ B.carrier
    rw [heq]
    exact (hT_atoms p hpT).2
  rcases lem_five_sub .O B hBk with ⟨q, hq, hqK, hline⟩ | ⟨Q, hQ⟩
  · have hle := line_erase_upper_bound T hT_atoms hT_irr hT_nonline (by omega) p hpT q hq hqK
      (subset_generatedSubalgebra _ |>.trans hline)
    dsimp only at hle
    omega
  · let ψ := quatWindowIsoH3H Q
    let S := T.erase p
    have hS_sub : (S : Set Albert) ⊆ Q.subalgebra.carrier := (subset_generatedSubalgebra _).trans hQ
    let S' := pullFinset ψ S hS_sub
    have hS_irr : IsIrredundant S := by
      refine ⟨fun a ha => hT_irr.1 a (Finset.mem_of_mem_erase ha), fun a ha ha_in => ?_⟩
      apply hT_irr.2 a (Finset.mem_of_mem_erase ha)
      exact generatedSubalgebra_mono (fun z hz => by
        simp only [Finset.mem_coe, Finset.mem_erase] at hz ⊢
        exact ⟨hz.1, Finset.mem_of_mem_erase hz.2⟩) ha_in
    have hS'_irr : IsIrredundant S' := pullFinset_isIrredundant ψ S hS_sub hS_irr
    have hS'_atoms : ∀ a ∈ S', IsAtom a ∧ a ∈ (H3Subalgebra .H).carrier := fun a ha =>
      ⟨hS'_irr.1 a ha, pullFinset_mem_subalgebra ψ S hS_sub ha⟩
    have hS'_nonline : ¬ ∃ q' : Albert, ∃ hq' : IsAtom q', q' ∈ (H3Subalgebra .H).carrier ∧
        (S' : Set Albert) ⊆ (lineSubalgebra q' hq').carrier :=
      pullFinset_nonline (fun z _ => mem_H3O z) ψ S hS_sub fun ⟨q, hq, hqO, hlineS⟩ => by
        have hle := line_erase_upper_bound T hT_atoms hT_irr hT_nonline (by omega) p hpT q hq hqO hlineS
        dsimp only at hle
        omega
    have hH := prop_arity_upper_H S' hS'_atoms hS'_irr hS'_nonline
    have hS'_card : S'.card = S.card := pullFinset_card ψ S hS_sub
    have hS_add : S.card + 1 = T.card := Finset.card_erase_add_one hpT
    omega

theorem prop_arity_upper_claim (k : CDLevel) (T : Finset Albert)
    (hT_atoms : ∀ p ∈ T, IsAtom p ∧ p ∈ (H3Subalgebra k).carrier)
    (hT_irr : IsIrredundant T)
    (hT_nonline : ¬ ∃ q : Albert, ∃ hq : IsAtom q, q ∈ (H3Subalgebra k).carrier ∧
      (T : Set Albert) ⊆ (lineSubalgebra q hq).carrier) :
    T.card ≤ arityBound k ∧
      (k = .C → T.card = 4 → ∀ a ∈ T, ∃! b ∈ T, b ≠ a ∧ jordanMul a b = 0) := by
  cases k with
  | R => exact ⟨prop_arity_upper_R T hT_atoms hT_irr hT_nonline, fun h _ => by cases h⟩
  | C =>
    have hC := prop_arity_upper_C T hT_atoms hT_irr hT_nonline
    exact ⟨hC.1, fun _ h4 => hC.2 h4⟩
  | H => exact ⟨prop_arity_upper_H T hT_atoms hT_irr hT_nonline, fun h _ => by cases h⟩
  | O => exact ⟨prop_arity_upper_O T hT_atoms hT_irr hT_nonline, fun h _ => by cases h⟩

private theorem H3_not_le_lineSubalgebra (k : CDLevel) (q : Albert) (hq : IsAtom q) :
    ¬ (H3Subalgebra k).carrier ≤ (lineSubalgebra q hq).carrier := by
  intro hle
  have hRk : (H3Subalgebra .R).carrier ≤ (H3Subalgebra k).carrier :=
    H3Subalgebra_mono (by cases k <;> decide)
  have hd_mem : ∀ i : Fin 3, diagAtom i ∈ (lineSubalgebra q hq).carrier := fun i =>
    hle (hRk (diagAtom_mem_H3Subalgebra .R i))
  have hd_bool : ∀ i : Fin 3, q.1 i = 0 ∨ q.1 i = 1 := fun i => by
    have hi := (mem_lineSubalgebra_iff q hq (diagAtom i)).mp (hd_mem i)
    have hpi : tracePairing q (diagAtom i) = q.1 i := by
      fin_cases i <;> simp [tracePairing_eq_coords, diagAtom_fst, diagAtom_snd,
        octDot_zero_right]
    rw [hpi, jordanMul_comm] at hi
    fin_cases i
    · have hj := congrArg (fun a : Albert => a.1 0) hi
      change (jordanMul (diagAtom 0) q).1 0 = (q.1 0 • q).1 0 at hj
      rw [jordanMul_diagAtom0] at hj
      simp [albert_smul_fst] at hj
      have hfac : q.1 0 * (q.1 0 - 1) = 0 := by linarith
      rcases mul_eq_zero.mp hfac with h0 | h1
      · exact Or.inl h0
      · exact Or.inr (sub_eq_zero.mp h1)
    · have hj := congrArg (fun a : Albert => a.1 1) hi
      change (jordanMul (diagAtom 1) q).1 1 = (q.1 1 • q).1 1 at hj
      rw [jordanMul_diagAtom1] at hj
      simp [albert_smul_fst] at hj
      have hfac : q.1 1 * (q.1 1 - 1) = 0 := by linarith
      rcases mul_eq_zero.mp hfac with h0 | h1
      · exact Or.inl h0
      · exact Or.inr (sub_eq_zero.mp h1)
    · have hj := congrArg (fun a : Albert => a.1 2) hi
      change (jordanMul (diagAtom 2) q).1 2 = (q.1 2 • q).1 2 at hj
      rw [jordanMul_diagAtom2] at hj
      simp [albert_smul_fst] at hj
      have hfac : q.1 2 * (q.1 2 - 1) = 0 := by linarith
      rcases mul_eq_zero.mp hfac with h0 | h1
      · exact Or.inl h0
      · exact Or.inr (sub_eq_zero.mp h1)
  have hsum : q.1 0 + q.1 1 + q.1 2 = 1 := by simpa [albertTrace, Fin.sum_univ_three] using hq.2
  have hs01_mem : slotElem01 octOne ∈ (lineSubalgebra q hq).carrier :=
    hle (hRk ⟨(octSubalgebraOfLevel .R).one_mem,
      (octSubalgebraOfLevel .R).carrier.zero_mem, (octSubalgebraOfLevel .R).carrier.zero_mem⟩)
  have hs02_mem : slotElem02 octOne ∈ (lineSubalgebra q hq).carrier :=
    hle (hRk ⟨(octSubalgebraOfLevel .R).carrier.zero_mem,
      (octSubalgebraOfLevel .R).one_mem, (octSubalgebraOfLevel .R).carrier.zero_mem⟩)
  have hdiag_uniq : ∀ i : Fin 3, q.1 i = 1 → q = diagAtom i := fun i hi => by
    have htp : tracePairing (diagAtom i) q = 1 := by
      fin_cases i <;>
        simpa [tracePairing_eq_coords, diagAtom_fst, diagAtom_snd,
          octDot_zero_left, octDot_zero_right] using hi
    have hq_self : tracePairing q q = 1 := by
      show albertTrace (jordanMul q q) = 1
      rw [hq.1, hq.2]
    have hd_self : tracePairing (diagAtom i) (diagAtom i) = 1 := by
      show albertTrace (jordanMul (diagAtom i) (diagAtom i)) = 1
      rw [(diagAtom_isAtom i).1, (diagAtom_isAtom i).2]
    have hsq : tracePairing (diagAtom i - q) (diagAtom i - q) = 0 := by
      rw [tracePairing_sub_left, tracePairing_sub_right, tracePairing_sub_right,
        hd_self, hq_self, tracePairing_comm q (diagAtom i), htp]
      ring
    rw [tracePairing_eq_coords] at hsq
    simp only [octDot_self] at hsq
    have hn0 : 0 ≤ octNormSq ((diagAtom i - q).2 0) := octNormSq_nonneg _
    have hn1 : 0 ≤ octNormSq ((diagAtom i - q).2 1) := octNormSq_nonneg _
    have hn2 : 0 ≤ octNormSq ((diagAtom i - q).2 2) := octNormSq_nonneg _
    have hd0 : (diagAtom i - q).1 0 = 0 := by nlinarith
    have hd1 : (diagAtom i - q).1 1 = 0 := by nlinarith
    have hd2 : (diagAtom i - q).1 2 = 0 := by nlinarith
    have ho0 : (diagAtom i - q).2 0 = 0 := (octNormSq_eq_zero _).mp (by nlinarith)
    have ho1 : (diagAtom i - q).2 1 = 0 := (octNormSq_eq_zero _).mp (by nlinarith)
    have ho2 : (diagAtom i - q).2 2 = 0 := (octNormSq_eq_zero _).mp (by nlinarith)
    exact (sub_eq_zero.mp (albert_ext hd0 hd1 hd2 ho0 ho1 ho2)).symm
  rcases hd_bool 0 with h0 | h0 <;> rcases hd_bool 1 with h1 | h1 <;> rcases hd_bool 2 with h2 | h2
  · linarith
  · have hq2 : q = diagAtom 2 := hdiag_uniq 2 h2
    have hm := (mem_lineSubalgebra_iff q hq (slotElem02 octOne)).mp hs02_mem
    rw [hq2] at hm
    have htp : tracePairing (diagAtom 2) (slotElem02 octOne) = 0 := by
      simp [tracePairing_eq_coords, diagAtom_fst, diagAtom_snd,
        slotElem02_fst, slotElem02_snd_0, slotElem02_snd_1, slotElem02_snd_2,
        octDot_zero_left, octDot_zero_right]
    rw [htp, zero_smul, jordanMul_diagAtom2] at hm
    have h21 := congrArg (fun a : Albert => (a.2 1).1.re) hm
    dsimp only at h21
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, slotElem02_snd_1,
      oct_smul_fst, Quaternion.re_smul, smul_eq_mul, albert_zero_snd] at h21
    simp [octOne, octonionScalar] at h21
    try norm_num at h21
  · have hq1 : q = diagAtom 1 := hdiag_uniq 1 h1
    have hm := (mem_lineSubalgebra_iff q hq (slotElem01 octOne)).mp hs01_mem
    rw [hq1] at hm
    have htp : tracePairing (diagAtom 1) (slotElem01 octOne) = 0 := by
      simp [tracePairing_eq_coords, diagAtom_fst, diagAtom_snd,
        slotElem01_fst, slotElem01_snd_0, slotElem01_snd_1, slotElem01_snd_2,
        octDot_zero_left, octDot_zero_right]
    rw [htp, zero_smul, jordanMul_diagAtom1] at hm
    have h20 := congrArg (fun a : Albert => (a.2 0).1.re) hm
    dsimp only at h20
    simp only [Matrix.cons_val_zero, slotElem01_snd_0, oct_smul_fst,
      Quaternion.re_smul, smul_eq_mul, albert_zero_snd] at h20
    simp [octOne, octonionScalar] at h20
    try norm_num at h20
  · linarith
  · have hq0 : q = diagAtom 0 := hdiag_uniq 0 h0
    have hm := (mem_lineSubalgebra_iff q hq (slotElem01 octOne)).mp hs01_mem
    rw [hq0] at hm
    have htp : tracePairing (diagAtom 0) (slotElem01 octOne) = 0 := by
      simp [tracePairing_eq_coords, diagAtom_fst, diagAtom_snd,
        slotElem01_fst, slotElem01_snd_0, slotElem01_snd_1, slotElem01_snd_2,
        octDot_zero_left, octDot_zero_right]
    rw [htp, zero_smul, jordanMul_diagAtom0] at hm
    have h20 := congrArg (fun a : Albert => (a.2 0).1.re) hm
    dsimp only at h20
    simp only [Matrix.cons_val_zero, slotElem01_snd_0, oct_smul_fst,
      Quaternion.re_smul, smul_eq_mul, albert_zero_snd] at h20
    simp [octOne, octonionScalar] at h20
    try norm_num at h20
  · linarith
  · linarith
  · linarith

theorem prop_arity (k : CDLevel) :
    sSup {n : ℕ | ∃ T : Finset Albert, T.card = n ∧
      (∀ p ∈ T, IsAtom p ∧ p ∈ (H3Subalgebra k).carrier) ∧
      IsIrredundant T ∧ generatedSubalgebra (T : Set Albert) = H3Subalgebra k} = arityBound k := by
  let S : Set ℕ := {n : ℕ | ∃ T : Finset Albert, T.card = n ∧
    (∀ p ∈ T, IsAtom p ∧ p ∈ (H3Subalgebra k).carrier) ∧
    IsIrredundant T ∧ generatedSubalgebra (T : Set Albert) = H3Subalgebra k}
  have hmem : arityBound k ∈ S := by
    obtain ⟨T, hcard, hTa, hTi, hTg⟩ := prop_arity_lower k
    exact ⟨T, hcard, hTa, hTi, hTg⟩
  have hle : ∀ n ∈ S, n ≤ arityBound k := by
    rintro n ⟨T, rfl, hTa, hTi, hTg⟩
    refine (prop_arity_upper_claim k T hTa hTi ?_).1
    rintro ⟨q, hq, _, hline⟩
    apply H3_not_le_lineSubalgebra k q hq
    rw [← hTg]
    exact generatedSubalgebra_le (B := lineSubalgebra q hq) hline
  have hbdd : BddAbove S := ⟨arityBound k, hle⟩
  exact le_antisymm (csSup_le ⟨arityBound k, hmem⟩ hle) (le_csSup hbdd hmem)

end Section3

/-! ## Section 4: Helly Number (`lem:five:helly`, `cor:helly`) and Line Counterexample -/

section Section4

def HasHellyProp (h : ℕ) : Prop :=
  ∀ S : Set Albert, (∀ s ∈ S, IsAtom s) →
    (∀ T : Finset Albert, (T : Set Albert) ⊆ S → T.card ≤ h →
      ∃ B : NativeJordanSubalgebra, B ≠ ⊤ ∧ (T : Set Albert) ⊆ B.carrier) →
    ∃ B : NativeJordanSubalgebra, B ≠ ⊤ ∧ S ⊆ B.carrier

theorem finite_gen_subset_of_generates (S : Set Albert)
    (hS_atoms : ∀ s ∈ S, IsAtom s) (hS : generatedSubalgebra S = ⊤) :
    ∃ T : Finset Albert, (T : Set Albert) ⊆ S ∧
      IsIrredundant T ∧ generatedSubalgebra (T : Set Albert) = ⊤ := by
  classical
  let Ucarrier : Submodule ℝ Albert :=
    { carrier := {x : Albert | ∃ T : Finset Albert, (T : Set Albert) ⊆ S ∧
        x ∈ (generatedSubalgebra (T : Set Albert)).carrier}
      zero_mem' := ⟨∅, by simp, (generatedSubalgebra ((∅ : Finset Albert) : Set Albert)).carrier.zero_mem⟩
      add_mem' := by
        rintro x y ⟨Tx, hTx, hx⟩ ⟨Ty, hTy, hy⟩
        refine ⟨Tx ∪ Ty, ?_, ?_⟩
        · rw [Finset.coe_union]; exact Set.union_subset hTx hTy
        · exact (generatedSubalgebra ((Tx ∪ Ty : Finset Albert) : Set Albert)).carrier.add_mem
            (generatedSubalgebra_mono (Finset.coe_subset.mpr Finset.subset_union_left) hx)
            (generatedSubalgebra_mono (Finset.coe_subset.mpr Finset.subset_union_right) hy)
      smul_mem' := by
        rintro r x ⟨Tx, hTx, hx⟩
        exact ⟨Tx, hTx, (generatedSubalgebra (Tx : Set Albert)).carrier.smul_mem r hx⟩ }
  let U : NativeJordanSubalgebra :=
    { carrier := Ucarrier
      unit_mem := ⟨∅, by simp, (generatedSubalgebra ((∅ : Finset Albert) : Set Albert)).unit_mem⟩
      product_mem := by
        rintro x ⟨Tx, hTx, hx⟩ y ⟨Ty, hTy, hy⟩
        refine ⟨Tx ∪ Ty, ?_, ?_⟩
        · rw [Finset.coe_union]; exact Set.union_subset hTx hTy
        · exact (generatedSubalgebra ((Tx ∪ Ty : Finset Albert) : Set Albert)).product_mem _
            (generatedSubalgebra_mono (Finset.coe_subset.mpr Finset.subset_union_left) hx) _
            (generatedSubalgebra_mono (Finset.coe_subset.mpr Finset.subset_union_right) hy) }
  have hSU : S ⊆ U.carrier := fun s hs =>
    ⟨{s}, by simp [hs], subset_generatedSubalgebra (({s} : Finset Albert) : Set Albert) (by simp)⟩
  have htopU : ∀ x : Albert, x ∈ U.carrier := fun x => by
    have hmem : x ∈ (generatedSubalgebra S).carrier := by rw [hS]; exact trivial
    exact generatedSubalgebra_le hSU hmem
  have : Module.Finite ℝ Octonion :=
    inferInstanceAs (FiniteDimensional ℝ (Quaternion ℝ × Quaternion ℝ))
  have : Module.Finite ℝ Albert :=
    inferInstanceAs (FiniteDimensional ℝ ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
  let b := Module.finBasis ℝ Albert
  choose Tf hTf_sub hTf_mem using fun i => htopU (b i)
  let T₀ : Finset Albert := Finset.univ.biUnion Tf
  have hT₀_sub : (T₀ : Set Albert) ⊆ S := by
    intro x hx
    simp only [T₀, Finset.coe_biUnion, Finset.mem_coe, Finset.mem_univ, Set.mem_iUnion,
      exists_prop, true_and] at hx
    rcases hx with ⟨i, hi⟩
    exact hTf_sub i hi
  have hT₀_gen : generatedSubalgebra (T₀ : Set Albert) = ⊤ := by
    apply nativeJordanSubalgebra_ext
    change (generatedSubalgebra (T₀ : Set Albert)).carrier = (⊤ : Submodule ℝ Albert)
    rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact generatedSubalgebra_mono
      (Finset.coe_subset.mpr (Finset.subset_biUnion_of_mem Tf (Finset.mem_univ i))) (hTf_mem i)
  have hshrink : ∀ n : ℕ, ∀ T : Finset Albert, T.card = n →
      (T : Set Albert) ⊆ S → generatedSubalgebra (T : Set Albert) = ⊤ →
      ∃ T' : Finset Albert, (T' : Set Albert) ⊆ S ∧ IsIrredundant T' ∧
        generatedSubalgebra (T' : Set Albert) = ⊤ := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro T hcard hTS hgen
      have hTa : ∀ p ∈ T, IsAtom p := fun p hp => hS_atoms p (hTS hp)
      by_cases hIrr : IsIrredundant T
      · exact ⟨T, hTS, hIrr, hgen⟩
      · have hnot := (isIrredundant_iff_no_proper_same_gen T hTa).not.mp hIrr
        push Not at hnot
        obtain ⟨U', hU'ssub, hU'eq⟩ := hnot
        have hU'lt : U'.card < n := hcard ▸ Finset.card_lt_card hU'ssub
        exact ih U'.card hU'lt U' rfl
          ((Finset.coe_subset.mpr hU'ssub.subset).trans hTS) (hU'eq.trans hgen)
  exact hshrink T₀.card T₀ rfl hT₀_sub hT₀_gen

theorem lem_five_helly :
    (∀ h, HasHellyProp h ↔ 5 ≤ h) ∧ sInf {h : ℕ | HasHellyProp h} = arityBound .O := by
  classical
  have hiff : ∀ h, HasHellyProp h ↔ 5 ≤ h := fun h => by
    constructor
    · intro hH
      by_contra hlt
      have hle4 : h ≤ 4 := by omega
      let S : Set Albert := Set.range pentadF
      have hS_atoms : ∀ s ∈ S, IsAtom s := by
        rintro _ ⟨i, rfl⟩; exact pentadF_isAtom i
      have hsub : ∀ T : Finset Albert, (T : Set Albert) ⊆ S → T.card ≤ h →
          ∃ B : NativeJordanSubalgebra, B ≠ ⊤ ∧ (T : Set Albert) ⊆ B.carrier := by
        intro T hTS hTcard
        have hk : ∃ k : Fin 5, pentadF k ∉ T := by
          by_contra hall
          push Not at hall
          have himg : Finset.univ.image pentadF ⊆ T := by
            intro x hx
            rcases Finset.mem_image.mp hx with ⟨k, _, rfl⟩
            exact hall k
          have hcard5 : 5 ≤ T.card := by
            have hc := Finset.card_le_card himg
            rw [Finset.card_image_of_injective _ pentadF_injective, Finset.card_fin] at hc
            exact hc
          omega
        obtain ⟨k, hk_not⟩ := hk
        obtain ⟨Q, hQ⟩ := pentadDrop_in_quaternionicWindow k
        refine ⟨Q.subalgebra, ?_, fun t ht => ?_⟩
        · exact (proper_iff_special Q.subalgebra).mpr ⟨6, by norm_num, ⟨symplecticQuatEmbed Q⟩⟩
        · obtain ⟨i, rfl⟩ := hTS ht
          have hik : i ≠ k := fun h => hk_not (h ▸ ht)
          obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hik
          exact hQ j
      obtain ⟨B, hB_ne, hBS⟩ := hH S hS_atoms hsub
      apply hB_ne
      apply nativeJordanSubalgebra_ext
      change B.carrier = (⊤ : Submodule ℝ Albert)
      rw [eq_top_iff]
      intro x _
      exact pentadF_generatesAlbert x B fun i => hBS ⟨i, rfl⟩
    · intro h5 S hS_atoms hsub
      by_contra hnone
      have hS_top : generatedSubalgebra S = ⊤ := by
        by_contra hne
        exact hnone ⟨generatedSubalgebra S, hne, subset_generatedSubalgebra S⟩
      obtain ⟨T, hTS, hT_irr, hT_top⟩ := finite_gen_subset_of_generates S hS_atoms hS_top
      have hT_atoms : ∀ p ∈ T, IsAtom p ∧ p ∈ (H3Subalgebra .O).carrier := fun p hp =>
        ⟨hS_atoms p (hTS hp), by rw [H3Subalgebra_O_eq_top]; trivial⟩
      have hT_nonline : ¬ ∃ q : Albert, ∃ hq : IsAtom q, q ∈ (H3Subalgebra .O).carrier ∧
          (T : Set Albert) ⊆ (lineSubalgebra q hq).carrier := by
        rintro ⟨q, hq, _, hline⟩
        apply H3_not_le_lineSubalgebra .O q hq
        rw [H3Subalgebra_O_eq_top, ← hT_top]
        exact generatedSubalgebra_le (B := lineSubalgebra q hq) hline
      have hT_card : T.card ≤ arityBound .O := (prop_arity_upper_claim .O T hT_atoms hT_irr hT_nonline).1
      change T.card ≤ 5 at hT_card
      obtain ⟨B, hB_ne, hTB⟩ := hsub T hTS (hT_card.trans h5)
      apply hB_ne
      apply nativeJordanSubalgebra_ext
      change B.carrier = (⊤ : Submodule ℝ Albert)
      rw [eq_top_iff]
      intro x _
      have hx_top : x ∈ (generatedSubalgebra (T : Set Albert)).carrier := by rw [hT_top]; trivial
      exact generatedSubalgebra_le hTB hx_top
  refine ⟨hiff, ?_⟩
  have h5_mem : 5 ∈ {h : ℕ | HasHellyProp h} := (hiff 5).mpr le_rfl
  exact le_antisymm (Nat.sInf_le h5_mem) (le_csInf ⟨5, h5_mem⟩ fun h hh => (hiff h).mp hh)

theorem cor_helly_geometric (S : Set Albert) (hS : ∀ s ∈ S, IsAtom s) :
    (∃ B : NativeJordanSubalgebra, B ≠ ⊤ ∧ S ⊆ (B.carrier : Set Albert)) ↔
      (∀ T : Finset Albert, (T : Set Albert) ⊆ S → T.card ≤ 5 →
        ∃ B : NativeJordanSubalgebra, B ≠ ⊤ ∧ (T : Set Albert) ⊆ (B.carrier : Set Albert)) := by
  constructor
  · rintro ⟨B, hB_ne, hBS⟩ T hTS _
    exact ⟨B, hB_ne, hTS.trans hBS⟩
  · exact (lem_five_helly.1 5).mpr le_rfl S hS

theorem cor_helly_special (S : Set Albert) (hS : ∀ s ∈ S, IsAtom s) :
    (∃ B : NativeJordanSubalgebra, IsSpecialSubalgebra B ∧ S ⊆ (B.carrier : Set Albert)) ↔
      (∀ T : Finset Albert, (T : Set Albert) ⊆ S → T.card ≤ 5 →
        ∃ B : NativeJordanSubalgebra, IsSpecialSubalgebra B ∧ (T : Set Albert) ⊆ (B.carrier : Set Albert)) := by
  have hgeom := cor_helly_geometric S hS
  constructor
  · rintro ⟨B, hsp, hBS⟩
    have h1 : ∃ B : NativeJordanSubalgebra, B ≠ ⊤ ∧ S ⊆ (B.carrier : Set Albert) :=
      ⟨B, (proper_iff_special B).mpr hsp, hBS⟩
    intro T hTS hTcard
    obtain ⟨B', hB'_ne, hTB'⟩ := hgeom.mp h1 T hTS hTcard
    exact ⟨B', (proper_iff_special B').mp hB'_ne, hTB'⟩
  · intro hT
    have h2 : ∀ T : Finset Albert, (T : Set Albert) ⊆ S → T.card ≤ 5 →
        ∃ B : NativeJordanSubalgebra, B ≠ ⊤ ∧ (T : Set Albert) ⊆ (B.carrier : Set Albert) := by
      intro T hTS hTcard
      obtain ⟨B, hsp, hTB⟩ := hT T hTS hTcard
      exact ⟨B, (proper_iff_special B).mpr hsp, hTB⟩
    obtain ⟨B, hB_ne, hBS⟩ := hgeom.mpr h2
    exact ⟨B, (proper_iff_special B).mp hB_ne, hBS⟩

theorem cor_helly_sharp : ¬ HasHellyProp 4 := by
  intro h4
  have h5 := (lem_five_helly.1 4).mp h4
  omega

private theorem embedding_projective_data {n : ℕ} (B : NativeJordanSubalgebra) (d : ℕ)
    (ι : SuppliedHermitianEmbedding B d) (c : ℝ) (hc : 0 < c)
    (htr : ∀ x y : B.carrier,
      (Matrix.trace (ι.map x * ι.map y)).re = c * tracePairing x.1 y.1)
    (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i)) (hpB : ∀ i, p i ∈ B.carrier) :
    ∃ (P : Fin n → HermitianEmbeddingMatrix d),
      ∀ ρ : Albert, IsDensity ρ →
        ∃ (σ : HermitianEmbeddingMatrix d)
          (M : AlgebraicProjectiveData (Fin n) (HermitianEmbeddingMatrix d)),
          IsEmbeddingDensity d σ ∧
          M.projection = P ∧
          (∀ X, M.state X = (Matrix.trace (σ * X)).re) ∧
          AlgebraicMomentBinding M ∧
          M.Matches p ρ := by
  let P : Fin n → HermitianEmbeddingMatrix d := fun i => ι.map ⟨p i, hpB i⟩
  have hP_herm : ∀ i, (P i).IsHermitian := fun i => ι.hermitian ⟨p i, hpB i⟩
  have hP_id : ∀ i, P i * P i = P i := fun i => by
    have hj := ι.jordan ⟨p i, hpB i⟩ ⟨p i, hpB i⟩
    have hp1 : (⟨jordanMul (p i) (p i), B.product_mem _ (hpB i) _ (hpB i)⟩ : B.carrier) =
        ⟨p i, hpB i⟩ := Subtype.ext (hp i).1
    rw [hp1] at hj
    have h2 : (1 / 2 : ℝ) • (P i * P i + P i * P i) = P i * P i := by module
    change P i = (1 / 2 : ℝ) • (P i * P i + P i * P i) at hj
    rw [h2] at hj
    exact hj.symm
  refine ⟨P, fun ρ hρ => ?_⟩
  obtain ⟨σ, hσ_dens, hstats⟩ :=
    suppliedEmbedding_scaled_state_transport B d ι c hc htr ρ hρ
  let st : HermitianEmbeddingMatrix d →ₗ[ℝ] ℝ :=
    { toFun := fun X => (Matrix.trace (σ * X)).re
      map_add' := fun X Y => by rw [mul_add, Matrix.trace_add, Complex.add_re]
      map_smul' := fun r X => by
        rw [Algebra.mul_smul_comm, Matrix.trace_smul, Complex.real_smul, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, RingHom.id_apply, smul_eq_mul] }
  let M : AlgebraicProjectiveData (Fin n) (HermitianEmbeddingMatrix d) :=
    { projection := P
      idempotent := hP_id
      selfAdjoint := fun i => (hP_herm i).eq
      state := st
      state_unit := by
        change (Matrix.trace (σ * 1)).re = 1
        rw [Matrix.mul_one, hσ_dens.2, Complex.one_re]
      state_star := fun X => by
        change (Matrix.trace (σ * star X)).re = (Matrix.trace (σ * X)).re
        have h1 : Matrix.trace (σ * star X) = star (Matrix.trace (σ * X)) := by
          rw [Matrix.star_eq_conjTranspose, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
            hσ_dens.1.isHermitian.eq, Matrix.trace_mul_comm]
        rw [h1, Complex.star_def, Complex.conj_re]
      state_positive := fun X => trace_psd_mul_sq_nonneg hσ_dens.1 X }
  exact ⟨σ, M, hσ_dens, rfl, fun _ => rfl, algebraicMomentBinding M, fun w => hstats n p hpB w⟩

theorem cor_helly_operational_if {n : ℕ} (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i))
    (hsub : ∀ T : Finset (Fin n), T.card ≤ 5 →
      ∃ B : NativeJordanSubalgebra, B ≠ ⊤ ∧ ∀ i ∈ T, p i ∈ B.carrier) :
    ∃ (d : ℕ) (P : Fin n → HermitianEmbeddingMatrix d),
      d ∈ ({6, 24} : Set ℕ) ∧
      ∀ ρ : Albert, IsDensity ρ →
        ∃ (σ : HermitianEmbeddingMatrix d)
          (M : AlgebraicProjectiveData (Fin n) (HermitianEmbeddingMatrix d)),
          IsEmbeddingDensity d σ ∧
          M.projection = P ∧
          (∀ X, M.state X = (Matrix.trace (σ * X)).re) ∧
          AlgebraicMomentBinding M ∧
          M.Matches p ρ := by
  have hS_atoms : ∀ s ∈ Set.range p, IsAtom s := by
    rintro _ ⟨i, rfl⟩; exact hp i
  have h5 : ∀ T : Finset Albert, (T : Set Albert) ⊆ Set.range p → T.card ≤ 5 →
      ∃ B : NativeJordanSubalgebra, B ≠ ⊤ ∧ (T : Set Albert) ⊆ B.carrier := by
    intro T hTp hTcard
    classical
    have hidx : ∀ t : T, ∃ i : Fin n, p i = t.1 := fun t => hTp t.2
    choose idx hidx_eq using hidx
    let T' : Finset (Fin n) := T.attach.image idx
    have hT'card : T'.card ≤ 5 := by
      have hle := Finset.card_image_le (f := idx) (s := T.attach)
      rw [Finset.card_attach] at hle
      exact hle.trans hTcard
    obtain ⟨B, hB_ne, hTB⟩ := hsub T' hT'card
    refine ⟨B, hB_ne, fun t ht => ?_⟩
    have hteq : t = p (idx ⟨t, ht⟩) := (hidx_eq ⟨t, ht⟩).symm
    rw [hteq]
    exact hTB (idx ⟨t, ht⟩) (Finset.mem_image_of_mem idx (Finset.mem_attach T ⟨t, ht⟩))
  obtain ⟨B, hB_ne, hSB⟩ := (cor_helly_geometric (Set.range p) hS_atoms).mpr h5
  have hpB : ∀ i : Fin n, p i ∈ B.carrier := fun i => hSB ⟨i, rfl⟩
  have hlt : B.carrier < (H3Subalgebra .O).carrier := by
    rw [H3Subalgebra_O_eq_top]
    exact lt_of_le_of_ne le_top fun h => hB_ne (nativeJordanSubalgebra_ext h)
  rcases lem_five_sub .O B hlt with ⟨q, hq, _, hline⟩ | ⟨Q, hQ⟩
  · obtain ⟨P, hP⟩ := embedding_projective_data (lineSubalgebra q hq) 24
      (lineCliffordEmbed q hq) 8 (by norm_num) (lineCliffordEmbed_tracePairing q hq)
      p hp (fun i => hline (hpB i))
    exact ⟨24, P, by simp, hP⟩
  · obtain ⟨P, hP⟩ := embedding_projective_data Q.subalgebra 6
      (symplecticQuatEmbed Q) 2 (by norm_num) (symplecticQuatEmbed_tracePairing Q)
      p hp (fun i => hQ (hpB i))
    exact ⟨6, P, by simp, hP⟩

private theorem wordAmplitude_comp {α β A : Type*} [Ring A] (f : α → β) (P : β → A)
    (w : Word α) :
    wordAmplitude (P ∘ f) w = wordAmplitude P (w.map fun a => (f a.1, a.2)) := by
  suffices h : ∀ (acc : A) (w : Word α),
      w.foldl (fun x a => algebraicOutcome (P ∘ f) a * x) acc =
      (w.map fun a => (f a.1, a.2)).foldl (fun x a => algebraicOutcome P a * x) acc from h 1 w
  intro acc w
  induction w generalizing acc with
  | nil => rfl
  | cons a w ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hact : algebraicOutcome (P ∘ f) a = algebraicOutcome P (f a.1, a.2) := by
      rcases a with ⟨i, b⟩
      cases b <;> rfl
    rw [hact]
    exact ih _

private theorem wordOperator_comp {α β A : Type*} [Ring A] [StarRing A] (f : α → β) (P : β → A)
    (w : Word α) :
    wordOperator (P ∘ f) w = wordOperator P (w.map fun a => (f a.1, a.2)) := by
  simp only [wordOperator, wordAmplitude_comp]

private theorem nativeWordProbability_comp {α β : Type*} (f : α → β) (p : β → Albert)
    (ρ : Albert) (w : Word α) :
    nativeWordProbability (p ∘ f) ρ w =
      nativeWordProbability p ρ (w.map fun a => (f a.1, a.2)) := by
  suffices h : ∀ (acc : Albert) (w : Word α),
      w.foldl (fun x a => quadraticMap (nativeOutcome (p ∘ f) a) x) acc =
      (w.map fun a => (f a.1, a.2)).foldl (fun x a => quadraticMap (nativeOutcome p a) x) acc by
    unfold nativeWordProbability nativeBranchState
    rw [h ρ w]
  intro acc w
  induction w generalizing acc with
  | nil => rfl
  | cons a w ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hact : nativeOutcome (p ∘ f) a = nativeOutcome p (f a.1, a.2) := by
      rcases a with ⟨i, b⟩
      cases b <;> rfl
    rw [hact]
    exact ih _

private def restrictProjectiveData {α β : Type*} {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData β A) (f : α → β) : AlgebraicProjectiveData α A where
  projection := M.projection ∘ f
  idempotent i := M.idempotent (f i)
  selfAdjoint i := M.selfAdjoint (f i)
  state := M.state
  state_unit := M.state_unit
  state_star := M.state_star
  state_positive := M.state_positive

private theorem restrictProjectiveData_matches {α β : Type*} {A : Type}
    [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    [StarModule ℝ A]
    (M : AlgebraicProjectiveData β A) (f : α → β) (p : β → Albert) (ρ : Albert)
    (hmatch : M.Matches p ρ) :
    (restrictProjectiveData M f).Matches (p ∘ f) ρ := fun w => by
  change M.state (wordOperator (M.projection ∘ f) w) = nativeWordProbability (p ∘ f) ρ w
  rw [wordOperator_comp, nativeWordProbability_comp]
  exact hmatch (w.map fun a => (f a.1, a.2))

theorem cor_helly_operational_iff (hsep : AlbertUniformSeparationContract 5)
    {n : ℕ} (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i)) :
    (∃ (d : ℕ) (P : Fin n → HermitianEmbeddingMatrix d),
      d ∈ ({6, 24} : Set ℕ) ∧
      ∀ ρ : Albert, IsDensity ρ →
        ∃ (σ : HermitianEmbeddingMatrix d)
          (M : AlgebraicProjectiveData (Fin n) (HermitianEmbeddingMatrix d)),
          IsEmbeddingDensity d σ ∧
          M.projection = P ∧
          (∀ X, M.state X = (Matrix.trace (σ * X)).re) ∧
          AlgebraicMomentBinding M ∧
          M.Matches p ρ) ↔
      (∀ (k : ℕ), k ≤ 5 → ∀ (f : Fin k → Fin n), Function.Injective f →
        ∃ (A : Type) (_ : Ring A) (_ : StarRing A) (_ : Module ℝ A)
          (_ : IsScalarTower ℝ A A) (_ : SMulCommClass ℝ A A) (_ : StarModule ℝ A)
          (M : AlgebraicProjectiveData (Fin k) A) (ρ : Albert),
          IsDensity ρ ∧ AlgebraicMomentBinding M ∧ M.Matches (p ∘ f) ρ) := by
  constructor
  · rintro ⟨d, P, _, hrep⟩ k _ f _
    have hρ₀ : IsDensity (diagAtom 0) :=
      ⟨⟨diagAtom 0, (diagAtom_isAtom 0).1.symm⟩, (diagAtom_isAtom 0).2⟩
    obtain ⟨σ, M, _, _, _, _, hmatch⟩ := hrep (diagAtom 0) hρ₀
    exact ⟨HermitianEmbeddingMatrix d, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, restrictProjectiveData M f, diagAtom 0, hρ₀,
      algebraicMomentBinding (restrictProjectiveData M f),
      restrictProjectiveData_matches M f p (diagAtom 0) hmatch⟩
  · intro hrhs
    apply cor_helly_operational_if p hp
    intro T hTcard
    by_cases hTempty : T = ∅
    · subst hTempty
      let B1 : NativeJordanSubalgebra :=
        { carrier := Submodule.span ℝ {albertUnit}
          unit_mem := Submodule.subset_span (Set.mem_singleton albertUnit)
          product_mem := by
            rintro _ hx _ hy
            rcases Submodule.mem_span_singleton.mp hx with ⟨a, rfl⟩
            rcases Submodule.mem_span_singleton.mp hy with ⟨b, rfl⟩
            rw [jordanMul_smul_left, jordanMul_smul_right, jordanMul_albertUnit_left, smul_smul]
            exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton albertUnit)) }
      refine ⟨B1, fun htop => ?_, fun i hi => by simp at hi⟩
      have hmem : diagAtom 0 ∈ B1.carrier := by rw [htop]; trivial
      rcases Submodule.mem_span_singleton.mp hmem with ⟨a, ha⟩
      have ha0 := congrArg (fun x : Albert => x.1 0) ha
      have ha1 := congrArg (fun x : Albert => x.1 1) ha
      simp [albert_smul_fst, albertUnit_fst, diagAtom_fst] at ha0 ha1
      linarith
    · have hTne : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hTempty
      let k : ℕ := T.card
      have hk_pos : 0 < k := Finset.card_pos.mpr hTne
      by_contra hnone
      push Not at hnone
      have hgen_top : generatedSubalgebra {x | ∃ i ∈ T, p i = x} = ⊤ := by
        by_contra hne
        obtain ⟨i, hiT, hi_not⟩ := hnone (generatedSubalgebra {x | ∃ i ∈ T, p i = x}) hne
        exact hi_not (subset_generatedSubalgebra _ ⟨i, hiT, rfl⟩)
      let e : Fin k ≃ T := (Fintype.equivFinOfCardEq (α := ↥T) (n := k) (Fintype.card_coe T)).symm
      let f : Fin k → Fin n := fun j => (e j).1
      have hf : Function.Injective f := fun a b hab => e.injective (Subtype.ext hab)
      obtain ⟨A, _, _, _, _, _, _, M, ρ, hρ, _, hmatch⟩ := hrhs k hTcard f hf
      let clamp : Fin 5 → Fin k := fun i => ⟨min i.1 (k - 1), by omega⟩
      let q : Fin 5 → Albert := fun i => p (f (clamp i))
      have hq_atoms : ∀ i : Fin 5, IsAtom (q i) := fun i => hp (f (clamp i))
      have hq_gen : GeneratesAlbert q := by
        intro x B hBq
        have hx_top : x ∈ (generatedSubalgebra {x | ∃ i ∈ T, p i = x}).carrier := by
          rw [hgen_top]; trivial
        refine generatedSubalgebra_le ?_ hx_top
        rintro _ ⟨i, hiT, rfl⟩
        let j : Fin k := e.symm ⟨i, hiT⟩
        have hj_eq : f j = i := congrArg Subtype.val (e.apply_symm_apply ⟨i, hiT⟩)
        let i5 : Fin 5 := ⟨j.1, by omega⟩
        have hclamp : clamp i5 = j := Fin.ext (by simp [clamp, i5]; omega)
        have hq_eq : q i5 = p i := by dsimp only [q]; rw [hclamp, hj_eq]
        rw [← hq_eq]
        exact hBq i5
      obtain ⟨_L, c, γ, hγ, _hL, hpos, hneg⟩ := hsep.all_states q hq_atoms hq_gen
      let M5 := restrictProjectiveData M clamp
      have hM5_bind : AlgebraicMomentBinding M5 := algebraicMomentBinding M5
      have hM5_match : M5.Matches q ρ := restrictProjectiveData_matches M clamp (p ∘ f) ρ hmatch
      have hm_nonneg := hpos (momentsOfProjectiveData M5) hM5_bind.admissible
      have hm_eq : c.evaluate (momentWordProbability (momentsOfProjectiveData M5)) =
          c.evaluate (nativeWordProbability q ρ) := by
        unfold FiniteRealWordFunctional.evaluate
        congr 1
        refine List.map_congr_left fun t _ => ?_
        rw [(hM5_bind.probabilities t.2).trans (hM5_match t.2)]
      have hρ_neg := hneg ρ hρ
      linarith

def quatCornerSubmodule (Q : QuaternionicWindow) (q : Albert) : Submodule ℝ Albert where
  carrier := {x : Albert | x ∈ Q.subalgebra.carrier ∧ jordanMul q x = 0}
  zero_mem' := ⟨Q.subalgebra.carrier.zero_mem, jordanMul_zero_right q⟩
  add_mem' hx hy := ⟨Q.subalgebra.carrier.add_mem hx.1 hy.1, by
    rw [jordanMul_add_right, hx.2, hy.2, add_zero]⟩
  smul_mem' r _ hx := ⟨Q.subalgebra.carrier.smul_mem r hx.1, by
    rw [jordanMul_smul_right, hx.2, smul_zero]⟩

private def sympJ (v : Fin 6 → ℂ) : Fin 6 → ℂ := fun r =>
  let p := fin3ProdFin2Equiv6.symm r
  if p.2 = 0 then -star (v (fin3ProdFin2Equiv6 (p.1, 1)))
  else star (v (fin3ProdFin2Equiv6 (p.1, 0)))

private theorem sympJ_sympJ (v : Fin 6 → ℂ) : sympJ (sympJ v) = -v := by
  funext r
  simp only [sympJ, Pi.neg_apply]
  rcases hp : fin3ProdFin2Equiv6.symm r with ⟨i, j⟩
  have hr : fin3ProdFin2Equiv6 (i, j) = r := by
    rw [← hp, fin3ProdFin2Equiv6.apply_symm_apply]
  have h10 : ((1 : Fin 2) = 0) ↔ False := by decide
  fin_cases j
  · simp [fin3ProdFin2Equiv6.symm_apply_apply, h10]
    dsimp only at hr
    exact congrArg v hr
  · simp [fin3ProdFin2Equiv6.symm_apply_apply]
    dsimp only at hr
    exact congrArg v hr

private theorem sympJ_sub (u v : Fin 6 → ℂ) : sympJ (u - v) = sympJ u - sympJ v := by
  funext r
  simp only [sympJ, Pi.sub_apply, star_sub]
  rcases hp : fin3ProdFin2Equiv6.symm r with ⟨i, j⟩
  (fin_cases j <;> simp)
  ring

private theorem vecIp_sympJ_sympJ (u v : Fin 6 → ℂ) :
    vecIp (sympJ u) (sympJ v) = vecIp v u := by
  unfold vecIp
  have hl : (∑ r : Fin 6, star (sympJ u r) * sympJ v r) =
      ∑ p : Fin 3 × Fin 2,
        star (sympJ u (fin3ProdFin2Equiv6 p)) * sympJ v (fin3ProdFin2Equiv6 p) :=
    Fintype.sum_equiv fin3ProdFin2Equiv6.symm _
      (fun p => star (sympJ u (fin3ProdFin2Equiv6 p)) * sympJ v (fin3ProdFin2Equiv6 p))
      (fun r => by rw [fin3ProdFin2Equiv6.apply_symm_apply])
  have hr : (∑ r : Fin 6, star (v r) * u r) =
      ∑ p : Fin 3 × Fin 2,
        star (v (fin3ProdFin2Equiv6 p)) * u (fin3ProdFin2Equiv6 p) :=
    Fintype.sum_equiv fin3ProdFin2Equiv6.symm _
      (fun p => star (v (fin3ProdFin2Equiv6 p)) * u (fin3ProdFin2Equiv6 p))
      (fun r => by rw [fin3ProdFin2Equiv6.apply_symm_apply])
  have h10 : ((1 : Fin 2) = 0) ↔ False := by decide
  rw [hl, hr, Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.sum_univ_two, sympJ, fin3ProdFin2Equiv6.symm_apply_apply]
  simp only [Fin.isValue, ↓reduceIte, h10, star_neg, star_star]
  ring

private theorem vecIp_sympJ_skew (u v : Fin 6 → ℂ) :
    vecIp (sympJ u) v = -vecIp (sympJ v) u := by
  unfold vecIp
  have hl : (∑ r : Fin 6, star (sympJ u r) * v r) =
      ∑ p : Fin 3 × Fin 2,
        star (sympJ u (fin3ProdFin2Equiv6 p)) * v (fin3ProdFin2Equiv6 p) :=
    Fintype.sum_equiv fin3ProdFin2Equiv6.symm _
      (fun p => star (sympJ u (fin3ProdFin2Equiv6 p)) * v (fin3ProdFin2Equiv6 p))
      (fun r => by rw [fin3ProdFin2Equiv6.apply_symm_apply])
  have hr : (∑ r : Fin 6, star (sympJ v r) * u r) =
      ∑ p : Fin 3 × Fin 2,
        star (sympJ v (fin3ProdFin2Equiv6 p)) * u (fin3ProdFin2Equiv6 p) :=
    Fintype.sum_equiv fin3ProdFin2Equiv6.symm _
      (fun p => star (sympJ v (fin3ProdFin2Equiv6 p)) * u (fin3ProdFin2Equiv6 p))
      (fun r => by rw [fin3ProdFin2Equiv6.apply_symm_apply])
  have h10 : ((1 : Fin 2) = 0) ↔ False := by decide
  rw [hl, hr, Fintype.sum_prod_type, Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.sum_univ_two, sympJ, fin3ProdFin2Equiv6.symm_apply_apply]
  simp only [Fin.isValue, ↓reduceIte, h10, star_neg, star_star]
  ring

private theorem vecIp_sympJ_self (u : Fin 6 → ℂ) : vecIp (sympJ u) u = 0 := by
  have h := vecIp_sympJ_skew u u
  have h2 : (2 : ℂ) * vecIp (sympJ u) u = 0 := by linear_combination h
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

private theorem symplecticQuatMat6_mulVec_sympJ (M : QuatMatrix3) (v : Fin 6 → ℂ) :
    (symplecticQuatMat6 M).mulVec (sympJ v) = sympJ ((symplecticQuatMat6 M).mulVec v) := by
  funext r
  rcases hp : fin3ProdFin2Equiv6.symm r with ⟨i, j⟩
  have hsum : ∀ (f : Fin 6 → ℂ), (∑ c : Fin 6, f c) =
      ∑ q : Fin 3 × Fin 2, f (fin3ProdFin2Equiv6 q) := fun f =>
    Fintype.sum_equiv fin3ProdFin2Equiv6.symm f (fun q => f (fin3ProdFin2Equiv6 q))
      (fun c => by rw [fin3ProdFin2Equiv6.apply_symm_apply])
  have h10 : ((1 : Fin 2) = 0) ↔ False := by decide
  have h0 : ∀ h, ((⟨0, h⟩ : Fin 2) = 0) ↔ True := fun _ => iff_true_intro (Fin.ext rfl)
  have h1 : ∀ h, ((⟨1, h⟩ : Fin 2) = 0) ↔ False := fun _ =>
    iff_false_intro (Fin.ne_of_val_ne Nat.one_ne_zero)
  simp only [Matrix.mulVec, dotProduct, sympJ, hp, symplecticQuatMat6, Matrix.of_apply]
  fin_cases j
  · simp only [h0, ↓reduceIte]
    rw [hsum, hsum, Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [star_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Fin.sum_univ_two, fin3ProdFin2Equiv6.symm_apply_apply, Fin.isValue,
      ↓reduceIte, h10, star_mul']
    apply Complex.ext <;> simp [quatMat2] <;> ring
  · simp only [h1, ↓reduceIte]
    rw [hsum, hsum, Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [star_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Fin.sum_univ_two, fin3ProdFin2Equiv6.symm_apply_apply, Fin.isValue,
      ↓reduceIte, h10, star_mul']
    apply Complex.ext <;> simp [quatMat2] <;> ring

private theorem vecIp_herm_mulVec {d : ℕ} (X : HermitianEmbeddingMatrix d) (hX : X.IsHermitian)
    (u v : Fin d → ℂ) : vecIp (X.mulVec u) v = vecIp u (X.mulVec v) := by
  simp only [vecIp, Matrix.mulVec, dotProduct, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  have hij : star (X i j) = X j i := congrFun (congrFun hX.eq j) i
  rw [hij]
  ring

private theorem vecIp_neg_left {d : ℕ} (u v : Fin d → ℂ) : vecIp (-u) v = -vecIp u v := by
  simp only [vecIp, Pi.neg_apply, star_neg, neg_mul, Finset.sum_neg_distrib]

private theorem vecIp_add_left {d : ℕ} (u₁ u₂ v : Fin d → ℂ) :
    vecIp (u₁ + u₂) v = vecIp u₁ v + vecIp u₂ v := by
  simp only [vecIp, Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib]

private theorem vecIp_sub_left {d : ℕ} (u₁ u₂ v : Fin d → ℂ) :
    vecIp (u₁ - u₂) v = vecIp u₁ v - vecIp u₂ v := by
  simp only [vecIp, Pi.sub_apply, star_sub, sub_mul, Finset.sum_sub_distrib]

theorem quat_corner_finrank_le_six (Q : QuaternionicWindow) (q : Albert) (hq : IsAtom q)
    (hqQ : q ∈ Q.subalgebra.carrier) :
    Module.finrank ℝ (quatCornerSubmodule Q q) ≤ 6 := by
  let P : HermitianEmbeddingMatrix 6 := (symplecticQuatEmbed Q).map ⟨q, hqQ⟩
  have hP_herm : P.IsHermitian := (symplecticQuatEmbed Q).hermitian ⟨q, hqQ⟩
  have hP_id : P * P = P := by
    have hj := (symplecticQuatEmbed Q).jordan ⟨q, hqQ⟩ ⟨q, hqQ⟩
    have hqq : (⟨jordanMul q q, Q.subalgebra.product_mem _ hqQ _ hqQ⟩ : Q.subalgebra.carrier) =
        ⟨q, hqQ⟩ := Subtype.ext hq.1
    rw [hqq] at hj
    have h2 : (1 / 2 : ℝ) • (P * P + P * P) = P * P := by module
    change P = (1 / 2 : ℝ) • (P * P + P * P) at hj
    rw [h2] at hj
    exact hj.symm
  have hP_tr : Matrix.trace P = 2 := by
    have hre : (Matrix.trace P).re = 2 := by
      have h1 := symplecticQuatEmbed_tracePairing Q ⟨q, hqQ⟩ ⟨albertUnit, Q.subalgebra.unit_mem⟩
      rw [(symplecticQuatEmbed Q).unit, Matrix.mul_one, tracePairing_unit_right_local,
        hq.2, mul_one] at h1
      exact h1
    have him : (Matrix.trace P).im = 0 := by
      rw [Matrix.trace]
      have him_sum : ∀ s : Finset (Fin 6),
          (∑ k ∈ s, P.diag k).im = ∑ k ∈ s, (P k k).im := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp
        | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Complex.add_im, ih]; rfl
      rw [him_sum Finset.univ]
      refine Finset.sum_eq_zero fun k _ => ?_
      have hk := congrArg Complex.im (congrFun (congrFun hP_herm.eq k) k)
      simp [Matrix.conjTranspose_apply] at hk
      linarith
    exact Complex.ext hre him
  have hP_sympJ : ∀ v : Fin 6 → ℂ, P.mulVec (sympJ v) = sympJ (P.mulVec v) := fun v =>
    symplecticQuatMat6_mulVec_sympJ ((quatWindowEquiv Q ⟨q, hqQ⟩ : QuatHermitian3) : QuatMatrix3) v
  let Qp : HermitianEmbeddingMatrix 6 := 1 - P
  have hQp_herm : Qp.IsHermitian := Matrix.isHermitian_one.sub hP_herm
  have hQp_id : Qp * Qp = Qp := by
    dsimp only [Qp]
    calc
      (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hP_id]; abel
  have hQp_tr : Matrix.trace Qp = (4 : ℂ) := by
    dsimp only [Qp]
    rw [Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin, hP_tr]
    norm_num
  have hQp_sympJ : ∀ v : Fin 6 → ℂ, Qp.mulVec (sympJ v) = sympJ (Qp.mulVec v) := fun v => by
    dsimp only [Qp]
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec, hP_sympJ,
      sympJ_sub]
  obtain ⟨u, hu_norm, hu_orth, hu_sum⟩ :=
    hermitian_idempotent_spectral_rank (d := 6) (k := 4) Qp hQp_herm hQp_id hQp_tr
  have hQp_u : ∀ i : Fin 4, Qp.mulVec (u i) = u i := fun i => by
    funext a
    simp only [Matrix.mulVec, dotProduct, hu_sum]
    calc
      ∑ b : Fin 6, (∑ r : Fin 4, u r a * star (u r b)) * u i b
        = ∑ b : Fin 6, ∑ r : Fin 4, u r a * star (u r b) * u i b := by
          refine Finset.sum_congr rfl fun b _ => Finset.sum_mul _ _ _
      _ = ∑ r : Fin 4, ∑ b : Fin 6, u r a * star (u r b) * u i b := Finset.sum_comm
      _ = ∑ r : Fin 4, (∑ b : Fin 6, star (u r b) * u i b) * u r a := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun b _ => by ring
      _ = ∑ r : Fin 4, vecIp (u r) (u i) * u r a := rfl
      _ = u i a := by
          rw [Finset.sum_eq_single i]
          · rw [hu_norm i, one_mul]
          · intro r _ hri; rw [hu_orth r i hri, zero_mul]
          · intro hi; exact absurd (Finset.mem_univ i) hi
  let e₀ : Fin 6 → ℂ := u 0
  let e₁ : Fin 6 → ℂ := sympJ e₀
  have he₀_norm : vecIp e₀ e₀ = 1 := hu_norm 0
  have he₁_norm : vecIp e₁ e₁ = 1 := by rw [vecIp_sympJ_sympJ, he₀_norm]
  have he₁₀ : vecIp e₁ e₀ = 0 := vecIp_sympJ_self e₀
  have he₀₁ : vecIp e₀ e₁ = 0 := by rw [← vecIp_conj, he₁₀, star_zero]
  have hQp_e₀ : Qp.mulVec e₀ = e₀ := hQp_u 0
  have hQp_e₁ : Qp.mulVec e₁ = e₁ := by dsimp only [e₁]; rw [hQp_sympJ, hQp_e₀]
  let proj : Fin 4 → (Fin 6 → ℂ) := fun i => u i - vecIp e₀ (u i) • e₀ - vecIp e₁ (u i) • e₁
  have hproj_e₀ : ∀ i : Fin 4, vecIp e₀ (proj i) = 0 := fun i => by
    dsimp only [proj]
    rw [vecIp_sub_right, vecIp_sub_right, vecIp_smul_right, vecIp_smul_right,
      he₀_norm, he₀₁, mul_one, mul_zero, sub_zero, sub_self]
  have hproj_e₁ : ∀ i : Fin 4, vecIp e₁ (proj i) = 0 := fun i => by
    dsimp only [proj]
    rw [vecIp_sub_right, vecIp_sub_right, vecIp_smul_right, vecIp_smul_right,
      he₁₀, he₁_norm, mul_zero, mul_one, sub_zero, sub_self]
  have hproj_norm : ∀ i : Fin 4, vecIp (proj i) (proj i) =
      1 - star (vecIp e₀ (u i)) * vecIp e₀ (u i) - star (vecIp e₁ (u i)) * vecIp e₁ (u i) := fun i => by
    have h1 : vecIp (proj i) (proj i) = vecIp (u i) (proj i) := by
      nth_rw 1 [show proj i = u i - vecIp e₀ (u i) • e₀ - vecIp e₁ (u i) • e₁ from rfl]
      rw [vecIp_sub_left, vecIp_sub_left, vecIp_smul_left, vecIp_smul_left,
        hproj_e₀ i, hproj_e₁ i, mul_zero, mul_zero, sub_zero, sub_zero]
    rw [h1]
    dsimp only [proj]
    rw [vecIp_sub_right, vecIp_sub_right, vecIp_smul_right, vecIp_smul_right, hu_norm i,
      ← vecIp_conj e₀ (u i), ← vecIp_conj e₁ (u i)]
    ring
  have hsum_e : ∀ w : Fin 6 → ℂ, Qp.mulVec w = w → vecIp w w = 1 →
      (∑ i : Fin 4, star (vecIp w (u i)) * vecIp w (u i)) = 1 := fun w hQw hww => by
    have hQmul : ∀ a, Qp.mulVec w a = ∑ i : Fin 4, vecIp (u i) w * u i a := fun a => by
      simp only [Matrix.mulVec, dotProduct, hu_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [vecIp, Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => by ring
    have hip : vecIp w (Qp.mulVec w) = ∑ i : Fin 4, star (vecIp w (u i)) * vecIp w (u i) := by
      rw [vecIp]
      simp only [hQmul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hs : (∑ a : Fin 6, star (w a) * (vecIp (u i) w * u i a)) =
          vecIp (u i) w * ∑ a : Fin 6, star (w a) * u i a := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => by ring
      rw [hs]
      change vecIp (u i) w * vecIp w (u i) = star (vecIp w (u i)) * vecIp w (u i)
      rw [← vecIp_conj w (u i)]
    rw [hQw, hww] at hip
    exact hip.symm
  have hsum_proj : (∑ i : Fin 4, (vecIp (proj i) (proj i)).re) = 2 := by
    have hcsum : (∑ i : Fin 4, vecIp (proj i) (proj i)) = (2 : ℂ) := by
      simp only [hproj_norm, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one,
        hsum_e e₀ hQp_e₀ he₀_norm, hsum_e e₁ hQp_e₁ he₁_norm]
      norm_num
    rw [← Complex.re_sum, hcsum]
    norm_num
  have hex_pos : ∃ i₀ : Fin 4, 0 < (vecIp (proj i₀) (proj i₀)).re := by
    by_contra hnone
    push Not at hnone
    have hle : (∑ i : Fin 4, (vecIp (proj i) (proj i)).re) ≤ 0 :=
      Finset.sum_nonpos fun i _ => hnone i
    linarith
  obtain ⟨i₀, hi₀_pos⟩ := hex_pos
  let w := proj i₀
  let nw : ℝ := Real.sqrt (vecIp w w).re
  have hnw_pos : 0 < nw := Real.sqrt_pos.mpr hi₀_pos
  let e₂ : Fin 6 → ℂ := ((nw⁻¹ : ℝ) : ℂ) • w
  let e₃ : Fin 6 → ℂ := sympJ e₂
  have he₂_norm : vecIp e₂ e₂ = 1 := by
    dsimp only [e₂]
    rw [vecIp_smul_left, vecIp_smul_right, Complex.star_def, Complex.conj_ofReal]
    have him : (vecIp w w).im = 0 := by
      have hs := vecIp_conj w w
      have him' := congrArg Complex.im hs
      simp only [Complex.star_def, Complex.conj_im] at him'
      linarith
    have hw_eq : vecIp w w = ((vecIp w w).re : ℂ) := Complex.ext rfl him
    rw [hw_eq]
    have hsq : nw * nw = (vecIp w w).re := Real.mul_self_sqrt hi₀_pos.le
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    field_simp [hnw_pos.ne']
    linarith [hsq]
  have he₃_norm : vecIp e₃ e₃ = 1 := by rw [vecIp_sympJ_sympJ, he₂_norm]
  have he₀₂ : vecIp e₀ e₂ = 0 := by
    dsimp only [e₂]; rw [vecIp_smul_right, hproj_e₀ i₀, mul_zero]
  have he₁₂ : vecIp e₁ e₂ = 0 := by
    dsimp only [e₂]; rw [vecIp_smul_right, hproj_e₁ i₀, mul_zero]
  have he₂₀ : vecIp e₂ e₀ = 0 := by rw [← vecIp_conj, he₀₂, star_zero]
  have he₂₁ : vecIp e₂ e₁ = 0 := by rw [← vecIp_conj, he₁₂, star_zero]
  have he₁₃ : vecIp e₁ e₃ = 0 := by
    dsimp only [e₁, e₃]; rw [vecIp_sympJ_sympJ, he₂₀]
  have he₀₃ : vecIp e₀ e₃ = 0 := by
    have he0' : e₀ = -sympJ e₁ := by dsimp only [e₁]; rw [sympJ_sympJ, neg_neg]
    rw [he0', vecIp_neg_left]; dsimp only [e₃]; rw [vecIp_sympJ_sympJ, he₂₁, neg_zero]
  have he₃₂ : vecIp e₃ e₂ = 0 := vecIp_sympJ_self e₂
  have he₂₃ : vecIp e₂ e₃ = 0 := by rw [← vecIp_conj, he₃₂, star_zero]
  let eb : Fin 4 → (Fin 6 → ℂ) := ![e₀, e₁, e₂, e₃]
  have heb_orth : ∀ j k : Fin 4, vecIp (eb j) (eb k) = if j = k then 1 else 0 := fun j k => by
    fin_cases j <;> fin_cases k <;> simp [eb, he₀_norm, he₀₁, he₀₂, he₀₃, he₁₀, he₁_norm, he₁₂, he₁₃,
      he₂₀, he₂₁, he₂_norm, he₂₃, he₃₂, he₃_norm,
      show vecIp e₃ e₀ = 0 from by rw [← vecIp_conj, he₀₃, star_zero],
      show vecIp e₃ e₁ = 0 from by rw [← vecIp_conj, he₁₃, star_zero]]
  have hQp_e₂ : Qp.mulVec e₂ = e₂ := by
    have hQw : Qp.mulVec w = w := by
      dsimp only [w, proj]
      rw [Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
        hQp_u i₀, hQp_e₀, hQp_e₁]
    dsimp only [e₂]
    rw [Matrix.mulVec_smul, hQw]
  have hQp_e₃ : Qp.mulVec e₃ = e₃ := by
    dsimp only [e₃]; rw [hQp_sympJ, hQp_e₂]
  have hQp_eb : ∀ k : Fin 4, Qp.mulVec (eb k) = eb k := fun k => by
    fin_cases k <;> simp [eb, hQp_e₀, hQp_e₁, hQp_e₂, hQp_e₃]
  let E : HermitianEmbeddingMatrix 6 := Matrix.of fun a b => ∑ k : Fin 4, eb k a * star (eb k b)
  have hE_herm : E.IsHermitian := by
    rw [Matrix.IsHermitian]; ext a b
    simp only [Matrix.conjTranspose_apply, E, Matrix.of_apply, star_sum, star_mul', star_star]
    refine Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hE_mul : E * E = E := by
    ext a b
    simp only [Matrix.mul_apply, E, Matrix.of_apply]
    calc
      ∑ c : Fin 6, (∑ k : Fin 4, eb k a * star (eb k c)) * (∑ l : Fin 4, eb l c * star (eb l b))
        = ∑ c : Fin 6, ∑ k : Fin 4, ∑ l : Fin 4, eb k a * star (eb k c) * (eb l c * star (eb l b)) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => Finset.mul_sum _ _ _
      _ = ∑ k : Fin 4, ∑ c : Fin 6, ∑ l : Fin 4, eb k a * star (eb k c) * (eb l c * star (eb l b)) :=
          Finset.sum_comm
      _ = ∑ k : Fin 4, ∑ l : Fin 4, (∑ c : Fin 6, star (eb k c) * eb l c) *
            (eb k a * star (eb l b)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun c _ => by ring
      _ = ∑ k : Fin 4, ∑ l : Fin 4, vecIp (eb k) (eb l) * (eb k a * star (eb l b)) := rfl
      _ = ∑ k : Fin 4, eb k a * star (eb k b) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_eq_single k]
          · simp [heb_orth k k]
          · intro l _ hlk; rw [heb_orth k l]; simp [Ne.symm hlk]
          · intro hk; exact absurd (Finset.mem_univ k) hk
  have hQpE : Qp * E = E := by
    ext a b
    simp only [Matrix.mul_apply, E, Matrix.of_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk : Qp.mulVec (eb k) a = eb k a := congrFun (hQp_eb k) a
    calc
      ∑ c : Fin 6, Qp a c * (eb k c * star (eb k b))
        = (∑ c : Fin 6, Qp a c * eb k c) * star (eb k b) := by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun c _ => by ring
      _ = Qp.mulVec (eb k) a * star (eb k b) := rfl
      _ = eb k a * star (eb k b) := by rw [hk]
  have hEQp : E * Qp = E := by
    have h := congrArg Matrix.conjTranspose hQpE
    rw [Matrix.conjTranspose_mul, hE_herm.eq, hQp_herm.eq] at h
    exact h
  have hQp_eq_E : Qp = E := by
    let D := Qp - E
    have hD_herm : D.IsHermitian := hQp_herm.sub hE_herm
    have hD_id : D * D = D := by
      dsimp only [D]
      calc
        (Qp - E) * (Qp - E) = Qp * Qp - Qp * E - E * Qp + E * E := by noncomm_ring
        _ = Qp - E := by rw [hQp_id, hQpE, hEQp, hE_mul]; abel
    have hE_tr : Matrix.trace E = (4 : ℂ) := by
      rw [Matrix.trace]
      simp only [Matrix.diag, E, Matrix.of_apply]
      rw [Finset.sum_comm]
      have h1 : ∀ k : Fin 4, (∑ a : Fin 6, eb k a * star (eb k a)) = 1 := fun k => by
        have hkk := heb_orth k k
        simp only [↓reduceIte] at hkk
        rw [← hkk]
        refine Finset.sum_congr rfl fun a _ => mul_comm _ _
      simp only [h1, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one]
      norm_num
    have hD_tr : Matrix.trace D = 0 := by
      dsimp only [D]; rw [Matrix.trace_sub, hQp_tr, hE_tr, sub_self]
    have hD_sq_tr : (Matrix.trace (D.conjTranspose * D)).re = 0 := by
      rw [hD_herm.eq, hD_id, hD_tr, Complex.zero_re]
    have hD_norm : (Matrix.trace (D.conjTranspose * D)).re =
        ∑ a : Fin 6, ∑ b : Fin 6, ((D a b).re ^ 2 + (D a b).im ^ 2) := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Complex.re_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      simp [sq]
    rw [hD_norm] at hD_sq_tr
    have hall : ∀ a b : Fin 6, (D a b).re ^ 2 + (D a b).im ^ 2 = 0 := fun a b => by
      have ha : (∑ d : Fin 6, ((D a d).re ^ 2 + (D a d).im ^ 2)) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => Finset.sum_nonneg fun d _ =>
          add_nonneg (sq_nonneg _) (sq_nonneg _))).mp hD_sq_tr a (Finset.mem_univ a)
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun d _ =>
        add_nonneg (sq_nonneg _) (sq_nonneg _))).mp ha b (Finset.mem_univ b)
    ext a b
    have hab := hall a b
    have hre : (D a b).re = 0 := sq_eq_zero_iff.mp (by linarith [sq_nonneg (D a b).re, sq_nonneg (D a b).im])
    have him : (D a b).im = 0 := sq_eq_zero_iff.mp (by linarith [sq_nonneg (D a b).re, sq_nonneg (D a b).im])
    exact sub_eq_zero.mp (Complex.ext hre him)
  let Φ : quatCornerSubmodule Q q →ₗ[ℝ] (Fin 6 → ℝ) :=
    { toFun := fun x =>
        let X := (symplecticQuatEmbed Q).map ⟨x.1, x.2.1⟩
        ![(vecIp e₀ (X.mulVec e₀)).re,
          (vecIp e₂ (X.mulVec e₂)).re,
          (vecIp e₀ (X.mulVec e₂)).re,
          (vecIp e₀ (X.mulVec e₂)).im,
          (vecIp e₁ (X.mulVec e₂)).re,
          (vecIp e₁ (X.mulVec e₂)).im]
      map_add' := fun x y => by
        funext idx
        have hadd : (symplecticQuatEmbed Q).map ⟨(x + y).1, (x + y).2.1⟩ =
            (symplecticQuatEmbed Q).map ⟨x.1, x.2.1⟩ +
              (symplecticQuatEmbed Q).map ⟨y.1, y.2.1⟩ := by
          rw [← (symplecticQuatEmbed Q).map.map_add]; rfl
        dsimp only
        rw [hadd]
        simp only [Matrix.add_mulVec, vecIp_add_right, Complex.add_re, Complex.add_im]
        fin_cases idx <;> rfl
      map_smul' := fun r x => by
        funext idx
        have hsmul : (symplecticQuatEmbed Q).map ⟨(r • x).1, (r • x).2.1⟩ =
            r • (symplecticQuatEmbed Q).map ⟨x.1, x.2.1⟩ := by
          rw [← (symplecticQuatEmbed Q).map.map_smul]; rfl
        have hsmul_v : ∀ v : Fin 6 → ℂ, (r • v) = (r : ℂ) • v := fun v =>
          funext fun i => by rw [Pi.smul_apply, Pi.smul_apply, Complex.real_smul, smul_eq_mul]
        dsimp only
        rw [hsmul]
        simp only [Matrix.smul_mulVec, hsmul_v, vecIp_smul_right, Complex.mul_re, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero, RingHom.id_apply]
        fin_cases idx <;> rfl }
  have hΦ_inj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro x hΦx
    let X : HermitianEmbeddingMatrix 6 := (symplecticQuatEmbed Q).map ⟨x.1, x.2.1⟩
    have hX_herm : X.IsHermitian := (symplecticQuatEmbed Q).hermitian ⟨x.1, x.2.1⟩
    have hX_sympJ : ∀ v : Fin 6 → ℂ, X.mulVec (sympJ v) = sympJ (X.mulVec v) := fun v =>
      symplecticQuatMat6_mulVec_sympJ ((quatWindowEquiv Q ⟨x.1, x.2.1⟩ : QuatHermitian3) : QuatMatrix3) v
    have hPX_add : P * X + X * P = 0 := by
      have hj := (symplecticQuatEmbed Q).jordan ⟨q, hqQ⟩ ⟨x.1, x.2.1⟩
      have h0 : (⟨jordanMul q x.1, Q.subalgebra.product_mem _ hqQ _ x.2.1⟩ : Q.subalgebra.carrier) = 0 :=
        Subtype.ext x.2.2
      rw [h0, map_zero] at hj
      have h2 := congrArg (fun M : HermitianEmbeddingMatrix 6 => (2 : ℝ) • M) hj.symm
      rw [smul_smul, show (2 : ℝ) * (1 / 2 : ℝ) = 1 by norm_num, one_smul, smul_zero] at h2
      exact h2
    have hPX : P * X = 0 := by
      have h1 : P * (P * X + X * P) = 0 := by rw [hPX_add, mul_zero]
      have h2 : (P * X + X * P) * P = 0 := by rw [hPX_add, zero_mul]
      rw [mul_add, ← Matrix.mul_assoc P P X, hP_id, ← Matrix.mul_assoc P X P] at h1
      rw [add_mul, Matrix.mul_assoc X P P, hP_id] at h2
      have heq : P * X = X * P := by
        calc
          P * X = -(P * X * P) := eq_neg_of_add_eq_zero_left h1
          _ = X * P := (eq_neg_of_add_eq_zero_right h2).symm
      rw [← heq] at hPX_add
      have h2PX : (2 : ℂ) • (P * X) = 0 := by
        rw [two_smul]; exact hPX_add
      exact (smul_eq_zero.mp h2PX).resolve_left (by norm_num)
    have hXP : X * P = 0 := by
      rw [hPX, zero_add] at hPX_add; exact hPX_add
    have hX_E : E * X * E = X := by
      rw [← hQp_eq_E]
      dsimp only [Qp]
      calc
        (1 - P) * X * (1 - P) = X - P * X - X * P + P * X * P := by noncomm_ring
        _ = X := by rw [hPX, hXP, zero_mul, sub_zero, sub_zero, add_zero]
    have h00_re : (vecIp e₀ (X.mulVec e₀)).re = 0 := congrFun hΦx 0
    have h22_re : (vecIp e₂ (X.mulVec e₂)).re = 0 := congrFun hΦx 1
    have h02_re : (vecIp e₀ (X.mulVec e₂)).re = 0 := congrFun hΦx 2
    have h02_im : (vecIp e₀ (X.mulVec e₂)).im = 0 := congrFun hΦx 3
    have h12_re : (vecIp e₁ (X.mulVec e₂)).re = 0 := congrFun hΦx 4
    have h12_im : (vecIp e₁ (X.mulVec e₂)).im = 0 := congrFun hΦx 5
    have him_diag : ∀ v : Fin 6 → ℂ, (vecIp v (X.mulVec v)).im = 0 := fun v => by
      have hs : star (vecIp v (X.mulVec v)) = vecIp v (X.mulVec v) := by
        rw [vecIp_conj, vecIp_herm_mulVec X hX_herm]
      have him := congrArg Complex.im hs
      simp only [Complex.star_def, Complex.conj_im] at him
      linarith
    have h00 : vecIp e₀ (X.mulVec e₀) = 0 := Complex.ext h00_re (him_diag e₀)
    have h22 : vecIp e₂ (X.mulVec e₂) = 0 := Complex.ext h22_re (him_diag e₂)
    have h02 : vecIp e₀ (X.mulVec e₂) = 0 := Complex.ext h02_re h02_im
    have h12 : vecIp e₁ (X.mulVec e₂) = 0 := Complex.ext h12_re h12_im
    have h11 : vecIp e₁ (X.mulVec e₁) = 0 := by
      dsimp only [e₁]
      rw [hX_sympJ, vecIp_sympJ_sympJ, vecIp_herm_mulVec X hX_herm, h00]
    have h33 : vecIp e₃ (X.mulVec e₃) = 0 := by
      dsimp only [e₃]
      rw [hX_sympJ, vecIp_sympJ_sympJ, vecIp_herm_mulVec X hX_herm, h22]
    have h10 : vecIp e₁ (X.mulVec e₀) = 0 := by
      have hskew : vecIp (sympJ e₀) (X.mulVec e₀) = -vecIp (sympJ (X.mulVec e₀)) e₀ :=
        vecIp_sympJ_skew e₀ (X.mulVec e₀)
      rw [← hX_sympJ, vecIp_herm_mulVec X hX_herm] at hskew
      have h2 : (2 : ℂ) * vecIp e₁ (X.mulVec e₀) = 0 := by
        change (2 : ℂ) * vecIp (sympJ e₀) (X.mulVec e₀) = 0
        linear_combination hskew
      exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
    have h32 : vecIp e₃ (X.mulVec e₂) = 0 := by
      have hskew : vecIp (sympJ e₂) (X.mulVec e₂) = -vecIp (sympJ (X.mulVec e₂)) e₂ :=
        vecIp_sympJ_skew e₂ (X.mulVec e₂)
      rw [← hX_sympJ, vecIp_herm_mulVec X hX_herm] at hskew
      have h2 : (2 : ℂ) * vecIp e₃ (X.mulVec e₂) = 0 := by
        change (2 : ℂ) * vecIp (sympJ e₂) (X.mulVec e₂) = 0
        linear_combination hskew
      exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
    have h01 : vecIp e₀ (X.mulVec e₁) = 0 := by
      rw [← vecIp_conj, vecIp_herm_mulVec X hX_herm, h10, star_zero]
    have h23 : vecIp e₂ (X.mulVec e₃) = 0 := by
      rw [← vecIp_conj, vecIp_herm_mulVec X hX_herm, h32, star_zero]
    have h13 : vecIp e₁ (X.mulVec e₃) = 0 := by
      dsimp only [e₁, e₃]
      rw [hX_sympJ, vecIp_sympJ_sympJ, ← vecIp_conj, h02, star_zero]
    have h03 : vecIp e₀ (X.mulVec e₃) = 0 := by
      have he0' : e₀ = -sympJ e₁ := by dsimp only [e₁]; rw [sympJ_sympJ, neg_neg]
      rw [he0', vecIp_neg_left]; dsimp only [e₃]
      rw [hX_sympJ, vecIp_sympJ_sympJ, ← vecIp_conj, h12, star_zero, neg_zero]
    have h20 : vecIp e₂ (X.mulVec e₀) = 0 := by
      rw [← vecIp_conj, vecIp_herm_mulVec X hX_herm, h02, star_zero]
    have h21 : vecIp e₂ (X.mulVec e₁) = 0 := by
      rw [← vecIp_conj, vecIp_herm_mulVec X hX_herm, h12, star_zero]
    have h30 : vecIp e₃ (X.mulVec e₀) = 0 := by
      rw [← vecIp_conj, vecIp_herm_mulVec X hX_herm, h03, star_zero]
    have h31 : vecIp e₃ (X.mulVec e₁) = 0 := by
      rw [← vecIp_conj, vecIp_herm_mulVec X hX_herm, h13, star_zero]
    have hall_jk : ∀ j k : Fin 4, vecIp (eb j) (X.mulVec (eb k)) = 0 := fun j k => by
      fin_cases j <;> fin_cases k <;>
        simp [eb, h00, h01, h02, h03, h10, h11, h12, h13, h20, h21, h22, h23, h30, h31, h32, h33]
    have hX0 : X = 0 := by
      rw [← hX_E, Matrix.mul_assoc]
      have hXE : ∀ c b, (X * E) c b = ∑ k : Fin 4, X.mulVec (eb k) c * star (eb k b) := fun c b => by
        simp only [Matrix.mul_apply, E, Matrix.of_apply, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [Matrix.mulVec, dotProduct, Finset.sum_mul]
        refine Finset.sum_congr rfl fun d' _ => by ring
      ext a b
      simp only [Matrix.mul_apply, hXE, E, Matrix.of_apply, Matrix.zero_apply]
      calc
        ∑ c : Fin 6, (∑ j : Fin 4, eb j a * star (eb j c)) *
            (∑ k : Fin 4, X.mulVec (eb k) c * star (eb k b))
          = ∑ c : Fin 6, ∑ j : Fin 4, ∑ k : Fin 4,
              eb j a * star (eb j c) * (X.mulVec (eb k) c * star (eb k b)) := by
            refine Finset.sum_congr rfl fun c _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ => Finset.mul_sum _ _ _
        _ = ∑ j : Fin 4, ∑ c : Fin 6, ∑ k : Fin 4,
              eb j a * star (eb j c) * (X.mulVec (eb k) c * star (eb k b)) := Finset.sum_comm
        _ = 0 := by
            refine Finset.sum_eq_zero fun j _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_eq_zero fun k _ => ?_
            have hsum_c : (∑ c : Fin 6, eb j a * star (eb j c) * (X.mulVec (eb k) c * star (eb k b))) =
                (eb j a * star (eb k b)) * vecIp (eb j) (X.mulVec (eb k)) := by
              simp only [vecIp, Finset.mul_sum]
              refine Finset.sum_congr rfl fun c _ => by ring
            rw [hsum_c, hall_jk j k, mul_zero]
    have hmap0 : (symplecticQuatEmbed Q).map ⟨x.1, x.2.1⟩ = (symplecticQuatEmbed Q).map 0 := by
      rw [map_zero]
      exact hX0
    exact Subtype.ext (congrArg (Subtype.val : Q.subalgebra.carrier → Albert)
      ((symplecticQuatEmbed Q).injective hmap0))
  rw [(LinearEquiv.ofInjective Φ hΦ_inj).finrank_eq]
  exact (Submodule.finrank_le (LinearMap.range Φ)).trans_eq (Module.finrank_fin_fun ℝ)

def spinAtom (u : Octonion) : Albert :=
  mkAlbert ![0, 1 / 2, 1 / 2] ![0, 0, (1 / 2 : ℝ) • u]

private theorem spinAtom_isAtom {u : Octonion} (hu : octNormSq u = 1) : IsAtom (spinAtom u) := by
  constructor
  · apply albert_ext
    · rw [jordanMul_diag_0]; simp [spinAtom, octDot_zero_left]
    · rw [jordanMul_diag_1]
      simp [spinAtom, octDot_self, octNormSq_smul, hu, octNormSq_zero]
      norm_num
    · rw [jordanMul_diag_2]
      simp [spinAtom, octDot_self, octNormSq_smul, hu, octNormSq_zero]
      norm_num
    · rw [jordanMul_off_0]; simp [spinAtom, octonionMul_zero_left]
    · rw [jordanMul_off_1]; simp [spinAtom, octonionMul_zero_left]
    · rw [jordanMul_off_2]
      simp [spinAtom, octonionMul_zero_right, octonionConj_zero]
      module
  · simp [albertTrace, spinAtom, Fin.sum_univ_three]
    norm_num

private noncomputable def hellyRotS2 : ℝ := 1 / Real.sqrt 2

private theorem hellyRotS2_sq_add : hellyRotS2 ^ 2 + hellyRotS2 ^ 2 = 1 := by
  dsimp only [hellyRotS2]
  rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)]
  norm_num

private noncomputable def hellyRot45 : NativeAlbertAutomorphism :=
  realRotation12AlbertAuto hellyRotS2 hellyRotS2 hellyRotS2_sq_add

private theorem hellyRot45_corner (a b : ℝ) (z : Octonion) :
    hellyRot45.linearEquiv (mkAlbert ![0, a, b] ![0, 0, z]) =
      mkAlbert ![0, (a + b) / 2 + octonionReal z, (a + b) / 2 - octonionReal z]
        ![0, 0, ((b - a) / 2) • octOne + (1 / 2 : ℝ) • (z - octonionConj z)] := by
  let x := mkAlbert ![0, a, b] ![0, 0, z]
  change realConjAlbert (realRotation12 hellyRotS2 hellyRotS2) x = _
  have hM : ∀ k l : Fin 3, albertMatrix x k l =
      match k, l with
      | 1, 1 => octonionScalar a
      | 1, 2 => z
      | 2, 1 => octonionConj z
      | 2, 2 => octonionScalar b
      | _, _ => 0 := fun k l => by
    fin_cases k <;> fin_cases l <;>
      simp [x, albertMatrix, octonionScalar_zero, octonionConj_zero]
  have hsq : hellyRotS2 ^ 2 = 1 / 2 := by
    dsimp only [hellyRotS2]; rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)]
  have hmul : hellyRotS2 * hellyRotS2 = 1 / 2 := by rw [← sq, hsq]
  have hent : ∀ i j : Fin 3,
      realConjMatrix (realRotation12 hellyRotS2 hellyRotS2) (albertMatrix x) i j =
        match i, j with
        | 1, 1 => (1 / 2 : ℝ) • octonionScalar a + (1 / 2 : ℝ) • z +
                    (1 / 2 : ℝ) • octonionConj z + (1 / 2 : ℝ) • octonionScalar b
        | 2, 2 => (1 / 2 : ℝ) • octonionScalar a - (1 / 2 : ℝ) • z -
                    (1 / 2 : ℝ) • octonionConj z + (1 / 2 : ℝ) • octonionScalar b
        | 1, 2 => (-1 / 2 : ℝ) • octonionScalar a + (1 / 2 : ℝ) • z -
                    (1 / 2 : ℝ) • octonionConj z + (1 / 2 : ℝ) • octonionScalar b
        | 2, 1 => (-1 / 2 : ℝ) • octonionScalar a - (1 / 2 : ℝ) • z +
                    (1 / 2 : ℝ) • octonionConj z + (1 / 2 : ℝ) • octonionScalar b
        | _, _ => 0 := fun i j => by
    rw [realConjMatrix, Fin.sum_univ_three]
    simp only [Fin.sum_univ_three, hM]
    fin_cases i <;> fin_cases j <;>
      simp [realRotation12, hmul, neg_smul] <;> module
  have hconj_re : octonionReal (octonionConj z) = octonionReal z := by
    rw [octConj_eq_two_real_sub, octonionReal_sub, octonionReal_smul, octOne, octonionReal_scalar]
    ring
  have hsc : ∀ r : ℝ, octonionScalar r = r • octOne := fun r => by
    apply oct_ext
    · change r = (r • octOne.1).re; simp [octOne, octonionScalar]
    · change 0 = (r • octOne.1).imI; simp [octOne, octonionScalar]
    · change 0 = (r • octOne.1).imJ; simp [octOne, octonionScalar]
    · change 0 = (r • octOne.1).imK; simp [octOne, octonionScalar]
    · change 0 = (r • octOne.2).re; simp [octOne, octonionScalar]
    · change 0 = (r • octOne.2).imI; simp [octOne, octonionScalar]
    · change 0 = (r • octOne.2).imJ; simp [octOne, octonionScalar]
    · change 0 = (r • octOne.2).imK; simp [octOne, octonionScalar]
  unfold realConjAlbert
  apply albert_ext
  · simp [albertCoordinates, hent, octonionReal_zero]
  · simp [albertCoordinates, hent, octonionReal_add, octonionReal_smul, octonionReal_scalar, hconj_re]
    ring
  · simp [albertCoordinates, hent, octonionReal_add, octonionReal_sub, octonionReal_smul,
      octonionReal_scalar, hconj_re]
    ring
  · simp [albertCoordinates, hent]
  · simp [albertCoordinates, hent]
  · simp [albertCoordinates, hent, hsc]
    module

private theorem hellyRot45_diagAtom1 :
    hellyRot45.linearEquiv (diagAtom 1) = spinAtom (-octOne) := by
  have h1 : diagAtom 1 = mkAlbert ![0, 1, 0] ![0, 0, 0] := by
    apply albert_ext <;> simp [diagAtom_fst, diagAtom_snd]
  rw [h1, hellyRot45_corner]
  apply albert_ext <;>
    simp [spinAtom, octonionReal_zero, octonionConj_zero, sub_self, smul_zero, add_zero, smul_neg]
  norm_num

private theorem hellyRot45_spinAtom_one :
    hellyRot45.linearEquiv (spinAtom octOne) = diagAtom 1 := by
  dsimp only [spinAtom]
  rw [hellyRot45_corner]
  have hcz : ∀ r : ℝ, octonionConj (r • octOne) = r • octOne := fun r => by
    rw [octonionConj_smul, octonionConj_one]
  have hrz : ∀ r : ℝ, octonionReal (r • octOne) = r := fun r => by
    rw [octonionReal_smul, octOne, octonionReal_scalar, mul_one]
  apply albert_ext
  · simp [diagAtom_fst]
  · simp [diagAtom_fst, hrz]; norm_num
  · simp [diagAtom_fst, hrz]
  · simp [diagAtom_snd]
  · simp [diagAtom_snd]
  · simp [diagAtom_snd, hcz]

private theorem hellyRot45_spinAtom_im {w : Octonion} (hw : octonionReal w = 0) :
    hellyRot45.linearEquiv (spinAtom w) = spinAtom w := by
  dsimp only [spinAtom]
  rw [hellyRot45_corner]
  have hcw : octonionConj w = -w := octonionConj_eq_neg_of_real_zero hw
  (apply albert_ext <;> simp [octonionReal_smul, hw, octonionConj_smul, hcw])
  module

private noncomputable def swapSpinAuto (u : Octonion) (hu : octNormSq u = 1) :
    NativeAlbertAutomorphism :=
  have hcu : octNormSq (octonionConj u) = 1 := by simpa only [octNormSq_conj] using hu
  (middleMoufangAlbertAuto u hu).comp
    (hellyRot45.comp (middleMoufangAlbertAuto (octonionConj u) hcu))

private theorem middleMoufangAlbertAuto_spinAtom {u w : Octonion} (hu : octNormSq u = 1) :
    (middleMoufangAlbertAuto u hu).linearEquiv (spinAtom w) = spinAtom (octonionMul w u) := by
  rw [middleMoufangAlbertAuto_apply]
  apply albert_ext <;>
    simp [spinAtom, octonionMul_zero_right, octonionMul_zero_left, octonionMul_smul_left]

private theorem swapSpinAuto_diagAtom1 {u : Octonion} (hu : octNormSq u = 1) :
    (swapSpinAuto u hu).linearEquiv (diagAtom 1) = spinAtom (-u) := by
  have hcu : octNormSq (octonionConj u) = 1 := by simpa only [octNormSq_conj] using hu
  change (middleMoufangAlbertAuto u hu).linearEquiv
    (hellyRot45.linearEquiv ((middleMoufangAlbertAuto (octonionConj u) hcu).linearEquiv (diagAtom 1))) = _
  rw [middleMoufangAlbertAuto_diagAtom, hellyRot45_diagAtom1, middleMoufangAlbertAuto_spinAtom,
    octonionMul_neg_left, octonionMul_one_left]

private theorem swapSpinAuto_spinAtom_self {u : Octonion} (hu : octNormSq u = 1) :
    (swapSpinAuto u hu).linearEquiv (spinAtom u) = diagAtom 1 := by
  have hcu : octNormSq (octonionConj u) = 1 := by simpa only [octNormSq_conj] using hu
  change (middleMoufangAlbertAuto u hu).linearEquiv
    (hellyRot45.linearEquiv ((middleMoufangAlbertAuto (octonionConj u) hcu).linearEquiv (spinAtom u))) = _
  rw [middleMoufangAlbertAuto_spinAtom, octMul_self_conj, hu]
  change (middleMoufangAlbertAuto u hu).linearEquiv (hellyRot45.linearEquiv (spinAtom octOne)) = _
  rw [hellyRot45_spinAtom_one, middleMoufangAlbertAuto_diagAtom]

private theorem swapSpinAuto_spinAtom_ortho {u v : Octonion} (hu : octNormSq u = 1)
    (huv : octDot v u = 0) :
    (swapSpinAuto u hu).linearEquiv (spinAtom v) = spinAtom v := by
  have hcu : octNormSq (octonionConj u) = 1 := by simpa only [octNormSq_conj] using hu
  change (middleMoufangAlbertAuto u hu).linearEquiv
    (hellyRot45.linearEquiv ((middleMoufangAlbertAuto (octonionConj u) hcu).linearEquiv (spinAtom v))) = _
  rw [middleMoufangAlbertAuto_spinAtom]
  have hreal0 : octonionReal (octonionMul v (octonionConj u)) = 0 := by
    have hre : octonionReal (octonionMul v (octonionConj u)) =
        octDot (octonionMul v (octonionConj u)) octOne := by
      rw [octDot_comm, show octOne = octonionScalar 1 from rfl, octDot_scalar_left, one_mul]
    rw [hre, octDot_mul_right v (octonionConj u) octOne, octonionMul_one_left,
      octonionConj_conj, huv]
  rw [hellyRot45_spinAtom_im hreal0, middleMoufangAlbertAuto_spinAtom,
    octMul_right_conj_cancel, hu, one_smul]

def lineHellyCounterexample6 : Fin 6 → Albert
  | 0 => diagAtom 1
  | 1 => spinAtom octOne
  | 2 => spinAtom octI
  | 3 => spinAtom octJ
  | 4 => spinAtom octK
  | 5 => spinAtom octL

private theorem spinAtom_mem_line0 (u : Octonion) :
    spinAtom u ∈ (lineSubalgebra (diagAtom 0) (diagAtom_isAtom 0)).carrier := by
  rw [mem_lineSubalgebra_iff]
  have htp : tracePairing (diagAtom 0) (spinAtom u) = 0 := by
    simp [tracePairing_eq_coords, diagAtom_fst, diagAtom_snd, spinAtom, octDot_zero_left]
  rw [htp, zero_smul, jordanMul_diagAtom0]
  apply albert_ext <;> simp [spinAtom, albert_zero_fst, albert_zero_snd]

private theorem spinAtom_mem_standardQuat {u : Octonion} (hu : u.2 = 0) :
    spinAtom u ∈ standardQuaternionicWindow.subalgebra.carrier := by
  rw [mem_standardQuaternionicWindow_iff]
  exact ⟨rfl, rfl, by
    rw [show (spinAtom u).2 2 = (1 / 2 : ℝ) • u from rfl, oct_smul_snd, hu, smul_zero]⟩

theorem lineHellyCounterexample6_controls :
    (∀ i, IsAtom (lineHellyCounterexample6 i)) ∧
    (∀ T : Finset Albert, (T : Set Albert) ⊆ Set.range lineHellyCounterexample6 → T.card ≤ 5 →
      ∃ Q : QuaternionicWindow, ∀ t ∈ T, t ∈ Q.subalgebra.carrier) ∧
    (¬ ∃ Q : QuaternionicWindow, ∀ i, lineHellyCounterexample6 i ∈ Q.subalgebra.carrier) ∧
    (∀ i, lineHellyCounterexample6 i ∈ (lineSubalgebra (diagAtom 0) (diagAtom_isAtom 0)).carrier) := by
  classical
  have : Module.Finite ℝ Octonion :=
    inferInstanceAs (FiniteDimensional ℝ (Quaternion ℝ × Quaternion ℝ))
  have : Module.Finite ℝ Albert :=
    inferInstanceAs (FiniteDimensional ℝ ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
  have hat : ∀ i, IsAtom (lineHellyCounterexample6 i) := fun i => by
    fin_cases i
    · exact diagAtom_isAtom 1
    · exact spinAtom_isAtom octNormSq_one
    · exact spinAtom_isAtom octNormSq_I
    · exact spinAtom_isAtom octNormSq_J
    · exact spinAtom_isAtom octNormSq_K
    · exact spinAtom_isAtom octNormSq_L
  have hline : ∀ i, lineHellyCounterexample6 i ∈
      (lineSubalgebra (diagAtom 0) (diagAtom_isAtom 0)).carrier := fun i => by
    fin_cases i
    · change diagAtom 1 ∈ (lineSubalgebra (diagAtom 0) (diagAtom_isAtom 0)).carrier
      rw [mem_lineSubalgebra_iff]
      have htp : tracePairing (diagAtom 0) (diagAtom 1) = 0 := by
        simp [tracePairing_eq_coords, diagAtom_fst, diagAtom_snd, octDot_zero_left]
      rw [htp, zero_smul, jordanMul_diagAtom0]
      apply albert_ext <;> simp [diagAtom_fst, diagAtom_snd, albert_zero_fst, albert_zero_snd]
    · exact spinAtom_mem_line0 octOne
    · exact spinAtom_mem_line0 octI
    · exact spinAtom_mem_line0 octJ
    · exact spinAtom_mem_line0 octK
    · exact spinAtom_mem_line0 octL
  have hinj : Function.Injective lineHellyCounterexample6 := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> first
      | rfl
      | (have hf := congrArg (fun x : Albert => x.1 1) hab
         have hs := congrArg (fun x : Albert => (x.2 2).1.re) hab
         have hs1 := congrArg (fun x : Albert => (x.2 2).1.imI) hab
         have hs2 := congrArg (fun x : Albert => (x.2 2).1.imJ) hab
         have hs3 := congrArg (fun x : Albert => (x.2 2).1.imK) hab
         have hs4 := congrArg (fun x : Albert => (x.2 2).2.re) hab
         simp [lineHellyCounterexample6, diagAtom_fst, spinAtom,
           mkAlbert_fst, mkAlbert_snd, oct_smul_fst, oct_smul_snd] at hf hs hs1 hs2 hs3 hs4
         all_goals
           simp [octOne, octonionScalar, octI, octJ, octK, octL] at hs hs1 hs2 hs3 hs4)
  have h5win : ∀ T : Finset Albert, (T : Set Albert) ⊆ Set.range lineHellyCounterexample6 → T.card ≤ 5 →
      ∃ Q : QuaternionicWindow, ∀ t ∈ T, t ∈ Q.subalgebra.carrier := by
    intro T hT_sub hT_card
    have hm : ∃ m : Fin 6, lineHellyCounterexample6 m ∉ T := by
      by_contra hall
      push Not at hall
      have himg : Finset.univ.image lineHellyCounterexample6 ⊆ T := by
        intro x hx; rcases Finset.mem_image.mp hx with ⟨m, _, rfl⟩; exact hall m
      have hc := Finset.card_le_card himg
      rw [Finset.card_image_of_injective _ hinj, Finset.card_fin] at hc
      omega
    obtain ⟨m, hm_not⟩ := hm
    have hdiag1Q : diagAtom 1 ∈ standardQuaternionicWindow.subalgebra.carrier := by
      rw [mem_standardQuaternionicWindow_iff]; exact ⟨rfl, rfl, rfl⟩
    have h1Q : spinAtom octOne ∈ standardQuaternionicWindow.subalgebra.carrier :=
      spinAtom_mem_standardQuat rfl
    have hIQ : spinAtom octI ∈ standardQuaternionicWindow.subalgebra.carrier :=
      spinAtom_mem_standardQuat rfl
    have hJQ : spinAtom octJ ∈ standardQuaternionicWindow.subalgebra.carrier :=
      spinAtom_mem_standardQuat rfl
    have hKQ : spinAtom octK ∈ standardQuaternionicWindow.subalgebra.carrier :=
      spinAtom_mem_standardQuat rfl
    have hn1Q : spinAtom (-octOne) ∈ standardQuaternionicWindow.subalgebra.carrier :=
      spinAtom_mem_standardQuat (show (-octOne).2 = 0 from neg_zero)
    have hnIQ : spinAtom (-octI) ∈ standardQuaternionicWindow.subalgebra.carrier :=
      spinAtom_mem_standardQuat (show (-octI).2 = 0 from neg_zero)
    have hnJQ : spinAtom (-octJ) ∈ standardQuaternionicWindow.subalgebra.carrier :=
      spinAtom_mem_standardQuat (show (-octJ).2 = 0 from neg_zero)
    have hnKQ : spinAtom (-octK) ∈ standardQuaternionicWindow.subalgebra.carrier :=
      spinAtom_mem_standardQuat (show (-octK).2 = 0 from neg_zero)
    have h_via_auto : ∀ g : NativeAlbertAutomorphism,
        (∀ i : Fin 6, i ≠ m → g.linearEquiv (lineHellyCounterexample6 i) ∈
          standardQuaternionicWindow.subalgebra.carrier) →
        ∃ Q : QuaternionicWindow, ∀ t ∈ T, t ∈ Q.subalgebra.carrier := fun g hg =>
      ⟨standardQuaternionicWindow.transport g.symm, fun t ht => by
        obtain ⟨i, rfl⟩ := hT_sub ht
        have him : i ≠ m := fun h => hm_not ((congrArg (· ∈ T) (congrArg lineHellyCounterexample6 h)).mp ht)
        exact ⟨g.linearEquiv (lineHellyCounterexample6 i), hg i him, by
          change g.linearEquiv.symm (g.linearEquiv (lineHellyCounterexample6 i)) =
            lineHellyCounterexample6 i
          exact g.linearEquiv.symm_apply_apply _⟩⟩
    rcases octDot_unit_basis with
      ⟨hd1I, hd1J, hd1K, hd1L, hdIJ, hdIK, hdIL, hdJK, hdJL, hdKL⟩
    have hdn1L : octDot (-octOne) octL = 0 := by rw [octDot_neg_left, hd1L, neg_zero]
    have hdI1 : octDot octI octOne = 0 := by rw [octDot_comm]; exact hd1I
    have hdJ1 : octDot octJ octOne = 0 := by rw [octDot_comm]; exact hd1J
    have hdK1 : octDot octK octOne = 0 := by rw [octDot_comm]; exact hd1K
    have hdL1 : octDot octL octOne = 0 := by rw [octDot_comm]; exact hd1L
    have hdJI : octDot octJ octI = 0 := by rw [octDot_comm]; exact hdIJ
    have hdKI : octDot octK octI = 0 := by rw [octDot_comm]; exact hdIK
    have hdLI : octDot octL octI = 0 := by rw [octDot_comm]; exact hdIL
    have hdKJ : octDot octK octJ = 0 := by rw [octDot_comm]; exact hdJK
    have hdLJ : octDot octL octJ = 0 := by rw [octDot_comm]; exact hdJL
    have hdLK : octDot octL octK = 0 := by rw [octDot_comm]; exact hdKL
    let psiL := swapSpinAuto octL octNormSq_L
    fin_cases m
    · refine h_via_auto psiL fun i hi => ?_
      fin_cases i
      · exact absurd rfl hi
      · dsimp only [psiL, lineHellyCounterexample6]
        rw [swapSpinAuto_spinAtom_ortho octNormSq_L hd1L]; exact h1Q
      · dsimp only [psiL, lineHellyCounterexample6]
        rw [swapSpinAuto_spinAtom_ortho octNormSq_L hdIL]; exact hIQ
      · dsimp only [psiL, lineHellyCounterexample6]
        rw [swapSpinAuto_spinAtom_ortho octNormSq_L hdJL]; exact hJQ
      · dsimp only [psiL, lineHellyCounterexample6]
        rw [swapSpinAuto_spinAtom_ortho octNormSq_L hdKL]; exact hKQ
      · dsimp only [psiL, lineHellyCounterexample6]
        rw [swapSpinAuto_spinAtom_self octNormSq_L]; exact hdiag1Q
    · refine h_via_auto (psiL.comp (swapSpinAuto octOne octNormSq_one)) fun i hi => ?_
      fin_cases i
      · change psiL.linearEquiv ((swapSpinAuto octOne octNormSq_one).linearEquiv (diagAtom 1)) ∈ _
        rw [swapSpinAuto_diagAtom1, swapSpinAuto_spinAtom_ortho octNormSq_L hdn1L]; exact hn1Q
      · exact absurd rfl hi
      · change psiL.linearEquiv ((swapSpinAuto octOne octNormSq_one).linearEquiv (spinAtom octI)) ∈ _
        rw [swapSpinAuto_spinAtom_ortho octNormSq_one hdI1,
          swapSpinAuto_spinAtom_ortho octNormSq_L hdIL]; exact hIQ
      · change psiL.linearEquiv ((swapSpinAuto octOne octNormSq_one).linearEquiv (spinAtom octJ)) ∈ _
        rw [swapSpinAuto_spinAtom_ortho octNormSq_one hdJ1,
          swapSpinAuto_spinAtom_ortho octNormSq_L hdJL]; exact hJQ
      · change psiL.linearEquiv ((swapSpinAuto octOne octNormSq_one).linearEquiv (spinAtom octK)) ∈ _
        rw [swapSpinAuto_spinAtom_ortho octNormSq_one hdK1,
          swapSpinAuto_spinAtom_ortho octNormSq_L hdKL]; exact hKQ
      · change psiL.linearEquiv ((swapSpinAuto octOne octNormSq_one).linearEquiv (spinAtom octL)) ∈ _
        rw [swapSpinAuto_spinAtom_ortho octNormSq_one hdL1,
          swapSpinAuto_spinAtom_self octNormSq_L]; exact hdiag1Q
    · refine h_via_auto (psiL.comp (swapSpinAuto octI octNormSq_I)) fun i hi => ?_
      fin_cases i
      · change psiL.linearEquiv ((swapSpinAuto octI octNormSq_I).linearEquiv (diagAtom 1)) ∈ _
        rw [swapSpinAuto_diagAtom1, swapSpinAuto_spinAtom_ortho octNormSq_L
          (by rw [octDot_neg_left, hdIL, neg_zero])]; exact hnIQ
      · change psiL.linearEquiv ((swapSpinAuto octI octNormSq_I).linearEquiv (spinAtom octOne)) ∈ _
        rw [swapSpinAuto_spinAtom_ortho octNormSq_I hd1I,
          swapSpinAuto_spinAtom_ortho octNormSq_L hd1L]; exact h1Q
      · exact absurd rfl hi
      · change psiL.linearEquiv ((swapSpinAuto octI octNormSq_I).linearEquiv (spinAtom octJ)) ∈ _
        rw [swapSpinAuto_spinAtom_ortho octNormSq_I hdJI,
          swapSpinAuto_spinAtom_ortho octNormSq_L hdJL]; exact hJQ
      · change psiL.linearEquiv ((swapSpinAuto octI octNormSq_I).linearEquiv (spinAtom octK)) ∈ _
        rw [swapSpinAuto_spinAtom_ortho octNormSq_I hdKI,
          swapSpinAuto_spinAtom_ortho octNormSq_L hdKL]; exact hKQ
      · change psiL.linearEquiv ((swapSpinAuto octI octNormSq_I).linearEquiv (spinAtom octL)) ∈ _
        rw [swapSpinAuto_spinAtom_ortho octNormSq_I hdLI,
          swapSpinAuto_spinAtom_self octNormSq_L]; exact hdiag1Q
    · refine h_via_auto (psiL.comp (swapSpinAuto octJ octNormSq_J)) fun i hi => ?_
      fin_cases i
      · change psiL.linearEquiv ((swapSpinAuto octJ octNormSq_J).linearEquiv (diagAtom 1)) ∈ _
        rw [swapSpinAuto_diagAtom1, swapSpinAuto_spinAtom_ortho octNormSq_L
          (by rw [octDot_neg_left, hdJL, neg_zero])]; exact hnJQ
      · change psiL.linearEquiv ((swapSpinAuto octJ octNormSq_J).linearEquiv (spinAtom octOne)) ∈ _
        rw [swapSpinAuto_spinAtom_ortho octNormSq_J hd1J,
          swapSpinAuto_spinAtom_ortho octNormSq_L hd1L]; exact h1Q
      · change psiL.linearEquiv ((swapSpinAuto octJ octNormSq_J).linearEquiv (spinAtom octI)) ∈ _
        rw [swapSpinAuto_spinAtom_ortho octNormSq_J hdIJ,
          swapSpinAuto_spinAtom_ortho octNormSq_L hdIL]; exact hIQ
      · exact absurd rfl hi
      · change psiL.linearEquiv ((swapSpinAuto octJ octNormSq_J).linearEquiv (spinAtom octK)) ∈ _
        rw [swapSpinAuto_spinAtom_ortho octNormSq_J hdKJ,
          swapSpinAuto_spinAtom_ortho octNormSq_L hdKL]; exact hKQ
      · change psiL.linearEquiv ((swapSpinAuto octJ octNormSq_J).linearEquiv (spinAtom octL)) ∈ _
        rw [swapSpinAuto_spinAtom_ortho octNormSq_J hdLJ,
          swapSpinAuto_spinAtom_self octNormSq_L]; exact hdiag1Q
    · refine h_via_auto (psiL.comp (swapSpinAuto octK octNormSq_K)) fun i hi => ?_
      fin_cases i
      · change psiL.linearEquiv ((swapSpinAuto octK octNormSq_K).linearEquiv (diagAtom 1)) ∈ _
        rw [swapSpinAuto_diagAtom1, swapSpinAuto_spinAtom_ortho octNormSq_L
          (by rw [octDot_neg_left, hdKL, neg_zero])]; exact hnKQ
      · change psiL.linearEquiv ((swapSpinAuto octK octNormSq_K).linearEquiv (spinAtom octOne)) ∈ _
        rw [swapSpinAuto_spinAtom_ortho octNormSq_K hd1K,
          swapSpinAuto_spinAtom_ortho octNormSq_L hd1L]; exact h1Q
      · change psiL.linearEquiv ((swapSpinAuto octK octNormSq_K).linearEquiv (spinAtom octI)) ∈ _
        rw [swapSpinAuto_spinAtom_ortho octNormSq_K hdIK,
          swapSpinAuto_spinAtom_ortho octNormSq_L hdIL]; exact hIQ
      · change psiL.linearEquiv ((swapSpinAuto octK octNormSq_K).linearEquiv (spinAtom octJ)) ∈ _
        rw [swapSpinAuto_spinAtom_ortho octNormSq_K hdJK,
          swapSpinAuto_spinAtom_ortho octNormSq_L hdJL]; exact hJQ
      · exact absurd rfl hi
      · change psiL.linearEquiv ((swapSpinAuto octK octNormSq_K).linearEquiv (spinAtom octL)) ∈ _
        rw [swapSpinAuto_spinAtom_ortho octNormSq_K hdLK,
          swapSpinAuto_spinAtom_self octNormSq_L]; exact hdiag1Q
    · refine ⟨standardQuaternionicWindow, fun t ht => ?_⟩
      obtain ⟨i, rfl⟩ := hT_sub ht
      have hi5 : i ≠ 5 := fun h => hm_not ((congrArg (· ∈ T) (congrArg lineHellyCounterexample6 h)).mp ht)
      fin_cases i
      · exact hdiag1Q
      · exact h1Q
      · exact hIQ
      · exact hJQ
      · exact hKQ
      · exact absurd rfl hi5
  have hno_win : ¬ ∃ Q : QuaternionicWindow,
      ∀ i, lineHellyCounterexample6 i ∈ Q.subalgebra.carrier := by
    rintro ⟨Q, hQ⟩
    have hm0 : jordanMul (diagAtom 0) (lineHellyCounterexample6 0) = 0 := by
      have hm := (mem_lineSubalgebra_iff (diagAtom 0) (diagAtom_isAtom 0)
        (lineHellyCounterexample6 0)).mp (hline 0)
      have htp : tracePairing (diagAtom 0) (lineHellyCounterexample6 0) = 0 := by
        simp [lineHellyCounterexample6, tracePairing_eq_coords, diagAtom_fst, diagAtom_snd,
          octDot_zero_left]
      simpa [htp] using hm
    have hm1 : jordanMul (diagAtom 0) (lineHellyCounterexample6 1) = 0 := by
      have hm := (mem_lineSubalgebra_iff (diagAtom 0) (diagAtom_isAtom 0)
        (lineHellyCounterexample6 1)).mp (hline 1)
      have htp : tracePairing (diagAtom 0) (lineHellyCounterexample6 1) = 0 := by
        simp [lineHellyCounterexample6, spinAtom, tracePairing_eq_coords, diagAtom_fst,
          diagAtom_snd, octDot_zero_left]
      simpa [htp] using hm
    have h01_ne : lineHellyCounterexample6 0 ≠ lineHellyCounterexample6 1 :=
      fun h => by have := hinj h; cases this
    obtain ⟨_, hsup⟩ := eq_fiv_support (diagAtom 0) (lineHellyCounterexample6 0)
      (lineHellyCounterexample6 1) (diagAtom_isAtom 0) (hat 0) (hat 1) hm0 hm1 h01_ne
    have hf_mem : albertUnit - diagAtom 0 ∈ Q.subalgebra.carrier := by
      rw [hsup]
      exact Q.subalgebra.carrier.smul_mem _ (Q.subalgebra.carrier.sub_mem
        (Q.subalgebra.carrier.add_mem (hQ 0) (hQ 1))
        (Q.subalgebra.carrier.smul_mem _ (Q.subalgebra.product_mem _ (hQ 0) _ (hQ 1))))
    have hdiag0_mem : diagAtom 0 ∈ Q.subalgebra.carrier := by
      have heq : diagAtom 0 = albertUnit - (albertUnit - diagAtom 0) := by abel
      rw [heq]
      exact Q.subalgebra.carrier.sub_mem Q.subalgebra.unit_mem hf_mem
    have hdim_le : Module.finrank ℝ (quatCornerSubmodule Q (diagAtom 0)) ≤ 6 :=
      quat_corner_finrank_le_six Q (diagAtom 0) (diagAtom_isAtom 0) hdiag0_mem
    let f7 : Fin 7 → Albert := ![albertUnit - diagAtom 0, lineHellyCounterexample6 0,
      lineHellyCounterexample6 1, lineHellyCounterexample6 2, lineHellyCounterexample6 3,
      lineHellyCounterexample6 4, lineHellyCounterexample6 5]
    have hf7_mem : ∀ j : Fin 7, f7 j ∈ quatCornerSubmodule Q (diagAtom 0) := fun j => by
      have hj_orth : ∀ x, x ∈ (lineSubalgebra (diagAtom 0) (diagAtom_isAtom 0)).carrier →
          x.1 0 = 0 → x.2 0 = 0 → x.2 1 = 0 → jordanMul (diagAtom 0) x = 0 := by
        intro x hx hx0 _ _
        have hm := (mem_lineSubalgebra_iff (diagAtom 0) (diagAtom_isAtom 0) x).mp hx
        have htp : tracePairing (diagAtom 0) x = 0 := by
          simp [tracePairing_eq_coords, diagAtom_fst, diagAtom_snd, hx0, octDot_zero_left]
        simpa [htp] using hm
      fin_cases j
      · exact ⟨hf_mem, by
          change jordanMul (diagAtom 0) (albertUnit - diagAtom 0) = 0
          rw [jordanMul_sub_right, jordanMul_albertUnit_right, (diagAtom_isAtom 0).1, sub_self]⟩
      · exact ⟨hQ 0, hm0⟩
      · exact ⟨hQ 1, hm1⟩
      · exact ⟨hQ 2, hj_orth _ (hline 2) rfl rfl rfl⟩
      · exact ⟨hQ 3, hj_orth _ (hline 3) rfl rfl rfl⟩
      · exact ⟨hQ 4, hj_orth _ (hline 4) rfl rfl rfl⟩
      · exact ⟨hQ 5, hj_orth _ (hline 5) rfl rfl rfl⟩
    let v7 : Fin 7 → quatCornerSubmodule Q (diagAtom 0) := fun j => ⟨f7 j, hf7_mem j⟩
    have hv7_indep : LinearIndependent ℝ v7 := by
      have h_c_spin : ∀ (r : ℝ) (u : Octonion),
          r • spinAtom u = mkAlbert ![0, r / 2, r / 2] ![0, 0, (r / 2 : ℝ) • u] := fun r u => by
        apply albert_ext
        · simp [spinAtom, albert_smul_fst]
        · simp [spinAtom, albert_smul_fst]; ring
        · simp [spinAtom, albert_smul_fst]; ring
        · simp [spinAtom, albert_smul_snd]
        · simp [spinAtom, albert_smul_snd]
        · rw [albert_smul_snd]
          simp [spinAtom, mkAlbert_snd, smul_smul, div_eq_mul_inv]
      have h_spin_pair : ∀ (r : ℝ) (u : Octonion),
          r • spinAtom u =
            mkAlbert ![0, r / 2, r / 2]
              ![0, 0, (((r / 2 : ℝ) • u.1, (r / 2 : ℝ) • u.2) : Octonion)] := fun r u => by
        rw [h_c_spin]
        exact congrArg (fun z : Octonion => mkAlbert ![0, r / 2, r / 2] ![0, 0, z])
          (Prod.ext (oct_smul_fst (r / 2) u) (oct_smul_snd (r / 2) u))
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have hc' : ∑ j : Fin 7, c j • f7 j = 0 := congrArg Subtype.val hc
      have hre := congrArg (fun x : Albert => (x.2 2).1.re) hc'
      have himI := congrArg (fun x : Albert => (x.2 2).1.imI) hc'
      have himJ := congrArg (fun x : Albert => (x.2 2).1.imJ) hc'
      have himK := congrArg (fun x : Albert => (x.2 2).1.imK) hc'
      have hlre := congrArg (fun x : Albert => (x.2 2).2.re) hc'
      have hf1 := congrArg (fun x : Albert => x.1 1) hc'
      have hf2 := congrArg (fun x : Albert => x.1 2) hc'
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue, Fin.succ_zero_eq_one,
        Fin.succ_one_eq_two, add_zero, f7, lineHellyCounterexample6, h_spin_pair, mkAlbert_fst,
        mkAlbert_snd, albert_add_fst, albert_add_snd, albert_smul_fst,
        albert_smul_snd, albert_sub_fst, albert_sub_snd, albertUnit_fst, albertUnit_snd,
        diagAtom_fst, diagAtom_snd, smul_eq_mul,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
        oct_smul_fst, oct_smul_snd, oct_add_fst, oct_add_snd,
        Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add,
        Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul, Quaternion.imK_smul,
        albert_zero_fst, albert_zero_snd] at hre himI himJ himK hlre hf1 hf2
      simp [octOne, octonionScalar, octI, octJ, octK, octL] at hre himI himJ himK hlre hf1 hf2
      have hc2 : c 2 = 0 := by linarith
      have hc3 : c 3 = 0 := by linarith
      have hc4 : c 4 = 0 := by linarith
      have hc5 : c 5 = 0 := by linarith
      have hc6 : c 6 = 0 := by linarith
      have hc0 : c 0 = 0 := by linarith
      have hc1 : c 1 = 0 := by linarith
      intro j; fin_cases j <;> assumption
    have h7_le := hv7_indep.fintype_card_le_finrank
    rw [Fintype.card_fin] at h7_le
    omega
  exact ⟨hat, h5win, hno_win, hline⟩

end Section4

end

end AlbertSequential
