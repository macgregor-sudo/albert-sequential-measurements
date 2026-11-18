/- SPDX-License-Identifier: Apache-2.0 -/
module

public import OctonionGeometry
public import FrameSlotNormalizers
public import AcceptedRootAtomAdapter
public import Interfaces.SeparationAndConverse
public import AlbertExceptionality
public import NativeSquareCone
public import NativeWordDuality
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Subalgebra Coordinates, Line Algebra, Subalgebra Classification, and Complex Embeddings

Formalizes:
1. `lem:five:coord`: coordinate reconstruction `B = H_3(F)` and dimension formula
   `3 + 3 * Module.finrank ℝ F.carrier`, plus Cayley-Dickson level subalgebras
   `H3Subalgebra k` for `k ∈ {.R, .C, .H, .O}` and `generatedSubalgebra`.
2. Line algebra `lineSubalgebra q hq`, support identity `eq_fiv_support`, and
   irredundancy dichotomies `lem_fiv_facts_a` and `lem_fiv_facts_b`.
3. `JordanSubalgebraIso`, atom preservation `iso_maps_atom`, line-plus-off-line
   classification `lem_five_line`, and subalgebra dichotomy `lem_five_sub` across all
   Cayley-Dickson levels.
4. Explicit Hermitian matrix representations `symplecticQuatEmbed` (`M_6(ℂ)`) and
   `lineCliffordEmbed` (`M_{24}(ℂ)`), uniform-trace density transport, and unconditional
   `proper_iff_special`.
-/

@[expose] public section
noncomputable section

namespace AlbertSequential

open NativeAnalysis
open Classical
open scoped ComplexOrder

/-! ## Section 0: Subalgebra Order, Extensionality, and Coordinate Helpers -/

private theorem albert_ext {x y : Albert}
    (hd0 : x.1 0 = y.1 0) (hd1 : x.1 1 = y.1 1) (hd2 : x.1 2 = y.1 2)
    (ho0 : x.2 0 = y.2 0) (ho1 : x.2 1 = y.2 1) (ho2 : x.2 2 = y.2 2) : x = y := by
  apply Prod.ext <;> funext k <;> fin_cases k <;> assumption

private theorem oct_zero_fst : (0 : Octonion).1 = 0 := rfl
private theorem oct_zero_snd : (0 : Octonion).2 = 0 := rfl
private theorem oct_add_fst (x y : Octonion) : (x + y).1 = x.1 + y.1 := rfl
private theorem oct_add_snd (x y : Octonion) : (x + y).2 = x.2 + y.2 := rfl
private theorem oct_smul_fst (r : ℝ) (x : Octonion) : (r • x).1 = r • x.1 := rfl
private theorem oct_smul_snd (r : ℝ) (x : Octonion) : (r • x).2 = r • x.2 := rfl
private theorem oct_conj_fst (x : Octonion) : (octonionConj x).1 = star x.1 := rfl
private theorem oct_conj_snd (x : Octonion) : (octonionConj x).2 = -x.2 := rfl

private theorem albert_zero_fst (j : Fin 3) : (0 : Albert).1 j = 0 := rfl
private theorem albert_zero_snd (k : Fin 3) : (0 : Albert).2 k = 0 := rfl
private theorem albert_add_fst (x y : Albert) (j : Fin 3) : (x + y).1 j = x.1 j + y.1 j := rfl
private theorem albert_add_snd (x y : Albert) (k : Fin 3) : (x + y).2 k = x.2 k + y.2 k := rfl
private theorem albert_sub_fst (x y : Albert) (j : Fin 3) : (x - y).1 j = x.1 j - y.1 j := rfl
private theorem albert_sub_snd (x y : Albert) (k : Fin 3) : (x - y).2 k = x.2 k - y.2 k := rfl
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

@[ext]
theorem nativeJordanSubalgebra_ext {B₁ B₂ : NativeJordanSubalgebra}
    (h : B₁.carrier = B₂.carrier) : B₁ = B₂ := by
  cases B₁; cases B₂; simp only at h; subst h; rfl

instance : Top NativeJordanSubalgebra where
  top :=
    { carrier := ⊤
      unit_mem := trivial
      product_mem := fun _ _ _ _ => trivial }

@[simp]
theorem mem_top_nativeJordanSubalgebra (x : Albert) :
    x ∈ (⊤ : NativeJordanSubalgebra).carrier := trivial

instance : LE NativeJordanSubalgebra where
  le B₁ B₂ := B₁.carrier ≤ B₂.carrier

instance : PartialOrder NativeJordanSubalgebra where
  le_refl B := le_refl B.carrier
  le_trans _ _ _ h12 h23 := fun _ hx => h23 (h12 hx)
  le_antisymm _ _ h12 h21 := nativeJordanSubalgebra_ext (le_antisymm h12 h21)

private theorem albert_decompose_slots (x : Albert) :
    x = x.1 0 • diagAtom 0 + x.1 1 • diagAtom 1 + x.1 2 • diagAtom 2 +
        slotElem01 (x.2 0) + slotElem02 (x.2 1) + slotElem12 (x.2 2) := by
  apply albert_ext
  · rw [albert_add_fst, albert_add_fst, albert_add_fst, albert_add_fst, albert_add_fst,
      albert_smul_fst, albert_smul_fst, albert_smul_fst, diagAtom_fst, diagAtom_fst, diagAtom_fst,
      slotElem01_fst, slotElem02_fst, slotElem12_fst]; norm_num
  · rw [albert_add_fst, albert_add_fst, albert_add_fst, albert_add_fst, albert_add_fst,
      albert_smul_fst, albert_smul_fst, albert_smul_fst, diagAtom_fst, diagAtom_fst, diagAtom_fst,
      slotElem01_fst, slotElem02_fst, slotElem12_fst]; norm_num
  · rw [albert_add_fst, albert_add_fst, albert_add_fst, albert_add_fst, albert_add_fst,
      albert_smul_fst, albert_smul_fst, albert_smul_fst, diagAtom_fst, diagAtom_fst, diagAtom_fst,
      slotElem01_fst, slotElem02_fst, slotElem12_fst]; norm_num
  · rw [albert_add_snd, albert_add_snd, albert_add_snd, albert_add_snd, albert_add_snd,
      albert_smul_snd, albert_smul_snd, albert_smul_snd, diagAtom_snd, diagAtom_snd, diagAtom_snd,
      slotElem01_snd_0, slotElem02_snd_0, slotElem12_snd_0]; simp
  · rw [albert_add_snd, albert_add_snd, albert_add_snd, albert_add_snd, albert_add_snd,
      albert_smul_snd, albert_smul_snd, albert_smul_snd, diagAtom_snd, diagAtom_snd, diagAtom_snd,
      slotElem01_snd_1, slotElem02_snd_1, slotElem12_snd_1]; simp
  · rw [albert_add_snd, albert_add_snd, albert_add_snd, albert_add_snd, albert_add_snd,
      albert_smul_snd, albert_smul_snd, albert_smul_snd, diagAtom_snd, diagAtom_snd, diagAtom_snd,
      slotElem01_snd_2, slotElem02_snd_2, slotElem12_snd_2]; simp

private theorem tracePairing_diagAtom0 (x : Albert) :
    tracePairing (diagAtom 0) x = x.1 0 :=
  tracePairing_diagAtom 0 x

private theorem tracePairing_diagAtom1 (x : Albert) :
    tracePairing (diagAtom 1) x = x.1 1 :=
  tracePairing_diagAtom 1 x

private theorem tracePairing_diagAtom2 (x : Albert) :
    tracePairing (diagAtom 2) x = x.1 2 :=
  tracePairing_diagAtom 2 x

/-! ## Section 1: Cayley-Dickson Levels, `H3(F)`, `generatedSubalgebra`, and `lem:five:coord` -/

inductive CDLevel : Type
  | R | C | H | O
  deriving DecidableEq

private theorem albertSharp_fst_0 (x : Albert) :
    (albertSharp x).1 0 = x.1 1 * x.1 2 - octNormSq (x.2 2) := rfl

def octRealSubalgebra : OctSubalgebra where
  carrier :=
    { carrier := {x : Octonion | x.1.imI = 0 ∧ x.1.imJ = 0 ∧ x.1.imK = 0 ∧ x.2 = 0}
      add_mem' := fun {x y} hx hy =>
        ⟨by change (x + y).1.imI = 0; rw [oct_add_fst, Quaternion.imI_add, hx.1, hy.1, add_zero],
         by change (x + y).1.imJ = 0; rw [oct_add_fst, Quaternion.imJ_add, hx.2.1, hy.2.1, add_zero],
         by change (x + y).1.imK = 0; rw [oct_add_fst, Quaternion.imK_add, hx.2.2.1, hy.2.2.1, add_zero],
         by change (x + y).2 = 0; rw [oct_add_snd, hx.2.2.2, hy.2.2.2, add_zero]⟩
      zero_mem' := ⟨rfl, rfl, rfl, rfl⟩
      smul_mem' := fun r {x} hx =>
        ⟨by change (r • x).1.imI = 0; rw [oct_smul_fst, Quaternion.imI_smul, hx.1, smul_zero],
         by change (r • x).1.imJ = 0; rw [oct_smul_fst, Quaternion.imJ_smul, hx.2.1, smul_zero],
         by change (r • x).1.imK = 0; rw [oct_smul_fst, Quaternion.imK_smul, hx.2.2.1, smul_zero],
         by change (r • x).2 = 0; rw [oct_smul_snd, hx.2.2.2, smul_zero]⟩ }
  one_mem := ⟨rfl, rfl, rfl, rfl⟩
  mul_mem := fun x hx y hy => by
    have hxs : x = octonionScalar x.1.re := by
      apply Prod.ext
      · apply Quaternion.ext <;> simp [octonionScalar, hx.1, hx.2.1, hx.2.2.1]
      · exact hx.2.2.2
    have hys : y = octonionScalar y.1.re := by
      apply Prod.ext
      · apply Quaternion.ext <;> simp [octonionScalar, hy.1, hy.2.1, hy.2.2.1]
      · exact hy.2.2.2
    rw [hxs, hys]
    change (octonionMul (octonionScalar x.1.re) (octonionScalar y.1.re)).1.imI = 0 ∧
      (octonionMul (octonionScalar x.1.re) (octonionScalar y.1.re)).1.imJ = 0 ∧
      (octonionMul (octonionScalar x.1.re) (octonionScalar y.1.re)).1.imK = 0 ∧
      (octonionMul (octonionScalar x.1.re) (octonionScalar y.1.re)).2 = 0
    simp [octonionMul, octonionScalar]
  conj_mem := fun x hx =>
    ⟨by rw [oct_conj_fst, Quaternion.imI_star, hx.1, neg_zero],
     by rw [oct_conj_fst, Quaternion.imJ_star, hx.2.1, neg_zero],
     by rw [oct_conj_fst, Quaternion.imK_star, hx.2.2.1, neg_zero],
     by rw [oct_conj_snd, hx.2.2.2, neg_zero]⟩

def octComplexISubalgebra : OctSubalgebra where
  carrier :=
    { carrier := {x : Octonion | x.1.imJ = 0 ∧ x.1.imK = 0 ∧ x.2 = 0}
      add_mem' := fun {x y} hx hy =>
        ⟨by change (x + y).1.imJ = 0; rw [oct_add_fst, Quaternion.imJ_add, hx.1, hy.1, add_zero],
         by change (x + y).1.imK = 0; rw [oct_add_fst, Quaternion.imK_add, hx.2.1, hy.2.1, add_zero],
         by change (x + y).2 = 0; rw [oct_add_snd, hx.2.2, hy.2.2, add_zero]⟩
      zero_mem' := ⟨rfl, rfl, rfl⟩
      smul_mem' := fun r {x} hx =>
        ⟨by change (r • x).1.imJ = 0; rw [oct_smul_fst, Quaternion.imJ_smul, hx.1, smul_zero],
         by change (r • x).1.imK = 0; rw [oct_smul_fst, Quaternion.imK_smul, hx.2.1, smul_zero],
         by change (r • x).2 = 0; rw [oct_smul_snd, hx.2.2, smul_zero]⟩ }
  one_mem := ⟨rfl, rfl, rfl⟩
  mul_mem := fun x hx y hy => by
    have h1 : x = complexToOctonion ⟨x.1.re, x.1.imI⟩ := by
      apply Prod.ext
      · apply Quaternion.ext <;> simp [complexToOctonion_apply, hx.1, hx.2.1]
      · exact hx.2.2
    have h2 : y = complexToOctonion ⟨y.1.re, y.1.imI⟩ := by
      apply Prod.ext
      · apply Quaternion.ext <;> simp [complexToOctonion_apply, hy.1, hy.2.1]
      · exact hy.2.2
    change (octonionMul x y).1.imJ = 0 ∧ (octonionMul x y).1.imK = 0 ∧ (octonionMul x y).2 = 0
    rw [h1, h2]
    simp [complexToOctonion_apply, octonionMul]
  conj_mem := fun x hx =>
    ⟨by rw [oct_conj_fst, Quaternion.imJ_star, hx.1, neg_zero],
     by rw [oct_conj_fst, Quaternion.imK_star, hx.2.1, neg_zero],
     by rw [oct_conj_snd, hx.2.2, neg_zero]⟩

def octQuatStandardSubalgebra : OctSubalgebra where
  carrier :=
    { carrier := {x : Octonion | x.2 = 0}
      add_mem' := fun {x y} hx hy => by change (x + y).2 = 0; rw [oct_add_snd, hx, hy, add_zero]
      zero_mem' := rfl
      smul_mem' := fun r {x} hx => by change (r • x).2 = 0; rw [oct_smul_snd, hx, smul_zero] }
  one_mem := rfl
  mul_mem := fun x hx y hy => by
    change (octonionMul x y).2 = 0
    have h1 : x = quatEmbed1 x.1 := Prod.ext rfl hx
    have h2 : y = quatEmbed1 y.1 := Prod.ext rfl hy
    rw [h1, h2, ← quatEmbed1_isQuatEmbedding.map_mul]
    rfl
  conj_mem := fun x hx => by change (octonionConj x).2 = 0; rw [oct_conj_snd, hx, neg_zero]

def octTopSubalgebra : OctSubalgebra where
  carrier := ⊤
  one_mem := trivial
  mul_mem := fun _ _ _ _ => trivial
  conj_mem := fun _ _ => trivial

def octSubalgebraOfLevel : CDLevel → OctSubalgebra
  | .R => octRealSubalgebra
  | .C => octComplexISubalgebra
  | .H => octQuatStandardSubalgebra
  | .O => octTopSubalgebra

theorem octSubalgebraOfLevel_mono {k₁ k₂ : CDLevel}
    (hle : (match k₁ with | .R => 0 | .C => 1 | .H => 2 | .O => 3) ≤
           (match k₂ with | .R => 0 | .C => 1 | .H => 2 | .O => 3)) :
    (octSubalgebraOfLevel k₁).carrier ≤ (octSubalgebraOfLevel k₂).carrier := by
  cases k₁ <;> cases k₂ <;> simp at hle ⊢ <;> intro x hx
  all_goals
    first
    | exact trivial
    | exact hx.2.2.2
    | exact hx.2.2
    | exact ⟨hx.2.1, hx.2.2.1, hx.2.2.2⟩

private def octRealEquiv : octRealSubalgebra.carrier ≃ₗ[ℝ] ℝ where
  toFun x := x.1.1.re
  invFun r := ⟨octonionScalar r, show (octonionScalar r).1.imI = 0 ∧ (octonionScalar r).1.imJ = 0 ∧
    (octonionScalar r).1.imK = 0 ∧ (octonionScalar r).2 = 0 from ⟨rfl, rfl, rfl, rfl⟩⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · have hx := x.2
      change x.1.1.imI = 0 ∧ x.1.1.imJ = 0 ∧ x.1.1.imK = 0 ∧ x.1.2 = 0 at hx
      apply Quaternion.ext <;> simp [octonionScalar, hx.1, hx.2.1, hx.2.2.1]
    · exact x.2.2.2.2.symm
  right_inv _ := rfl
  map_add' x y := by
    change (x.1 + y.1).1.re = x.1.1.re + y.1.1.re
    rw [oct_add_fst, Quaternion.re_add]
  map_smul' r x := by
    change (r • x.1).1.re = r * x.1.1.re
    rw [oct_smul_fst, Quaternion.re_smul, smul_eq_mul]

private def octComplexEquiv : octComplexISubalgebra.carrier ≃ₗ[ℝ] ℂ where
  toFun x := ⟨x.1.1.re, x.1.1.imI⟩
  invFun z := ⟨complexToOctonion z, show (complexToOctonion z).1.imJ = 0 ∧
    (complexToOctonion z).1.imK = 0 ∧ (complexToOctonion z).2 = 0 from ⟨rfl, rfl, rfl⟩⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · have hx := x.2
      change x.1.1.imJ = 0 ∧ x.1.1.imK = 0 ∧ x.1.2 = 0 at hx
      apply Quaternion.ext <;> simp [complexToOctonion_apply, hx.1, hx.2.1]
    · exact x.2.2.2.symm
  right_inv z := by apply Complex.ext <;> rfl
  map_add' x y := by
    apply Complex.ext
    · change (x.1 + y.1).1.re = x.1.1.re + y.1.1.re; rw [oct_add_fst, Quaternion.re_add]
    · change (x.1 + y.1).1.imI = x.1.1.imI + y.1.1.imI; rw [oct_add_fst, Quaternion.imI_add]
  map_smul' r x := by
    apply Complex.ext
    · change (r • x.1).1.re = (r • (⟨x.1.1.re, x.1.1.imI⟩ : ℂ)).re
      rw [oct_smul_fst, Quaternion.re_smul, Complex.real_smul]; simp
    · change (r • x.1).1.imI = (r • (⟨x.1.1.re, x.1.1.imI⟩ : ℂ)).im
      rw [oct_smul_fst, Quaternion.imI_smul, Complex.real_smul]; simp

private def octQuatEquiv : octQuatStandardSubalgebra.carrier ≃ₗ[ℝ] Quaternion ℝ where
  toFun x := x.1.1
  invFun q := ⟨quatEmbed1 q, show (quatEmbed1 q).2 = 0 from rfl⟩
  left_inv x := by apply Subtype.ext; exact Prod.ext rfl x.2.symm
  right_inv _ := rfl
  map_add' x y := by change (x.1 + y.1).1 = x.1.1 + y.1.1; rw [oct_add_fst]
  map_smul' r x := by change (r • x.1).1 = r • x.1.1; rw [oct_smul_fst]

private def complexToR2 : ℂ ≃ₗ[ℝ] (Fin 2 → ℝ) where
  toFun z := ![z.re, z.im]
  invFun v := ⟨v 0, v 1⟩
  left_inv z := by apply Complex.ext <;> simp
  right_inv v := by funext i; fin_cases i <;> rfl
  map_add' z w := by funext i; fin_cases i <;> simp
  map_smul' r z := by funext i; fin_cases i <;> simp [Complex.real_smul]

theorem octSubalgebraOfLevel_finrank (k : CDLevel) :
    Module.finrank ℝ (octSubalgebraOfLevel k).carrier =
      match k with | .R => 1 | .C => 2 | .H => 4 | .O => 8 := by
  cases k
  · exact octRealEquiv.finrank_eq.trans (Module.finrank_self ℝ)
  · exact (octComplexEquiv.trans complexToR2).finrank_eq.trans (by simp)
  · exact octQuatEquiv.finrank_eq.trans Quaternion.finrank_eq_four
  · exact (show octTopSubalgebra.carrier = (⊤ : Submodule ℝ Octonion) from rfl) ▸
      (finrank_top ℝ Octonion).trans oct_finrank

def jordanSubalgebraH3 (F : OctSubalgebra) : NativeJordanSubalgebra where
  carrier :=
    { carrier := {x : Albert | x.2 0 ∈ F.carrier ∧ x.2 1 ∈ F.carrier ∧ x.2 2 ∈ F.carrier}
      add_mem' := fun {x y} hx hy =>
        ⟨F.carrier.add_mem hx.1 hy.1, F.carrier.add_mem hx.2.1 hy.2.1,
         F.carrier.add_mem hx.2.2 hy.2.2⟩
      zero_mem' := ⟨F.carrier.zero_mem, F.carrier.zero_mem, F.carrier.zero_mem⟩
      smul_mem' := fun r {x} hx =>
        ⟨F.carrier.smul_mem r hx.1, F.carrier.smul_mem r hx.2.1, F.carrier.smul_mem r hx.2.2⟩ }
  unit_mem := ⟨F.carrier.zero_mem, F.carrier.zero_mem, F.carrier.zero_mem⟩
  product_mem := fun x hx y hy => by
    refine ⟨?_, ?_, ?_⟩
    · rw [jordanMul_off_0]
      exact F.carrier.smul_mem _ (F.carrier.add_mem
        (F.carrier.add_mem (F.carrier.add_mem (F.carrier.smul_mem _ hy.1)
          (F.carrier.smul_mem _ hx.1))
          (F.mul_mem _ hx.2.1 _ (F.conj_mem _ hy.2.2)))
        (F.mul_mem _ hy.2.1 _ (F.conj_mem _ hx.2.2)))
    · rw [jordanMul_off_1]
      exact F.carrier.smul_mem _ (F.carrier.add_mem
        (F.carrier.add_mem (F.carrier.add_mem (F.carrier.smul_mem _ hy.2.1)
          (F.carrier.smul_mem _ hx.2.1))
          (F.mul_mem _ hx.1 _ hy.2.2))
        (F.mul_mem _ hy.1 _ hx.2.2))
    · rw [jordanMul_off_2]
      exact F.carrier.smul_mem _ (F.carrier.add_mem
        (F.carrier.add_mem (F.carrier.add_mem (F.carrier.smul_mem _ hy.2.2)
          (F.carrier.smul_mem _ hx.2.2))
          (F.mul_mem _ (F.conj_mem _ hx.1) _ hy.2.1))
        (F.mul_mem _ (F.conj_mem _ hy.1) _ hx.2.1))

@[simp]
theorem mem_jordanSubalgebraH3_iff (F : OctSubalgebra) (x : Albert) :
    x ∈ (jordanSubalgebraH3 F).carrier ↔
      x.2 0 ∈ F.carrier ∧ x.2 1 ∈ F.carrier ∧ x.2 2 ∈ F.carrier :=
  Iff.rfl

def H3Subalgebra (k : CDLevel) : NativeJordanSubalgebra :=
  jordanSubalgebraH3 (octSubalgebraOfLevel k)

theorem H3Subalgebra_mono {k₁ k₂ : CDLevel}
    (hle : (match k₁ with | .R => 0 | .C => 1 | .H => 2 | .O => 3) ≤
           (match k₂ with | .R => 0 | .C => 1 | .H => 2 | .O => 3)) :
    (H3Subalgebra k₁).carrier ≤ (H3Subalgebra k₂).carrier := by
  intro x hx
  have hF := octSubalgebraOfLevel_mono hle
  exact ⟨hF hx.1, hF hx.2.1, hF hx.2.2⟩

theorem diagAtom_mem_jordanSubalgebraH3 (F : OctSubalgebra) (i : Fin 3) :
    diagAtom i ∈ (jordanSubalgebraH3 F).carrier := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [diagAtom, F.carrier.zero_mem]

theorem diagAtom_mem_H3Subalgebra (k : CDLevel) (i : Fin 3) :
    diagAtom i ∈ (H3Subalgebra k).carrier :=
  diagAtom_mem_jordanSubalgebraH3 _ i

theorem H3Subalgebra_C_eq_standardComplexWindow :
    (H3Subalgebra .C).carrier = standardComplexWindow.toSubalgebra.carrier := by
  ext x
  rw [H3Subalgebra, mem_jordanSubalgebraH3_iff]
  change ((x.2 0).1.imJ = 0 ∧ (x.2 0).1.imK = 0 ∧ (x.2 0).2 = 0) ∧
      ((x.2 1).1.imJ = 0 ∧ (x.2 1).1.imK = 0 ∧ (x.2 1).2 = 0) ∧
      ((x.2 2).1.imJ = 0 ∧ (x.2 2).1.imK = 0 ∧ (x.2 2).2 = 0) ↔
      standardComplexWindow.Contains x
  rw [standardComplexWindow_contains_iff]
  tauto

theorem H3Subalgebra_H_eq_standardQuaternionicWindow :
    H3Subalgebra .H = standardQuaternionicWindow.subalgebra := by
  ext x
  change ((x.2 0).2 = 0 ∧ (x.2 1).2 = 0 ∧ (x.2 2).2 = 0) ↔
    x ∈ standardQuaternionicWindow.subalgebra.carrier
  exact (mem_standardQuaternionicWindow_iff x).symm

@[simp]
theorem H3Subalgebra_O_eq_top : H3Subalgebra .O = ⊤ := by
  ext x
  change (x.2 0 ∈ (⊤ : Submodule ℝ Octonion) ∧ x.2 1 ∈ (⊤ : Submodule ℝ Octonion) ∧
    x.2 2 ∈ (⊤ : Submodule ℝ Octonion)) ↔ True
  simp

private def jordanSubalgebraH3Equiv (F : OctSubalgebra) :
    (jordanSubalgebraH3 F).carrier ≃ₗ[ℝ] ((Fin 3 → ℝ) × (Fin 3 → F.carrier)) where
  toFun x := (x.1.1, ![⟨x.1.2 0, x.2.1⟩, ⟨x.1.2 1, x.2.2.1⟩, ⟨x.1.2 2, x.2.2.2⟩])
  invFun p :=
    ⟨(p.1, fun k => (p.2 k).1),
     ⟨(p.2 0).2, (p.2 1).2, (p.2 2).2⟩⟩
  left_inv x := by
    apply Subtype.ext
    apply albert_ext <;> rfl
  right_inv p := by
    apply Prod.ext
    · rfl
    · funext k; fin_cases k <;> rfl
  map_add' x y := by
    apply Prod.ext
    · rfl
    · funext k; fin_cases k <;> rfl
  map_smul' r x := by
    apply Prod.ext
    · rfl
    · funext k; fin_cases k <;> rfl

theorem finrank_jordanSubalgebraH3 (F : OctSubalgebra) :
    Module.finrank ℝ (jordanSubalgebraH3 F).carrier = 3 + 3 * Module.finrank ℝ F.carrier := by
  have : Module.Finite ℝ Octonion :=
    inferInstanceAs (FiniteDimensional ℝ (Quaternion ℝ × Quaternion ℝ))
  rw [(jordanSubalgebraH3Equiv F).finrank_eq, Module.finrank_prod,
    Module.finrank_pi, Module.finrank_pi_fintype]
  simp

theorem finrank_H3Subalgebra (k : CDLevel) :
    Module.finrank ℝ (H3Subalgebra k).carrier =
      match k with | .R => 6 | .C => 9 | .H => 15 | .O => 27 := by
  rw [H3Subalgebra, finrank_jordanSubalgebraH3, octSubalgebraOfLevel_finrank]
  cases k <;> norm_num

def generatedSubalgebra (S : Set Albert) : NativeJordanSubalgebra where
  carrier := sInf {C : Submodule ℝ Albert |
    S ⊆ C ∧ albertUnit ∈ C ∧ ∀ x ∈ C, ∀ y ∈ C, jordanMul x y ∈ C}
  unit_mem := Submodule.mem_sInf.mpr fun _ h => h.2.1
  product_mem x hx y hy := Submodule.mem_sInf.mpr fun C hC =>
    hC.2.2 x (Submodule.mem_sInf.mp hx C hC) y (Submodule.mem_sInf.mp hy C hC)

theorem mem_generatedSubalgebra_iff (S : Set Albert) (x : Albert) :
    x ∈ (generatedSubalgebra S).carrier ↔
      ∀ B : NativeJordanSubalgebra, S ⊆ B.carrier → x ∈ B.carrier := by
  constructor
  · intro hx B hSB
    exact Submodule.mem_sInf.mp hx B.carrier ⟨hSB, B.unit_mem, B.product_mem⟩
  · intro hx
    refine Submodule.mem_sInf.mpr fun C hC => ?_
    let B : NativeJordanSubalgebra :=
      { carrier := C, unit_mem := hC.2.1, product_mem := hC.2.2 }
    exact hx B hC.1

theorem subset_generatedSubalgebra (S : Set Albert) :
    S ⊆ (generatedSubalgebra S).carrier :=
  fun _ hx => (mem_generatedSubalgebra_iff S _).mpr fun _ hB => hB hx

theorem generatedSubalgebra_le {S : Set Albert} {B : NativeJordanSubalgebra}
    (hSB : S ⊆ B.carrier) : generatedSubalgebra S ≤ B :=
  fun _ hx => (mem_generatedSubalgebra_iff S _).mp hx B hSB

theorem generatedSubalgebra_mono {S₁ S₂ : Set Albert} (h : S₁ ⊆ S₂) :
    generatedSubalgebra S₁ ≤ generatedSubalgebra S₂ :=
  generatedSubalgebra_le (h.trans (subset_generatedSubalgebra S₂))

theorem inGeneratedAlgebra_iff_mem_generatedSubalgebra {ι : Type*} (p : ι → Albert) (x : Albert) :
    InGeneratedAlgebra p x ↔ x ∈ (generatedSubalgebra (Set.range p)).carrier := by
  rw [InGeneratedAlgebra, mem_generatedSubalgebra_iff]
  constructor
  · intro h B hB; exact h B (fun i => hB ⟨i, rfl⟩)
  · intro h B hB; exact h B (Set.range_subset_iff.mpr hB)

theorem generatesAlbert_iff_generatedSubalgebra_eq_top {ι : Type*} (p : ι → Albert) :
    GeneratesAlbert p ↔ generatedSubalgebra (Set.range p) = ⊤ := by
  constructor
  · intro h
    ext x
    simp only [mem_top_nativeJordanSubalgebra, iff_true]
    exact (inGeneratedAlgebra_iff_mem_generatedSubalgebra p x).mp (h x)
  · intro h x
    rw [inGeneratedAlgebra_iff_mem_generatedSubalgebra, h]
    trivial

private theorem slotElem_ones_closure (B : NativeJordanSubalgebra)
    (hc : (slotElem01 (octonionScalar 1) ∈ B.carrier ∧ slotElem02 (octonionScalar 1) ∈ B.carrier) ∨
          (slotElem01 (octonionScalar 1) ∈ B.carrier ∧ slotElem12 (octonionScalar 1) ∈ B.carrier) ∨
          (slotElem02 (octonionScalar 1) ∈ B.carrier ∧ slotElem12 (octonionScalar 1) ∈ B.carrier)) :
    slotElem01 octOne ∈ B.carrier ∧ slotElem02 octOne ∈ B.carrier ∧ slotElem12 octOne ∈ B.carrier := by
  change (slotElem01 octOne ∈ B.carrier ∧ slotElem02 octOne ∈ B.carrier) ∨
      (slotElem01 octOne ∈ B.carrier ∧ slotElem12 octOne ∈ B.carrier) ∨
      (slotElem02 octOne ∈ B.carrier ∧ slotElem12 octOne ∈ B.carrier) at hc
  rcases hc with ⟨h01, h02⟩ | ⟨h01, h12⟩ | ⟨h02, h12⟩
  · exact ⟨h01, h02, slotElem02_mem_12_of_mem h01 h02⟩
  · exact ⟨h01, slotElem01_mem_02_of_mem h12 h01, h12⟩
  · exact ⟨by simpa [octonionConj_one] using slotElem12_mem_01_of_mem h02 h12, h02, h12⟩

theorem lem_five_coord (B : NativeJordanSubalgebra)
    (hd0 : diagAtom 0 ∈ B.carrier) (hd1 : diagAtom 1 ∈ B.carrier) (hd2 : diagAtom 2 ∈ B.carrier)
    (hc : (slotElem01 (octonionScalar 1) ∈ B.carrier ∧ slotElem02 (octonionScalar 1) ∈ B.carrier) ∨
          (slotElem01 (octonionScalar 1) ∈ B.carrier ∧ slotElem12 (octonionScalar 1) ∈ B.carrier) ∨
          (slotElem02 (octonionScalar 1) ∈ B.carrier ∧ slotElem12 (octonionScalar 1) ∈ B.carrier)) :
  ∃ F : OctSubalgebra,
    (F.carrier : Set Octonion) = {a : Octonion | slotElem01 a ∈ B.carrier} ∧
    B = jordanSubalgebraH3 F ∧
    Module.finrank ℝ B.carrier = 3 + 3 * Module.finrank ℝ F.carrier := by
  obtain ⟨hs01, hs02, hs12⟩ := slotElem_ones_closure B hc
  let F := slotSubalgebraOfJordanSubalgebra B hd0 hd1 hd2 hs01 hs02 hs12
  refine ⟨F, rfl, ?_, ?_⟩
  · apply nativeJordanSubalgebra_ext
    apply le_antisymm
    · intro x hx
      refine ⟨?_, ?_, ?_⟩
      · change slotElem01 (x.2 0) ∈ B.carrier
        rw [← peirce01_extract x]
        exact B.carrier.smul_mem _ (B.product_mem _ hd0 _ (B.product_mem _ hd1 _ hx))
      · rw [mem_slotSubalgebra_iff_slotElem02 B hd0 hd1 hd2 hs01 hs02 hs12]
        rw [← peirce02_extract x]
        exact B.carrier.smul_mem _ (B.product_mem _ hd0 _ (B.product_mem _ hd2 _ hx))
      · rw [mem_slotSubalgebra_iff_slotElem12 B hd0 hd1 hd2 hs01 hs02 hs12]
        rw [← peirce12_extract x]
        exact B.carrier.smul_mem _ (B.product_mem _ hd1 _ (B.product_mem _ hd2 _ hx))
    · intro x hx
      rw [albert_decompose_slots x]
      have h01 : slotElem01 (x.2 0) ∈ B.carrier := hx.1
      have h02 : slotElem02 (x.2 1) ∈ B.carrier :=
        (mem_slotSubalgebra_iff_slotElem02 B hd0 hd1 hd2 hs01 hs02 hs12 _).mp hx.2.1
      have h12 : slotElem12 (x.2 2) ∈ B.carrier :=
        (mem_slotSubalgebra_iff_slotElem12 B hd0 hd1 hd2 hs01 hs02 hs12 _).mp hx.2.2
      exact B.carrier.add_mem (B.carrier.add_mem (B.carrier.add_mem
        (B.carrier.add_mem (B.carrier.add_mem (B.carrier.smul_mem _ hd0)
          (B.carrier.smul_mem _ hd1)) (B.carrier.smul_mem _ hd2)) h01) h02) h12
  · have hBeq : B = jordanSubalgebraH3 F := by
      apply nativeJordanSubalgebra_ext
      apply le_antisymm
      · intro x hx
        refine ⟨?_, ?_, ?_⟩
        · change slotElem01 (x.2 0) ∈ B.carrier
          rw [← peirce01_extract x]
          exact B.carrier.smul_mem _ (B.product_mem _ hd0 _ (B.product_mem _ hd1 _ hx))
        · rw [mem_slotSubalgebra_iff_slotElem02 B hd0 hd1 hd2 hs01 hs02 hs12]
          rw [← peirce02_extract x]
          exact B.carrier.smul_mem _ (B.product_mem _ hd0 _ (B.product_mem _ hd2 _ hx))
        · rw [mem_slotSubalgebra_iff_slotElem12 B hd0 hd1 hd2 hs01 hs02 hs12]
          rw [← peirce12_extract x]
          exact B.carrier.smul_mem _ (B.product_mem _ hd1 _ (B.product_mem _ hd2 _ hx))
      · intro x hx
        rw [albert_decompose_slots x]
        have h01 : slotElem01 (x.2 0) ∈ B.carrier := hx.1
        have h02 : slotElem02 (x.2 1) ∈ B.carrier :=
          (mem_slotSubalgebra_iff_slotElem02 B hd0 hd1 hd2 hs01 hs02 hs12 _).mp hx.2.1
        have h12 : slotElem12 (x.2 2) ∈ B.carrier :=
          (mem_slotSubalgebra_iff_slotElem12 B hd0 hd1 hd2 hs01 hs02 hs12 _).mp hx.2.2
        exact B.carrier.add_mem (B.carrier.add_mem (B.carrier.add_mem
          (B.carrier.add_mem (B.carrier.add_mem (B.carrier.smul_mem _ hd0)
            (B.carrier.smul_mem _ hd1)) (B.carrier.smul_mem _ hd2)) h01) h02) h12
    rw [hBeq]
    exact finrank_jordanSubalgebraH3 F

theorem lem_five_coord_gen (X : Set Albert)
    (hd0 : diagAtom 0 ∈ (generatedSubalgebra X).carrier)
    (hd1 : diagAtom 1 ∈ (generatedSubalgebra X).carrier)
    (hd2 : diagAtom 2 ∈ (generatedSubalgebra X).carrier)
    (hc : (slotElem01 (octonionScalar 1) ∈ (generatedSubalgebra X).carrier ∧
           slotElem02 (octonionScalar 1) ∈ (generatedSubalgebra X).carrier) ∨
          (slotElem01 (octonionScalar 1) ∈ (generatedSubalgebra X).carrier ∧
           slotElem12 (octonionScalar 1) ∈ (generatedSubalgebra X).carrier) ∨
          (slotElem02 (octonionScalar 1) ∈ (generatedSubalgebra X).carrier ∧
           slotElem12 (octonionScalar 1) ∈ (generatedSubalgebra X).carrier)) :
  ∃ F : OctSubalgebra,
    generatedSubalgebra X = jordanSubalgebraH3 F ∧
    ∀ G : OctSubalgebra,
      (∀ x ∈ X, x.2 0 ∈ G.carrier ∧ x.2 1 ∈ G.carrier ∧ x.2 2 ∈ G.carrier) → F.carrier ≤ G.carrier := by
  obtain ⟨F, hFset, hBeq, _⟩ := lem_five_coord (generatedSubalgebra X) hd0 hd1 hd2 hc
  refine ⟨F, hBeq, fun G hXG => ?_⟩
  have hle : generatedSubalgebra X ≤ jordanSubalgebraH3 G := generatedSubalgebra_le hXG
  rw [hBeq] at hle
  intro a ha
  have ha01 : slotElem01 a ∈ (jordanSubalgebraH3 F).carrier := ⟨ha, F.carrier.zero_mem, F.carrier.zero_mem⟩
  exact (hle ha01).1

/-! ## Section 2: Line Algebra `lineSubalgebra`, `eq_fiv_support`, and `lem:fiv:facts` -/

theorem tracePairing_eq_zero_iff_jordanMul_eq_zero_of_isPositive
    (q x : Albert) (hq : IsAtom q) (hx : IsPositive x) :
    tracePairing q x = 0 ↔ jordanMul q x = 0 := by
  constructor
  · intro h0
    exact (idempotent_support_lemma hq.1 hx h0).1
  · intro h0
    unfold tracePairing
    rw [h0, albertTrace_zero]

private theorem lineSubalgebra_closed_diag0 (x y : Albert)
    (hx : x.2 0 = 0 ∧ x.2 1 = 0) (hy : y.2 0 = 0 ∧ y.2 1 = 0) :
    (jordanMul x y).2 0 = 0 ∧ (jordanMul x y).2 1 = 0 := by
  refine ⟨?_, ?_⟩
  · rw [jordanMul_off_0, hx.1, hx.2, hy.1, hy.2]
    simp [octonionMul_zero_left]
  · rw [jordanMul_off_1, hx.1, hx.2, hy.1, hy.2]
    simp [octonionMul_zero_left]

private theorem mem_line_diag0_iff (x : Albert) :
    jordanMul (diagAtom 0) x = tracePairing (diagAtom 0) x • diagAtom 0 ↔
      x.2 0 = 0 ∧ x.2 1 = 0 := by
  rw [tracePairing_diagAtom0]
  constructor
  · intro h
    have h0 := congrArg (fun a : Albert => a.2 0) h
    have h1 := congrArg (fun a : Albert => a.2 1) h
    rw [jordanMul_diagAtom0, albert_smul_snd, diagAtom_snd, smul_zero] at h0 h1
    change (1 / 2 : ℝ) • x.2 0 = 0 at h0
    change (1 / 2 : ℝ) • x.2 1 = 0 at h1
    exact ⟨(smul_eq_zero.mp h0).resolve_left (by norm_num),
      (smul_eq_zero.mp h1).resolve_left (by norm_num)⟩
  · rintro ⟨h0, h1⟩
    rw [jordanMul_diagAtom0]
    apply albert_ext
    · rw [albert_smul_fst, diagAtom_fst]; simp
    · rw [albert_smul_fst, diagAtom_fst]; simp
    · rw [albert_smul_fst, diagAtom_fst]; simp
    · rw [albert_smul_snd, diagAtom_snd, smul_zero]; change (1 / 2 : ℝ) • x.2 0 = 0; simp [h0]
    · rw [albert_smul_snd, diagAtom_snd, smul_zero]; change (1 / 2 : ℝ) • x.2 1 = 0; simp [h1]
    · rw [albert_smul_snd, diagAtom_snd, smul_zero]; rfl

def lineSubalgebra (q : Albert) (hq : IsAtom q) : NativeJordanSubalgebra where
  carrier :=
    { carrier := {x : Albert | jordanMul q x = tracePairing q x • q}
      add_mem' := fun {x y} hx hy => by
        change jordanMul q (x + y) = tracePairing q (x + y) • q
        rw [jordanMul_add_right, tracePairing_add_right, add_smul, hx, hy]
      zero_mem' := by
        change jordanMul q 0 = tracePairing q 0 • q
        rw [jordanMul_zero_right, tracePairing, jordanMul_zero_right, albertTrace_zero, zero_smul]
      smul_mem' := fun r {x} hx => by
        change jordanMul q (r • x) = tracePairing q (r • x) • q
        rw [jordanMul_smul_right, tracePairing_smul_right, hx, smul_smul] }
  unit_mem := by
    change jordanMul q albertUnit = tracePairing q albertUnit • q
    rw [jordanMul_albertUnit_right, tracePairing_unit_right, hq.2, one_smul]
  product_mem := fun x hx y hy => by
    change jordanMul q (jordanMul x y) = tracePairing q (jordanMul x y) • q
    obtain ⟨g, hg⟩ := atom_to_diagAtom0 q hq
    have hgx : g.linearEquiv x ∈ {z : Albert | z.2 0 = 0 ∧ z.2 1 = 0} := (mem_line_diag0_iff _).mp (by
      have hx' := congrArg g.linearEquiv (show jordanMul q x = tracePairing q x • q from hx)
      rwa [g.preserves_product, map_smul, ← g.map_tracePairing q x, hg] at hx')
    have hgy : g.linearEquiv y ∈ {z : Albert | z.2 0 = 0 ∧ z.2 1 = 0} := (mem_line_diag0_iff _).mp (by
      have hy' := congrArg g.linearEquiv (show jordanMul q y = tracePairing q y • q from hy)
      rwa [g.preserves_product, map_smul, ← g.map_tracePairing q y, hg] at hy')
    have hgxy := (mem_line_diag0_iff (g.linearEquiv (jordanMul x y))).mpr (by
      rw [g.preserves_product]
      exact lineSubalgebra_closed_diag0 _ _ hgx hgy)
    apply g.linearEquiv.injective
    rw [g.preserves_product, map_smul, ← g.map_tracePairing q (jordanMul x y), hg]
    exact hgxy

@[simp]
theorem mem_lineSubalgebra_iff (q : Albert) (hq : IsAtom q) (x : Albert) :
    x ∈ (lineSubalgebra q hq).carrier ↔ jordanMul q x = tracePairing q x • q :=
  Iff.rfl

theorem mem_lineSubalgebra_iff_idem (q : Albert) (hq : IsAtom q) (x : Albert) :
    x ∈ (lineSubalgebra q hq).carrier ↔ jordanMul q (jordanMul q x) = jordanMul q x := by
  rw [mem_lineSubalgebra_iff]
  constructor
  · intro h
    rw [h, jordanMul_smul_right, hq.1]
  · intro h
    have hp := peirce_decomposition hq.1 x
    dsimp only at hp
    have hxhalf : (4 : ℝ) • (jordanMul q x - jordanMul q (jordanMul q x)) = 0 := by
      rw [h, sub_self, smul_zero]
    rw [hxhalf, add_zero] at hp
    have hx_split := hp.1
    have hx0_mul := hp.2.2.2
    have hq1 : jordanMul q x = quadraticMap q x := by
      conv_lhs => rw [← hx_split, jordanMul_add_right, hx0_mul, add_zero, hp.2.1]
    rw [hq1, quadraticMap_atom q x hq]

theorem atom_of_mem_lineSubalgebra {q a : Albert} (hq : IsAtom q) (ha : IsAtom a)
    (haL : a ∈ (lineSubalgebra q hq).carrier) : a = q ∨ jordanMul q a = 0 := by
  obtain ⟨g, hg⟩ := atom_to_diagAtom0 q hq
  let a' := g.linearEquiv a
  have ha' : IsAtom a' := g.map_isAtom ha
  have ha'0 : a'.2 0 = 0 ∧ a'.2 1 = 0 := (mem_line_diag0_iff a').mp (by
    have hL : jordanMul q a = tracePairing q a • q := (mem_lineSubalgebra_iff q hq a).mp haL
    have hL' := congrArg g.linearEquiv hL
    rwa [g.preserves_product, map_smul, ← g.map_tracePairing q a, hg] at hL')
  have hsq : a'.1 0 ^ 2 = a'.1 0 := by
    have hz := congrArg (fun x : Albert => x.1 0) ha'.1
    rw [jordanMul_diag_0, octDot_self, octDot_self, ha'0.1, ha'0.2,
      (octNormSq_eq_zero 0).mpr rfl] at hz
    simpa [pow_two] using hz
  have h01 : a'.1 0 = 0 ∨ a'.1 0 = 1 := by
    have hfac : a'.1 0 * (a'.1 0 - 1) = 0 := by linarith
    rcases mul_eq_zero.mp hfac with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  rcases h01 with h0 | h1
  · right
    apply g.linearEquiv.injective
    rw [g.preserves_product, map_zero, hg, jordanMul_diagAtom0]
    apply albert_ext
    · rw [albert_zero_fst]; change a'.1 0 = 0; exact h0
    · rw [albert_zero_fst]; rfl
    · rw [albert_zero_fst]; rfl
    · rw [albert_zero_snd]; change (1 / 2 : ℝ) • a'.2 0 = 0; rw [ha'0.1, smul_zero]
    · rw [albert_zero_snd]; change (1 / 2 : ℝ) • a'.2 1 = 0; rw [ha'0.2, smul_zero]
    · rw [albert_zero_snd]; rfl
  · left
    have htr : a'.1 0 + a'.1 1 + a'.1 2 = 1 := by
      simpa [albertTrace, Fin.sum_univ_three] using ha'.2
    have hn1 := isAtom_diag_nonneg ha' 1
    have hn2 := isAtom_diag_nonneg ha' 2
    have ha1 : a'.1 1 = 0 := by linarith
    have ha2 : a'.1 2 = 0 := by linarith
    have ha12 : a'.2 2 = 0 := (isAtom_zero_row1 ha' ha1).2
    apply g.linearEquiv.injective
    rw [hg]
    apply albert_ext
    · rw [diagAtom_fst]; change a'.1 0 = 1; exact h1
    · rw [diagAtom_fst]; change a'.1 1 = 0; exact ha1
    · rw [diagAtom_fst]; change a'.1 2 = 0; exact ha2
    · rw [diagAtom_snd]; exact ha'0.1
    · rw [diagAtom_snd]; exact ha'0.2
    · rw [diagAtom_snd]; exact ha12

private theorem diag0_ortho_atom_coords {a : Albert} (ha : IsAtom a) (h0 : jordanMul (diagAtom 0) a = 0) :
    a.1 0 = 0 ∧ a.1 1 + a.1 2 = 1 ∧ a.2 0 = 0 ∧ a.2 1 = 0 ∧
      octNormSq (a.2 2) = a.1 1 * a.1 2 := by
  have ha0 : a.1 0 = 0 := by
    have hz := congrArg (fun x : Albert => x.1 0) h0
    rw [jordanMul_diagAtom0, albert_zero_fst] at hz
    exact hz
  have hrow := isAtom_zero_row0 ha ha0
  have htr : a.1 0 + a.1 1 + a.1 2 = 1 := by
    simpa [albertTrace, Fin.sum_univ_three] using ha.2
  have hsharp := congrArg (fun x : Albert => x.1 0) (albertSharp_of_isAtom ha)
  rw [albertSharp_fst_0, albert_zero_fst] at hsharp
  exact ⟨ha0, by linarith, hrow.1, hrow.2, by linarith⟩

theorem eq_fiv_support (q a b : Albert) (hq : IsAtom q) (ha : IsAtom a) (hb : IsAtom b)
    (hqa : jordanMul q a = 0) (hqb : jordanMul q b = 0) (hab : a ≠ b) :
    tracePairing a b < 1 ∧
    albertUnit - q = (1 - tracePairing a b)⁻¹ • (a + b - (2 : ℝ) • jordanMul a b) := by
  have hlt : tracePairing a b < 1 := by
    have hnn := tracePairing_self_nonneg (a - b)
    have hne : tracePairing (a - b) (a - b) ≠ 0 := by
      intro h0
      exact hab (sub_eq_zero.mp ((tracePairing_self_eq_zero _).mp h0))
    have hpos : 0 < tracePairing (a - b) (a - b) := lt_of_le_of_ne hnn (Ne.symm hne)
    rw [tracePairing_sub_left, tracePairing_sub_right, tracePairing_sub_right,
      tracePairing_comm b a] at hpos
    have haa : tracePairing a a = 1 := by
      unfold tracePairing; rw [ha.1]; exact ha.2
    have hbb : tracePairing b b = 1 := by
      unfold tracePairing; rw [hb.1]; exact hb.2
    linarith
  refine ⟨hlt, ?_⟩
  obtain ⟨g, hg⟩ := atom_to_diagAtom0 q hq
  let a' := g.linearEquiv a
  let b' := g.linearEquiv b
  have ha' := diag0_ortho_atom_coords (g.map_isAtom ha)
    (by rw [← hg, ← g.preserves_product, hqa, map_zero])
  have hb' := diag0_ortho_atom_coords (g.map_isAtom hb)
    (by rw [← hg, ← g.preserves_product, hqb, map_zero])
  have hid : a' + b' - (2 : ℝ) • jordanMul a' b' =
      (1 - tracePairing a' b') • (albertUnit - diagAtom 0) := by
    have ha2 : a'.1 2 = 1 - a'.1 1 := by linarith [ha'.2.1]
    have hb2 : b'.1 2 = 1 - b'.1 1 := by linarith [hb'.2.1]
    have htr : tracePairing a' b' =
        a'.1 1 * b'.1 1 + (1 - a'.1 1) * (1 - b'.1 1) + 2 * octDot (a'.2 2) (b'.2 2) := by
      rw [tracePairing_eq_coords, ha'.1, hb'.1, ha'.2.2.1, hb'.2.2.1, ha'.2.2.2.1, hb'.2.2.2.1,
        ha2, hb2, octDot_zero_left]
      ring
    apply albert_ext
    · rw [albert_sub_fst, albert_add_fst, albert_smul_fst, jordanMul_diag_0,
        albert_smul_fst, albert_sub_fst, albertUnit_fst, diagAtom_fst,
        ha'.1, hb'.1, ha'.2.2.1, hb'.2.2.1, ha'.2.2.2.1, hb'.2.2.2.1]
      norm_num [octDot_zero_left]
    · rw [albert_sub_fst, albert_add_fst, albert_smul_fst, jordanMul_diag_1,
        albert_smul_fst, albert_sub_fst, albertUnit_fst,
        show (diagAtom 0).1 1 = 0 from rfl,
        ha'.2.2.1, hb'.2.2.1, octDot_zero_left, add_zero, htr]
      ring
    · rw [albert_sub_fst, albert_add_fst, albert_smul_fst, jordanMul_diag_2,
        albert_smul_fst, albert_sub_fst, albertUnit_fst,
        show (diagAtom 0).1 2 = 0 from rfl,
        ha'.2.2.2.1, hb'.2.2.2.1, octDot_zero_left, add_zero, ha2, hb2, htr]
      ring
    · rw [albert_sub_snd, albert_add_snd, albert_smul_snd, jordanMul_off_0,
        albert_smul_snd, albert_sub_snd, albertUnit_snd, diagAtom_snd,
        ha'.2.2.1, hb'.2.2.1, ha'.2.2.2.1, hb'.2.2.2.1,
        octonionMul_zero_left, octonionMul_zero_left, smul_zero, add_zero, sub_zero, smul_zero]
      module
    · rw [albert_sub_snd, albert_add_snd, albert_smul_snd, jordanMul_off_1,
        albert_smul_snd, albert_sub_snd, albertUnit_snd, diagAtom_snd,
        ha'.2.2.1, hb'.2.2.1, ha'.2.2.2.1, hb'.2.2.2.1,
        octonionMul_zero_left, octonionMul_zero_left, smul_zero, add_zero, sub_zero, smul_zero]
      module
    · rw [albert_sub_snd, albert_add_snd, albert_smul_snd, jordanMul_off_2,
        albert_smul_snd, albert_sub_snd, albertUnit_snd, diagAtom_snd,
        ha'.2.2.1, hb'.2.2.1, ha'.2.2.2.1, hb'.2.2.2.1, ha'.2.1, hb'.2.1,
        one_smul, octonionConj_zero, octonionMul_zero_left, add_zero, sub_self, smul_zero]
      module
  have h1 : a + b - (2 : ℝ) • jordanMul a b = (1 - tracePairing a b) • (albertUnit - q) := by
    apply g.linearEquiv.injective
    rw [map_sub, map_add, map_smul, g.preserves_product, map_smul, map_sub, g.preserves_unit, hg,
      ← g.map_tracePairing a b]
    exact hid
  rw [h1, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hlt.ne'), one_smul]

def IsIrredundant (T : Finset Albert) : Prop :=
  (∀ p ∈ T, IsAtom p) ∧ ∀ p ∈ T, p ∉ (generatedSubalgebra (T.erase p : Set Albert)).carrier

theorem isIrredundant_iff_no_proper_same_gen (T : Finset Albert) (hT : ∀ p ∈ T, IsAtom p) :
    IsIrredundant T ↔
      ∀ U ⊂ T, generatedSubalgebra (U : Set Albert) ≠ generatedSubalgebra (T : Set Albert) := by
  constructor
  · intro hIrr U hUT heq
    obtain ⟨p, hpT, hpU⟩ := Finset.exists_of_ssubset hUT
    have hnot : p ∉ (generatedSubalgebra (T.erase p : Set Albert)).carrier := hIrr.2 p hpT
    have hsub : (U : Set Albert) ⊆ (T.erase p : Set Albert) := by
      intro x hx
      simp only [Finset.mem_coe, Finset.mem_erase]
      exact ⟨fun hxp => hpU (hxp ▸ hx), hUT.1 hx⟩
    have hpT' : p ∈ (generatedSubalgebra (T : Set Albert)).carrier :=
      subset_generatedSubalgebra _ hpT
    rw [← heq] at hpT'
    exact hnot (generatedSubalgebra_mono hsub hpT')
  · intro hU
    refine ⟨hT, fun p hpT hpgen => ?_⟩
    have hssub : T.erase p ⊂ T := Finset.erase_ssubset hpT
    apply hU (T.erase p) hssub
    apply le_antisymm
    · exact generatedSubalgebra_mono (Finset.erase_subset p T)
    · apply generatedSubalgebra_le
      intro x hx
      by_cases hxp : x = p
      · subst hxp; exact hpgen
      · exact subset_generatedSubalgebra _ (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hxp, hx⟩))

theorem lem_fiv_facts_a (T : Finset Albert) (hT : IsIrredundant T)
    (c a b : Albert) (hc : c ∈ T) (ha : a ∈ T) (hb : b ∈ T) (hab : a ≠ b)
    (hca : jordanMul c a = 0) (hcb : jordanMul c b = 0) : False := by
  have hqc := hT.1 c hc
  have hqa := hT.1 a ha
  have hqb := hT.1 b hb
  have hac : a ≠ c := by
    intro h
    rw [h, hqc.1] at hca
    have := hqc.2
    rw [hca, albertTrace_zero] at this
    norm_num at this
  have hbc : b ≠ c := by
    intro h
    rw [h, hqc.1] at hcb
    have := hqc.2
    rw [hcb, albertTrace_zero] at this
    norm_num at this
  obtain ⟨_, hsup⟩ := eq_fiv_support c a b hqc hqa hqb hca hcb hab
  let B := generatedSubalgebra (T.erase c : Set Albert)
  have haB : a ∈ B.carrier := subset_generatedSubalgebra _ (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hac, ha⟩))
  have hbB : b ∈ B.carrier := subset_generatedSubalgebra _ (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hbc, hb⟩))
  have hunitB : albertUnit - c ∈ B.carrier := by
    rw [hsup]
    exact B.carrier.smul_mem _ (B.carrier.sub_mem (B.carrier.add_mem haB hbB)
      (B.carrier.smul_mem _ (B.product_mem _ haB _ hbB)))
  have hcB : c ∈ B.carrier := by
    have heq : c = albertUnit - (albertUnit - c) := by abel
    rw [heq]
    exact B.carrier.sub_mem B.unit_mem hunitB
  exact hT.2 c hc hcB

theorem lem_fiv_facts_b (T : Finset Albert) (hT : IsIrredundant T) (hcard : 3 ≤ T.card)
    (q : Albert) (hq : IsAtom q) (hsub : (T : Set Albert) ⊆ (lineSubalgebra q hq).carrier) :
    q ∉ T ∧ ∀ t ∈ T, jordanMul q t = 0 := by
  have hqnot : q ∉ T := by
    intro hqT
    have hcard_erase : 2 ≤ (T.erase q).card := by
      have := Finset.card_erase_add_one hqT
      omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (T.erase q).card)
    have haT : a ∈ T := Finset.mem_of_mem_erase ha
    have hbT : b ∈ T := Finset.mem_of_mem_erase hb
    have haq : a ≠ q := (Finset.mem_erase.mp ha).1
    have hbq : b ≠ q := (Finset.mem_erase.mp hb).1
    have hqa : jordanMul q a = 0 :=
      (atom_of_mem_lineSubalgebra hq (hT.1 a haT) (hsub haT)).resolve_left haq
    have hqb : jordanMul q b = 0 :=
      (atom_of_mem_lineSubalgebra hq (hT.1 b hbT) (hsub hbT)).resolve_left hbq
    exact lem_fiv_facts_a T hT q a b hqT haT hbT hab hqa hqb
  refine ⟨hqnot, fun t ht => ?_⟩
  exact (atom_of_mem_lineSubalgebra hq (hT.1 t ht) (hsub ht)).resolve_left (fun h => hqnot (h ▸ ht))

/-! ## Section 3: `JordanSubalgebraIso`, `iso_maps_atom`, Unitary Frames, and `lem:five:line` -/

structure JordanSubalgebraIso (B₁ B₂ : NativeJordanSubalgebra) where
  toLinearEquiv : B₁.carrier ≃ₗ[ℝ] B₂.carrier
  map_unit : toLinearEquiv ⟨albertUnit, B₁.unit_mem⟩ = ⟨albertUnit, B₂.unit_mem⟩
  map_jordan : ∀ x y : B₁.carrier,
    toLinearEquiv ⟨jordanMul x.1 y.1, B₁.product_mem x.1 x.2 y.1 y.2⟩ =
      ⟨jordanMul (toLinearEquiv x).1 (toLinearEquiv y).1,
       B₂.product_mem _ (toLinearEquiv x).2 _ (toLinearEquiv y).2⟩

def JordanSubalgebraIso.refl (B : NativeJordanSubalgebra) : JordanSubalgebraIso B B where
  toLinearEquiv := LinearEquiv.refl ℝ B.carrier
  map_unit := rfl
  map_jordan _ _ := rfl

def JordanSubalgebraIso.symm {B₁ B₂ : NativeJordanSubalgebra}
    (ψ : JordanSubalgebraIso B₁ B₂) : JordanSubalgebraIso B₂ B₁ where
  toLinearEquiv := ψ.toLinearEquiv.symm
  map_unit := ψ.toLinearEquiv.injective (by
    rw [LinearEquiv.apply_symm_apply, ψ.map_unit])
  map_jordan x y := ψ.toLinearEquiv.injective (by
    rw [LinearEquiv.apply_symm_apply]
    have h := ψ.map_jordan (ψ.toLinearEquiv.symm x) (ψ.toLinearEquiv.symm y)
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
    exact h.symm)

def JordanSubalgebraIso.trans {B₁ B₂ B₃ : NativeJordanSubalgebra}
    (ψ₁ : JordanSubalgebraIso B₁ B₂) (ψ₂ : JordanSubalgebraIso B₂ B₃) :
    JordanSubalgebraIso B₁ B₃ where
  toLinearEquiv := ψ₁.toLinearEquiv.trans ψ₂.toLinearEquiv
  map_unit := by
    change ψ₂.toLinearEquiv (ψ₁.toLinearEquiv ⟨albertUnit, B₁.unit_mem⟩) = ⟨albertUnit, B₃.unit_mem⟩
    rw [ψ₁.map_unit, ψ₂.map_unit]
  map_jordan x y := by
    change ψ₂.toLinearEquiv (ψ₁.toLinearEquiv ⟨jordanMul x.1 y.1, _⟩) = _
    rw [ψ₁.map_jordan, ψ₂.map_jordan]
    rfl

theorem JordanSubalgebraIso.map_quadraticMap {B₁ B₂ : NativeJordanSubalgebra}
    (ψ : JordanSubalgebraIso B₁ B₂) (x y : B₁.carrier) :
    (ψ.toLinearEquiv ⟨quadraticMap x.1 y.1, by
      unfold quadraticMap
      rw [two_nsmul]
      exact B₁.carrier.sub_mem
        (B₁.carrier.add_mem (B₁.product_mem _ x.2 _ (B₁.product_mem _ x.2 _ y.2))
          (B₁.product_mem _ x.2 _ (B₁.product_mem _ x.2 _ y.2)))
        (B₁.product_mem _ (B₁.product_mem _ x.2 _ x.2) _ y.2)⟩).1 =
      quadraticMap (ψ.toLinearEquiv x).1 (ψ.toLinearEquiv y).1 := by
  have h1 := congrArg Subtype.val (ψ.map_jordan x y)
  have h2 := congrArg Subtype.val (ψ.map_jordan x ⟨jordanMul x.1 y.1, B₁.product_mem _ x.2 _ y.2⟩)
  have h3 := congrArg Subtype.val (ψ.map_jordan ⟨jordanMul x.1 x.1, B₁.product_mem _ x.2 _ x.2⟩ y)
  have hxx := congrArg Subtype.val (ψ.map_jordan x x)
  dsimp only at h1 h2 h3 hxx
  have heq : (⟨quadraticMap x.1 y.1, by
      unfold quadraticMap; rw [two_nsmul]
      exact B₁.carrier.sub_mem
        (B₁.carrier.add_mem (B₁.product_mem _ x.2 _ (B₁.product_mem _ x.2 _ y.2))
          (B₁.product_mem _ x.2 _ (B₁.product_mem _ x.2 _ y.2)))
        (B₁.product_mem _ (B₁.product_mem _ x.2 _ x.2) _ y.2)⟩ : B₁.carrier) =
      (⟨jordanMul x.1 (jordanMul x.1 y.1), B₁.product_mem _ x.2 _ (B₁.product_mem _ x.2 _ y.2)⟩ +
       ⟨jordanMul x.1 (jordanMul x.1 y.1), B₁.product_mem _ x.2 _ (B₁.product_mem _ x.2 _ y.2)⟩) -
      ⟨jordanMul (jordanMul x.1 x.1) y.1, B₁.product_mem _ (B₁.product_mem _ x.2 _ x.2) _ y.2⟩ := by
    apply Subtype.ext
    simp only [Submodule.coe_sub, Submodule.coe_add, quadraticMap, two_nsmul]
  rw [heq, map_sub, map_add, Submodule.coe_sub, Submodule.coe_add, h2, h3, h1, hxx]
  unfold quadraticMap
  rw [two_nsmul]

theorem JordanSubalgebraIso.map_jordanMul_eq {B₁ B₂ : NativeJordanSubalgebra}
    (ψ : JordanSubalgebraIso B₁ B₂) (x y : B₁.carrier) :
    (ψ.toLinearEquiv ⟨jordanMul x.1 y.1, B₁.product_mem _ x.2 _ y.2⟩).1 =
      jordanMul (ψ.toLinearEquiv x).1 (ψ.toLinearEquiv y).1 :=
  congrArg Subtype.val (ψ.map_jordan x y)

def JordanSubalgebraIso.ofAutoOnTop (g : NativeAlbertAutomorphism) :
    JordanSubalgebraIso (H3Subalgebra .O) (H3Subalgebra .O) where
  toLinearEquiv :=
    { toFun := fun x => ⟨g.linearEquiv x.1, by simp⟩
      invFun := fun y => ⟨g.linearEquiv.symm y.1, by simp⟩
      left_inv := fun x => Subtype.ext (g.linearEquiv.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (g.linearEquiv.apply_symm_apply y.1)
      map_add' := fun x y => Subtype.ext (g.linearEquiv.map_add x.1 y.1)
      map_smul' := fun r x => Subtype.ext (g.linearEquiv.map_smul r x.1) }
  map_unit := Subtype.ext g.preserves_unit
  map_jordan x y := Subtype.ext (g.preserves_product x.1 y.1)

private theorem albertSharp_fst_1 (x : Albert) :
    (albertSharp x).1 1 = x.1 0 * x.1 2 - octNormSq (x.2 1) := rfl
private theorem albertSharp_fst_2 (x : Albert) :
    (albertSharp x).1 2 = x.1 0 * x.1 1 - octNormSq (x.2 0) := rfl
private theorem albertSharp_snd_2 (x : Albert) :
    (albertSharp x).2 2 = octonionMul (octonionConj (x.2 0)) (x.2 1) - x.1 0 • x.2 2 := rfl

private theorem quadraticMap_compl_diagAtom0 (y : Albert) :
    quadraticMap (albertUnit - diagAtom 0) y =
      ((![0, y.1 1, y.1 2], ![0, 0, y.2 2]) : Albert) := by
  let c := albertUnit - diagAtom 0
  have hc_fst0 : c.1 0 = 0 := by show albertUnit.1 0 - (diagAtom 0).1 0 = 0; norm_num [albertUnit, diagAtom]
  have hc_fst1 : c.1 1 = 1 := by show albertUnit.1 1 - (diagAtom 0).1 1 = 1; norm_num [albertUnit, diagAtom]
  have hc_fst2 : c.1 2 = 1 := by show albertUnit.1 2 - (diagAtom 0).1 2 = 1; norm_num [albertUnit, diagAtom]
  have hc_snd : ∀ k, c.2 k = 0 := fun k => by show albertUnit.2 k - (diagAtom 0).2 k = 0; simp [albertUnit, diagAtom]
  have hcc : jordanMul c c = c := by
    apply albert_ext
    · rw [jordanMul_diag_0, hc_fst0, hc_snd 0, hc_snd 1]; simp [octDot_zero_left]
    · rw [jordanMul_diag_1, hc_fst1, hc_snd 0, hc_snd 2]; simp [octDot_zero_left]
    · rw [jordanMul_diag_2, hc_fst2, hc_snd 1, hc_snd 2]; simp [octDot_zero_left]
    · rw [jordanMul_off_0, hc_snd 0, hc_snd 1, hc_snd 2, octonionMul_zero_left]; simp
    · rw [jordanMul_off_1, hc_snd 0, hc_snd 1, hc_snd 2, octonionMul_zero_left]; simp
    · rw [jordanMul_off_2, hc_snd 0, hc_snd 1, hc_snd 2, octonionConj_zero, octonionMul_zero_left]; simp
  let cy : Albert := (![0, y.1 1, y.1 2], ![(1 / 2 : ℝ) • y.2 0, (1 / 2 : ℝ) • y.2 1, y.2 2])
  have hcy : jordanMul c y = cy := by
    apply albert_ext
    · rw [jordanMul_diag_0, hc_fst0, hc_snd 0, hc_snd 1]; simp [cy, octDot_zero_left]
    · rw [jordanMul_diag_1, hc_fst1, hc_snd 0, hc_snd 2]; simp [cy, octDot_zero_left]
    · rw [jordanMul_diag_2, hc_fst2, hc_snd 1, hc_snd 2]; simp [cy, octDot_zero_left]
    · rw [jordanMul_off_0, hc_fst0, hc_fst1, hc_snd 0, hc_snd 1, hc_snd 2]
      repeat rw [octonionConj_zero]
      repeat first | rw [octonionMul_zero_left] | rw [octonionMul_zero_right]
      simp [cy, smul_zero, add_zero]
    · rw [jordanMul_off_1, hc_fst0, hc_fst2, hc_snd 0, hc_snd 1, hc_snd 2]
      repeat first | rw [octonionMul_zero_left] | rw [octonionMul_zero_right]
      simp [cy, smul_zero, add_zero]
    · rw [jordanMul_off_2, hc_fst1, hc_fst2, hc_snd 0, hc_snd 1, hc_snd 2]
      repeat rw [octonionConj_zero]
      repeat first | rw [octonionMul_zero_left] | rw [octonionMul_zero_right]
      simp [cy, smul_zero, add_zero]; module
  unfold quadraticMap
  rw [hcc, two_nsmul]
  let cy2 : Albert := (![0, y.1 1, y.1 2], ![(1 / 4 : ℝ) • y.2 0, (1 / 4 : ℝ) • y.2 1, y.2 2])
  have hcy2 : jordanMul c cy = cy2 := by
    apply albert_ext
    · rw [jordanMul_diag_0, hc_fst0, hc_snd 0, hc_snd 1]; simp [cy, cy2, octDot_zero_left]
    · rw [jordanMul_diag_1, hc_fst1, hc_snd 0, hc_snd 2]; simp [cy, cy2, octDot_zero_left]
    · rw [jordanMul_diag_2, hc_fst2, hc_snd 1, hc_snd 2]; simp [cy, cy2, octDot_zero_left]
    · rw [jordanMul_off_0, hc_fst0, hc_fst1, hc_snd 0, hc_snd 1, hc_snd 2]
      repeat rw [octonionConj_zero]
      repeat first | rw [octonionMul_zero_left] | rw [octonionMul_zero_right]
      simp [cy, cy2, smul_zero, add_zero, smul_smul]; norm_num
    · rw [jordanMul_off_1, hc_fst0, hc_fst2, hc_snd 0, hc_snd 1, hc_snd 2]
      repeat first | rw [octonionMul_zero_left] | rw [octonionMul_zero_right]
      simp [cy, cy2, smul_zero, add_zero, smul_smul]; norm_num
    · rw [jordanMul_off_2, hc_fst1, hc_fst2, hc_snd 0, hc_snd 1, hc_snd 2]
      repeat rw [octonionConj_zero]
      repeat first | rw [octonionMul_zero_left] | rw [octonionMul_zero_right]
      simp [cy, cy2, smul_zero, add_zero]; module
  rw [hcy, hcy2]
  apply albert_ext
  · rw [albert_sub_fst, albert_add_fst]; simp [cy, cy2]
  · rw [albert_sub_fst, albert_add_fst]; simp [cy, cy2]
  · rw [albert_sub_fst, albert_add_fst]; simp [cy, cy2]
  · rw [albert_sub_snd, albert_add_snd]; simp [cy, cy2]; module
  · rw [albert_sub_snd, albert_add_snd]; simp [cy, cy2]; module
  · rw [albert_sub_snd, albert_add_snd]; simp [cy, cy2]

private theorem compl_atom_compress_sq {p a : Albert} (hp : IsAtom p) (ha : IsAtom a) :
    let c := quadraticMap (albertUnit - p) a
    jordanMul c c = (albertTrace c) • c ∧ 0 ≤ albertTrace c ∧ albertTrace c ≤ 1 ∧
      jordanMul p c = 0 := by
  intro c
  obtain ⟨g, hg⟩ := atom_to_diagAtom0 p hp
  let y := g.linearEquiv a
  have hy : IsAtom y := g.map_isAtom ha
  let gc : Albert := (![0, y.1 1, y.1 2], ![0, 0, y.2 2])
  have hgc : g.linearEquiv c = gc := by
    dsimp only [c]
    rw [g.map_quadraticMap, map_sub, g.preserves_unit, hg, quadraticMap_compl_diagAtom0]
  have htr : albertTrace c = y.1 1 + y.1 2 := by
    rw [← g.preserves_trace c, hgc]
    simp [gc, albertTrace, Fin.sum_univ_three]
  have htr_y : y.1 0 + y.1 1 + y.1 2 = 1 := by
    simpa [albertTrace, Fin.sum_univ_three] using hy.2
  have hn0 := isAtom_diag_nonneg hy 0
  have hn1 := isAtom_diag_nonneg hy 1
  have hn2 := isAtom_diag_nonneg hy 2
  have hsharp0 := congrArg (fun x : Albert => x.1 0) (albertSharp_of_isAtom hy)
  rw [albertSharp_fst_0, albert_zero_fst] at hsharp0
  have hnorm : octDot (y.2 2) (y.2 2) = y.1 1 * y.1 2 := by
    have hdot : octDot (y.2 2) (y.2 2) = octNormSq (y.2 2) := rfl
    linarith
  have hsq_g : jordanMul (g.linearEquiv c) (g.linearEquiv c) =
      (y.1 1 + y.1 2) • g.linearEquiv c := by
    rw [hgc]
    apply albert_ext
    · rw [albert_smul_fst, jordanMul_diag_0]; simp [gc, octDot_zero_left]
    · rw [albert_smul_fst, jordanMul_diag_1]; simp [gc, octDot_zero_left, hnorm]; ring
    · rw [albert_smul_fst, jordanMul_diag_2]; simp [gc, octDot_zero_left, hnorm]; ring
    · rw [albert_smul_snd, jordanMul_off_0]; simp [gc, octonionMul_zero_left]
    · rw [albert_smul_snd, jordanMul_off_1]; simp [gc, octonionMul_zero_left]
    · rw [albert_smul_snd, jordanMul_off_2]; simp [gc, octonionConj_zero, octonionMul_zero_left]; module
  have hmul_g : jordanMul (g.linearEquiv p) (g.linearEquiv c) = 0 := by
    rw [hg, hgc, jordanMul_diagAtom0]
    apply albert_ext <;> simp [gc, albert_zero_fst, albert_zero_snd, smul_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply g.linearEquiv.injective
    rw [g.preserves_product, map_smul, hsq_g, htr]
  · rw [htr]; linarith
  · rw [htr]; linarith
  · apply g.linearEquiv.injective
    rw [g.preserves_product, map_zero]
    exact hmul_g

theorem iso_maps_atom {k : CDLevel} {B : NativeJordanSubalgebra}
    (ψ : JordanSubalgebraIso (H3Subalgebra k) B)
    (p : (H3Subalgebra k).carrier) (hp : IsAtom p.1) :
    IsAtom (ψ.toLinearEquiv p).1 := by
  have hd_mem : ∀ i : Fin 3, diagAtom i ∈ (H3Subalgebra k).carrier := diagAtom_mem_H3Subalgebra k
  let e_compl : (H3Subalgebra k).carrier := ⟨albertUnit - p.1, (H3Subalgebra k).carrier.sub_mem (H3Subalgebra k).unit_mem p.2⟩
  let c : Fin 3 → (H3Subalgebra k).carrier := fun i =>
    ⟨quadraticMap (albertUnit - p.1) (diagAtom i), by
      unfold quadraticMap; rw [two_nsmul]
      exact (H3Subalgebra k).carrier.sub_mem
        ((H3Subalgebra k).carrier.add_mem
          ((H3Subalgebra k).product_mem _ e_compl.2 _ ((H3Subalgebra k).product_mem _ e_compl.2 _ (hd_mem i)))
          ((H3Subalgebra k).product_mem _ e_compl.2 _ ((H3Subalgebra k).product_mem _ e_compl.2 _ (hd_mem i))))
        ((H3Subalgebra k).product_mem _ ((H3Subalgebra k).product_mem _ e_compl.2 _ e_compl.2) _ (hd_mem i))⟩
  have hlin : ∑ i : Fin 3, quadraticMap (albertUnit - p.1) (diagAtom i) =
      quadraticMap (albertUnit - p.1) (∑ i : Fin 3, diagAtom i) := by
    simp only [quadraticMap, two_nsmul, Fin.sum_univ_three, jordanMul_add_right]
    abel
  have hsum_c : ∑ i : Fin 3, (c i).1 = albertUnit - p.1 := by
    rw [show (∑ i : Fin 3, (c i).1) = ∑ i : Fin 3, quadraticMap (albertUnit - p.1) (diagAtom i) from rfl,
      hlin, diagAtom_sum_eq_unit]
    have hcc : jordanMul (albertUnit - p.1) (albertUnit - p.1) = albertUnit - p.1 := by
      simp only [jordanMul_sub_left, jordanMul_sub_right, jordanMul_albertUnit_left,
        jordanMul_albertUnit_right, hp.1]; abel
    unfold quadraticMap
    simp only [jordanMul_albertUnit_right, hcc, two_nsmul]; abel
  have hsum_tr : ∑ i : Fin 3, albertTrace (c i).1 = 2 := by
    have htr : ∑ i : Fin 3, albertTrace (c i).1 = albertTrace (∑ i : Fin 3, (c i).1) := by
      simp [Fin.sum_univ_three, albertTrace_add]
    have hau : albertTrace albertUnit = 3 := by simp [albertTrace, albertUnit]
    rw [htr, hsum_c, albertTrace_sub, hau, hp.2]; norm_num
  have hex : ∃ i : Fin 3, 0 < albertTrace (c i).1 := by
    by_contra hnot
    push Not at hnot
    have hle0 : ∑ i : Fin 3, albertTrace (c i).1 ≤ 0 := Finset.sum_nonpos (fun i _ => hnot i)
    linarith
  obtain ⟨i₀, hi₀⟩ := hex
  have hc_props := compl_atom_compress_sq hp (diagAtom_isAtom i₀)
  let t := albertTrace (c i₀).1
  let p₁ : (H3Subalgebra k).carrier := t⁻¹ • c i₀
  have hp₁_val : p₁.1 = t⁻¹ • (c i₀).1 := rfl
  have hp₁_atom : IsAtom p₁.1 := by
    constructor
    · rw [hp₁_val, jordanMul_smul_left, jordanMul_smul_right, hc_props.1, smul_smul, smul_smul]
      have ht : albertTrace (quadraticMap (albertUnit - p.1) (diagAtom i₀)) = t := rfl
      rw [ht]
      congr 1; field_simp [hi₀.ne']
    · rw [hp₁_val, albertTrace_smul]
      exact inv_mul_cancel₀ hi₀.ne'
  have hp_p₁ : jordanMul p.1 p₁.1 = 0 := by
    rw [hp₁_val, jordanMul_smul_right, hc_props.2.2.2, smul_zero]
  let p₂ : (H3Subalgebra k).carrier :=
    ⟨albertUnit, (H3Subalgebra k).unit_mem⟩ - p - p₁
  have hp₂_sum : p.1 + p₁.1 + p₂.1 = albertUnit := by
    change p.1 + p₁.1 + (albertUnit - p.1 - p₁.1) = albertUnit
    abel
  have hp₂_id : jordanMul p₂.1 p₂.1 = p₂.1 := by
    change jordanMul (albertUnit - p.1 - p₁.1) (albertUnit - p.1 - p₁.1) = albertUnit - p.1 - p₁.1
    simp only [jordanMul_sub_left, jordanMul_sub_right, jordanMul_albertUnit_left,
      jordanMul_albertUnit_right, hp.1, hp₁_atom.1, hp_p₁, show jordanMul p₁.1 p.1 = 0 from
      by rw [jordanMul_comm]; exact hp_p₁]
    abel
  have hp₂_tr : albertTrace p₂.1 = 1 := by
    change albertTrace (albertUnit - p.1 - p₁.1) = 1
    have hau : albertTrace albertUnit = 3 := by simp [albertTrace, albertUnit]
    rw [albertTrace_sub, albertTrace_sub, hau, hp.2, hp₁_atom.2]; norm_num
  have hp₂_atom : IsAtom p₂.1 := ⟨hp₂_id, hp₂_tr⟩
  let q₀ := ψ.toLinearEquiv p
  let q₁ := ψ.toLinearEquiv p₁
  let q₂ := ψ.toLinearEquiv p₂
  have hq0_id : jordanMul q₀.1 q₀.1 = q₀.1 := by
    rw [← ψ.map_jordanMul_eq p p]; exact congrArg (fun z => (ψ.toLinearEquiv z).1) (Subtype.ext hp.1)
  have hq1_id : jordanMul q₁.1 q₁.1 = q₁.1 := by
    rw [← ψ.map_jordanMul_eq p₁ p₁]; exact congrArg (fun z => (ψ.toLinearEquiv z).1) (Subtype.ext hp₁_atom.1)
  have hq2_id : jordanMul q₂.1 q₂.1 = q₂.1 := by
    rw [← ψ.map_jordanMul_eq p₂ p₂]; exact congrArg (fun z => (ψ.toLinearEquiv z).1) (Subtype.ext hp₂_atom.1)
  have hq_sum : q₀.1 + q₁.1 + q₂.1 = albertUnit := by
    have hs : p + p₁ + p₂ = ⟨albertUnit, (H3Subalgebra k).unit_mem⟩ := Subtype.ext hp₂_sum
    have hmap := congrArg (fun z => (ψ.toLinearEquiv z).1) hs
    rw [map_add, map_add, Submodule.coe_add, Submodule.coe_add, ψ.map_unit] at hmap
    exact hmap
  have hne0 : q₀.1 ≠ 0 := fun h => by
    have h0 : p = 0 := ψ.toLinearEquiv.injective (Subtype.ext (by rw [map_zero]; exact h))
    have htr0 : albertTrace p.1 = 0 := by rw [congrArg Subtype.val h0]; exact albertTrace_zero
    linarith [hp.2]
  have hne1 : q₁.1 ≠ 0 := fun h => by
    have h0 : p₁ = 0 := ψ.toLinearEquiv.injective (Subtype.ext (by rw [map_zero]; exact h))
    have htr0 : albertTrace p₁.1 = 0 := by rw [congrArg Subtype.val h0]; exact albertTrace_zero
    linarith [hp₁_atom.2]
  have hne2 : q₂.1 ≠ 0 := fun h => by
    have h0 : p₂ = 0 := ψ.toLinearEquiv.injective (Subtype.ext (by rw [map_zero]; exact h))
    have htr0 : albertTrace p₂.1 = 0 := by rw [congrArg Subtype.val h0]; exact albertTrace_zero
    linarith [hp₂_atom.2]
  have hge1 : ∀ {z : Albert}, jordanMul z z = z → z ≠ 0 → 1 ≤ albertTrace z := fun {z} hz hzne => by
    rcases idempotent_dichotomy z hz with ⟨rfl, _⟩ | ⟨_, htr⟩ | ⟨_, htr⟩ | ⟨_, htr⟩
    · exact absurd rfl hzne
    · linarith
    · linarith
    · linarith
  have htr_sum : albertTrace q₀.1 + albertTrace q₁.1 + albertTrace q₂.1 = 3 := by
    have hau : albertTrace albertUnit = 3 := by simp [albertTrace, albertUnit]
    rw [← albertTrace_add, ← albertTrace_add, hq_sum, hau]
  have htr0 : albertTrace q₀.1 = 1 := by
    linarith [hge1 hq0_id hne0, hge1 hq1_id hne1, hge1 hq2_id hne2]
  exact ⟨hq0_id, htr0⟩

/-! ### Section 3.1: Associative 3×3 Hermitian Matrix Unitary Conjugation (`ℝ`, `ℂ`, `ℍ`) -/

structure AssocCD (D : Type) [Ring D] [StarRing D] [Algebra ℝ D] [StarModule ℝ D]
    [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] where
  re : D →ₗ[ℝ] ℝ
  normSq : D → ℝ
  embed : D →ₗ[ℝ] Octonion
  subalgebra : OctSubalgebra
  range_embed : LinearMap.range embed = subalgebra.carrier
  re_one : re 1 = 1
  re_mul_comm : ∀ a b : D, re (a * b) = re (b * a)
  mul_star_self : ∀ a : D, a * star a = normSq a • (1 : D)
  star_mul_self : ∀ a : D, star a * a = normSq a • (1 : D)
  normSq_nonneg : ∀ a : D, 0 ≤ normSq a
  normSq_eq_zero : ∀ a : D, normSq a = 0 ↔ a = 0
  re_smul_one : ∀ a : D, star a = a → a = re a • (1 : D)
  embed_one : embed 1 = octOne
  embed_mul : ∀ a b : D, octonionMul (embed a) (embed b) = embed (a * b)
  embed_star : ∀ a : D, octonionConj (embed a) = embed (star a)
  embed_re : ∀ a : D, octonionReal (embed a) = re a
  embed_normSq : ∀ a : D, octNormSq (embed a) = normSq a

def assocCD_R : AssocCD ℝ where
  re := LinearMap.id
  normSq a := a * a
  embed :=
    { toFun := octonionScalar
      map_add' := fun a b => by
        apply Prod.ext
        · rw [oct_add_fst]; apply Quaternion.ext <;> simp [octonionScalar]
        · rw [oct_add_snd]; simp [octonionScalar]
      map_smul' := fun r a => by
        apply Prod.ext
        · rw [oct_smul_fst]; apply Quaternion.ext <;> simp [octonionScalar]
        · rw [oct_smul_snd]; simp [octonionScalar] }
  subalgebra := octRealSubalgebra
  range_embed := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨rfl, rfl, rfl, rfl⟩
    · intro hx
      refine ⟨x.1.re, ?_⟩
      change octonionScalar x.1.re = x
      apply Prod.ext
      · apply Quaternion.ext
        · simp [octonionScalar]
        · simpa [octonionScalar] using hx.1.symm
        · simpa [octonionScalar] using hx.2.1.symm
        · simpa [octonionScalar] using hx.2.2.1.symm
      · exact hx.2.2.2.symm
  re_one := rfl
  re_mul_comm a b := mul_comm a b
  mul_star_self a := by simp [smul_eq_mul]
  star_mul_self a := by simp [smul_eq_mul]
  normSq_nonneg a := mul_self_nonneg a
  normSq_eq_zero a := mul_self_eq_zero
  re_smul_one a _ := by simp [smul_eq_mul]
  embed_one := rfl
  embed_mul a b := by
    change octonionMul (octonionScalar a) (octonionScalar b) = octonionScalar (a * b)
    apply Prod.ext <;> simp [octonionMul, octonionScalar]
  embed_star a := by
    change octonionConj (octonionScalar a) = octonionScalar (star a)
    apply Prod.ext <;> [apply Quaternion.ext <;> simp [octonionConj, octonionScalar]; simp [octonionConj, octonionScalar]]
  embed_re a := rfl
  embed_normSq a := by
    change octNormSq (octonionScalar a) = a * a
    rw [octNormSq_eq_coords]; simp [octonionScalar]; ring

def assocCD_C : AssocCD ℂ where
  re :=
    { toFun := Complex.re
      map_add' := Complex.add_re
      map_smul' := fun r z => by simp [Complex.real_smul] }
  normSq z := z.re ^ 2 + z.im ^ 2
  embed := complexToOctonion
  subalgebra := octComplexISubalgebra
  range_embed := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨rfl, rfl, rfl⟩
    · intro hx
      refine ⟨⟨x.1.re, x.1.imI⟩, ?_⟩
      apply Prod.ext
      · apply Quaternion.ext <;> simp [complexToOctonion_apply, hx.1, hx.2.1]
      · exact hx.2.2.symm
  re_one := rfl
  re_mul_comm z w := by simp [Complex.mul_re]; ring
  mul_star_self z := by
    apply Complex.ext
    · simp [Complex.real_smul, sq]
    · simp [Complex.real_smul, sq]; ring
  star_mul_self z := by
    apply Complex.ext
    · simp [Complex.real_smul, sq]
    · simp [Complex.real_smul, sq]; ring
  normSq_nonneg z := by positivity
  normSq_eq_zero z := by
    constructor
    · intro h
      have h1 : z.re = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
      have h2 : z.im = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
      exact Complex.ext h1 h2
    · rintro rfl; norm_num
  re_smul_one z hz := by
    have him : z.im = 0 := by
      have h := congrArg Complex.im hz
      simp at h
      linarith
    apply Complex.ext <;> simp [Complex.real_smul, him]
  embed_one := complexToOctonion_one
  embed_mul z w := by
    apply Prod.ext
    · apply Quaternion.ext
      · simp [complexToOctonion_apply, octonionMul]; ring
      · simp [complexToOctonion_apply, octonionMul]
      · simp [complexToOctonion_apply, octonionMul]
      · simp [complexToOctonion_apply, octonionMul]
    · simp [complexToOctonion_apply, octonionMul]
  embed_star z := by
    apply Prod.ext
    · apply Quaternion.ext <;> simp [complexToOctonion_apply, octonionConj]
    · simp [complexToOctonion_apply, octonionConj]
  embed_re z := rfl
  embed_normSq z := by
    rw [octNormSq_eq_coords]; simp [complexToOctonion_apply]

def assocCD_H : AssocCD (Quaternion ℝ) where
  re :=
    { toFun := fun q => q.re
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  normSq := quatNormSq
  embed := quatEmbed1
  subalgebra := octQuatStandardSubalgebra
  range_embed := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      rfl
    · intro hx
      exact ⟨x.1, Prod.ext rfl hx.symm⟩
  re_one := rfl
  re_mul_comm := quaternion_real_mul_comm
  mul_star_self q := by
    apply Quaternion.ext <;> (simp [quatNormSq]; ring)
  star_mul_self q := by
    apply Quaternion.ext <;> (simp [quatNormSq]; ring)
  normSq_nonneg q := by unfold quatNormSq; positivity
  normSq_eq_zero q := by
    unfold quatNormSq
    constructor
    · intro h
      apply Quaternion.ext <;> simp <;> nlinarith [sq_nonneg q.re, sq_nonneg q.imI, sq_nonneg q.imJ, sq_nonneg q.imK]
    · rintro rfl; simp
  re_smul_one q hq := quat_eq_re_smul_one hq
  embed_one := by rw [quatEmbed1_apply]; rfl
  embed_mul a b := (quatEmbed1_isQuatEmbedding.map_mul a b).symm
  embed_star a := (quatEmbed1_isQuatEmbedding.map_star a).symm
  embed_re a := quatEmbed1_isQuatEmbedding.map_re a
  embed_normSq a := by
    rw [octNormSq_eq_coords]; unfold quatNormSq
    rw [quatEmbed1_apply]; simp [pow_two]

def assocMatToAlbert {D : Type} [Ring D] [StarRing D] [Algebra ℝ D] [StarModule ℝ D]
    [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] (A : AssocCD D)
    (M : Matrix (Fin 3) (Fin 3) D) : Albert :=
  (fun i => A.re (M i i), ![A.embed (M 0 1), A.embed (M 0 2), A.embed (M 1 2)])

theorem assocMatToAlbert_fst {D : Type} [Ring D] [StarRing D] [Algebra ℝ D] [StarModule ℝ D]
    [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] (A : AssocCD D)
    (M : Matrix (Fin 3) (Fin 3) D) (i : Fin 3) :
    (assocMatToAlbert A M).1 i = A.re (M i i) := rfl

theorem assocMatToAlbert_snd_0 {D : Type} [Ring D] [StarRing D] [Algebra ℝ D] [StarModule ℝ D]
    [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] (A : AssocCD D)
    (M : Matrix (Fin 3) (Fin 3) D) :
    (assocMatToAlbert A M).2 0 = A.embed (M 0 1) := rfl

theorem assocMatToAlbert_snd_1 {D : Type} [Ring D] [StarRing D] [Algebra ℝ D] [StarModule ℝ D]
    [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] (A : AssocCD D)
    (M : Matrix (Fin 3) (Fin 3) D) :
    (assocMatToAlbert A M).2 1 = A.embed (M 0 2) := rfl

theorem assocMatToAlbert_snd_2 {D : Type} [Ring D] [StarRing D] [Algebra ℝ D] [StarModule ℝ D]
    [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] (A : AssocCD D)
    (M : Matrix (Fin 3) (Fin 3) D) :
    (assocMatToAlbert A M).2 2 = A.embed (M 1 2) := rfl

theorem assocCD_embed_injective {D : Type} [Ring D] [StarRing D] [Algebra ℝ D] [StarModule ℝ D]
    [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] (A : AssocCD D) :
    Function.Injective A.embed := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have hn : A.normSq a = 0 := by
    rw [← A.embed_normSq, ha, (octNormSq_eq_zero 0).mpr rfl]
  exact (A.normSq_eq_zero a).mp hn

theorem assocMatToAlbert_mem {D : Type} [Ring D] [StarRing D] [Algebra ℝ D] [StarModule ℝ D]
    [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] (A : AssocCD D)
    (M : Matrix (Fin 3) (Fin 3) D) :
    assocMatToAlbert A M ∈ (jordanSubalgebraH3 A.subalgebra).carrier := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [← A.range_embed]
  · exact ⟨M 0 1, rfl⟩
  · exact ⟨M 0 2, rfl⟩
  · exact ⟨M 1 2, rfl⟩

theorem albertMatrix_assocMatToAlbert {D : Type} [Ring D] [StarRing D] [Algebra ℝ D] [StarModule ℝ D]
    [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] (A : AssocCD D)
    {M : Matrix (Fin 3) (Fin 3) D} (hM : star M = M) (i j : Fin 3) :
    albertMatrix (assocMatToAlbert A M) i j = A.embed (M i j) := by
  have hMij : ∀ a b, star (M b a) = M a b := fun a b =>
    congrArg (fun N : Matrix (Fin 3) (Fin 3) D => N a b) hM
  have hdiag : ∀ k : Fin 3, octonionScalar (A.re (M k k)) = A.embed (M k k) := fun k => by
    rw [octonionScalar_eq_smul, ← octOne_eq_scalar, ← A.embed_one, ← A.embed.map_smul,
      ← A.re_smul_one (M k k) (hMij k k)]
  fin_cases i <;> fin_cases j <;> dsimp
  · exact hdiag 0
  · rfl
  · rfl
  · change octonionConj (A.embed (M 0 1)) = A.embed (M 1 0)
    rw [A.embed_star, hMij]
  · exact hdiag 1
  · rfl
  · change octonionConj (A.embed (M 0 2)) = A.embed (M 2 0)
    rw [A.embed_star, hMij]
  · change octonionConj (A.embed (M 1 2)) = A.embed (M 2 1)
    rw [A.embed_star, hMij]
  · exact hdiag 2

theorem jordanMul_assocMatToAlbert {D : Type} [Ring D] [StarRing D] [Algebra ℝ D] [StarModule ℝ D]
    [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] (A : AssocCD D)
    {M N : selfAdjoint (Matrix (Fin 3) (Fin 3) D)} :
    assocMatToAlbert A ((1 / 2 : ℝ) • ((M : Matrix (Fin 3) (Fin 3) D) * N + N * M)) =
      jordanMul (assocMatToAlbert A M) (assocMatToAlbert A N) := by
  have hmul : ∀ X Y : selfAdjoint (Matrix (Fin 3) (Fin 3) D), ∀ i j : Fin 3,
      octonionMatrixMul (albertMatrix (assocMatToAlbert A X)) (albertMatrix (assocMatToAlbert A Y)) i j =
        A.embed (((X : Matrix (Fin 3) (Fin 3) D) * Y) i j) := fun X Y i j => by
    unfold octonionMatrixMul
    simp only [albertMatrix_assocMatToAlbert A X.prop, albertMatrix_assocMatToAlbert A Y.prop,
      A.embed_mul, ← map_sum, Matrix.mul_apply]
  unfold jordanMul albertCoordinates
  apply albert_ext
  · change A.re (((1 / 2 : ℝ) • ((M : Matrix (Fin 3) (Fin 3) D) * N + N * M)) 0 0) =
      (1 / 2 : ℝ) * octonionReal _
    simp only [Pi.add_apply, Matrix.smul_apply, Matrix.add_apply, map_smul, map_add, smul_eq_mul]
    rw [hmul M N 0 0, hmul N M 0 0, ← A.embed.map_add, A.embed_re, map_add]
  · change A.re (((1 / 2 : ℝ) • ((M : Matrix (Fin 3) (Fin 3) D) * N + N * M)) 1 1) =
      (1 / 2 : ℝ) * octonionReal _
    simp only [Pi.add_apply, Matrix.smul_apply, Matrix.add_apply, map_smul, map_add, smul_eq_mul]
    rw [hmul M N 1 1, hmul N M 1 1, ← A.embed.map_add, A.embed_re, map_add]
  · change A.re (((1 / 2 : ℝ) • ((M : Matrix (Fin 3) (Fin 3) D) * N + N * M)) 2 2) =
      (1 / 2 : ℝ) * octonionReal _
    simp only [Pi.add_apply, Matrix.smul_apply, Matrix.add_apply, map_smul, map_add, smul_eq_mul]
    rw [hmul M N 2 2, hmul N M 2 2, ← A.embed.map_add, A.embed_re, map_add]
  · change A.embed (((1 / 2 : ℝ) • ((M : Matrix (Fin 3) (Fin 3) D) * N + N * M)) 0 1) =
      (1 / 2 : ℝ) • (_ + _)
    simp only [Matrix.smul_apply, Matrix.add_apply, map_smul, map_add]
    rw [hmul M N 0 1, hmul N M 0 1]
  · change A.embed (((1 / 2 : ℝ) • ((M : Matrix (Fin 3) (Fin 3) D) * N + N * M)) 0 2) =
      (1 / 2 : ℝ) • (_ + _)
    simp only [Matrix.smul_apply, Matrix.add_apply, map_smul, map_add]
    rw [hmul M N 0 2, hmul N M 0 2]
  · change A.embed (((1 / 2 : ℝ) • ((M : Matrix (Fin 3) (Fin 3) D) * N + N * M)) 1 2) =
      (1 / 2 : ℝ) • (_ + _)
    simp only [Matrix.smul_apply, Matrix.add_apply, map_smul, map_add]
    rw [hmul M N 1 2, hmul N M 1 2]

theorem tracePairing_assocMatToAlbert {D : Type} [Ring D] [StarRing D] [Algebra ℝ D] [StarModule ℝ D]
    [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] (A : AssocCD D)
    (M N : selfAdjoint (Matrix (Fin 3) (Fin 3) D)) :
    tracePairing (assocMatToAlbert A M) (assocMatToAlbert A N) =
      ∑ i : Fin 3, A.re (((M : Matrix (Fin 3) (Fin 3) D) * N) i i) := by
  unfold tracePairing
  rw [← jordanMul_assocMatToAlbert A]
  change (∑ i : Fin 3, A.re (((1 / 2 : ℝ) • ((M : Matrix (Fin 3) (Fin 3) D) * N + N * M)) i i)) = _
  have hcomm : ∑ i : Fin 3, A.re (((N : Matrix (Fin 3) (Fin 3) D) * M) i i) =
      ∑ i : Fin 3, A.re (((M : Matrix (Fin 3) (Fin 3) D) * N) i i) := by
    simp_rw [Matrix.mul_apply, map_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => A.re_mul_comm _ _
  simp only [Matrix.smul_apply, Matrix.add_apply, map_smul, map_add, smul_eq_mul,
    ← Finset.mul_sum, Finset.sum_add_distrib, hcomm]
  ring

def assocHermEquiv {D : Type} [Ring D] [StarRing D] [Algebra ℝ D] [StarModule ℝ D]
    [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] (A : AssocCD D) :
    selfAdjoint (Matrix (Fin 3) (Fin 3) D) ≃ₗ[ℝ] (jordanSubalgebraH3 A.subalgebra).carrier :=
  let toFunLM : selfAdjoint (Matrix (Fin 3) (Fin 3) D) →ₗ[ℝ] (jordanSubalgebraH3 A.subalgebra).carrier :=
    { toFun := fun M => ⟨assocMatToAlbert A M.1, assocMatToAlbert_mem A M.1⟩
      map_add' := fun M N => Subtype.ext (by
        apply albert_ext <;> simp [assocMatToAlbert] <;> rfl)
      map_smul' := fun r M => Subtype.ext (by
        apply albert_ext <;> simp [assocMatToAlbert] <;> rfl) }
  have hinj : Function.Injective toFunLM := by
    intro M N hMN
    have hv := congrArg Subtype.val hMN
    apply Subtype.ext
    funext i j
    have hMij : ∀ a b, star (M.1 b a) = M.1 a b := fun a b =>
      congrArg (fun X : Matrix (Fin 3) (Fin 3) D => X a b) M.prop
    have hNij : ∀ a b, star (N.1 b a) = N.1 a b := fun a b =>
      congrArg (fun X : Matrix (Fin 3) (Fin 3) D => X a b) N.prop
    have hd : ∀ k : Fin 3, M.1 k k = N.1 k k := fun k => by
      have hk := congrArg (fun x : Albert => x.1 k) hv
      change A.re (M.1 k k) = A.re (N.1 k k) at hk
      rw [A.re_smul_one _ (hMij k k), A.re_smul_one _ (hNij k k), hk]
    have h01 : M.1 0 1 = N.1 0 1 := assocCD_embed_injective A (congrArg (fun x : Albert => x.2 0) hv)
    have h02 : M.1 0 2 = N.1 0 2 := assocCD_embed_injective A (congrArg (fun x : Albert => x.2 1) hv)
    have h12 : M.1 1 2 = N.1 1 2 := assocCD_embed_injective A (congrArg (fun x : Albert => x.2 2) hv)
    fin_cases i <;> fin_cases j <;> dsimp
    · exact hd 0
    · exact h01
    · exact h02
    · rw [← hMij 1 0, ← hNij 1 0, h01]
    · exact hd 1
    · exact h12
    · rw [← hMij 2 0, ← hNij 2 0, h02]
    · rw [← hMij 2 1, ← hNij 2 1, h12]
    · exact hd 2
  have hsurj : Function.Surjective toFunLM := by
    rintro ⟨x, hx⟩
    have hx0 : x.2 0 ∈ LinearMap.range A.embed := by rw [A.range_embed]; exact hx.1
    have hx1 : x.2 1 ∈ LinearMap.range A.embed := by rw [A.range_embed]; exact hx.2.1
    have hx2 : x.2 2 ∈ LinearMap.range A.embed := by rw [A.range_embed]; exact hx.2.2
    obtain ⟨a01, ha01⟩ := hx0
    obtain ⟨a02, ha02⟩ := hx1
    obtain ⟨a12, ha12⟩ := hx2
    let M : Matrix (Fin 3) (Fin 3) D := fun i j =>
      if i = 0 ∧ j = 0 then (x.1 0) • (1 : D)
      else if i = 1 ∧ j = 1 then (x.1 1) • (1 : D)
      else if i = 2 ∧ j = 2 then (x.1 2) • (1 : D)
      else if i = 0 ∧ j = 1 then a01
      else if i = 1 ∧ j = 0 then star a01
      else if i = 0 ∧ j = 2 then a02
      else if i = 2 ∧ j = 0 then star a02
      else if i = 1 ∧ j = 2 then a12
      else star a12
    have hM : M ∈ selfAdjoint (Matrix (Fin 3) (Fin 3) D) := by
      rw [selfAdjoint.mem_iff]
      funext i j
      rw [Matrix.star_apply]
      fin_cases i <;> fin_cases j <;> dsimp [M] <;> simp [star_smul]
    refine ⟨⟨M, hM⟩, Subtype.ext ?_⟩
    apply albert_ext
    · change A.re ((x.1 0) • (1 : D)) = x.1 0; rw [map_smul, A.re_one, smul_eq_mul, mul_one]
    · change A.re ((x.1 1) • (1 : D)) = x.1 1; rw [map_smul, A.re_one, smul_eq_mul, mul_one]
    · change A.re ((x.1 2) • (1 : D)) = x.1 2; rw [map_smul, A.re_one, smul_eq_mul, mul_one]
    · exact ha01
    · exact ha02
    · exact ha12
  LinearEquiv.ofBijective toFunLM ⟨hinj, hsurj⟩

theorem assocHermEquiv_apply {D : Type} [Ring D] [StarRing D] [Algebra ℝ D] [StarModule ℝ D]
    [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] (A : AssocCD D)
    (M : selfAdjoint (Matrix (Fin 3) (Fin 3) D)) :
    (assocHermEquiv A M).1 = assocMatToAlbert A M.1 := rfl

theorem assocHermEquiv_one {D : Type} [Ring D] [StarRing D] [Algebra ℝ D] [StarModule ℝ D]
    [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] (A : AssocCD D) :
    (assocHermEquiv A 1).1 = albertUnit := by
  apply albert_ext
  · change A.re 1 = 1; exact A.re_one
  · change A.re 1 = 1; exact A.re_one
  · change A.re 1 = 1; exact A.re_one
  · change A.embed 0 = 0; exact map_zero A.embed
  · change A.embed 0 = 0; exact map_zero A.embed
  · change A.embed 0 = 0; exact map_zero A.embed

theorem assocHermEquiv_diagAtom {D : Type} [Ring D] [StarRing D] [Algebra ℝ D] [StarModule ℝ D]
    [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] (A : AssocCD D) (m : Fin 3) :
    let Emm : Matrix (Fin 3) (Fin 3) D := fun i j => if i = m ∧ j = m then 1 else 0
    have hE : Emm ∈ selfAdjoint (Matrix (Fin 3) (Fin 3) D) := by
      rw [selfAdjoint.mem_iff]; funext i j
      rw [Matrix.star_apply]
      dsimp [Emm]
      split_ifs with h1 h2 <;> simp_all
    (assocHermEquiv A ⟨Emm, hE⟩).1 = diagAtom m := by
  intro Emm hE
  apply albert_ext <;> fin_cases m <;>
    simp [assocHermEquiv_apply, assocMatToAlbert, Emm, diagAtom, A.re_one]

def assocCD_unitaryIso {D : Type} [Ring D] [StarRing D] [Algebra ℝ D] [StarModule ℝ D]
    [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] (A : AssocCD D)
    (U : Matrix (Fin 3) (Fin 3) D) (h1 : star U * U = 1) (h2 : U * star U = 1) :
    JordanSubalgebraIso (jordanSubalgebraH3 A.subalgebra) (jordanSubalgebraH3 A.subalgebra) :=
  let conjMat : selfAdjoint (Matrix (Fin 3) (Fin 3) D) ≃ₗ[ℝ] selfAdjoint (Matrix (Fin 3) (Fin 3) D) :=
    { toFun := fun M => ⟨star U * M.1 * U, by
        rw [selfAdjoint.mem_iff, star_mul, star_mul, star_star, M.prop, mul_assoc]⟩
      invFun := fun M => ⟨U * M.1 * star U, by
        rw [selfAdjoint.mem_iff, star_mul, star_mul, star_star, M.prop, mul_assoc]⟩
      left_inv := fun M => Subtype.ext (by
        calc
          U * (star U * M.1 * U) * star U = (U * star U) * M.1 * (U * star U) := by simp only [mul_assoc]
          _ = M.1 := by rw [h2, one_mul, mul_one])
      right_inv := fun M => Subtype.ext (by
        calc
          star U * (U * M.1 * star U) * U = (star U * U) * M.1 * (star U * U) := by simp only [mul_assoc]
          _ = M.1 := by rw [h1, one_mul, mul_one])
      map_add' := fun M N => Subtype.ext (by simp [mul_add, add_mul])
      map_smul' := fun r M => Subtype.ext (by simp) }
  { toLinearEquiv := (assocHermEquiv A).symm.trans (conjMat.trans (assocHermEquiv A))
    map_unit := by
      apply Subtype.ext
      have hunit : (assocHermEquiv A).symm ⟨albertUnit, (jordanSubalgebraH3 A.subalgebra).unit_mem⟩ = 1 :=
        (assocHermEquiv A).symm_apply_eq.mpr (Subtype.ext (assocHermEquiv_one A).symm)
      change (assocHermEquiv A (conjMat ((assocHermEquiv A).symm ⟨albertUnit, _⟩))).1 = albertUnit
      rw [hunit]
      have hc1 : conjMat 1 = 1 := Subtype.ext (by change star U * 1 * U = 1; rw [mul_one, h1])
      rw [hc1]
      exact assocHermEquiv_one A
    map_jordan := fun x y => by
      apply Subtype.ext
      set M := (assocHermEquiv A).symm x
      set N := (assocHermEquiv A).symm y
      have hMx : assocMatToAlbert A M.1 = x.1 :=
        congrArg Subtype.val ((assocHermEquiv A).apply_symm_apply x)
      have hNy : assocMatToAlbert A N.1 = y.1 :=
        congrArg Subtype.val ((assocHermEquiv A).apply_symm_apply y)
      have hP : jordanMul x.1 y.1 =
          assocMatToAlbert A ((1 / 2 : ℝ) • ((M : Matrix (Fin 3) (Fin 3) D) * N + N * M)) := by
        rw [jordanMul_assocMatToAlbert A, hMx, hNy]
      have hP_herm : (1 / 2 : ℝ) • ((M : Matrix (Fin 3) (Fin 3) D) * N + N * M) ∈
          selfAdjoint (Matrix (Fin 3) (Fin 3) D) := by
        rw [selfAdjoint.mem_iff, star_smul, star_add, star_mul, star_mul, M.prop, N.prop,
          star_trivial, add_comm]
      have hsymmP : (assocHermEquiv A).symm
          ⟨jordanMul x.1 y.1, (jordanSubalgebraH3 A.subalgebra).product_mem _ x.2 _ y.2⟩ =
          ⟨(1 / 2 : ℝ) • ((M : Matrix (Fin 3) (Fin 3) D) * N + N * M), hP_herm⟩ :=
        (assocHermEquiv A).symm_apply_eq.mpr (Subtype.ext hP)
      change (assocHermEquiv A (conjMat ((assocHermEquiv A).symm
        ⟨jordanMul x.1 y.1, _⟩))).1 =
        jordanMul (assocHermEquiv A (conjMat M)).1 (assocHermEquiv A (conjMat N)).1
      rw [hsymmP, assocHermEquiv_apply, assocHermEquiv_apply, assocHermEquiv_apply,
        ← jordanMul_assocMatToAlbert A]
      change assocMatToAlbert A (star U * ((1 / 2 : ℝ) • (M.1 * N.1 + N.1 * M.1)) * U) =
        assocMatToAlbert A ((1 / 2 : ℝ) • ((star U * M.1 * U) * (star U * N.1 * U) +
          (star U * N.1 * U) * (star U * M.1 * U)))
      congr 1
      have hmulMN : (star U * M.1 * U) * (star U * N.1 * U) = star U * (M.1 * N.1) * U := by
        calc
          (star U * M.1 * U) * (star U * N.1 * U)
            = star U * M.1 * (U * star U) * N.1 * U := by simp only [mul_assoc]
          _ = star U * (M.1 * N.1) * U := by rw [h2, mul_one]; simp only [mul_assoc]
      have hmulNM : (star U * N.1 * U) * (star U * M.1 * U) = star U * (N.1 * M.1) * U := by
        calc
          (star U * N.1 * U) * (star U * M.1 * U)
            = star U * N.1 * (U * star U) * M.1 * U := by simp only [mul_assoc]
          _ = star U * (N.1 * M.1) * U := by rw [h2, mul_one]; simp only [mul_assoc]
      simp only [hmulMN, hmulNM, mul_smul_comm, smul_mul_assoc, mul_add, add_mul] }

private theorem assocCD_atom_dyad_0 {D : Type} [Ring D] [StarRing D] [Algebra ℝ D] [StarModule ℝ D]
    [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] (A : AssocCD D)
    (M : selfAdjoint (Matrix (Fin 3) (Fin 3) D)) (hM : IsAtom (assocMatToAlbert A M.1))
    (h0 : 0 < A.re (M.1 0 0)) :
    ∃ u : Fin 3 → D, (∑ i : Fin 3, A.normSq (u i) = 1) ∧ ∀ i j : Fin 3, M.1 i j = u i * star (u j) := by
  let d0 := A.re (M.1 0 0)
  let s := Real.sqrt d0
  have hspos : 0 < s := Real.sqrt_pos.mpr h0
  have hsne : s ≠ 0 := hspos.ne'
  have hs2 : s * s = d0 := Real.mul_self_sqrt h0.le
  have hMij : ∀ a b, star (M.1 b a) = M.1 a b := fun a b =>
    congrArg (fun X : Matrix (Fin 3) (Fin 3) D => X a b) M.prop
  have hdiag : ∀ k : Fin 3, M.1 k k = A.re (M.1 k k) • (1 : D) := fun k => A.re_smul_one _ (hMij k k)
  have hsharp := albertSharp_of_isAtom hM
  have hs_fst1 : d0 * A.re (M.1 2 2) = A.normSq (M.1 0 2) := by
    have hz := congrArg (fun x : Albert => x.1 1) hsharp
    rw [albertSharp_fst_1, albert_zero_fst, assocMatToAlbert_fst, assocMatToAlbert_fst,
      assocMatToAlbert_snd_1, A.embed_normSq] at hz
    linarith
  have hs_fst2 : d0 * A.re (M.1 1 1) = A.normSq (M.1 0 1) := by
    have hz := congrArg (fun x : Albert => x.1 2) hsharp
    rw [albertSharp_fst_2, albert_zero_fst, assocMatToAlbert_fst, assocMatToAlbert_fst,
      assocMatToAlbert_snd_0, A.embed_normSq] at hz
    linarith
  have hs_snd2 : star (M.1 0 1) * M.1 0 2 = d0 • M.1 1 2 := by
    have hz := congrArg (fun x : Albert => x.2 2) hsharp
    rw [albertSharp_snd_2, albert_zero_snd, assocMatToAlbert_fst, assocMatToAlbert_snd_0,
      assocMatToAlbert_snd_1, assocMatToAlbert_snd_2, A.embed_star, A.embed_mul,
      ← A.embed.map_smul] at hz
    exact assocCD_embed_injective A (sub_eq_zero.mp hz)
  let u : Fin 3 → D := fun i => (1 / s) • M.1 i 0
  have hu_mul : ∀ i j : Fin 3, d0 • M.1 i j = M.1 i 0 * star (M.1 j 0) := fun i j => by
    fin_cases i <;> fin_cases j <;> dsimp
    · rw [hdiag 0, smul_smul, star_smul, star_trivial, star_one, smul_mul_smul_comm, one_mul]
    · rw [hdiag 0, smul_mul_assoc, one_mul, hMij 0 1]
    · rw [hdiag 0, smul_mul_assoc, one_mul, hMij 0 2]
    · conv_rhs => rw [hdiag 0, star_smul, star_trivial, star_one, mul_smul_comm, mul_one]
    · rw [hdiag 1, smul_smul, hs_fst2]
      have hnorm : A.normSq (M.1 1 0) = A.normSq (M.1 0 1) := by
        rw [← A.embed_normSq, ← A.embed_normSq, ← hMij 1 0, ← A.embed_star, octNormSq_conj]
      rw [← hnorm, ← A.mul_star_self (M.1 1 0)]
    · rw [← hs_snd2, hMij 1 0, hMij 0 2]
    · conv_rhs => rw [hdiag 0, star_smul, star_trivial, star_one, mul_smul_comm, mul_one]
    · have h21 := congrArg star hs_snd2
      rw [star_mul, star_star, star_smul, star_trivial d0, hMij 2 1, hMij 2 0, ← hMij 0 1] at h21
      exact h21.symm
    · rw [hdiag 2, smul_smul, hs_fst1]
      have hnorm : A.normSq (M.1 2 0) = A.normSq (M.1 0 2) := by
        rw [← A.embed_normSq, ← A.embed_normSq, ← hMij 2 0, ← A.embed_star, octNormSq_conj]
      rw [← hnorm, ← A.mul_star_self (M.1 2 0)]
  refine ⟨u, ?_, ?_⟩
  · have hu_norm : ∀ i : Fin 3, A.normSq (u i) = A.re (M.1 i i) := fun i => by
      have h1 : u i * star (u i) = A.re (M.1 i i) • (1 : D) := by
        change ((1 / s) • M.1 i 0) * star ((1 / s) • M.1 i 0) = _
        rw [star_smul, star_trivial, smul_mul_smul_comm, ← hu_mul i i, smul_smul]
        conv_lhs => rw [hdiag i, smul_smul]
        congr 1; rw [← hs2]; field_simp [hsne]
      have h2 := congrArg A.re h1
      rw [A.mul_star_self, map_smul, map_smul, A.re_one, smul_eq_mul, smul_eq_mul, mul_one, mul_one] at h2
      exact h2
    simp_rw [hu_norm]
    simpa [albertTrace, Fin.sum_univ_three, assocMatToAlbert_fst] using hM.2
  · intro i j
    have h1 := hu_mul i j
    change M.1 i j = ((1 / s) • M.1 i 0) * star ((1 / s) • M.1 j 0)
    rw [star_smul, star_trivial, smul_mul_smul_comm, ← h1, smul_smul]
    have hmul1 : (1 / s * (1 / s)) * d0 = 1 := by rw [← hs2]; field_simp [hsne]
    rw [hmul1, one_smul]

private def reindexHerm3 {D : Type} [Ring D] [StarRing D]
    (σ : Equiv.Perm (Fin 3)) (M : selfAdjoint (Matrix (Fin 3) (Fin 3) D)) :
    selfAdjoint (Matrix (Fin 3) (Fin 3) D) :=
  ⟨M.1.reindex σ σ, by
    rw [selfAdjoint.mem_iff]; funext i j
    rw [Matrix.star_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.submatrix_apply]
    exact congrArg (fun X : Matrix (Fin 3) (Fin 3) D => X (σ.symm i) (σ.symm j)) M.prop⟩

private theorem assocCD_atom_dyad {D : Type} [Ring D] [StarRing D] [Algebra ℝ D] [StarModule ℝ D]
    [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] (A : AssocCD D)
    (M : selfAdjoint (Matrix (Fin 3) (Fin 3) D)) (hM : IsAtom (assocMatToAlbert A M.1)) :
    ∃ u : Fin 3 → D, (∑ i : Fin 3, A.normSq (u i) = 1) ∧ ∀ i j : Fin 3, M.1 i j = u i * star (u j) := by
  have htr : A.re (M.1 0 0) + A.re (M.1 1 1) + A.re (M.1 2 2) = 1 := by
    simpa [albertTrace, Fin.sum_univ_three, assocMatToAlbert_fst] using hM.2
  have hpos : 0 < A.re (M.1 0 0) ∨ 0 < A.re (M.1 1 1) ∨ 0 < A.re (M.1 2 2) := by
    by_contra hnot
    push Not at hnot
    linarith [hnot.1, hnot.2.1, hnot.2.2]
  have perm_atom : ∀ (σ : Equiv.Perm (Fin 3)),
      IsAtom (assocMatToAlbert A (reindexHerm3 σ M).1) := fun σ => by
    let M' := reindexHerm3 σ M
    let e := Matrix.reindexAlgEquiv ℝ D σ
    have hMM : M.1 * M.1 = M.1 := by
      have hj : (assocHermEquiv A ⟨M.1 * M.1, by rw [selfAdjoint.mem_iff, star_mul, M.prop]⟩).1 =
          (assocHermEquiv A M).1 := by
        change assocMatToAlbert A (M.1 * M.1) = assocMatToAlbert A M.1
        have h12 : M.1 * M.1 = (1 / 2 : ℝ) • (M.1 * M.1 + M.1 * M.1) := by module
        rw [h12, jordanMul_assocMatToAlbert A]
        exact hM.1
      exact congrArg Subtype.val ((assocHermEquiv A).injective (Subtype.ext hj))
    have he_mul : M'.1 * M'.1 = M'.1 := by
      change (e M.1) * (e M.1) = e M.1
      rw [← map_mul, hMM]
    constructor
    · change jordanMul (assocMatToAlbert A M'.1) (assocMatToAlbert A M'.1) = assocMatToAlbert A M'.1
      have h12 : (1 / 2 : ℝ) • (M'.1 * M'.1 + M'.1 * M'.1) = M'.1 := by rw [he_mul]; module
      rw [← jordanMul_assocMatToAlbert A (M := M') (N := M'), h12]
    · have htr' : albertTrace (assocMatToAlbert A M'.1) = ∑ i : Fin 3, A.re (M'.1 i i) := by
        simp [albertTrace, Fin.sum_univ_three, assocMatToAlbert_fst]
      rw [htr']
      change ∑ i : Fin 3, A.re (M.1 (σ.symm i) (σ.symm i)) = 1
      rw [Equiv.sum_comp σ.symm (fun k => A.re (M.1 k k))]
      simpa [Fin.sum_univ_three] using htr
  rcases hpos with h0 | h1 | h2
  · exact assocCD_atom_dyad_0 A M hM h0
  · let σ := Equiv.swap (0 : Fin 3) 1
    obtain ⟨u', hu'norm, hu'eq⟩ := assocCD_atom_dyad_0 A (reindexHerm3 σ M) (perm_atom σ)
      (by simpa [reindexHerm3, σ] using h1)
    refine ⟨fun i => u' (σ i), ?_, fun i j => ?_⟩
    · rw [Equiv.sum_comp σ (fun k => A.normSq (u' k))]
      exact hu'norm
    · have h := hu'eq (σ i) (σ j)
      simpa [reindexHerm3, σ] using h
  · let σ := Equiv.swap (0 : Fin 3) 2
    obtain ⟨u', hu'norm, hu'eq⟩ := assocCD_atom_dyad_0 A (reindexHerm3 σ M) (perm_atom σ)
      (by simpa [reindexHerm3, σ] using h2)
    refine ⟨fun i => u' (σ i), ?_, fun i j => ?_⟩
    · rw [Equiv.sum_comp σ (fun k => A.normSq (u' k))]
      exact hu'norm
    · have h := hu'eq (σ i) (σ j)
      simpa [reindexHerm3, σ] using h

private theorem assocCD_frame_to_standard {D : Type} [Ring D] [StarRing D] [Algebra ℝ D] [StarModule ℝ D]
    [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] (A : AssocCD D)
    (F : NativeJordanFrame) (hF : ∀ m : Fin 3, F.atom m ∈ (jordanSubalgebraH3 A.subalgebra).carrier) :
    ∃ (U : Matrix (Fin 3) (Fin 3) D) (h1 : star U * U = 1) (h2 : U * star U = 1),
      ∀ m : Fin 3,
        ((assocCD_unitaryIso A U h1 h2).toLinearEquiv ⟨F.atom m, hF m⟩).1 = diagAtom m := by
  let M : Fin 3 → selfAdjoint (Matrix (Fin 3) (Fin 3) D) := fun m =>
    (assocHermEquiv A).symm ⟨F.atom m, hF m⟩
  have hMeq : ∀ m : Fin 3, assocMatToAlbert A (M m).1 = F.atom m := fun m =>
    congrArg Subtype.val ((assocHermEquiv A).apply_symm_apply ⟨F.atom m, hF m⟩)
  have hdyad : ∀ m : Fin 3, ∃ u : Fin 3 → D,
      (∑ i : Fin 3, A.normSq (u i) = 1) ∧ ∀ i j : Fin 3, (M m).1 i j = u i * star (u j) := fun m =>
    assocCD_atom_dyad A (M m) (by rw [hMeq m]; exact F.atoms m)
  choose u hu_norm hu_eq using hdyad
  let U : Matrix (Fin 3) (Fin 3) D := fun i m => u m i
  have hUUt : U * star U = 1 := by
    have hsumM : M 0 + M 1 + M 2 = 1 := by
      apply (assocHermEquiv A).injective
      rw [map_add, map_add]
      apply Subtype.ext
      change (assocHermEquiv A (M 0)).1 + (assocHermEquiv A (M 1)).1 + (assocHermEquiv A (M 2)).1 =
        (assocHermEquiv A 1).1
      rw [assocHermEquiv_apply, assocHermEquiv_apply, assocHermEquiv_apply,
        hMeq 0, hMeq 1, hMeq 2, assocHermEquiv_one A]
      simpa [Fin.sum_univ_three] using F.sum_unit
    funext i j
    change (∑ m : Fin 3, U i m * star (U j m)) = (1 : Matrix (Fin 3) (Fin 3) D) i j
    simp_rw [U, ← hu_eq _ i j, Fin.sum_univ_three]
    exact congrArg (fun X : selfAdjoint (Matrix (Fin 3) (Fin 3) D) => X.1 i j) hsumM
  have hUtU : star U * U = 1 := by
    funext m n
    by_cases hmn : m = n
    · subst hmn
      change ∑ i : Fin 3, star (u m i) * u m i = (1 : Matrix (Fin 3) (Fin 3) D) m m
      simp_rw [A.star_mul_self, ← Finset.sum_smul, hu_norm m, one_smul, Matrix.one_apply_eq]
    · have htp : tracePairing (F.atom m) (F.atom n) = 0 := by
        unfold tracePairing; rw [F.orthogonal m n hmn, albertTrace_zero]
      rw [← hMeq m, ← hMeq n, tracePairing_assocMatToAlbert A] at htp
      let c : D := ∑ i : Fin 3, star (u m i) * u n i
      have hnormc : A.normSq c = 0 := by
        have hcalc : (∑ i : Fin 3, A.re (((M m).1 * (M n).1) i i)) = A.normSq c := by
          have hmul_entry : ∀ i : Fin 3, ((M m).1 * (M n).1) i i =
              ∑ j : Fin 3, (u m i * star (u m j)) * (u n j * star (u n i)) := fun i => by
            simp_rw [Matrix.mul_apply, hu_eq]
          simp_rw [hmul_entry, map_sum]
          have hstep : ∀ i j : Fin 3,
              A.re ((u m i * star (u m j)) * (u n j * star (u n i))) =
                A.re ((star (u n i) * u m i) * (star (u m j) * u n j)) := fun i j => by
            rw [A.re_mul_comm (u m i * star (u m j)) (u n j * star (u n i))]
            have hassoc : (u n j * star (u n i)) * (u m i * star (u m j)) =
                u n j * ((star (u n i) * u m i) * star (u m j)) := by simp only [mul_assoc]
            rw [hassoc, A.re_mul_comm]
            simp only [mul_assoc]
          simp_rw [hstep, ← map_sum, ← Finset.mul_sum, ← Finset.sum_mul]
          have hstar : star c = ∑ i : Fin 3, star (u n i) * u m i := by
            dsimp [c]; rw [star_sum]
            refine Finset.sum_congr rfl fun _ _ => by rw [star_mul, star_star]
          have hsum_eq : (∑ i : Fin 3, star (u n i) * u m i) * ∑ j : Fin 3, star (u m j) * u n j =
              star c * c := by rw [hstar]
          rw [hsum_eq, A.star_mul_self, map_smul, A.re_one, smul_eq_mul, mul_one]
        linarith
      have hc0 := (A.normSq_eq_zero c).mp hnormc
      change c = (1 : Matrix (Fin 3) (Fin 3) D) m n
      rw [hc0, Matrix.one_apply_ne hmn]
  refine ⟨U, hUtU, hUUt, fun m => ?_⟩
  let Emm : Matrix (Fin 3) (Fin 3) D := fun i j => if i = m ∧ j = m then 1 else 0
  have hE : Emm ∈ selfAdjoint (Matrix (Fin 3) (Fin 3) D) := by
    rw [selfAdjoint.mem_iff]; funext i j
    rw [Matrix.star_apply]; dsimp [Emm]; split_ifs with h1 h2 <;> simp_all
  have hMU : (M m).1 = U * Emm * star U := by
    funext i j
    rw [hu_eq m i j]
    change u m i * star (u m j) = ∑ a : Fin 3, (∑ b : Fin 3, U i b * Emm b a) * star (U j a)
    have hinner : ∀ a : Fin 3, (∑ b : Fin 3, U i b * Emm b a) = if a = m then u m i else 0 := fun a => by
      dsimp [Emm, U]
      rw [Finset.sum_eq_single m]
      · by_cases ha : a = m <;> simp [ha]
      · intro b _ hb; simp [hb]
      · intro hm; exact False.elim (hm (Finset.mem_univ m))
    simp_rw [hinner]
    rw [Finset.sum_eq_single m]
    · simp [U]
    · intro a _ ha; simp [ha]
    · intro hm; exact False.elim (hm (Finset.mem_univ m))
  have hconj : star U * (M m).1 * U = Emm := by
    rw [hMU]
    calc
      star U * (U * Emm * star U) * U = (star U * U) * Emm * (star U * U) := by simp only [mul_assoc]
      _ = Emm := by rw [hUtU, one_mul, mul_one]
  change (assocHermEquiv A ⟨star U * (M m).1 * U, _⟩).1 = diagAtom m
  have hE_eq : (⟨star U * (M m).1 * U, by
      rw [selfAdjoint.mem_iff, star_mul, star_mul, star_star, (M m).prop, mul_assoc]⟩ :
      selfAdjoint (Matrix (Fin 3) (Fin 3) D)) = ⟨Emm, hE⟩ := Subtype.ext hconj
  rw [hE_eq]
  exact assocHermEquiv_diagAtom A m

private theorem assocCD_diag_unitary {D : Type} [Ring D] [StarRing D] [Algebra ℝ D] [StarModule ℝ D]
    [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] (A : AssocCD D)
    (d : Fin 3 → D) (hd : ∀ i : Fin 3, A.normSq (d i) = 1) :
    let U : Matrix (Fin 3) (Fin 3) D := Matrix.diagonal d
    star U * U = 1 ∧ U * star U = 1 := by
  intro U
  have h1 : ∀ i, star (d i) * d i = 1 := fun i => by rw [A.star_mul_self, hd i, one_smul]
  have h2 : ∀ i, d i * star (d i) = 1 := fun i => by rw [A.mul_star_self, hd i, one_smul]
  constructor
  · funext i j
    simp only [U, Matrix.mul_apply, Matrix.star_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij; simp [h1 i, Matrix.one_apply_eq]
    · simp [Ne.symm hij, Matrix.one_apply_ne hij]
  · funext i j
    simp only [U, Matrix.mul_apply, Matrix.star_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij; simp [h2 i, Matrix.one_apply_eq]
    · simp [Ne.symm hij, Matrix.one_apply_ne hij]

/-! ### Section 3.2: Unified `H3Subalgebra k` Automorphisms and `lem:five:line` -/

private theorem JordanSubalgebraIso.generated_map_eq {B₁ B₂ : NativeJordanSubalgebra}
    (ψ : JordanSubalgebraIso B₁ B₂) (S : Set B₁.carrier) :
    ∀ y : Albert,
      y ∈ (generatedSubalgebra (Subtype.val '' S)).carrier ↔
        ∃ y₁ : B₁.carrier, y = y₁.1 ∧
          (ψ.toLinearEquiv y₁).1 ∈
            (generatedSubalgebra ((fun z : B₁.carrier => (ψ.toLinearEquiv z).1) '' S)).carrier := by
  let X : Set Albert := Subtype.val '' S
  let Y : Set Albert := (fun z : B₁.carrier => (ψ.toLinearEquiv z).1) '' S
  have hXB : X ⊆ B₁.carrier := by rintro _ ⟨z, _, rfl⟩; exact z.2
  have hgen_le : generatedSubalgebra X ≤ B₁ := generatedSubalgebra_le hXB
  let Bpull : NativeJordanSubalgebra :=
    { carrier :=
        { carrier := {x : Albert | ∃ hx : x ∈ B₁.carrier,
            (ψ.toLinearEquiv ⟨x, hx⟩).1 ∈ (generatedSubalgebra Y).carrier}
          add_mem' := fun {a b} ⟨ha, ha'⟩ ⟨hb, hb'⟩ =>
            ⟨B₁.carrier.add_mem ha hb, by
              have heq : (⟨a + b, B₁.carrier.add_mem ha hb⟩ : B₁.carrier) =
                  ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
              rw [heq, map_add, Submodule.coe_add]
              exact (generatedSubalgebra Y).carrier.add_mem ha' hb'⟩
          zero_mem' := ⟨B₁.carrier.zero_mem, by
            have heq : (⟨0, B₁.carrier.zero_mem⟩ : B₁.carrier) = 0 := rfl
            rw [heq, map_zero, Submodule.coe_zero]
            exact (generatedSubalgebra Y).carrier.zero_mem⟩
          smul_mem' := fun r {a} ⟨ha, ha'⟩ =>
            ⟨B₁.carrier.smul_mem r ha, by
              have heq : (⟨r • a, B₁.carrier.smul_mem r ha⟩ : B₁.carrier) =
                  r • ⟨a, ha⟩ := rfl
              rw [heq, map_smul, Submodule.coe_smul]
              exact (generatedSubalgebra Y).carrier.smul_mem r ha'⟩ }
      unit_mem := ⟨B₁.unit_mem, by
        rw [ψ.map_unit]
        exact (generatedSubalgebra Y).unit_mem⟩
      product_mem := fun a ⟨ha, ha'⟩ b ⟨hb, hb'⟩ =>
        ⟨B₁.product_mem a ha b hb, by
          rw [ψ.map_jordan ⟨a, ha⟩ ⟨b, hb⟩]
          exact (generatedSubalgebra Y).product_mem _ ha' _ hb'⟩ }
  let Bpush : NativeJordanSubalgebra :=
    { carrier :=
        { carrier := {w : Albert | ∃ hw : w ∈ B₂.carrier,
            (ψ.toLinearEquiv.symm ⟨w, hw⟩).1 ∈ (generatedSubalgebra X).carrier}
          add_mem' := fun {a b} ⟨ha, ha'⟩ ⟨hb, hb'⟩ =>
            ⟨B₂.carrier.add_mem ha hb, by
              have heq : (⟨a + b, B₂.carrier.add_mem ha hb⟩ : B₂.carrier) =
                  ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
              rw [heq, map_add, Submodule.coe_add]
              exact (generatedSubalgebra X).carrier.add_mem ha' hb'⟩
          zero_mem' := ⟨B₂.carrier.zero_mem, by
            have heq : (⟨0, B₂.carrier.zero_mem⟩ : B₂.carrier) = 0 := rfl
            rw [heq, map_zero, Submodule.coe_zero]
            exact (generatedSubalgebra X).carrier.zero_mem⟩
          smul_mem' := fun r {a} ⟨ha, ha'⟩ =>
            ⟨B₂.carrier.smul_mem r ha, by
              have heq : (⟨r • a, B₂.carrier.smul_mem r ha⟩ : B₂.carrier) =
                  r • ⟨a, ha⟩ := rfl
              rw [heq, map_smul, Submodule.coe_smul]
              exact (generatedSubalgebra X).carrier.smul_mem r ha'⟩ }
      unit_mem := ⟨B₂.unit_mem, by
        change (ψ.symm.toLinearEquiv ⟨albertUnit, B₂.unit_mem⟩).1 ∈ (generatedSubalgebra X).carrier
        rw [ψ.symm.map_unit]
        exact (generatedSubalgebra X).unit_mem⟩
      product_mem := fun a ⟨ha, ha'⟩ b ⟨hb, hb'⟩ =>
        ⟨B₂.product_mem a ha b hb, by
          change ((ψ.symm).toLinearEquiv ⟨jordanMul a b, B₂.product_mem a ha b hb⟩).1 ∈ _
          rw [ψ.symm.map_jordan ⟨a, ha⟩ ⟨b, hb⟩]
          exact (generatedSubalgebra X).product_mem _ ha' _ hb'⟩ }
  have hX_pull : generatedSubalgebra X ≤ Bpull := generatedSubalgebra_le (by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨z.2, subset_generatedSubalgebra Y ⟨z, hz, rfl⟩⟩)
  have hY_push : generatedSubalgebra Y ≤ Bpush := generatedSubalgebra_le (by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨(ψ.toLinearEquiv z).2, ?_⟩
    rw [LinearEquiv.symm_apply_apply]
    exact subset_generatedSubalgebra X ⟨z, hz, rfl⟩)
  intro y
  constructor
  · intro hy
    obtain ⟨hyB, hyY⟩ := hX_pull hy
    exact ⟨⟨y, hyB⟩, rfl, hyY⟩
  · rintro ⟨y₁, rfl, hyY⟩
    obtain ⟨hwB, hyX⟩ := hY_push hyY
    have hsub : (⟨(ψ.toLinearEquiv y₁).1, hwB⟩ : B₂.carrier) = ψ.toLinearEquiv y₁ := rfl
    rw [hsub, LinearEquiv.symm_apply_apply] at hyX
    exact hyX

private theorem diag_conj_entry {D : Type} [Ring D] [StarRing D]
    (d : Fin 3 → D) (M : Matrix (Fin 3) (Fin 3) D) (i j : Fin 3) :
    (star (Matrix.diagonal d) * M * Matrix.diagonal d) i j = star (d i) * M i j * d j := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single j]
  · simp only [Matrix.diagonal_apply_eq]
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · simp [Matrix.star_apply, Matrix.diagonal_apply_eq]
    · intro l _ hl
      rw [Matrix.star_apply, Matrix.diagonal_apply_ne d hl, star_zero, zero_mul]
    · intro hi; exact False.elim (hi (Finset.mem_univ i))
  · intro k _ hk
    simp [Matrix.diagonal_apply_ne d hk]
  · intro hj; exact False.elim (hj (Finset.mem_univ j))

private theorem assocCD_normSq_smul {D : Type} [Ring D] [StarRing D] [Algebra ℝ D] [StarModule ℝ D]
    [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] (A : AssocCD D) (r : ℝ) (a : D) :
    A.normSq (r • a) = r ^ 2 * A.normSq a := by
  rw [← A.embed_normSq, map_smul, octNormSq_smul, A.embed_normSq]

private theorem assocCD_diag_unitaryIso_apply {D : Type} [Ring D] [StarRing D] [Algebra ℝ D] [StarModule ℝ D]
    [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] (A : AssocCD D)
    (d : Fin 3 → D) (hd : ∀ i : Fin 3, A.normSq (d i) = 1)
    (x : (jordanSubalgebraH3 A.subalgebra).carrier) :
    let U : Matrix (Fin 3) (Fin 3) D := Matrix.diagonal d
    let hU := assocCD_diag_unitary A d hd
    let α := assocCD_unitaryIso A U hU.1 hU.2
    let M := (assocHermEquiv A).symm x
    (α.toLinearEquiv x).1 = assocMatToAlbert A (star U * M.1 * U) := rfl

private theorem assocCD_diag_unitaryIso_fixes_diag {D : Type} [Ring D] [StarRing D] [Algebra ℝ D] [StarModule ℝ D]
    [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] (A : AssocCD D)
    (d : Fin 3 → D) (hd : ∀ i : Fin 3, A.normSq (d i) = 1) (m : Fin 3) :
    let U : Matrix (Fin 3) (Fin 3) D := Matrix.diagonal d
    let hU := assocCD_diag_unitary A d hd
    let α := assocCD_unitaryIso A U hU.1 hU.2
    (α.toLinearEquiv ⟨diagAtom m, diagAtom_mem_jordanSubalgebraH3 A.subalgebra m⟩).1 = diagAtom m := by
  intro U hU α
  let M := (assocHermEquiv A).symm ⟨diagAtom m, diagAtom_mem_jordanSubalgebraH3 A.subalgebra m⟩
  have hMeq : assocMatToAlbert A M.1 = diagAtom m :=
    congrArg Subtype.val ((assocHermEquiv A).apply_symm_apply _)
  have hMij : ∀ a b, star (M.1 b a) = M.1 a b := fun a b =>
    congrArg (fun X : Matrix (Fin 3) (Fin 3) D => X a b) M.prop
  have hd_entry : ∀ k : Fin 3, M.1 k k = (if k = m then (1 : ℝ) else 0) • (1 : D) := fun k => by
    rw [A.re_smul_one _ (hMij k k)]
    have hk := congrArg (fun a : Albert => a.1 k) hMeq
    change A.re (M.1 k k) = (diagAtom m).1 k at hk
    rw [hk, diagAtom_fst]
  have h01 : M.1 0 1 = 0 := assocCD_embed_injective A (by
    have h := congrArg (fun a : Albert => a.2 0) hMeq
    rw [assocMatToAlbert_snd_0, diagAtom_snd] at h; rw [h, map_zero])
  have h02 : M.1 0 2 = 0 := assocCD_embed_injective A (by
    have h := congrArg (fun a : Albert => a.2 1) hMeq
    rw [assocMatToAlbert_snd_1, diagAtom_snd] at h; rw [h, map_zero])
  have h12 : M.1 1 2 = 0 := assocCD_embed_injective A (by
    have h := congrArg (fun a : Albert => a.2 2) hMeq
    rw [assocMatToAlbert_snd_2, diagAtom_snd] at h; rw [h, map_zero])
  rw [assocCD_diag_unitaryIso_apply A d hd]
  have h1 : ∀ i, star (d i) * d i = 1 := fun i => by rw [A.star_mul_self, hd i, one_smul]
  apply albert_ext
  · change A.re ((star (Matrix.diagonal d) * M.1 * Matrix.diagonal d) 0 0) = (diagAtom m).1 0
    rw [diag_conj_entry, hd_entry 0]; split_ifs with hm
    · rw [one_smul, mul_one, h1 0, A.re_one]; simp [diagAtom_fst, hm]
    · simp [hm, diagAtom_fst]
  · change A.re ((star (Matrix.diagonal d) * M.1 * Matrix.diagonal d) 1 1) = (diagAtom m).1 1
    rw [diag_conj_entry, hd_entry 1]; split_ifs with hm
    · rw [one_smul, mul_one, h1 1, A.re_one]; simp [diagAtom_fst, hm]
    · simp [hm, diagAtom_fst]
  · change A.re ((star (Matrix.diagonal d) * M.1 * Matrix.diagonal d) 2 2) = (diagAtom m).1 2
    rw [diag_conj_entry, hd_entry 2]; split_ifs with hm
    · rw [one_smul, mul_one, h1 2, A.re_one]; simp [diagAtom_fst, hm]
    · simp [hm, diagAtom_fst]
  · change A.embed ((star (Matrix.diagonal d) * M.1 * Matrix.diagonal d) 0 1) = 0
    rw [diag_conj_entry, h01, mul_zero, zero_mul, map_zero]
  · change A.embed ((star (Matrix.diagonal d) * M.1 * Matrix.diagonal d) 0 2) = 0
    rw [diag_conj_entry, h02, mul_zero, zero_mul, map_zero]
  · change A.embed ((star (Matrix.diagonal d) * M.1 * Matrix.diagonal d) 1 2) = 0
    rw [diag_conj_entry, h12, mul_zero, zero_mul, map_zero]

private theorem assocCD_diag_unitaryIso_fixes_slot12_one {D : Type} [Ring D] [StarRing D] [Algebra ℝ D] [StarModule ℝ D]
    [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] (A : AssocCD D)
    (d : Fin 3 → D) (hd : ∀ i : Fin 3, A.normSq (d i) = 1) (hd1 : d 1 = 1) (hd2 : d 2 = 1) :
    let U : Matrix (Fin 3) (Fin 3) D := Matrix.diagonal d
    let hU := assocCD_diag_unitary A d hd
    let α := assocCD_unitaryIso A U hU.1 hU.2
    have hmem : slotElem12 octOne ∈ (jordanSubalgebraH3 A.subalgebra).carrier := by
      refine ⟨A.subalgebra.carrier.zero_mem, A.subalgebra.carrier.zero_mem, A.subalgebra.one_mem⟩
    (α.toLinearEquiv ⟨slotElem12 octOne, hmem⟩).1 = slotElem12 octOne := by
  intro U hU α hmem
  let M := (assocHermEquiv A).symm ⟨slotElem12 octOne, hmem⟩
  have hMeq : assocMatToAlbert A M.1 = slotElem12 octOne :=
    congrArg Subtype.val ((assocHermEquiv A).apply_symm_apply _)
  have hMij : ∀ a b, star (M.1 b a) = M.1 a b := fun a b =>
    congrArg (fun X : Matrix (Fin 3) (Fin 3) D => X a b) M.prop
  have hdk : ∀ k : Fin 3, M.1 k k = 0 := fun k => by
    rw [A.re_smul_one _ (hMij k k)]
    have hk := congrArg (fun a : Albert => a.1 k) hMeq
    change A.re (M.1 k k) = 0 at hk
    rw [hk, zero_smul]
  have h01 : M.1 0 1 = 0 := assocCD_embed_injective A (by
    have h := congrArg (fun a : Albert => a.2 0) hMeq
    rw [assocMatToAlbert_snd_0, slotElem12_snd_0] at h; rw [h, map_zero])
  have h02 : M.1 0 2 = 0 := assocCD_embed_injective A (by
    have h := congrArg (fun a : Albert => a.2 1) hMeq
    rw [assocMatToAlbert_snd_1, slotElem12_snd_1] at h; rw [h, map_zero])
  have h12 : M.1 1 2 = 1 := assocCD_embed_injective A (by
    have h := congrArg (fun a : Albert => a.2 2) hMeq
    rw [assocMatToAlbert_snd_2, slotElem12_snd_2, ← A.embed_one] at h; exact h)
  rw [assocCD_diag_unitaryIso_apply A d hd]
  apply albert_ext
  · change A.re ((star (Matrix.diagonal d) * M.1 * Matrix.diagonal d) 0 0) = 0
    rw [diag_conj_entry, hdk 0, mul_zero, zero_mul, map_zero]
  · change A.re ((star (Matrix.diagonal d) * M.1 * Matrix.diagonal d) 1 1) = 0
    rw [diag_conj_entry, hdk 1, mul_zero, zero_mul, map_zero]
  · change A.re ((star (Matrix.diagonal d) * M.1 * Matrix.diagonal d) 2 2) = 0
    rw [diag_conj_entry, hdk 2, mul_zero, zero_mul, map_zero]
  · change A.embed ((star (Matrix.diagonal d) * M.1 * Matrix.diagonal d) 0 1) = 0
    rw [diag_conj_entry, h01, mul_zero, zero_mul, map_zero]
  · change A.embed ((star (Matrix.diagonal d) * M.1 * Matrix.diagonal d) 0 2) = 0
    rw [diag_conj_entry, h02, mul_zero, zero_mul, map_zero]
  · change A.embed ((star (Matrix.diagonal d) * M.1 * Matrix.diagonal d) 1 2) = octOne
    rw [diag_conj_entry, hd1, hd2, h12, star_one, one_mul, mul_one, A.embed_one]

private theorem assocCD_diag_unitaryIso_fixes_slot01_one {D : Type} [Ring D] [StarRing D] [Algebra ℝ D] [StarModule ℝ D]
    [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] (A : AssocCD D)
    (d : Fin 3 → D) (hd : ∀ i : Fin 3, A.normSq (d i) = 1) (hd0 : d 0 = 1) (hd1 : d 1 = 1) :
    let U : Matrix (Fin 3) (Fin 3) D := Matrix.diagonal d
    let hU := assocCD_diag_unitary A d hd
    let α := assocCD_unitaryIso A U hU.1 hU.2
    have hmem : slotElem01 octOne ∈ (jordanSubalgebraH3 A.subalgebra).carrier := by
      refine ⟨A.subalgebra.one_mem, A.subalgebra.carrier.zero_mem, A.subalgebra.carrier.zero_mem⟩
    (α.toLinearEquiv ⟨slotElem01 octOne, hmem⟩).1 = slotElem01 octOne := by
  intro U hU α hmem
  let M := (assocHermEquiv A).symm ⟨slotElem01 octOne, hmem⟩
  have hMeq : assocMatToAlbert A M.1 = slotElem01 octOne :=
    congrArg Subtype.val ((assocHermEquiv A).apply_symm_apply _)
  have hMij : ∀ a b, star (M.1 b a) = M.1 a b := fun a b =>
    congrArg (fun X : Matrix (Fin 3) (Fin 3) D => X a b) M.prop
  have hdk : ∀ k : Fin 3, M.1 k k = 0 := fun k => by
    rw [A.re_smul_one _ (hMij k k)]
    have hk := congrArg (fun a : Albert => a.1 k) hMeq
    change A.re (M.1 k k) = 0 at hk
    rw [hk, zero_smul]
  have h01 : M.1 0 1 = 1 := assocCD_embed_injective A (by
    have h := congrArg (fun a : Albert => a.2 0) hMeq
    rw [assocMatToAlbert_snd_0, slotElem01_snd_0, ← A.embed_one] at h; exact h)
  have h02 : M.1 0 2 = 0 := assocCD_embed_injective A (by
    have h := congrArg (fun a : Albert => a.2 1) hMeq
    rw [assocMatToAlbert_snd_1, slotElem01_snd_1] at h; rw [h, map_zero])
  have h12 : M.1 1 2 = 0 := assocCD_embed_injective A (by
    have h := congrArg (fun a : Albert => a.2 2) hMeq
    rw [assocMatToAlbert_snd_2, slotElem01_snd_2] at h; rw [h, map_zero])
  rw [assocCD_diag_unitaryIso_apply A d hd]
  apply albert_ext
  · change A.re ((star (Matrix.diagonal d) * M.1 * Matrix.diagonal d) 0 0) = 0
    rw [diag_conj_entry, hdk 0, mul_zero, zero_mul, map_zero]
  · change A.re ((star (Matrix.diagonal d) * M.1 * Matrix.diagonal d) 1 1) = 0
    rw [diag_conj_entry, hdk 1, mul_zero, zero_mul, map_zero]
  · change A.re ((star (Matrix.diagonal d) * M.1 * Matrix.diagonal d) 2 2) = 0
    rw [diag_conj_entry, hdk 2, mul_zero, zero_mul, map_zero]
  · change A.embed ((star (Matrix.diagonal d) * M.1 * Matrix.diagonal d) 0 1) = octOne
    rw [diag_conj_entry, hd0, hd1, h01, star_one, one_mul, mul_one, A.embed_one]
  · change A.embed ((star (Matrix.diagonal d) * M.1 * Matrix.diagonal d) 0 2) = 0
    rw [diag_conj_entry, h02, mul_zero, zero_mul, map_zero]
  · change A.embed ((star (Matrix.diagonal d) * M.1 * Matrix.diagonal d) 1 2) = 0
    rw [diag_conj_entry, h12, mul_zero, zero_mul, map_zero]

private theorem assocCD_unit_mul_left_real {D : Type} [Ring D] [StarRing D] [Algebra ℝ D] [StarModule ℝ D]
    [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] (A : AssocCD D) (z : D) :
    ∃ (u : D) (r : ℝ), A.normSq u = 1 ∧ 0 ≤ r ∧ A.embed (star u * z) = octonionScalar r := by
  by_cases hz : z = 0
  · refine ⟨1, 0, by rw [← A.embed_normSq, A.embed_one, octNormSq_one], le_rfl, ?_⟩
    rw [hz, mul_zero, map_zero, octonionScalar_zero]
  · have hpos : 0 < A.normSq z :=
      lt_of_le_of_ne (A.normSq_nonneg z) (Ne.symm fun h => hz ((A.normSq_eq_zero z).mp h))
    let r := Real.sqrt (A.normSq z)
    have hrpos : 0 < r := Real.sqrt_pos.mpr hpos
    have hr2 : r ^ 2 = A.normSq z := Real.sq_sqrt hpos.le
    let u := (1 / r) • z
    refine ⟨u, r, ?_, hrpos.le, ?_⟩
    · rw [assocCD_normSq_smul, one_div, inv_pow, hr2]; field_simp [hrpos.ne']
    · have hmul : star u * z = r • (1 : D) := by
        dsimp [u]
        rw [star_smul, star_trivial, smul_mul_assoc, A.star_mul_self, smul_smul, ← hr2]
        congr 1; field_simp [hrpos.ne']
      rw [hmul, map_smul, A.embed_one, octOne_eq_scalar, ← octonionScalar_eq_smul]

private theorem assocCD_unit_mul_right_real {D : Type} [Ring D] [StarRing D] [Algebra ℝ D] [StarModule ℝ D]
    [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] (A : AssocCD D) (z : D) :
    ∃ (u : D) (r : ℝ), A.normSq u = 1 ∧ 0 ≤ r ∧ A.embed (z * star u) = octonionScalar r := by
  by_cases hz : z = 0
  · refine ⟨1, 0, by rw [← A.embed_normSq, A.embed_one, octNormSq_one], le_rfl, ?_⟩
    rw [hz, zero_mul, map_zero, octonionScalar_zero]
  · have hpos : 0 < A.normSq z :=
      lt_of_le_of_ne (A.normSq_nonneg z) (Ne.symm fun h => hz ((A.normSq_eq_zero z).mp h))
    let r := Real.sqrt (A.normSq z)
    have hrpos : 0 < r := Real.sqrt_pos.mpr hpos
    have hr2 : r ^ 2 = A.normSq z := Real.sq_sqrt hpos.le
    let u := (1 / r) • z
    refine ⟨u, r, ?_, hrpos.le, ?_⟩
    · rw [assocCD_normSq_smul, one_div, inv_pow, hr2]; field_simp [hrpos.ne']
    · have hmul : z * star u = r • (1 : D) := by
        dsimp [u]
        rw [star_smul, star_trivial, mul_smul_comm, A.mul_star_self, smul_smul, ← hr2]
        congr 1; field_simp [hrpos.ne']
      rw [hmul, map_smul, A.embed_one, octOne_eq_scalar, ← octonionScalar_eq_smul]

private theorem assocCD_frameStab_slot12_real {D : Type} [Ring D] [StarRing D] [Algebra ℝ D] [StarModule ℝ D]
    [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] (A : AssocCD D)
    (x : Albert) (hx : x ∈ (jordanSubalgebraH3 A.subalgebra).carrier) :
    ∃ (α : JordanSubalgebraIso (jordanSubalgebraH3 A.subalgebra) (jordanSubalgebraH3 A.subalgebra)),
      (∀ i, (α.toLinearEquiv ⟨diagAtom i, diagAtom_mem_jordanSubalgebraH3 A.subalgebra i⟩).1 = diagAtom i) ∧
      ∃ r : ℝ, 0 ≤ r ∧ (α.toLinearEquiv ⟨x, hx⟩).1.2 2 = octonionScalar r := by
  let M := (assocHermEquiv A).symm ⟨x, hx⟩
  obtain ⟨u, r, hu, hr, hmul⟩ := assocCD_unit_mul_left_real A (M.1 1 2)
  let d : Fin 3 → D := ![1, u, 1]
  have hd : ∀ i, A.normSq (d i) = 1 := fun i => by
    fin_cases i <;> dsimp [d] <;> [rw [← A.embed_normSq, A.embed_one, octNormSq_one]; exact hu;
      rw [← A.embed_normSq, A.embed_one, octNormSq_one]]
  let U := Matrix.diagonal d
  let hU := assocCD_diag_unitary A d hd
  let α := assocCD_unitaryIso A U hU.1 hU.2
  refine ⟨α, fun i => assocCD_diag_unitaryIso_fixes_diag A d hd i, r, hr, ?_⟩
  have hmul_eq : A.embed (star u * M.1 1 2) = octonionScalar r := hmul
  rw [assocCD_diag_unitaryIso_apply A d hd, assocMatToAlbert_snd_2, diag_conj_entry]
  change A.embed (star (d 1) * M.1 1 2 * d 2) = octonionScalar r
  simpa [d] using hmul_eq

private theorem assocCD_frameStab_slot01_real {D : Type} [Ring D] [StarRing D] [Algebra ℝ D] [StarModule ℝ D]
    [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] (A : AssocCD D)
    (x : Albert) (hx : x ∈ (jordanSubalgebraH3 A.subalgebra).carrier) :
    ∃ (α : JordanSubalgebraIso (jordanSubalgebraH3 A.subalgebra) (jordanSubalgebraH3 A.subalgebra)),
      (∀ i, (α.toLinearEquiv ⟨diagAtom i, diagAtom_mem_jordanSubalgebraH3 A.subalgebra i⟩).1 = diagAtom i) ∧
      ∃ r : ℝ, 0 ≤ r ∧ (α.toLinearEquiv ⟨x, hx⟩).1.2 0 = octonionScalar r := by
  let M := (assocHermEquiv A).symm ⟨x, hx⟩
  obtain ⟨u, r, hu, hr, hmul⟩ := assocCD_unit_mul_left_real A (M.1 0 1)
  let d : Fin 3 → D := ![u, 1, 1]
  have hd : ∀ i, A.normSq (d i) = 1 := fun i => by
    fin_cases i <;> dsimp [d] <;> [exact hu;
      rw [← A.embed_normSq, A.embed_one, octNormSq_one];
      rw [← A.embed_normSq, A.embed_one, octNormSq_one]]
  let U := Matrix.diagonal d
  let hU := assocCD_diag_unitary A d hd
  let α := assocCD_unitaryIso A U hU.1 hU.2
  refine ⟨α, fun i => assocCD_diag_unitaryIso_fixes_diag A d hd i, r, hr, ?_⟩
  rw [assocCD_diag_unitaryIso_apply A d hd, assocMatToAlbert_snd_0, diag_conj_entry]
  simpa [d] using hmul

private theorem assocCD_frameAnd12OneStab_slot02_real {D : Type} [Ring D] [StarRing D] [Algebra ℝ D] [StarModule ℝ D]
    [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] (A : AssocCD D)
    (x : Albert) (hx : x ∈ (jordanSubalgebraH3 A.subalgebra).carrier) :
    ∃ (α : JordanSubalgebraIso (jordanSubalgebraH3 A.subalgebra) (jordanSubalgebraH3 A.subalgebra)),
      (∀ i, (α.toLinearEquiv ⟨diagAtom i, diagAtom_mem_jordanSubalgebraH3 A.subalgebra i⟩).1 = diagAtom i) ∧
      (∀ h12 : slotElem12 octOne ∈ (jordanSubalgebraH3 A.subalgebra).carrier,
        (α.toLinearEquiv ⟨slotElem12 octOne, h12⟩).1 = slotElem12 octOne) ∧
      ∃ r : ℝ, 0 ≤ r ∧ (α.toLinearEquiv ⟨x, hx⟩).1.2 1 = octonionScalar r := by
  let M := (assocHermEquiv A).symm ⟨x, hx⟩
  obtain ⟨u, r, hu, hr, hmul⟩ := assocCD_unit_mul_left_real A (M.1 0 2)
  let d : Fin 3 → D := ![u, 1, 1]
  have hd : ∀ i, A.normSq (d i) = 1 := fun i => by
    fin_cases i <;> dsimp [d] <;> [exact hu;
      rw [← A.embed_normSq, A.embed_one, octNormSq_one];
      rw [← A.embed_normSq, A.embed_one, octNormSq_one]]
  let U := Matrix.diagonal d
  let hU := assocCD_diag_unitary A d hd
  let α := assocCD_unitaryIso A U hU.1 hU.2
  refine ⟨α, fun i => assocCD_diag_unitaryIso_fixes_diag A d hd i,
    fun _ => assocCD_diag_unitaryIso_fixes_slot12_one A d hd rfl rfl, r, hr, ?_⟩
  rw [assocCD_diag_unitaryIso_apply A d hd, assocMatToAlbert_snd_1, diag_conj_entry]
  simpa [d] using hmul

private theorem assocCD_frameAnd01OneStab_slot12_real {D : Type} [Ring D] [StarRing D] [Algebra ℝ D] [StarModule ℝ D]
    [IsScalarTower ℝ D D] [SMulCommClass ℝ D D] (A : AssocCD D)
    (x : Albert) (hx : x ∈ (jordanSubalgebraH3 A.subalgebra).carrier) :
    ∃ (α : JordanSubalgebraIso (jordanSubalgebraH3 A.subalgebra) (jordanSubalgebraH3 A.subalgebra)),
      (∀ i, (α.toLinearEquiv ⟨diagAtom i, diagAtom_mem_jordanSubalgebraH3 A.subalgebra i⟩).1 = diagAtom i) ∧
      (∀ h01 : slotElem01 octOne ∈ (jordanSubalgebraH3 A.subalgebra).carrier,
        (α.toLinearEquiv ⟨slotElem01 octOne, h01⟩).1 = slotElem01 octOne) ∧
      ∃ r : ℝ, 0 ≤ r ∧ (α.toLinearEquiv ⟨x, hx⟩).1.2 2 = octonionScalar r := by
  let M := (assocHermEquiv A).symm ⟨x, hx⟩
  obtain ⟨u, r, hu, hr, hmul⟩ := assocCD_unit_mul_right_real A (M.1 1 2)
  let d : Fin 3 → D := ![1, 1, star u]
  have hd : ∀ i, A.normSq (d i) = 1 := fun i => by
    fin_cases i <;> dsimp [d]
    · rw [← A.embed_normSq, A.embed_one, octNormSq_one]
    · rw [← A.embed_normSq, A.embed_one, octNormSq_one]
    · rw [← A.embed_normSq, ← A.embed_star, octNormSq_conj, A.embed_normSq, hu]
  let U := Matrix.diagonal d
  let hU := assocCD_diag_unitary A d hd
  let α := assocCD_unitaryIso A U hU.1 hU.2
  refine ⟨α, fun i => assocCD_diag_unitaryIso_fixes_diag A d hd i,
    fun _ => assocCD_diag_unitaryIso_fixes_slot01_one A d hd rfl rfl, r, hr, ?_⟩
  have hmul_eq : A.embed (M.1 1 2 * star u) = octonionScalar r := hmul
  rw [assocCD_diag_unitaryIso_apply A d hd, assocMatToAlbert_snd_2, diag_conj_entry]
  change A.embed (star (d 1) * M.1 1 2 * d 2) = octonionScalar r
  simpa [d] using hmul_eq

private theorem exists_frameAnd12OneStab_slot02_real (x : Albert) :
    ∃ g : NativeAlbertAutomorphism,
      (∀ i, g.linearEquiv (diagAtom i) = diagAtom i) ∧
      g.linearEquiv (slotElem12 octOne) = slotElem12 octOne ∧
      ∃ r : ℝ, 0 ≤ r ∧ (g.linearEquiv x).2 1 = octonionScalar r := by
  obtain ⟨h, hdiag, h01, r, hr, hslot⟩ :=
    exists_frameAnd01OneStab_slot02_real (swap02AlbertAuto.linearEquiv x)
  let g := (swap02AlbertAuto.comp h).comp swap02AlbertAuto
  refine ⟨g, ?_, ?_, r, hr, ?_⟩
  · intro i
    change swap02AlbertAuto.linearEquiv (h.linearEquiv (swap02AlbertAuto.linearEquiv (diagAtom i))) =
      diagAtom i
    rw [swap02AlbertAuto_diagAtom, hdiag, swap02AlbertAuto_diagAtom]
    simp
  · have hswap02_12 : swap02AlbertAuto.linearEquiv (slotElem12 octOne) = slotElem01 octOne := by
      rw [swap02AlbertAuto_apply]
      apply albert_ext <;> simp [slotElem12_fst, slotElem12_snd_0, slotElem12_snd_1, slotElem12_snd_2,
        slotElem01_fst, slotElem01_snd_0, slotElem01_snd_1, slotElem01_snd_2, octonionConj_one,
        octonionConj_zero]
    have hswap02_01 : swap02AlbertAuto.linearEquiv (slotElem01 octOne) = slotElem12 octOne := by
      rw [swap02AlbertAuto_apply]
      apply albert_ext <;> simp [slotElem12_fst, slotElem12_snd_0, slotElem12_snd_1, slotElem12_snd_2,
        slotElem01_fst, slotElem01_snd_0, slotElem01_snd_1, slotElem01_snd_2, octonionConj_one,
        octonionConj_zero]
    change swap02AlbertAuto.linearEquiv (h.linearEquiv (swap02AlbertAuto.linearEquiv (slotElem12 octOne))) =
      slotElem12 octOne
    rw [hswap02_12, h01, hswap02_01]
  · change (swap02AlbertAuto.linearEquiv (h.linearEquiv (swap02AlbertAuto.linearEquiv x))).2 1 =
      octonionScalar r
    rw [swap02AlbertAuto_apply]
    change octonionConj ((h.linearEquiv (swap02AlbertAuto.linearEquiv x)).2 1) = octonionScalar r
    rw [hslot, octonionConj_scalar]

private theorem exists_h3Auto_frame (k : CDLevel) (F : NativeJordanFrame)
    (hF : ∀ m : Fin 3, F.atom m ∈ (H3Subalgebra k).carrier) :
    ∃ α : JordanSubalgebraIso (H3Subalgebra k) (H3Subalgebra k),
      ∀ m : Fin 3, (α.toLinearEquiv ⟨F.atom m, hF m⟩).1 = diagAtom m := by
  cases k with
  | R =>
    obtain ⟨U, h1, h2, h⟩ := assocCD_frame_to_standard assocCD_R F hF
    exact ⟨assocCD_unitaryIso assocCD_R U h1 h2, h⟩
  | C =>
    obtain ⟨U, h1, h2, h⟩ := assocCD_frame_to_standard assocCD_C F hF
    exact ⟨assocCD_unitaryIso assocCD_C U h1 h2, h⟩
  | H =>
    obtain ⟨U, h1, h2, h⟩ := assocCD_frame_to_standard assocCD_H F hF
    exact ⟨assocCD_unitaryIso assocCD_H U h1 h2, h⟩
  | O =>
    obtain ⟨g, hg⟩ := native_frame_to_standardFrame F
    exact ⟨JordanSubalgebraIso.ofAutoOnTop g, hg⟩

private theorem exists_h3Auto_frameStab_slot12_real (k : CDLevel) (x : Albert)
    (hx : x ∈ (H3Subalgebra k).carrier) :
    ∃ α : JordanSubalgebraIso (H3Subalgebra k) (H3Subalgebra k),
      (∀ i, (α.toLinearEquiv ⟨diagAtom i, diagAtom_mem_H3Subalgebra k i⟩).1 = diagAtom i) ∧
      ∃ r : ℝ, 0 ≤ r ∧ (α.toLinearEquiv ⟨x, hx⟩).1.2 2 = octonionScalar r := by
  cases k with
  | R => exact assocCD_frameStab_slot12_real assocCD_R x hx
  | C => exact assocCD_frameStab_slot12_real assocCD_C x hx
  | H => exact assocCD_frameStab_slot12_real assocCD_H x hx
  | O =>
    obtain ⟨g, hdiag, r, hr, hslot⟩ := exists_frameStab_slot12_real x
    exact ⟨JordanSubalgebraIso.ofAutoOnTop g, hdiag, r, hr, hslot⟩

private theorem exists_h3Auto_frameStab_slot01_real (k : CDLevel) (x : Albert)
    (hx : x ∈ (H3Subalgebra k).carrier) :
    ∃ α : JordanSubalgebraIso (H3Subalgebra k) (H3Subalgebra k),
      (∀ i, (α.toLinearEquiv ⟨diagAtom i, diagAtom_mem_H3Subalgebra k i⟩).1 = diagAtom i) ∧
      ∃ r : ℝ, 0 ≤ r ∧ (α.toLinearEquiv ⟨x, hx⟩).1.2 0 = octonionScalar r := by
  cases k with
  | R => exact assocCD_frameStab_slot01_real assocCD_R x hx
  | C => exact assocCD_frameStab_slot01_real assocCD_C x hx
  | H => exact assocCD_frameStab_slot01_real assocCD_H x hx
  | O =>
    obtain ⟨g, hdiag, r, hr, hslot⟩ := exists_frameStab_slot01_real x
    exact ⟨JordanSubalgebraIso.ofAutoOnTop g, hdiag, r, hr, hslot⟩

private theorem exists_h3Auto_frameAnd12OneStab_slot02_real (k : CDLevel) (x : Albert)
    (hx : x ∈ (H3Subalgebra k).carrier) :
    ∃ α : JordanSubalgebraIso (H3Subalgebra k) (H3Subalgebra k),
      (∀ i, (α.toLinearEquiv ⟨diagAtom i, diagAtom_mem_H3Subalgebra k i⟩).1 = diagAtom i) ∧
      (∀ h12 : slotElem12 octOne ∈ (H3Subalgebra k).carrier,
        (α.toLinearEquiv ⟨slotElem12 octOne, h12⟩).1 = slotElem12 octOne) ∧
      ∃ r : ℝ, 0 ≤ r ∧ (α.toLinearEquiv ⟨x, hx⟩).1.2 1 = octonionScalar r := by
  cases k with
  | R => exact assocCD_frameAnd12OneStab_slot02_real assocCD_R x hx
  | C => exact assocCD_frameAnd12OneStab_slot02_real assocCD_C x hx
  | H => exact assocCD_frameAnd12OneStab_slot02_real assocCD_H x hx
  | O =>
    obtain ⟨g, hdiag, h12, r, hr, hslot⟩ := exists_frameAnd12OneStab_slot02_real x
    exact ⟨JordanSubalgebraIso.ofAutoOnTop g, hdiag, fun _ => h12, r, hr, hslot⟩

private theorem exists_h3Auto_frameAnd01OneStab_slot12_real (k : CDLevel) (x : Albert)
    (hx : x ∈ (H3Subalgebra k).carrier) :
    ∃ α : JordanSubalgebraIso (H3Subalgebra k) (H3Subalgebra k),
      (∀ i, (α.toLinearEquiv ⟨diagAtom i, diagAtom_mem_H3Subalgebra k i⟩).1 = diagAtom i) ∧
      (∀ h01 : slotElem01 octOne ∈ (H3Subalgebra k).carrier,
        (α.toLinearEquiv ⟨slotElem01 octOne, h01⟩).1 = slotElem01 octOne) ∧
      ∃ r : ℝ, 0 ≤ r ∧ (α.toLinearEquiv ⟨x, hx⟩).1.2 2 = octonionScalar r := by
  cases k with
  | R => exact assocCD_frameAnd01OneStab_slot12_real assocCD_R x hx
  | C => exact assocCD_frameAnd01OneStab_slot12_real assocCD_C x hx
  | H => exact assocCD_frameAnd01OneStab_slot12_real assocCD_H x hx
  | O =>
    obtain ⟨g, hdiag, h01, r, hr, hslot⟩ := exists_frameAnd01OneStab_slot12_real x
    exact ⟨JordanSubalgebraIso.ofAutoOnTop g, hdiag, fun _ => h01, r, hr, hslot⟩

private theorem slotElem12_octOne_mem_H3Subalgebra (k : CDLevel) :
    slotElem12 octOne ∈ (H3Subalgebra k).carrier :=
  ⟨(octSubalgebraOfLevel k).carrier.zero_mem, (octSubalgebraOfLevel k).carrier.zero_mem,
   (octSubalgebraOfLevel k).one_mem⟩

private theorem slotElem01_octOne_mem_H3Subalgebra (k : CDLevel) :
    slotElem01 octOne ∈ (H3Subalgebra k).carrier :=
  ⟨(octSubalgebraOfLevel k).one_mem, (octSubalgebraOfLevel k).carrier.zero_mem,
   (octSubalgebraOfLevel k).carrier.zero_mem⟩

private theorem slotElem02_octOne_mem_H3Subalgebra (k : CDLevel) :
    slotElem02 octOne ∈ (H3Subalgebra k).carrier :=
  ⟨(octSubalgebraOfLevel k).carrier.zero_mem, (octSubalgebraOfLevel k).one_mem,
   (octSubalgebraOfLevel k).carrier.zero_mem⟩

private theorem auto_map_quadraticMap (g : NativeAlbertAutomorphism) (x y : Albert) :
    g.linearEquiv (quadraticMap x y) = quadraticMap (g.linearEquiv x) (g.linearEquiv y) := by
  unfold quadraticMap
  rw [map_sub, map_nsmul, g.preserves_product, g.preserves_product, g.preserves_product, g.preserves_product]

private theorem tracePairing_comm_albert (x y : Albert) :
    tracePairing x y = tracePairing y x := by
  unfold tracePairing
  rw [jordanMul_comm]

private theorem tracePairing_atom_bounds {p q : Albert} (hp : IsAtom p) (hq : IsAtom q) :
    0 ≤ tracePairing p q ∧ tracePairing p q ≤ 1 := by
  obtain ⟨g, hg⟩ := atom_to_diagAtom0 q hq
  let p' := g.linearEquiv p
  have hp' : IsAtom p' := g.map_isAtom hp
  have htp : tracePairing p q = p'.1 0 := by
    rw [← tracePairing_diagAtom0 p', ← hg, g.map_tracePairing, tracePairing_comm_albert]
  rw [htp]
  exact ⟨isAtom_diag_nonneg hp' 0, isAtom_diag_le_one hp' 0⟩

private theorem diag1_ortho_atom_coords {a : Albert} (ha : IsAtom a)
    (h1 : jordanMul (diagAtom 1) a = 0) :
    a.1 1 = 0 ∧ a.2 0 = 0 ∧ a.2 2 = 0 ∧ a.1 0 + a.1 2 = 1 ∧
      a.1 0 * a.1 2 = octNormSq (a.2 1) := by
  let b := swap01AlbertAuto.linearEquiv a
  have hb : IsAtom b := swap01AlbertAuto.map_isAtom ha
  have hb0 : jordanMul (diagAtom 0) b = 0 := by
    have hs : swap01AlbertAuto.linearEquiv (diagAtom 1) = diagAtom 0 := by
      rw [swap01AlbertAuto_diagAtom]; rfl
    rw [← hs, ← swap01AlbertAuto.preserves_product, h1, map_zero]
  have hbc := diag0_ortho_atom_coords hb hb0
  have hba : b = (![a.1 1, a.1 0, a.1 2], ![octonionConj (a.2 0), a.2 2, a.2 1]) :=
    swap01AlbertAuto_apply a
  rw [hba] at hbc
  refine ⟨hbc.1, ?_, hbc.2.2.2.1, hbc.2.1, hbc.2.2.2.2.symm⟩
  simpa [octonionConj_conj, octonionConj_zero] using congrArg octonionConj hbc.2.2.1

theorem lem_five_line (k : CDLevel) {n : ℕ} (hn : 2 ≤ n)
    (q : Albert) (hq : IsAtom q) (hqK : q ∈ (H3Subalgebra k).carrier)
    (p : Albert) (hp : IsAtom p) (hpK : p ∈ (H3Subalgebra k).carrier)
    (hp_off : p ∉ (lineSubalgebra q hq).carrier)
    (s : Fin n → Albert) (hs_inj : Function.Injective s)
    (hs_atom : ∀ m, IsAtom (s m)) (hs_mem : ∀ m, s m ∈ (H3Subalgebra k).carrier)
    (hs_line : ∀ m, jordanMul q (s m) = 0)
    (hr_ne : ∀ m, s m ≠ (albertTrace (quadraticMap (albertUnit - q) p))⁻¹ • quadraticMap (albertUnit - q) p ∧
                  s m ≠ (albertUnit - q) - (albertTrace (quadraticMap (albertUnit - q) p))⁻¹ • quadraticMap (albertUnit - q) p) :
  ∃ (α : JordanSubalgebraIso (H3Subalgebra k) (H3Subalgebra k))
    (a : ℝ) (γ : Fin n → ℝ) (x : Fin n → Octonion),
    0 < a ∧ a < 1 ∧
    (∀ m, x m ∈ (octSubalgebraOfLevel k).carrier ∧ x m ≠ 0) ∧
    (∃ r₀ : ℝ, 0 < r₀ ∧ x ⟨0, by omega⟩ = octonionScalar r₀) ∧
    (α.toLinearEquiv ⟨q, hqK⟩).1 = diagAtom 1 ∧
    (let r := (albertTrace (quadraticMap (albertUnit - q) p))⁻¹ • quadraticMap (albertUnit - q) p
     ∃ hrK : r ∈ (H3Subalgebra k).carrier, (α.toLinearEquiv ⟨r, hrK⟩).1 = diagAtom 2) ∧
    (α.toLinearEquiv ⟨p, hpK⟩).1 =
      a • diagAtom 1 + (1 - a) • diagAtom 2 + slotElem12 (octonionScalar (Real.sqrt (a * (1 - a)))) ∧
    (∀ m, (α.toLinearEquiv ⟨s m, hs_mem m⟩).1 =
      γ m • diagAtom 0 + (1 - γ m) • diagAtom 2 + slotElem02 (x m)) ∧
    ∃ F : OctSubalgebra,
      F.carrier ≤ (octSubalgebraOfLevel k).carrier ∧
      (∀ m, m ≠ ⟨0, by omega⟩ → x m ∈ F.carrier) ∧
      (∀ G : OctSubalgebra, (∀ m, m ≠ ⟨0, by omega⟩ → x m ∈ G.carrier) → F.carrier ≤ G.carrier) ∧
      (∀ y : Albert, y ∈ (generatedSubalgebra (insert p (Set.range s))).carrier ↔
        ∃ yK : (H3Subalgebra k).carrier, y = yK.1 ∧ (α.toLinearEquiv yK).1 ∈ (jordanSubalgebraH3 F).carrier) := by
  let f := albertUnit - q
  let w := quadraticMap f p
  let t := albertTrace w
  let r := t⁻¹ • w
  let fr := f - r
  obtain ⟨g0, hg0⟩ := atom_to_diagAtom0 q hq
  let p0 := g0.linearEquiv p
  have hp0 : IsAtom p0 := g0.map_isAtom hp
  have hp0_sum : p0.1 0 + p0.1 1 + p0.1 2 = 1 := by
    simpa [albertTrace, Fin.sum_univ_three] using hp0.2
  have hgw : g0.linearEquiv w = (![0, p0.1 1, p0.1 2], ![0, 0, p0.2 2]) := by
    change g0.linearEquiv (quadraticMap (albertUnit - q) p) = _
    rw [auto_map_quadraticMap, map_sub, g0.preserves_unit, hg0]
    exact quadraticMap_compl_diagAtom0 p0
  have ht_val : t = 1 - p0.1 0 := by
    change albertTrace w = 1 - p0.1 0
    rw [← g0.preserves_trace w, hgw]
    simp only [albertTrace, Fin.sum_univ_three]
    dsimp
    linarith
  have hp0_d0_ne0 : p0.1 0 ≠ 0 := by
    intro h0
    have htp : tracePairing q p = 0 := by
      rw [← g0.map_tracePairing q p, hg0, tracePairing_diagAtom0]; exact h0
    have hj : jordanMul q p = 0 :=
      (support_of_atom_zero_pairing acceptedAtomAndRankOneBridge hq ⟨p, hp.1.symm⟩ htp).1
    apply hp_off
    rw [mem_lineSubalgebra_iff, hj, htp, zero_smul]
  have hp0_d0_ne1 : p0.1 0 ≠ 1 := by
    intro h1
    have hd1 : p0.1 1 = 0 := by
      have hnn1 := isAtom_diag_nonneg hp0 1
      have hnn2 := isAtom_diag_nonneg hp0 2
      linarith
    have hd2 : p0.1 2 = 0 := by linarith
    have hsharp := albertSharp_of_isAtom hp0
    have ho0 : p0.2 0 = 0 := (octNormSq_eq_zero _).mp (by
      have h := congrArg (fun a : Albert => a.1 2) hsharp
      rw [albertSharp_fst_2, albert_zero_fst, h1, hd1, mul_zero, zero_sub, neg_eq_zero] at h
      exact h)
    have ho1 : p0.2 1 = 0 := (octNormSq_eq_zero _).mp (by
      have h := congrArg (fun a : Albert => a.1 1) hsharp
      rw [albertSharp_fst_1, albert_zero_fst, h1, hd2, mul_zero, zero_sub, neg_eq_zero] at h
      exact h)
    have ho2 : p0.2 2 = 0 := (octNormSq_eq_zero _).mp (by
      have h := congrArg (fun a : Albert => a.1 0) hsharp
      rw [albertSharp_fst_0, albert_zero_fst, hd1, hd2, mul_zero, zero_sub, neg_eq_zero] at h
      exact h)
    have hp0_eq : p0 = diagAtom 0 := albert_ext h1 hd1 hd2 ho0 ho1 ho2
    have hpq : p = q := g0.linearEquiv.injective (by rw [hg0]; exact hp0_eq)
    apply hp_off
    rw [hpq]
    exact (mem_lineSubalgebra_iff q hq q).mpr (by
      rw [hq.1]; unfold tracePairing; rw [hq.1, hq.2, one_smul])
  have hp0_d0_pos : 0 < p0.1 0 := lt_of_le_of_ne (isAtom_diag_nonneg hp0 0) (Ne.symm hp0_d0_ne0)
  have hp0_d0_lt1 : p0.1 0 < 1 := lt_of_le_of_ne (isAtom_diag_le_one hp0 0) hp0_d0_ne1
  have ht_pos : 0 < t := by rw [ht_val]; linarith
  have hw_props := compl_atom_compress_sq hq hp
  have hr_atom : IsAtom r := by
    constructor
    · change jordanMul (t⁻¹ • w) (t⁻¹ • w) = t⁻¹ • w
      rw [jordanMul_smul_left, jordanMul_smul_right, hw_props.1, smul_smul, smul_smul]
      have ht : albertTrace (quadraticMap (albertUnit - q) p) = t := rfl
      rw [ht]
      congr 1; field_simp [ht_pos.ne']
    · change albertTrace (t⁻¹ • w) = 1
      rw [albertTrace_smul]; exact inv_mul_cancel₀ ht_pos.ne'
  have hqr : jordanMul q r = 0 := by
    change jordanMul q (t⁻¹ • w) = 0
    rw [jordanMul_smul_right, hw_props.2.2.2, smul_zero]
  have hfr_atom : IsAtom fr := by
    constructor
    · change jordanMul (albertUnit - q - r) (albertUnit - q - r) = albertUnit - q - r
      simp only [jordanMul_sub_left, jordanMul_sub_right, jordanMul_albertUnit_left,
        jordanMul_albertUnit_right, hq.1, hr_atom.1, hqr,
        show jordanMul r q = 0 from by rw [jordanMul_comm]; exact hqr]
      abel
    · change albertTrace (albertUnit - q - r) = 1
      have hau : albertTrace albertUnit = 3 := by simp [albertTrace, albertUnit]
      rw [albertTrace_sub, albertTrace_sub, hau, hq.2, hr_atom.2]; norm_num
  have hqfr : jordanMul q fr = 0 := by
    change jordanMul q (albertUnit - q - r) = 0
    rw [jordanMul_sub_right, jordanMul_sub_right, jordanMul_albertUnit_right, hq.1, hqr, sub_self, sub_zero]
  have hrfr : jordanMul r fr = 0 := by
    change jordanMul r (albertUnit - q - r) = 0
    rw [jordanMul_sub_right, jordanMul_sub_right, jordanMul_albertUnit_right,
      show jordanMul r q = 0 from by rw [jordanMul_comm]; exact hqr, hr_atom.1]
    abel
  let Frm : NativeJordanFrame :=
    { atom := ![fr, q, r]
      atoms := fun m => by fin_cases m <;> dsimp <;> [exact hfr_atom; exact hq; exact hr_atom]
      orthogonal := fun i j hij => by
        fin_cases i <;> fin_cases j <;> dsimp
        · exact absurd rfl hij
        · rw [jordanMul_comm]; exact hqfr
        · rw [jordanMul_comm]; exact hrfr
        · exact hqfr
        · exact absurd rfl hij
        · exact hqr
        · exact hrfr
        · rw [jordanMul_comm]; exact hqr
        · exact absurd rfl hij
      sum_unit := by
        rw [Fin.sum_univ_three]
        change fr + q + r = albertUnit
        dsimp [fr, f]; abel }
  have hfK : f ∈ (H3Subalgebra k).carrier := (H3Subalgebra k).carrier.sub_mem (H3Subalgebra k).unit_mem hqK
  have hwK : w ∈ (H3Subalgebra k).carrier := (peirce_components_mem_subalgebra (H3Subalgebra k) hqK hpK).2.2
  have hrK : r ∈ (H3Subalgebra k).carrier := (H3Subalgebra k).carrier.smul_mem _ hwK
  have hfrK : fr ∈ (H3Subalgebra k).carrier := (H3Subalgebra k).carrier.sub_mem hfK hrK
  have hFrm_mem : ∀ m : Fin 3, Frm.atom m ∈ (H3Subalgebra k).carrier := fun m => by
    fin_cases m <;> dsimp [Frm] <;> [exact hfrK; exact hqK; exact hrK]
  have hfr_p : jordanMul fr p = 0 := by
    have htp : tracePairing fr p = 0 := by
      have hgfr : g0.linearEquiv fr = (albertUnit - diagAtom 0) - t⁻¹ • g0.linearEquiv w := by
        dsimp [fr, f, r]
        rw [map_sub, map_sub, g0.preserves_unit, hg0, map_smul]
      rw [← g0.map_tracePairing fr p, hgfr, tracePairing_sub_left, tracePairing_sub_left,
        tracePairing_smul_left, hgw]
      rw [show tracePairing albertUnit p0 = 1 by
        rw [tracePairing_eq_coords]
        simp [albertUnit_fst, albertUnit_snd, octDot_zero_left, hp0_sum]]
      rw [show tracePairing (diagAtom 0) p0 = p0.1 0 from tracePairing_diagAtom0 p0]
      let zw : Albert := (![0, p0.1 1, p0.1 2], ![0, 0, p0.2 2])
      have hzw : tracePairing zw p0 =
          p0.1 1 * p0.1 1 + p0.1 2 * p0.1 2 + 2 * octDot (p0.2 2) (p0.2 2) := by
        rw [tracePairing_eq_coords]
        simp [zw, octDot_zero_left]
      change 1 - p0.1 0 - t⁻¹ * tracePairing zw p0 = 0
      rw [hzw, octDot_self]
      have hsharp0 := congrArg (fun a : Albert => a.1 0) (albertSharp_of_isAtom hp0)
      rw [albertSharp_fst_0, albert_zero_fst, sub_eq_zero] at hsharp0
      rw [← hsharp0]
      have h12sum : p0.1 1 + p0.1 2 = t := by linarith
      field_simp [ht_pos.ne']
      rw [← ht_val, ← h12sum]; ring
    exact (support_of_atom_zero_pairing acceptedAtomAndRankOneBridge hfr_atom ⟨p, hp.1.symm⟩ htp).1
  obtain ⟨α₀, hα₀⟩ := exists_h3Auto_frame k Frm hFrm_mem
  have hα₀_fr : (α₀.toLinearEquiv ⟨fr, hfrK⟩).1 = diagAtom 0 := hα₀ 0
  have hα₀_q : (α₀.toLinearEquiv ⟨q, hqK⟩).1 = diagAtom 1 := hα₀ 1
  have hα₀_r : (α₀.toLinearEquiv ⟨r, hrK⟩).1 = diagAtom 2 := hα₀ 2
  obtain ⟨α₁, hα₁_diag, r1, hr1_nn, hα₁_slot12⟩ :=
    exists_h3Auto_frameStab_slot12_real k (α₀.toLinearEquiv ⟨p, hpK⟩).1 (α₀.toLinearEquiv ⟨p, hpK⟩).2
  let i₀ : Fin n := ⟨0, by omega⟩
  let α01 := α₀.trans α₁
  obtain ⟨α₂, hα₂_diag, hα₂_12, r0, hr0_nn, hα₂_slot02⟩ :=
    exists_h3Auto_frameAnd12OneStab_slot02_real k
      (α01.toLinearEquiv ⟨s i₀, hs_mem i₀⟩).1 (α01.toLinearEquiv ⟨s i₀, hs_mem i₀⟩).2
  let α := α01.trans α₂
  have hα_fr : (α.toLinearEquiv ⟨fr, hfrK⟩).1 = diagAtom 0 := by
    change (α₂.toLinearEquiv (α₁.toLinearEquiv (α₀.toLinearEquiv ⟨fr, hfrK⟩))).1 = diagAtom 0
    have h1 : α₀.toLinearEquiv ⟨fr, hfrK⟩ = ⟨diagAtom 0, diagAtom_mem_H3Subalgebra k 0⟩ :=
      Subtype.ext hα₀_fr
    have h2 : α₁.toLinearEquiv ⟨diagAtom 0, diagAtom_mem_H3Subalgebra k 0⟩ =
        ⟨diagAtom 0, diagAtom_mem_H3Subalgebra k 0⟩ := Subtype.ext (hα₁_diag 0)
    rw [h1, h2]; exact hα₂_diag 0
  have hα_q : (α.toLinearEquiv ⟨q, hqK⟩).1 = diagAtom 1 := by
    change (α₂.toLinearEquiv (α₁.toLinearEquiv (α₀.toLinearEquiv ⟨q, hqK⟩))).1 = diagAtom 1
    have h1 : α₀.toLinearEquiv ⟨q, hqK⟩ = ⟨diagAtom 1, diagAtom_mem_H3Subalgebra k 1⟩ :=
      Subtype.ext hα₀_q
    have h2 : α₁.toLinearEquiv ⟨diagAtom 1, diagAtom_mem_H3Subalgebra k 1⟩ =
        ⟨diagAtom 1, diagAtom_mem_H3Subalgebra k 1⟩ := Subtype.ext (hα₁_diag 1)
    rw [h1, h2]; exact hα₂_diag 1
  have hα_r : (α.toLinearEquiv ⟨r, hrK⟩).1 = diagAtom 2 := by
    change (α₂.toLinearEquiv (α₁.toLinearEquiv (α₀.toLinearEquiv ⟨r, hrK⟩))).1 = diagAtom 2
    have h1 : α₀.toLinearEquiv ⟨r, hrK⟩ = ⟨diagAtom 2, diagAtom_mem_H3Subalgebra k 2⟩ :=
      Subtype.ext hα₀_r
    have h2 : α₁.toLinearEquiv ⟨diagAtom 2, diagAtom_mem_H3Subalgebra k 2⟩ =
        ⟨diagAtom 2, diagAtom_mem_H3Subalgebra k 2⟩ := Subtype.ext (hα₁_diag 2)
    rw [h1, h2]; exact hα₂_diag 2
  let p1 := (α01.toLinearEquiv ⟨p, hpK⟩).1
  have hp1_atom : IsAtom p1 := iso_maps_atom α01 ⟨p, hpK⟩ hp
  have hp1_fr : jordanMul (diagAtom 0) p1 = 0 := by
    have h0 : (α01.toLinearEquiv ⟨fr, hfrK⟩).1 = diagAtom 0 := by
      change (α₁.toLinearEquiv (α₀.toLinearEquiv ⟨fr, hfrK⟩)).1 = diagAtom 0
      rw [show α₀.toLinearEquiv ⟨fr, hfrK⟩ = ⟨diagAtom 0, diagAtom_mem_H3Subalgebra k 0⟩ from Subtype.ext hα₀_fr]
      exact hα₁_diag 0
    rw [← h0, ← α01.map_jordanMul_eq ⟨fr, hfrK⟩ ⟨p, hpK⟩]
    have h0' : (⟨jordanMul fr p, (H3Subalgebra k).product_mem _ hfrK _ hpK⟩ :
        (H3Subalgebra k).carrier) = 0 := Subtype.ext hfr_p
    rw [h0', map_zero, Submodule.coe_zero]
  have hp1_coords := diag0_ortho_atom_coords hp1_atom hp1_fr
  let a : ℝ := p1.1 1
  have hp1_form : p1 = a • diagAtom 1 + (1 - a) • diagAtom 2 + slotElem12 (octonionScalar r1) := by
    apply albert_ext
    · simp [albert_add_fst, albert_smul_fst, diagAtom_fst, slotElem12_fst, hp1_coords.1]
    · simp [albert_add_fst, albert_smul_fst, diagAtom_fst, slotElem12_fst, a]
    · simp [albert_add_fst, albert_smul_fst, diagAtom_fst, slotElem12_fst]; linarith [hp1_coords.2.1]
    · simp [albert_add_snd, albert_smul_snd, diagAtom_snd, slotElem12_snd_0]
      exact hp1_coords.2.2.1
    · simp [albert_add_snd, albert_smul_snd, diagAtom_snd, slotElem12_snd_1]
      exact hp1_coords.2.2.2.1
    · simp [albert_add_snd, albert_smul_snd, diagAtom_snd, slotElem12_snd_2]
      exact hα₁_slot12
  have ha_nonneg : 0 ≤ a := isAtom_diag_nonneg hp1_atom 1
  have ha_le1 : a ≤ 1 := isAtom_diag_le_one hp1_atom 1
  have ha_ne0 : a ≠ 0 := by
    intro ha0
    have hr1_0 : r1 = 0 := by
      have hsq : r1 ^ 2 = 0 := by
        have hns := hp1_coords.2.2.2.2
        rw [show p1.2 2 = octonionScalar r1 from hα₁_slot12, show p1.1 1 = a from rfl,
          show p1.1 2 = 1 - a by linarith [hp1_coords.2.1], ha0, zero_mul,
          octonionScalar_eq_smul, ← octOne_eq_scalar, octNormSq_smul, octNormSq_one, mul_one] at hns
        exact hns
      exact sq_eq_zero_iff.mp hsq
    have hp1_d2 : p1 = diagAtom 2 := by
      rw [hp1_form, ha0, hr1_0, octonionScalar_zero, zero_smul, sub_zero, one_smul, zero_add]
      have hs0 : slotElem12 (0 : Octonion) = 0 := by apply albert_ext <;> rfl
      rw [hs0, add_zero]
    have hpr : p = r := by
      have hsub : α01.toLinearEquiv ⟨p, hpK⟩ = α01.toLinearEquiv ⟨r, hrK⟩ := Subtype.ext (by
        change p1 = (α01.toLinearEquiv ⟨r, hrK⟩).1
        rw [hp1_d2]
        change diagAtom 2 = (α₁.toLinearEquiv (α₀.toLinearEquiv ⟨r, hrK⟩)).1
        rw [show α₀.toLinearEquiv ⟨r, hrK⟩ = ⟨diagAtom 2, diagAtom_mem_H3Subalgebra k 2⟩ from Subtype.ext hα₀_r,
          hα₁_diag 2])
      exact congrArg Subtype.val (α01.toLinearEquiv.injective hsub)
    apply hp_off
    rw [mem_lineSubalgebra_iff, hpr, hqr, ← hpr]
    rw [show tracePairing q p = 0 by unfold tracePairing; rw [hpr, hqr, albertTrace_zero], zero_smul]
  have ha_ne1 : a ≠ 1 := by
    intro ha1
    have hr1_0 : r1 = 0 := by
      have hsq : r1 ^ 2 = 0 := by
        have hns := hp1_coords.2.2.2.2
        rw [show p1.2 2 = octonionScalar r1 from hα₁_slot12, show p1.1 1 = a from rfl,
          show p1.1 2 = 1 - a by linarith [hp1_coords.2.1], ha1, sub_self, mul_zero,
          octonionScalar_eq_smul, ← octOne_eq_scalar, octNormSq_smul, octNormSq_one, mul_one] at hns
        exact hns
      exact sq_eq_zero_iff.mp hsq
    have hp1_d1 : p1 = diagAtom 1 := by
      rw [hp1_form, ha1, hr1_0, octonionScalar_zero, sub_self, zero_smul, add_zero, one_smul]
      have hs0 : slotElem12 (0 : Octonion) = 0 := by apply albert_ext <;> rfl
      rw [hs0, add_zero]
    have hpq : p = q := by
      have hsub : α01.toLinearEquiv ⟨p, hpK⟩ = α01.toLinearEquiv ⟨q, hqK⟩ := Subtype.ext (by
        change p1 = (α01.toLinearEquiv ⟨q, hqK⟩).1
        rw [hp1_d1]
        change diagAtom 1 = (α₁.toLinearEquiv (α₀.toLinearEquiv ⟨q, hqK⟩)).1
        rw [show α₀.toLinearEquiv ⟨q, hqK⟩ = ⟨diagAtom 1, diagAtom_mem_H3Subalgebra k 1⟩ from Subtype.ext hα₀_q,
          hα₁_diag 1])
      exact congrArg Subtype.val (α01.toLinearEquiv.injective hsub)
    apply hp_off
    rw [hpq]
    exact (mem_lineSubalgebra_iff q hq q).mpr (by
      rw [hq.1]; unfold tracePairing; rw [hq.1, hq.2, one_smul])
  have ha_pos : 0 < a := lt_of_le_of_ne ha_nonneg (Ne.symm ha_ne0)
  have ha_lt1 : a < 1 := lt_of_le_of_ne ha_le1 ha_ne1
  have hr1_eq : r1 = Real.sqrt (a * (1 - a)) := by
    have hsq : r1 ^ 2 = a * (1 - a) := by
      have hns := hp1_coords.2.2.2.2
      rw [show p1.2 2 = octonionScalar r1 from hα₁_slot12, show p1.1 1 = a from rfl,
        show p1.1 2 = 1 - a by linarith [hp1_coords.2.1],
        octonionScalar_eq_smul, ← octOne_eq_scalar, octNormSq_smul, octNormSq_one, mul_one] at hns
      exact hns
    rw [← hsq, Real.sqrt_sq hr1_nn]
  have hα_p : (α.toLinearEquiv ⟨p, hpK⟩).1 =
      a • diagAtom 1 + (1 - a) • diagAtom 2 + slotElem12 (octonionScalar (Real.sqrt (a * (1 - a)))) := by
    have hslot_smul : ∀ c : ℝ, slotElem12 (octonionScalar c) = c • slotElem12 octOne := fun c => by
      rw [octonionScalar_eq_smul, ← octOne_eq_scalar]
      apply albert_ext <;> simp [slotElem12_fst, slotElem12_snd_0, slotElem12_snd_1, slotElem12_snd_2,
        albert_smul_fst, albert_smul_snd]
    have hp1_sub : α01.toLinearEquiv ⟨p, hpK⟩ =
        a • ⟨diagAtom 1, diagAtom_mem_H3Subalgebra k 1⟩ +
        (1 - a) • ⟨diagAtom 2, diagAtom_mem_H3Subalgebra k 2⟩ +
        r1 • ⟨slotElem12 octOne, slotElem12_octOne_mem_H3Subalgebra k⟩ := by
      apply Subtype.ext
      change p1 = a • diagAtom 1 + (1 - a) • diagAtom 2 + r1 • slotElem12 octOne
      rw [hp1_form, hslot_smul r1]
    change (α₂.toLinearEquiv (α01.toLinearEquiv ⟨p, hpK⟩)).1 = _
    rw [hp1_sub, map_add, map_add, map_smul, map_smul, map_smul]
    simp only [Submodule.coe_add, Submodule.coe_smul, hα₂_diag 1, hα₂_diag 2,
      hα₂_12 (slotElem12_octOne_mem_H3Subalgebra k), hr1_eq, hslot_smul]
  let γ : Fin n → ℝ := fun m => (α.toLinearEquiv ⟨s m, hs_mem m⟩).1.1 0
  let x : Fin n → Octonion := fun m => (α.toLinearEquiv ⟨s m, hs_mem m⟩).1.2 1
  have hs_form : ∀ m, (α.toLinearEquiv ⟨s m, hs_mem m⟩).1 =
      γ m • diagAtom 0 + (1 - γ m) • diagAtom 2 + slotElem02 (x m) := fun m => by
    have hsm_atom : IsAtom (α.toLinearEquiv ⟨s m, hs_mem m⟩).1 := iso_maps_atom α ⟨s m, hs_mem m⟩ (hs_atom m)
    have hsm_q : jordanMul (diagAtom 1) (α.toLinearEquiv ⟨s m, hs_mem m⟩).1 = 0 := by
      rw [← hα_q, ← α.map_jordanMul_eq ⟨q, hqK⟩ ⟨s m, hs_mem m⟩]
      have h0 : (⟨jordanMul q (s m), (H3Subalgebra k).product_mem _ hqK _ (hs_mem m)⟩ :
          (H3Subalgebra k).carrier) = 0 := Subtype.ext (hs_line m)
      rw [h0, map_zero, Submodule.coe_zero]
    have hc := diag1_ortho_atom_coords hsm_atom hsm_q
    apply albert_ext
    · simp [albert_add_fst, albert_smul_fst, diagAtom_fst, slotElem02_fst, γ]
    · simp [albert_add_fst, albert_smul_fst, diagAtom_fst, slotElem02_fst, hc.1]
    · simp [albert_add_fst, albert_smul_fst, diagAtom_fst, slotElem02_fst]; linarith [hc.2.2.2.1]
    · simp [albert_add_snd, albert_smul_snd, diagAtom_snd, slotElem02_snd_0, hc.2.1]
    · simp [albert_add_snd, albert_smul_snd, diagAtom_snd, slotElem02_snd_1, x]
    · simp [albert_add_snd, albert_smul_snd, diagAtom_snd, slotElem02_snd_2, hc.2.2.1]
  have hx_mem_ne : ∀ m, x m ∈ (octSubalgebraOfLevel k).carrier ∧ x m ≠ 0 := fun m => by
    refine ⟨(α.toLinearEquiv ⟨s m, hs_mem m⟩).2.2.1, ?_⟩
    intro hx0
    have hsm_atom : IsAtom (α.toLinearEquiv ⟨s m, hs_mem m⟩).1 := iso_maps_atom α ⟨s m, hs_mem m⟩ (hs_atom m)
    have hsm_q : jordanMul (diagAtom 1) (α.toLinearEquiv ⟨s m, hs_mem m⟩).1 = 0 := by
      rw [← hα_q, ← α.map_jordanMul_eq ⟨q, hqK⟩ ⟨s m, hs_mem m⟩]
      have h0 : (⟨jordanMul q (s m), (H3Subalgebra k).product_mem _ hqK _ (hs_mem m)⟩ :
          (H3Subalgebra k).carrier) = 0 := Subtype.ext (hs_line m)
      rw [h0, map_zero, Submodule.coe_zero]
    have hc := diag1_ortho_atom_coords hsm_atom hsm_q
    have hprod0 : γ m * (1 - γ m) = 0 := by
      have hns := hc.2.2.2.2
      rw [show (α.toLinearEquiv ⟨s m, hs_mem m⟩).1.2 1 = x m from rfl, hx0,
        (octNormSq_eq_zero 0).mpr rfl] at hns
      simpa [γ, show (α.toLinearEquiv ⟨s m, hs_mem m⟩).1.1 2 = 1 - γ m by linarith [hc.2.2.2.1]] using hns
    rcases mul_eq_zero.mp hprod0 with h0 | h1
    · have hsm_eq : (α.toLinearEquiv ⟨s m, hs_mem m⟩).1 = diagAtom 2 := by
        rw [hs_form m, h0, zero_smul, sub_zero, one_smul, zero_add, hx0]
        have hs0 : slotElem02 (0 : Octonion) = 0 := by apply albert_ext <;> rfl
        rw [hs0, add_zero]
      have hsr : s m = r := congrArg Subtype.val (α.toLinearEquiv.injective
        (Subtype.ext (hsm_eq.trans hα_r.symm)))
      exact (hr_ne m).1 hsr
    · have hγ1 : γ m = 1 := by linarith
      have hsm_eq : (α.toLinearEquiv ⟨s m, hs_mem m⟩).1 = diagAtom 0 := by
        rw [hs_form m, hγ1, one_smul, sub_self, zero_smul, add_zero, hx0]
        have hs0 : slotElem02 (0 : Octonion) = 0 := by apply albert_ext <;> rfl
        rw [hs0, add_zero]
      have hsfr : s m = fr := congrArg Subtype.val (α.toLinearEquiv.injective
        (Subtype.ext (hsm_eq.trans hα_fr.symm)))
      exact (hr_ne m).2 hsfr
  have hx0_pos : ∃ r₀ : ℝ, 0 < r₀ ∧ x i₀ = octonionScalar r₀ := by
    have hr0_ne : r0 ≠ 0 := by
      intro h0
      apply (hx_mem_ne i₀).2
      change (α.toLinearEquiv ⟨s i₀, hs_mem i₀⟩).1.2 1 = 0
      rw [show (α.toLinearEquiv ⟨s i₀, hs_mem i₀⟩).1.2 1 = octonionScalar r0 from hα₂_slot02,
        h0, octonionScalar_zero]
    exact ⟨r0, lt_of_le_of_ne hr0_nn (Ne.symm hr0_ne), hα₂_slot02⟩
  refine ⟨α, a, γ, x, ha_pos, ha_lt1, hx_mem_ne, hx0_pos, hα_q, ⟨hrK, hα_r⟩, hα_p, hs_form, ?_⟩
  let S : Set (H3Subalgebra k).carrier := insert ⟨p, hpK⟩ (Set.range fun m => ⟨s m, hs_mem m⟩)
  have hS_val : Subtype.val '' S = insert p (Set.range s) := by
    ext z; simp [S]
  let Y : Set Albert := (fun z : (H3Subalgebra k).carrier => (α.toLinearEquiv z).1) '' S
  have hY_mem : Y = insert (α.toLinearEquiv ⟨p, hpK⟩).1 (Set.range fun m => (α.toLinearEquiv ⟨s m, hs_mem m⟩).1) := by
    ext z; simp [Y, S]
  have hdiag1_Y : diagAtom 1 ∈ (generatedSubalgebra Y).carrier := by
    let i₁ : Fin n := ⟨1, by omega⟩
    have hi01 : i₀ ≠ i₁ := fun h => by
      have := congrArg Fin.val h
      simp [i₀, i₁] at this
    have hs01_ne : (α.toLinearEquiv ⟨s i₀, hs_mem i₀⟩).1 ≠ (α.toLinearEquiv ⟨s i₁, hs_mem i₁⟩).1 := by
      intro h
      exact hi01 (hs_inj (congrArg Subtype.val (α.toLinearEquiv.injective (Subtype.ext h))))
    have hs0_in : (α.toLinearEquiv ⟨s i₀, hs_mem i₀⟩).1 ∈ (generatedSubalgebra Y).carrier :=
      subset_generatedSubalgebra Y (by rw [hY_mem]; right; exact ⟨i₀, rfl⟩)
    have hs1_in : (α.toLinearEquiv ⟨s i₁, hs_mem i₁⟩).1 ∈ (generatedSubalgebra Y).carrier :=
      subset_generatedSubalgebra Y (by rw [hY_mem]; right; exact ⟨i₁, rfl⟩)
    have hq0 : jordanMul (diagAtom 1) (α.toLinearEquiv ⟨s i₀, hs_mem i₀⟩).1 = 0 := by
      rw [← hα_q, ← α.map_jordanMul_eq ⟨q, hqK⟩ ⟨s i₀, hs_mem i₀⟩]
      have h0 : (⟨jordanMul q (s i₀), (H3Subalgebra k).product_mem _ hqK _ (hs_mem i₀)⟩ :
          (H3Subalgebra k).carrier) = 0 := Subtype.ext (hs_line i₀)
      rw [h0, map_zero, Submodule.coe_zero]
    have hq1 : jordanMul (diagAtom 1) (α.toLinearEquiv ⟨s i₁, hs_mem i₁⟩).1 = 0 := by
      rw [← hα_q, ← α.map_jordanMul_eq ⟨q, hqK⟩ ⟨s i₁, hs_mem i₁⟩]
      have h0 : (⟨jordanMul q (s i₁), (H3Subalgebra k).product_mem _ hqK _ (hs_mem i₁)⟩ :
          (H3Subalgebra k).carrier) = 0 := Subtype.ext (hs_line i₁)
      rw [h0, map_zero, Submodule.coe_zero]
    have hsupp := eq_fiv_support (diagAtom 1) (α.toLinearEquiv ⟨s i₀, hs_mem i₀⟩).1
      (α.toLinearEquiv ⟨s i₁, hs_mem i₁⟩).1 (diagAtom_isAtom 1)
      (iso_maps_atom α ⟨s i₀, hs_mem i₀⟩ (hs_atom i₀))
      (iso_maps_atom α ⟨s i₁, hs_mem i₁⟩ (hs_atom i₁)) hq0 hq1 hs01_ne
    have hcomp_in : albertUnit - diagAtom 1 ∈ (generatedSubalgebra Y).carrier := by
      rw [hsupp.2]
      exact (generatedSubalgebra Y).carrier.smul_mem _ ((generatedSubalgebra Y).carrier.sub_mem
        ((generatedSubalgebra Y).carrier.add_mem hs0_in hs1_in)
        ((generatedSubalgebra Y).carrier.smul_mem _
          ((generatedSubalgebra Y).product_mem _ hs0_in _ hs1_in)))
    have hsub : diagAtom 1 = albertUnit - (albertUnit - diagAtom 1) := by abel
    rw [hsub]
    exact (generatedSubalgebra Y).carrier.sub_mem (generatedSubalgebra Y).unit_mem hcomp_in
  have hp_Y : (α.toLinearEquiv ⟨p, hpK⟩).1 ∈ (generatedSubalgebra Y).carrier :=
    subset_generatedSubalgebra Y (by rw [hY_mem]; left; rfl)
  have hdiag2_Y : diagAtom 2 ∈ (generatedSubalgebra Y).carrier := by
    have hqfp : t • diagAtom 2 = quadraticMap (albertUnit - diagAtom 1) (α.toLinearEquiv ⟨p, hpK⟩).1 := by
      have hf_eq : (α.toLinearEquiv ⟨f, hfK⟩).1 = albertUnit - diagAtom 1 := by
        change (α.toLinearEquiv (⟨albertUnit, (H3Subalgebra k).unit_mem⟩ - ⟨q, hqK⟩)).1 = _
        rw [map_sub, Submodule.coe_sub, α.map_unit, hα_q]
      have hw_eq : (⟨w, hwK⟩ : (H3Subalgebra k).carrier) = t • ⟨r, hrK⟩ := by
        apply Subtype.ext
        change w = t • (t⁻¹ • w)
        rw [smul_smul, mul_inv_cancel₀ ht_pos.ne', one_smul]
      rw [← hα_r, ← hf_eq, ← α.map_quadraticMap ⟨f, hfK⟩ ⟨p, hpK⟩]
      change t • (α.toLinearEquiv ⟨r, hrK⟩).1 = (α.toLinearEquiv ⟨w, hwK⟩).1
      rw [hw_eq, map_smul, Submodule.coe_smul]
    have hmem : quadraticMap (albertUnit - diagAtom 1) (α.toLinearEquiv ⟨p, hpK⟩).1 ∈
        (generatedSubalgebra Y).carrier :=
      (peirce_components_mem_subalgebra (generatedSubalgebra Y) hdiag1_Y hp_Y).2.2
    rw [← hqfp] at hmem
    have hd2 : diagAtom 2 = t⁻¹ • (t • diagAtom 2) := by
      rw [smul_smul, inv_mul_cancel₀ ht_pos.ne', one_smul]
    rw [hd2]
    exact (generatedSubalgebra Y).carrier.smul_mem _ hmem
  have hdiag0_Y : diagAtom 0 ∈ (generatedSubalgebra Y).carrier := by
    have hd0 : diagAtom 0 = albertUnit - diagAtom 1 - diagAtom 2 := by
      have hs := diagAtom_sum_eq_unit
      rw [Fin.sum_univ_three] at hs
      rw [← hs]; abel
    rw [hd0]
    exact (generatedSubalgebra Y).carrier.sub_mem
      ((generatedSubalgebra Y).carrier.sub_mem (generatedSubalgebra Y).unit_mem hdiag1_Y) hdiag2_Y
  have hs12_Y : slotElem12 (octonionScalar 1) ∈ (generatedSubalgebra Y).carrier := by
    have hpe : (4 : ℝ) • jordanMul (diagAtom 1) (jordanMul (diagAtom 2) (α.toLinearEquiv ⟨p, hpK⟩).1) =
        slotElem12 (octonionScalar (Real.sqrt (a * (1 - a)))) := by
      rw [peirce12_extract, hα_p]
      simp [albert_add_snd, albert_smul_snd, diagAtom_snd, slotElem12_snd_2]
    have hmem : slotElem12 (octonionScalar (Real.sqrt (a * (1 - a)))) ∈ (generatedSubalgebra Y).carrier := by
      rw [← hpe]
      exact (generatedSubalgebra Y).carrier.smul_mem _
        ((generatedSubalgebra Y).product_mem _ hdiag1_Y _
          ((generatedSubalgebra Y).product_mem _ hdiag2_Y _ hp_Y))
    let c := Real.sqrt (a * (1 - a))
    have hcpos : 0 < c := Real.sqrt_pos.mpr (mul_pos ha_pos (sub_pos.mpr ha_lt1))
    have hsm : slotElem12 (octonionScalar 1) = c⁻¹ • slotElem12 (octonionScalar c) := by
      rw [octonionScalar_eq_smul c, ← octOne_eq_scalar]
      apply albert_ext <;> simp [slotElem12_fst, slotElem12_snd_0, slotElem12_snd_1, slotElem12_snd_2,
        albert_smul_fst, albert_smul_snd, octOne_eq_scalar]
      rw [smul_smul, inv_mul_cancel₀ hcpos.ne', one_smul]
    rw [hsm]
    exact (generatedSubalgebra Y).carrier.smul_mem _ hmem
  have hs02_Y : slotElem02 (octonionScalar 1) ∈ (generatedSubalgebra Y).carrier := by
    obtain ⟨r₀, hr₀_pos, hr₀_eq⟩ := hx0_pos
    have hs0_in : (α.toLinearEquiv ⟨s i₀, hs_mem i₀⟩).1 ∈ (generatedSubalgebra Y).carrier :=
      subset_generatedSubalgebra Y (by rw [hY_mem]; right; exact ⟨i₀, rfl⟩)
    have hpe : (4 : ℝ) • jordanMul (diagAtom 0) (jordanMul (diagAtom 2) (α.toLinearEquiv ⟨s i₀, hs_mem i₀⟩).1) =
        slotElem02 (octonionScalar r₀) := by
      rw [peirce02_extract, hs_form i₀, hr₀_eq]
      simp [albert_add_snd, albert_smul_snd, diagAtom_snd, slotElem02_snd_1]
    have hmem : slotElem02 (octonionScalar r₀) ∈ (generatedSubalgebra Y).carrier := by
      rw [← hpe]
      exact (generatedSubalgebra Y).carrier.smul_mem _
        ((generatedSubalgebra Y).product_mem _ hdiag0_Y _
          ((generatedSubalgebra Y).product_mem _ hdiag2_Y _ hs0_in))
    have hsm : slotElem02 (octonionScalar 1) = r₀⁻¹ • slotElem02 (octonionScalar r₀) := by
      rw [octonionScalar_eq_smul r₀, ← octOne_eq_scalar]
      apply albert_ext <;> simp [slotElem02_fst, slotElem02_snd_0, slotElem02_snd_1, slotElem02_snd_2,
        albert_smul_fst, albert_smul_snd, octOne_eq_scalar]
      rw [smul_smul, inv_mul_cancel₀ hr₀_pos.ne', one_smul]
    rw [hsm]
    exact (generatedSubalgebra Y).carrier.smul_mem _ hmem
  obtain ⟨F, hgenY, hminY⟩ := lem_five_coord_gen Y hdiag0_Y hdiag1_Y hdiag2_Y
    (Or.inr (Or.inr ⟨hs02_Y, hs12_Y⟩))
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · apply hminY (octSubalgebraOfLevel k)
    intro z hz
    rw [hY_mem] at hz
    rcases hz with rfl | ⟨m, rfl⟩
    · exact (α.toLinearEquiv ⟨p, hpK⟩).2
    · exact (α.toLinearEquiv ⟨s m, hs_mem m⟩).2
  · intro m _
    have hsm : (α.toLinearEquiv ⟨s m, hs_mem m⟩).1 ∈ (jordanSubalgebraH3 F).carrier := by
      rw [← hgenY]
      exact subset_generatedSubalgebra Y (by rw [hY_mem]; right; exact ⟨m, rfl⟩)
    have hsm2 := hsm.2.1
    rw [hs_form m] at hsm2
    simpa [albert_add_snd, albert_smul_snd, diagAtom_snd, slotElem02_snd_1] using hsm2
  · intro G hG
    apply hminY G
    intro z hz
    rw [hY_mem] at hz
    rcases hz with rfl | ⟨m, rfl⟩
    · rw [hα_p]
      refine ⟨?_, ?_, ?_⟩
      · simp [albert_add_snd, albert_smul_snd, diagAtom_snd, slotElem12_snd_0, G.carrier.zero_mem]
      · simp [albert_add_snd, albert_smul_snd, diagAtom_snd, slotElem12_snd_1, G.carrier.zero_mem]
      · simp only [albert_add_snd, albert_smul_snd, diagAtom_snd, smul_zero, zero_add, slotElem12_snd_2]
        rw [octonionScalar_eq_smul, ← octOne_eq_scalar]
        exact G.carrier.smul_mem _ G.one_mem
    · dsimp only
      rw [hs_form m]
      refine ⟨?_, ?_, ?_⟩
      · simp [albert_add_snd, albert_smul_snd, diagAtom_snd, slotElem02_snd_0, G.carrier.zero_mem]
      · simp only [albert_add_snd, albert_smul_snd, diagAtom_snd, smul_zero, zero_add, slotElem02_snd_1]
        by_cases hm : m = i₀
        · subst hm
          obtain ⟨r₀, _, hr₀_eq⟩ := hx0_pos
          rw [hr₀_eq, octonionScalar_eq_smul, ← octOne_eq_scalar]
          exact G.carrier.smul_mem _ G.one_mem
        · exact hG m hm
      · simp [albert_add_snd, albert_smul_snd, diagAtom_snd, slotElem02_snd_2, G.carrier.zero_mem]
  · intro y
    rw [← hS_val, JordanSubalgebraIso.generated_map_eq α S]
    change (∃ y₁ : (H3Subalgebra k).carrier, y = y₁.1 ∧ (α.toLinearEquiv y₁).1 ∈ (generatedSubalgebra Y).carrier) ↔ _
    rw [hgenY]

/-! ## Section 4: Spectral Idempotents, `lem:five:sub`, and Subalgebra Containment -/

def unitaryConjSubalgebraC (U : Matrix.unitaryGroup (Fin 3) ℂ)
    (B : NativeJordanSubalgebra) : NativeJordanSubalgebra :=
  let h1 : star U.1 * U.1 = 1 := Matrix.mem_unitaryGroup_iff'.mp U.prop
  let h2 : U.1 * star U.1 = 1 := Matrix.mem_unitaryGroup_iff.mp U.prop
  let ψ : JordanSubalgebraIso (H3Subalgebra .C) (H3Subalgebra .C) :=
    assocCD_unitaryIso assocCD_C U.1 h1 h2
  { carrier :=
      { carrier := {x : Albert | ∃ hx : x ∈ (H3Subalgebra .C).carrier,
          (ψ.toLinearEquiv ⟨x, hx⟩).1 ∈ B.carrier}
        add_mem' := fun {a b} ⟨ha, ha'⟩ ⟨hb, hb'⟩ =>
          ⟨(H3Subalgebra .C).carrier.add_mem ha hb, by
            have heq : (⟨a + b, (H3Subalgebra .C).carrier.add_mem ha hb⟩ : (H3Subalgebra .C).carrier) =
                ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
            rw [heq, map_add, Submodule.coe_add]
            exact B.carrier.add_mem ha' hb'⟩
        zero_mem' := ⟨(H3Subalgebra .C).carrier.zero_mem, by
          have heq : (⟨0, (H3Subalgebra .C).carrier.zero_mem⟩ : (H3Subalgebra .C).carrier) = 0 := rfl
          rw [heq, map_zero, Submodule.coe_zero]
          exact B.carrier.zero_mem⟩
        smul_mem' := fun r {a} ⟨ha, ha'⟩ =>
          ⟨(H3Subalgebra .C).carrier.smul_mem r ha, by
            have heq : (⟨r • a, (H3Subalgebra .C).carrier.smul_mem r ha⟩ : (H3Subalgebra .C).carrier) =
                r • ⟨a, ha⟩ := rfl
            rw [heq, map_smul, Submodule.coe_smul]
            exact B.carrier.smul_mem r ha'⟩ }
    unit_mem := ⟨(H3Subalgebra .C).unit_mem, by
      rw [ψ.map_unit]
      exact B.unit_mem⟩
    product_mem := fun a ⟨ha, ha'⟩ b ⟨hb, hb'⟩ =>
      ⟨(H3Subalgebra .C).product_mem a ha b hb, by
        rw [ψ.map_jordan ⟨a, ha⟩ ⟨b, hb⟩]
        exact B.product_mem _ ha' _ hb'⟩ }

private theorem finrank_unitaryConjSubalgebraC (U : Matrix.unitaryGroup (Fin 3) ℂ)
    (B : NativeJordanSubalgebra) (hBC : B.carrier ≤ (H3Subalgebra .C).carrier) :
    Module.finrank ℝ (unitaryConjSubalgebraC U B).carrier = Module.finrank ℝ B.carrier := by
  let h1 : star U.1 * U.1 = 1 := Matrix.mem_unitaryGroup_iff'.mp U.prop
  let h2 : U.1 * star U.1 = 1 := Matrix.mem_unitaryGroup_iff.mp U.prop
  let ψ : JordanSubalgebraIso (H3Subalgebra .C) (H3Subalgebra .C) :=
    assocCD_unitaryIso assocCD_C U.1 h1 h2
  let eqv : (unitaryConjSubalgebraC U B).carrier ≃ₗ[ℝ] B.carrier :=
    { toFun := fun x => ⟨(ψ.toLinearEquiv ⟨x.1, x.2.1⟩).1, x.2.2⟩
      invFun := fun b =>
        let y := ψ.toLinearEquiv.symm ⟨b.1, hBC b.2⟩
        ⟨y.1, y.2, by
          change (ψ.toLinearEquiv ⟨y.1, y.2⟩).1 ∈ B.carrier
          have hy : (⟨y.1, y.2⟩ : (H3Subalgebra .C).carrier) = y := rfl
          rw [hy, LinearEquiv.apply_symm_apply]
          exact b.2⟩
      left_inv := fun x => Subtype.ext (by
        change (ψ.toLinearEquiv.symm ⟨(ψ.toLinearEquiv ⟨x.1, x.2.1⟩).1, _⟩).1 = x.1
        have hsub : (⟨(ψ.toLinearEquiv ⟨x.1, x.2.1⟩).1, (ψ.toLinearEquiv ⟨x.1, x.2.1⟩).2⟩ :
            (H3Subalgebra .C).carrier) = ψ.toLinearEquiv ⟨x.1, x.2.1⟩ := rfl
        rw [hsub, LinearEquiv.symm_apply_apply])
      right_inv := fun b => Subtype.ext (by
        change (ψ.toLinearEquiv ⟨(ψ.toLinearEquiv.symm ⟨b.1, hBC b.2⟩).1, _⟩).1 = b.1
        have hsub : (⟨(ψ.toLinearEquiv.symm ⟨b.1, hBC b.2⟩).1,
            (ψ.toLinearEquiv.symm ⟨b.1, hBC b.2⟩).2⟩ : (H3Subalgebra .C).carrier) =
            ψ.toLinearEquiv.symm ⟨b.1, hBC b.2⟩ := rfl
        rw [hsub, LinearEquiv.apply_symm_apply])
      map_add' := fun a b => Subtype.ext (by
        have h : (⟨a.1 + b.1, (H3Subalgebra .C).carrier.add_mem a.2.1 b.2.1⟩ :
            (H3Subalgebra .C).carrier) = ⟨a.1, a.2.1⟩ + ⟨b.1, b.2.1⟩ := rfl
        change (ψ.toLinearEquiv ⟨a.1 + b.1, _⟩).1 = _
        rw [h, map_add, Submodule.coe_add]; rfl)
      map_smul' := fun r a => Subtype.ext (by
        have h : (⟨r • a.1, (H3Subalgebra .C).carrier.smul_mem r a.2.1⟩ :
            (H3Subalgebra .C).carrier) = r • ⟨a.1, a.2.1⟩ := rfl
        change (ψ.toLinearEquiv ⟨r • a.1, _⟩).1 = _
        rw [h, map_smul, Submodule.coe_smul]; rfl) }
  exact eqv.finrank_eq

private def autoSymm (g : NativeAlbertAutomorphism) : NativeAlbertAutomorphism where
  linearEquiv := g.linearEquiv.symm
  preserves_product x y := g.linearEquiv.injective (by
    rw [LinearEquiv.apply_symm_apply, g.preserves_product,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply])
  preserves_unit := g.linearEquiv.injective (by
    rw [LinearEquiv.apply_symm_apply, g.preserves_unit])
  preserves_trace x := by
    have h := g.preserves_trace (g.linearEquiv.symm x)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm

private def H3Auto : CDLevel → Type
  | .R => JordanSubalgebraIso (H3Subalgebra .R) (H3Subalgebra .R)
  | .C => Matrix.unitaryGroup (Fin 3) ℂ
  | .H => JordanSubalgebraIso (H3Subalgebra .H) (H3Subalgebra .H)
  | .O => NativeAlbertAutomorphism

private def H3Auto.toIso : ∀ {k : CDLevel}, H3Auto k → JordanSubalgebraIso (H3Subalgebra k) (H3Subalgebra k)
  | .R, α => α
  | .C, U => assocCD_unitaryIso assocCD_C U.1 (Matrix.mem_unitaryGroup_iff'.mp U.prop)
      (Matrix.mem_unitaryGroup_iff.mp U.prop)
  | .H, α => α
  | .O, g => JordanSubalgebraIso.ofAutoOnTop g

private def mulUnitary3 (U₁ U₂ : Matrix.unitaryGroup (Fin 3) ℂ) : Matrix.unitaryGroup (Fin 3) ℂ :=
  U₁ * U₂

private def H3Auto.trans : ∀ {k : CDLevel}, H3Auto k → H3Auto k → H3Auto k
  | .R, α, β => JordanSubalgebraIso.trans α β
  | .C, U₁, U₂ => mulUnitary3 U₁ U₂
  | .H, α, β => JordanSubalgebraIso.trans α β
  | .O, g₁, g₂ => g₂.comp g₁

private theorem H3Auto.toIso_trans {k : CDLevel} (a b : H3Auto k)
    (x : (H3Subalgebra k).carrier) :
    ((a.trans b).toIso.toLinearEquiv x).1 =
      (b.toIso.toLinearEquiv (a.toIso.toLinearEquiv x)).1 := by
  cases k with
  | R => rfl
  | C =>
    let u₁ : Matrix.unitaryGroup (Fin 3) ℂ := a
    let u₂ : Matrix.unitaryGroup (Fin 3) ℂ := b
    let x' : (jordanSubalgebraH3 assocCD_C.subalgebra).carrier := x
    let ax' : (jordanSubalgebraH3 assocCD_C.subalgebra).carrier := a.toIso.toLinearEquiv x
    let M := (assocHermEquiv assocCD_C).symm x'
    have hM1 : (assocHermEquiv assocCD_C).symm ax' =
        ⟨star u₁.1 * M.1 * u₁.1, by
          rw [selfAdjoint.mem_iff, star_mul, star_mul, star_star, M.prop, mul_assoc]⟩ := by
      apply (assocHermEquiv assocCD_C).injective
      rw [LinearEquiv.apply_symm_apply]
      rfl
    change assocMatToAlbert assocCD_C (star (u₁ * u₂).1 * M.1 * (u₁ * u₂).1) =
      assocMatToAlbert assocCD_C (star u₂.1 * ((assocHermEquiv assocCD_C).symm ax').1 * u₂.1)
    rw [hM1]
    congr 1
    change star (u₁.1 * u₂.1) * M.1 * (u₁.1 * u₂.1) = star u₂.1 * (star u₁.1 * M.1 * u₁.1) * u₂.1
    rw [star_mul]
    simp only [mul_assoc]
  | H => rfl
  | O => rfl

private theorem H3Auto.frame (k : CDLevel) (F : NativeJordanFrame)
    (hF : ∀ m : Fin 3, F.atom m ∈ (H3Subalgebra k).carrier) :
    ∃ α : H3Auto k, ∀ m : Fin 3, (α.toIso.toLinearEquiv ⟨F.atom m, hF m⟩).1 = diagAtom m := by
  cases k with
  | R =>
    obtain ⟨U, h1, h2, h⟩ := assocCD_frame_to_standard assocCD_R F hF
    exact ⟨assocCD_unitaryIso assocCD_R U h1 h2, h⟩
  | C =>
    obtain ⟨U, h1, h2, h⟩ := assocCD_frame_to_standard assocCD_C F hF
    exact ⟨⟨U, Matrix.mem_unitaryGroup_iff.mpr h2⟩, h⟩
  | H =>
    obtain ⟨U, h1, h2, h⟩ := assocCD_frame_to_standard assocCD_H F hF
    exact ⟨assocCD_unitaryIso assocCD_H U h1 h2, h⟩
  | O => exact native_frame_to_standardFrame F

private theorem H3Auto.frameStab_slot12_real (k : CDLevel) (x : Albert)
    (hx : x ∈ (H3Subalgebra k).carrier) :
    ∃ α : H3Auto k,
      (∀ i, (α.toIso.toLinearEquiv ⟨diagAtom i, diagAtom_mem_H3Subalgebra k i⟩).1 = diagAtom i) ∧
      ∃ r : ℝ, 0 ≤ r ∧ (α.toIso.toLinearEquiv ⟨x, hx⟩).1.2 2 = octonionScalar r := by
  cases k with
  | R => exact assocCD_frameStab_slot12_real assocCD_R x hx
  | C =>
    let M := (assocHermEquiv assocCD_C).symm ⟨x, hx⟩
    obtain ⟨u, r, hu, hr, hmul⟩ := assocCD_unit_mul_left_real assocCD_C (M.1 1 2)
    let d : Fin 3 → ℂ := ![1, u, 1]
    have hd : ∀ i, assocCD_C.normSq (d i) = 1 := fun i => by
      fin_cases i <;> dsimp [d] <;> [rw [← assocCD_C.embed_normSq, assocCD_C.embed_one, octNormSq_one]; exact hu;
        rw [← assocCD_C.embed_normSq, assocCD_C.embed_one, octNormSq_one]]
    let U := Matrix.diagonal d
    have hU := assocCD_diag_unitary assocCD_C d hd
    let Ug : H3Auto .C := (⟨U, Matrix.mem_unitaryGroup_iff.mpr hU.2⟩ : Matrix.unitaryGroup (Fin 3) ℂ)
    refine ⟨Ug, fun i => assocCD_diag_unitaryIso_fixes_diag assocCD_C d hd i, r, hr, ?_⟩
    have hmul_eq : assocCD_C.embed (star u * M.1 1 2) = octonionScalar r := hmul
    rw [show (Ug.toIso.toLinearEquiv ⟨x, hx⟩).1 =
        (assocCD_unitaryIso assocCD_C U hU.1 hU.2).toLinearEquiv ⟨x, hx⟩ from rfl]
    rw [assocCD_diag_unitaryIso_apply assocCD_C d hd, assocMatToAlbert_snd_2, diag_conj_entry]
    change assocCD_C.embed (star (d 1) * M.1 1 2 * d 2) = octonionScalar r
    simpa [d] using hmul_eq
  | H => exact assocCD_frameStab_slot12_real assocCD_H x hx
  | O => exact exists_frameStab_slot12_real x

private theorem H3Auto.frameAnd12OneStab_slot02_real (k : CDLevel) (x : Albert)
    (hx : x ∈ (H3Subalgebra k).carrier) :
    ∃ α : H3Auto k,
      (∀ i, (α.toIso.toLinearEquiv ⟨diagAtom i, diagAtom_mem_H3Subalgebra k i⟩).1 = diagAtom i) ∧
      (∀ h12 : slotElem12 octOne ∈ (H3Subalgebra k).carrier,
        (α.toIso.toLinearEquiv ⟨slotElem12 octOne, h12⟩).1 = slotElem12 octOne) ∧
      ∃ r : ℝ, 0 ≤ r ∧ (α.toIso.toLinearEquiv ⟨x, hx⟩).1.2 1 = octonionScalar r := by
  cases k with
  | R => exact assocCD_frameAnd12OneStab_slot02_real assocCD_R x hx
  | C =>
    let M := (assocHermEquiv assocCD_C).symm ⟨x, hx⟩
    obtain ⟨u, r, hu, hr, hmul⟩ := assocCD_unit_mul_left_real assocCD_C (M.1 0 2)
    let d : Fin 3 → ℂ := ![u, 1, 1]
    have hd : ∀ i, assocCD_C.normSq (d i) = 1 := fun i => by
      fin_cases i <;> dsimp [d] <;> [exact hu;
        rw [← assocCD_C.embed_normSq, assocCD_C.embed_one, octNormSq_one];
        rw [← assocCD_C.embed_normSq, assocCD_C.embed_one, octNormSq_one]]
    let U := Matrix.diagonal d
    have hU := assocCD_diag_unitary assocCD_C d hd
    let Ug : H3Auto .C := (⟨U, Matrix.mem_unitaryGroup_iff.mpr hU.2⟩ : Matrix.unitaryGroup (Fin 3) ℂ)
    refine ⟨Ug, fun i => assocCD_diag_unitaryIso_fixes_diag assocCD_C d hd i,
      fun _ => assocCD_diag_unitaryIso_fixes_slot12_one assocCD_C d hd rfl rfl, r, hr, ?_⟩
    rw [show (Ug.toIso.toLinearEquiv ⟨x, hx⟩).1 =
        (assocCD_unitaryIso assocCD_C U hU.1 hU.2).toLinearEquiv ⟨x, hx⟩ from rfl]
    rw [assocCD_diag_unitaryIso_apply assocCD_C d hd, assocMatToAlbert_snd_1, diag_conj_entry]
    simpa [d] using hmul
  | H => exact assocCD_frameAnd12OneStab_slot02_real assocCD_H x hx
  | O =>
    obtain ⟨g, hdiag, h12, r, hr, hslot⟩ := exists_frameAnd12OneStab_slot02_real x
    exact ⟨g, hdiag, fun _ => h12, r, hr, hslot⟩

private theorem jordanMul_diagLinear (a b : Fin 3 → ℝ) :
    jordanMul (a 0 • diagAtom 0 + a 1 • diagAtom 1 + a 2 • diagAtom 2)
              (b 0 • diagAtom 0 + b 1 • diagAtom 1 + b 2 • diagAtom 2) =
      (a 0 * b 0) • diagAtom 0 + (a 1 * b 1) • diagAtom 1 + (a 2 * b 2) • diagAtom 2 := by
  let x : Albert := a 0 • diagAtom 0 + a 1 • diagAtom 1 + a 2 • diagAtom 2
  let y : Albert := b 0 • diagAtom 0 + b 1 • diagAtom 1 + b 2 • diagAtom 2
  have hx : x.1 0 = a 0 ∧ x.1 1 = a 1 ∧ x.1 2 = a 2 ∧ x.2 0 = 0 ∧ x.2 1 = 0 ∧ x.2 2 = 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [x, albert_add_fst, albert_smul_fst, diagAtom_fst,
      albert_add_snd, albert_smul_snd, diagAtom_snd]
  have hy : y.1 0 = b 0 ∧ y.1 1 = b 1 ∧ y.1 2 = b 2 ∧ y.2 0 = 0 ∧ y.2 1 = 0 ∧ y.2 2 = 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [y, albert_add_fst, albert_smul_fst, diagAtom_fst,
      albert_add_snd, albert_smul_snd, diagAtom_snd]
  apply albert_ext
  · rw [jordanMul_diag_0, hx.1, hy.1, hx.2.2.2.1, hx.2.2.2.2.1, hy.2.2.2.1, hy.2.2.2.2.1]
    simp [octDot_zero_left, albert_add_fst, albert_smul_fst, diagAtom_fst]
  · rw [jordanMul_diag_1, hx.2.1, hy.2.1, hx.2.2.2.1, hx.2.2.2.2.2, hy.2.2.2.1, hy.2.2.2.2.2]
    simp [octDot_zero_left, albert_add_fst, albert_smul_fst, diagAtom_fst]
  · rw [jordanMul_diag_2, hx.2.2.1, hy.2.2.1, hx.2.2.2.2.1, hx.2.2.2.2.2, hy.2.2.2.2.1, hy.2.2.2.2.2]
    simp [octDot_zero_left, albert_add_fst, albert_smul_fst, diagAtom_fst]
  · rw [jordanMul_off_0, hx.2.2.2.1, hx.2.2.2.2.1, hx.2.2.2.2.2, hy.2.2.2.1, hy.2.2.2.2.1, hy.2.2.2.2.2]
    simp [octonionConj_zero, octonionMul_zero_left, albert_add_snd, albert_smul_snd, diagAtom_snd]
  · rw [jordanMul_off_1, hx.2.2.2.2.1, hx.2.2.2.2.2, hx.2.2.2.1, hy.2.2.2.2.1, hy.2.2.2.2.2, hy.2.2.2.1]
    simp [octonionMul_zero_left, albert_add_snd, albert_smul_snd, diagAtom_snd]
  · rw [jordanMul_off_2, hx.2.2.2.2.2, hx.2.2.2.1, hx.2.2.2.2.1, hy.2.2.2.2.2, hy.2.2.2.1, hy.2.2.2.2.1]
    simp [octonionConj_zero, octonionMul_zero_left, albert_add_snd, albert_smul_snd, diagAtom_snd]

private theorem subalgebra_spectral_decomp (B : NativeJordanSubalgebra)
    {x : Albert} (hx : x ∈ B.carrier) (hx_nonscalar : x ∉ Submodule.span ℝ {albertUnit}) :
    ∃ L : List (ℝ × Albert),
      (∀ t ∈ L, t.2 ∈ B.carrier ∧ jordanMul t.2 t.2 = t.2 ∧ t.2 ≠ 0 ∧ t.2 ≠ albertUnit) ∧
      L ≠ [] ∧ x = (L.map (fun t => t.1 • t.2)).sum := by
  obtain ⟨g0, hg0⟩ := Glennie.native_diagonalization (recoveredCoordinateEquiv x)
  let g := compactAutoToNativeAuto g0
  let y := g.linearEquiv x
  have hy_diag : y.2 0 = 0 ∧ y.2 1 = 0 ∧ y.2 2 = 0 := by
    have h1 : y = recoveredCoordinateEquiv.symm (g0.equiv (recoveredCoordinateEquiv x)) := rfl
    rw [h1]
    exact hg0
  let d : Fin 3 → ℝ := y.1
  have hy_eq : y = d 0 • diagAtom 0 + d 1 • diagAtom 1 + d 2 • diagAtom 2 := by
    apply albert_ext
    · simp [d, albert_add_fst, albert_smul_fst, diagAtom_fst]
    · simp [d, albert_add_fst, albert_smul_fst, diagAtom_fst]
    · simp [d, albert_add_fst, albert_smul_fst, diagAtom_fst]
    · simp [albert_add_snd, albert_smul_snd, diagAtom_snd, hy_diag.1]
    · simp [albert_add_snd, albert_smul_snd, diagAtom_snd, hy_diag.2.1]
    · simp [albert_add_snd, albert_smul_snd, diagAtom_snd, hy_diag.2.2]
  have hunit_eq : albertUnit = (1 : ℝ) • diagAtom 0 + (1 : ℝ) • diagAtom 1 + (1 : ℝ) • diagAtom 2 := by
    simpa [one_smul, Fin.sum_univ_three, add_assoc] using diagAtom_sum_eq_unit.symm
  have hdiag_inj : ∀ a b : Fin 3 → ℝ,
      a 0 • diagAtom 0 + a 1 • diagAtom 1 + a 2 • diagAtom 2 =
      b 0 • diagAtom 0 + b 1 • diagAtom 1 + b 2 • diagAtom 2 → a = b := by
    intro a b h
    funext i
    have hi := congrArg (fun z : Albert => z.1 i) h
    fin_cases i <;> simp [albert_add_fst, albert_smul_fst, diagAtom_fst] at hi ⊢ <;> exact hi
  have hnot_all_eq : ¬ (d 0 = d 1 ∧ d 1 = d 2) := by
    rintro ⟨h01, h12⟩
    apply hx_nonscalar
    have hxy : y = d 0 • albertUnit := by
      rw [hy_eq, hunit_eq, ← h12, ← h01]
      simp only [smul_add, smul_smul, mul_one]
    have hx_eq : x = d 0 • albertUnit := g.linearEquiv.injective (by
      change y = g.linearEquiv (d 0 • albertUnit)
      rw [map_smul, g.preserves_unit, hxy])
    rw [hx_eq]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self albertUnit)
  have mk1 : ∀ (μ ν : ℝ) (f : Fin 3 → ℝ), μ ≠ ν →
      (∀ i, d i = μ ∨ d i = ν) → (∃ i, d i = μ) → (∃ j, d j = ν) →
      let P := (μ - ν)⁻¹ • (x - ν • albertUnit)
      P ∈ B.carrier ∧ jordanMul P P = P ∧ P ≠ 0 ∧ P ≠ albertUnit ∧
      g.linearEquiv P =
        (if d 0 = μ then (1 : ℝ) else 0) • diagAtom 0 +
        (if d 1 = μ then (1 : ℝ) else 0) • diagAtom 1 +
        (if d 2 = μ then (1 : ℝ) else 0) • diagAtom 2 := by
    intro μ ν _ hne hvals ⟨iμ, hiμ⟩ ⟨jν, hjν⟩ P
    have hPmem : P ∈ B.carrier :=
      B.carrier.smul_mem _ (B.carrier.sub_mem hx (B.carrier.smul_mem _ B.unit_mem))
    have hgP : g.linearEquiv P =
        (if d 0 = μ then (1 : ℝ) else 0) • diagAtom 0 +
        (if d 1 = μ then (1 : ℝ) else 0) • diagAtom 1 +
        (if d 2 = μ then (1 : ℝ) else 0) • diagAtom 2 := by
      dsimp [P]
      rw [map_smul, map_sub, map_smul, g.preserves_unit]
      change (μ - ν)⁻¹ • (y - ν • albertUnit) = _
      rw [hy_eq, hunit_eq]
      apply albert_ext
      · simp only [albert_sub_fst, albert_add_fst, albert_smul_fst, diagAtom_fst]
        rcases hvals 0 with h0 | h0 <;> simp [h0, hne.symm, sub_ne_zero.mpr hne]
      · simp only [albert_sub_fst, albert_add_fst, albert_smul_fst, diagAtom_fst]
        rcases hvals 1 with h1 | h1 <;> simp [h1, hne.symm, sub_ne_zero.mpr hne]
      · simp only [albert_sub_fst, albert_add_fst, albert_smul_fst, diagAtom_fst]
        rcases hvals 2 with h2 | h2 <;> simp [h2, hne.symm, sub_ne_zero.mpr hne]
      · simp [-ite_smul, albert_sub_snd, albert_add_snd, albert_smul_snd, diagAtom_snd]
      · simp [-ite_smul, albert_sub_snd, albert_add_snd, albert_smul_snd, diagAtom_snd]
      · simp [-ite_smul, albert_sub_snd, albert_add_snd, albert_smul_snd, diagAtom_snd]
    have hPid : jordanMul P P = P := g.linearEquiv.injective (by
      rw [g.preserves_product, hgP,
        jordanMul_diagLinear (fun i => if d i = μ then (1 : ℝ) else 0)
          (fun i => if d i = μ then (1 : ℝ) else 0)]
      have hsq : ∀ t : Fin 3, (if d t = μ then (1 : ℝ) else 0) * (if d t = μ then 1 else 0) =
          if d t = μ then 1 else 0 := fun t => by split_ifs <;> norm_num
      simp only [hsq])
    have hPne0 : P ≠ 0 := fun h => by
      have hg0' := congrArg g.linearEquiv h
      rw [hgP, map_zero] at hg0'
      have hi := congrArg (fun z : Albert => z.1 iμ) hg0'
      simp only [albert_add_fst, albert_smul_fst, diagAtom_fst, albert_zero_fst] at hi
      fin_cases iμ <;> dsimp at hiμ ⊢ <;> simp [hiμ] at hi
    have hPne1 : P ≠ albertUnit := fun h => by
      have hg1' := congrArg g.linearEquiv h
      rw [hgP, g.preserves_unit] at hg1'
      have hj := congrArg (fun z : Albert => z.1 jν) hg1'
      simp only [albert_add_fst, albert_smul_fst, diagAtom_fst, albertUnit_fst] at hj
      fin_cases jν <;> dsimp at hjν ⊢ <;> simp [hjν, hne.symm] at hj
    exact ⟨hPmem, hPid, hPne0, hPne1, hgP⟩
  by_cases h01 : d 0 = d 1
  · have hne : d 0 ≠ d 2 := fun h => hnot_all_eq ⟨h01, h01.symm.trans h⟩
    have h0 := mk1 (d 0) (d 2) d hne (fun i => by fin_cases i <;> [left; left; right] <;> simp [h01])
      ⟨0, rfl⟩ ⟨2, rfl⟩
    have h2 := mk1 (d 2) (d 0) d hne.symm (fun i => by fin_cases i <;> [right; right; left] <;> simp [h01])
      ⟨2, rfl⟩ ⟨0, rfl⟩
    refine ⟨[(d 0, (d 0 - d 2)⁻¹ • (x - d 2 • albertUnit)),
             (d 2, (d 2 - d 0)⁻¹ • (x - d 0 • albertUnit))], ?_, by simp, ?_⟩
    · intro t ht; simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
      rcases ht with rfl | rfl
      · exact ⟨h0.1, h0.2.1, h0.2.2.1, h0.2.2.2.1⟩
      · exact ⟨h2.1, h2.2.1, h2.2.2.1, h2.2.2.2.1⟩
    · apply g.linearEquiv.injective
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        map_add, map_smul, h0.2.2.2.2, h2.2.2.2.2]
      change y = _
      rw [hy_eq, ← h01]
      apply albert_ext <;> simp [hne, hne.symm, albert_add_fst, albert_smul_fst, diagAtom_fst,
        albert_add_snd, albert_smul_snd, diagAtom_snd]
  · by_cases h02 : d 0 = d 2
    · have h0 := mk1 (d 0) (d 1) d h01 (fun i => by fin_cases i <;> [left; right; left] <;> simp [h02])
        ⟨0, rfl⟩ ⟨1, rfl⟩
      have h1 := mk1 (d 1) (d 0) d (Ne.symm h01) (fun i => by fin_cases i <;> [right; left; right] <;> simp [h02])
        ⟨1, rfl⟩ ⟨0, rfl⟩
      refine ⟨[(d 0, (d 0 - d 1)⁻¹ • (x - d 1 • albertUnit)),
               (d 1, (d 1 - d 0)⁻¹ • (x - d 0 • albertUnit))], ?_, by simp, ?_⟩
      · intro t ht; simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
        rcases ht with rfl | rfl
        · exact ⟨h0.1, h0.2.1, h0.2.2.1, h0.2.2.2.1⟩
        · exact ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1⟩
      · apply g.linearEquiv.injective
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
          map_add, map_smul, h0.2.2.2.2, h1.2.2.2.2]
        change y = _
        rw [hy_eq, ← h02]
        apply albert_ext <;> simp [h01, Ne.symm h01, albert_add_fst, albert_smul_fst, diagAtom_fst,
          albert_add_snd, albert_smul_snd, diagAtom_snd]
    · by_cases h12 : d 1 = d 2
      · have h0 := mk1 (d 0) (d 1) d h01 (fun i => by fin_cases i <;> [left; right; right] <;> simp [h12])
          ⟨0, rfl⟩ ⟨1, rfl⟩
        have h1 := mk1 (d 1) (d 0) d (Ne.symm h01) (fun i => by fin_cases i <;> [right; left; left] <;> simp [h12])
          ⟨1, rfl⟩ ⟨0, rfl⟩
        refine ⟨[(d 0, (d 0 - d 1)⁻¹ • (x - d 1 • albertUnit)),
                 (d 1, (d 1 - d 0)⁻¹ • (x - d 0 • albertUnit))], ?_, by simp, ?_⟩
        · intro t ht; simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
          rcases ht with rfl | rfl
          · exact ⟨h0.1, h0.2.1, h0.2.2.1, h0.2.2.2.1⟩
          · exact ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1⟩
        · apply g.linearEquiv.injective
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
            map_add, map_smul, h0.2.2.2.2, h1.2.2.2.2]
          change y = _
          rw [hy_eq, ← h12]
          apply albert_ext <;> simp [h01, Ne.symm h01, albert_add_fst, albert_smul_fst, diagAtom_fst,
            albert_add_snd, albert_smul_snd, diagAtom_snd]
      · have mk2 : ∀ (k0 : Fin 3) (μ ν κ : ℝ),
            d k0 = μ → μ ≠ ν → μ ≠ κ → (∀ j, j ≠ k0 → d j = ν ∨ d j = κ) →
            let P := ((μ - ν) * (μ - κ))⁻¹ • jordanMul (x - ν • albertUnit) (x - κ • albertUnit)
            P ∈ B.carrier ∧ jordanMul P P = P ∧ P ≠ 0 ∧ P ≠ albertUnit ∧
            g.linearEquiv P = diagAtom k0 := by
          intro k0 μ ν κ hk0 hmn hmk hrest P
          have hPmem : P ∈ B.carrier := B.carrier.smul_mem _ (B.product_mem _
            (B.carrier.sub_mem hx (B.carrier.smul_mem _ B.unit_mem)) _
            (B.carrier.sub_mem hx (B.carrier.smul_mem _ B.unit_mem)))
          have hgP : g.linearEquiv P = diagAtom k0 := by
            dsimp [P]
            rw [map_smul, g.preserves_product, map_sub, map_sub, map_smul, map_smul, g.preserves_unit]
            change ((μ - ν) * (μ - κ))⁻¹ • jordanMul (y - ν • albertUnit) (y - κ • albertUnit) = diagAtom k0
            rw [hy_eq, hunit_eq]
            have h1 : (d 0 • diagAtom 0 + d 1 • diagAtom 1 + d 2 • diagAtom 2) -
                ν • ((1 : ℝ) • diagAtom 0 + (1 : ℝ) • diagAtom 1 + (1 : ℝ) • diagAtom 2) =
                (d 0 - ν) • diagAtom 0 + (d 1 - ν) • diagAtom 1 + (d 2 - ν) • diagAtom 2 := by module
            have h2 : (d 0 • diagAtom 0 + d 1 • diagAtom 1 + d 2 • diagAtom 2) -
                κ • ((1 : ℝ) • diagAtom 0 + (1 : ℝ) • diagAtom 1 + (1 : ℝ) • diagAtom 2) =
                (d 0 - κ) • diagAtom 0 + (d 1 - κ) • diagAtom 1 + (d 2 - κ) • diagAtom 2 := by module
            rw [h1, h2, jordanMul_diagLinear (fun i => d i - ν) (fun i => d i - κ)]
            have hcoeff : ∀ j : Fin 3, ((μ - ν) * (μ - κ))⁻¹ * ((d j - ν) * (d j - κ)) =
                if j = k0 then 1 else 0 := fun j => by
              split_ifs with hj
              · subst hj; rw [hk0]
                exact inv_mul_cancel₀ (mul_ne_zero (sub_ne_zero.mpr hmn) (sub_ne_zero.mpr hmk))
              · rcases hrest j hj with h | h <;> simp [h]
            apply albert_ext <;> simp [-mul_inv_rev, albert_add_fst, albert_smul_fst, diagAtom_fst,
              albert_add_snd, albert_smul_snd, diagAtom_snd]
            · rw [hcoeff 0]
            · rw [hcoeff 1]
            · rw [hcoeff 2]
          have hPid : jordanMul P P = P := g.linearEquiv.injective (by
            rw [g.preserves_product, hgP, (diagAtom_isAtom k0).1])
          have hPne0 : P ≠ 0 := fun h => by
            have hg0' := congrArg g.linearEquiv h
            rw [hgP, map_zero] at hg0'
            have htr := congrArg albertTrace hg0'
            rw [(diagAtom_isAtom k0).2, albertTrace_zero] at htr; norm_num at htr
          have hPne1 : P ≠ albertUnit := fun h => by
            have hg1' := congrArg g.linearEquiv h
            rw [hgP, g.preserves_unit] at hg1'
            have htr := congrArg albertTrace hg1'
            rw [(diagAtom_isAtom k0).2] at htr
            have hau : albertTrace albertUnit = 3 := by simp [albertTrace, albertUnit]
            linarith
          exact ⟨hPmem, hPid, hPne0, hPne1, hgP⟩
        have p0 := mk2 0 (d 0) (d 1) (d 2) rfl h01 h02 (fun j hj => by fin_cases j <;> simp at hj ⊢)
        have p1 := mk2 1 (d 1) (d 0) (d 2) rfl (Ne.symm h01) h12 (fun j hj => by fin_cases j <;> simp at hj ⊢)
        have p2 := mk2 2 (d 2) (d 0) (d 1) rfl (Ne.symm h02) (Ne.symm h12) (fun j hj => by fin_cases j <;> simp at hj ⊢)
        refine ⟨[(d 0, ((d 0 - d 1) * (d 0 - d 2))⁻¹ • jordanMul (x - d 1 • albertUnit) (x - d 2 • albertUnit)),
                 (d 1, ((d 1 - d 0) * (d 1 - d 2))⁻¹ • jordanMul (x - d 0 • albertUnit) (x - d 2 • albertUnit)),
                 (d 2, ((d 2 - d 0) * (d 2 - d 1))⁻¹ • jordanMul (x - d 0 • albertUnit) (x - d 1 • albertUnit))],
          ?_, by simp, ?_⟩
        · intro t ht; simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
          rcases ht with rfl | rfl | rfl
          · exact ⟨p0.1, p0.2.1, p0.2.2.1, p0.2.2.2.1⟩
          · exact ⟨p1.1, p1.2.1, p1.2.2.1, p1.2.2.2.1⟩
          · exact ⟨p2.1, p2.2.1, p2.2.2.1, p2.2.2.2.1⟩
        · apply g.linearEquiv.injective
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
            map_add, map_smul, p0.2.2.2.2, p1.2.2.2.2, p2.2.2.2.2]
          change y = _
          rw [hy_eq]; abel

private theorem atom_of_nontrivial_idempotent_in_subalgebra (B : NativeJordanSubalgebra)
    {c : Albert} (hcB : c ∈ B.carrier) (hcid : jordanMul c c = c)
    (hc0 : c ≠ 0) (hc1 : c ≠ albertUnit) :
    (IsAtom c) ∨ (IsAtom (albertUnit - c) ∧ albertUnit - c ∈ B.carrier) := by
  rcases idempotent_dichotomy c hcid with ⟨rfl, _⟩ | ⟨ha, _⟩ | ⟨⟨q, hq, hcq⟩, _⟩ | ⟨rfl, _⟩
  · exact absurd rfl hc0
  · exact Or.inl ha
  · refine Or.inr ⟨?_, B.carrier.sub_mem B.unit_mem hcB⟩
    have hqc : albertUnit - c = q := by rw [hcq]; abel
    rw [hqc]; exact hq
  · exact absurd rfl hc1

private theorem subalgebra_exists_atom_of_ne_span_unit (B : NativeJordanSubalgebra)
    (hB : ¬ B.carrier ≤ Submodule.span ℝ {albertUnit}) :
    ∃ q ∈ B.carrier, IsAtom q := by
  obtain ⟨x, hxB, hx_ns⟩ := Set.not_subset.mp hB
  obtain ⟨L, hL, hLne, _⟩ := subalgebra_spectral_decomp B hxB hx_ns
  cases L with
  | nil => exact absurd rfl hLne
  | cons t ts =>
    have ht := hL t List.mem_cons_self
    rcases atom_of_nontrivial_idempotent_in_subalgebra B ht.1 ht.2.1 ht.2.2.1 ht.2.2.2 with h | h
    · exact ⟨t.2, ht.1, h⟩
    · exact ⟨albertUnit - t.2, h.2, h.1⟩

private theorem submodule_sum_map_mem (S : Submodule ℝ Albert) (L : List (ℝ × Albert))
    (hL : ∀ t ∈ L, t.2 ∈ S) : (L.map fun p => p.1 • p.2).sum ∈ S := by
  induction L with
  | nil => simp [S.zero_mem]
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons]
    exact S.add_mem (S.smul_mem _ (hL t List.mem_cons_self))
      (ih fun u hu => hL u (List.mem_cons.mpr (Or.inr hu)))

private theorem subalgebra_exists_atom_outside_line (B : NativeJordanSubalgebra)
    (q : Albert) (hq : IsAtom q) (hB : ¬ B.carrier ≤ (lineSubalgebra q hq).carrier) :
    ∃ p ∈ B.carrier, IsAtom p ∧ p ∉ (lineSubalgebra q hq).carrier := by
  obtain ⟨x, hxB, hxL⟩ := Set.not_subset.mp hB
  have hspan : Submodule.span ℝ {albertUnit} ≤ (lineSubalgebra q hq).carrier :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (lineSubalgebra q hq).unit_mem)
  have hx_ns : x ∉ Submodule.span ℝ {albertUnit} := fun h => hxL (hspan h)
  obtain ⟨L, hL, _, hxsum⟩ := subalgebra_spectral_decomp B hxB hx_ns
  have hex : ∃ t ∈ L, t.2 ∉ (lineSubalgebra q hq).carrier := by
    by_contra hnot
    push Not at hnot
    apply hxL
    rw [hxsum]
    exact submodule_sum_map_mem (lineSubalgebra q hq).carrier L hnot
  obtain ⟨t, htL, ht_out⟩ := hex
  have ht := hL t htL
  rcases atom_of_nontrivial_idempotent_in_subalgebra B ht.1 ht.2.1 ht.2.2.1 ht.2.2.2 with h | h
  · exact ⟨t.2, ht.1, h, ht_out⟩
  · refine ⟨albertUnit - t.2, h.2, h.1, fun hin => ht_out ?_⟩
    have heq : t.2 = albertUnit - (albertUnit - t.2) := by abel
    rw [heq]
    exact (lineSubalgebra q hq).carrier.sub_mem (lineSubalgebra q hq).unit_mem hin

private theorem lem_five_sub_core (k : CDLevel) (B : NativeJordanSubalgebra)
    (hBk_lt : B.carrier < (H3Subalgebra k).carrier)
    (hnotline : ¬ ∃ (q : Albert) (hq : IsAtom q), q ∈ (H3Subalgebra k).carrier ∧
      B.carrier ≤ (lineSubalgebra q hq).carrier) :
    ∃ (α : H3Auto k) (F : OctSubalgebra),
      F.carrier < (octSubalgebraOfLevel k).carrier ∧
      ∀ x : Albert, x ∈ B.carrier ↔
        ∃ hx : x ∈ (H3Subalgebra k).carrier,
          (α.toIso.toLinearEquiv ⟨x, hx⟩).1 ∈ (jordanSubalgebraH3 F).carrier := by
  have hBk : B.carrier ≤ (H3Subalgebra k).carrier := hBk_lt.le
  have hnot_span : ¬ B.carrier ≤ Submodule.span ℝ {albertUnit} := by
    intro hle
    apply hnotline
    refine ⟨diagAtom 0, diagAtom_isAtom 0, diagAtom_mem_H3Subalgebra k 0,
      hle.trans (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (lineSubalgebra _ _).unit_mem))⟩
  obtain ⟨q, hqB, hq⟩ := subalgebra_exists_atom_of_ne_span_unit B hnot_span
  have hqK : q ∈ (H3Subalgebra k).carrier := hBk hqB
  have hnot_line_q : ¬ B.carrier ≤ (lineSubalgebra q hq).carrier := fun h => hnotline ⟨q, hq, hqK, h⟩
  obtain ⟨p, hpB, hp, hp_off⟩ := subalgebra_exists_atom_outside_line B q hq hnot_line_q
  have hpK : p ∈ (H3Subalgebra k).carrier := hBk hpB
  let f := albertUnit - q
  let w := quadraticMap f p
  let t := albertTrace w
  let r := t⁻¹ • w
  let fr := f - r
  obtain ⟨g0, hg0⟩ := atom_to_diagAtom0 q hq
  let p0 := g0.linearEquiv p
  have hp0 : IsAtom p0 := g0.map_isAtom hp
  have hp0_sum : p0.1 0 + p0.1 1 + p0.1 2 = 1 := by
    simpa [albertTrace, Fin.sum_univ_three] using hp0.2
  have hgw : g0.linearEquiv w = (![0, p0.1 1, p0.1 2], ![0, 0, p0.2 2]) := by
    change g0.linearEquiv (quadraticMap (albertUnit - q) p) = _
    rw [auto_map_quadraticMap, map_sub, g0.preserves_unit, hg0]
    exact quadraticMap_compl_diagAtom0 p0
  have ht_val : t = 1 - p0.1 0 := by
    change albertTrace w = 1 - p0.1 0
    rw [← g0.preserves_trace w, hgw]
    simp only [albertTrace, Fin.sum_univ_three]; dsimp; linarith
  have hp0_d0_ne0 : p0.1 0 ≠ 0 := by
    intro h0
    have htp : tracePairing q p = 0 := by
      rw [← g0.map_tracePairing q p, hg0, tracePairing_diagAtom0]; exact h0
    have hj : jordanMul q p = 0 :=
      (support_of_atom_zero_pairing acceptedAtomAndRankOneBridge hq ⟨p, hp.1.symm⟩ htp).1
    apply hp_off; rw [mem_lineSubalgebra_iff, hj, htp, zero_smul]
  have hp0_d0_ne1 : p0.1 0 ≠ 1 := by
    intro h1
    have hd1 : p0.1 1 = 0 := by linarith [isAtom_diag_nonneg hp0 1, isAtom_diag_nonneg hp0 2]
    have hd2 : p0.1 2 = 0 := by linarith
    have hsharp := albertSharp_of_isAtom hp0
    have ho0 : p0.2 0 = 0 := (octNormSq_eq_zero _).mp (by
      have h := congrArg (fun a : Albert => a.1 2) hsharp
      rw [albertSharp_fst_2, albert_zero_fst, h1, hd1, mul_zero, zero_sub, neg_eq_zero] at h; exact h)
    have ho1 : p0.2 1 = 0 := (octNormSq_eq_zero _).mp (by
      have h := congrArg (fun a : Albert => a.1 1) hsharp
      rw [albertSharp_fst_1, albert_zero_fst, h1, hd2, mul_zero, zero_sub, neg_eq_zero] at h; exact h)
    have ho2 : p0.2 2 = 0 := (octNormSq_eq_zero _).mp (by
      have h := congrArg (fun a : Albert => a.1 0) hsharp
      rw [albertSharp_fst_0, albert_zero_fst, hd1, hd2, mul_zero, zero_sub, neg_eq_zero] at h; exact h)
    have hpq : p = q := g0.linearEquiv.injective (by rw [hg0]; exact albert_ext h1 hd1 hd2 ho0 ho1 ho2)
    apply hp_off; rw [hpq]
    exact (mem_lineSubalgebra_iff q hq q).mpr (by rw [hq.1]; unfold tracePairing; rw [hq.1, hq.2, one_smul])
  have ht_pos : 0 < t := by rw [ht_val]; linarith [lt_of_le_of_ne (isAtom_diag_le_one hp0 0) hp0_d0_ne1]
  have hw_props := compl_atom_compress_sq hq hp
  have hr_atom : IsAtom r := by
    constructor
    · change jordanMul (t⁻¹ • w) (t⁻¹ • w) = t⁻¹ • w
      rw [jordanMul_smul_left, jordanMul_smul_right, hw_props.1, smul_smul, smul_smul]
      have ht : albertTrace (quadraticMap (albertUnit - q) p) = t := rfl
      rw [ht]; congr 1; field_simp [ht_pos.ne']
    · change albertTrace (t⁻¹ • w) = 1
      rw [albertTrace_smul]; exact inv_mul_cancel₀ ht_pos.ne'
  have hqr : jordanMul q r = 0 := by
    change jordanMul q (t⁻¹ • w) = 0
    rw [jordanMul_smul_right, hw_props.2.2.2, smul_zero]
  have hfr_atom : IsAtom fr := by
    constructor
    · change jordanMul (albertUnit - q - r) (albertUnit - q - r) = albertUnit - q - r
      simp only [jordanMul_sub_left, jordanMul_sub_right, jordanMul_albertUnit_left,
        jordanMul_albertUnit_right, hq.1, hr_atom.1, hqr,
        show jordanMul r q = 0 from by rw [jordanMul_comm]; exact hqr]
      abel
    · change albertTrace (albertUnit - q - r) = 1
      have hau : albertTrace albertUnit = 3 := by simp [albertTrace, albertUnit]
      rw [albertTrace_sub, albertTrace_sub, hau, hq.2, hr_atom.2]; norm_num
  have hqfr : jordanMul q fr = 0 := by
    change jordanMul q (albertUnit - q - r) = 0
    rw [jordanMul_sub_right, jordanMul_sub_right, jordanMul_albertUnit_right, hq.1, hqr, sub_self, sub_zero]
  have hrfr : jordanMul r fr = 0 := by
    change jordanMul r (albertUnit - q - r) = 0
    rw [jordanMul_sub_right, jordanMul_sub_right, jordanMul_albertUnit_right,
      show jordanMul r q = 0 from by rw [jordanMul_comm]; exact hqr, hr_atom.1]
    abel
  have hfr_p : jordanMul fr p = 0 := by
    have htp : tracePairing fr p = 0 := by
      have hgfr : g0.linearEquiv fr = (albertUnit - diagAtom 0) - t⁻¹ • g0.linearEquiv w := by
        dsimp [fr, f, r]; rw [map_sub, map_sub, g0.preserves_unit, hg0, map_smul]
      rw [← g0.map_tracePairing fr p, hgfr, tracePairing_sub_left, tracePairing_sub_left,
        tracePairing_smul_left, hgw]
      rw [show tracePairing albertUnit p0 = 1 by
        rw [tracePairing_eq_coords]; simp [albertUnit_fst, albertUnit_snd, octDot_zero_left, hp0_sum]]
      rw [show tracePairing (diagAtom 0) p0 = p0.1 0 from tracePairing_diagAtom0 p0]
      let zw : Albert := (![0, p0.1 1, p0.1 2], ![0, 0, p0.2 2])
      have hzw : tracePairing zw p0 = p0.1 1 * p0.1 1 + p0.1 2 * p0.1 2 + 2 * octDot (p0.2 2) (p0.2 2) := by
        rw [tracePairing_eq_coords]; simp [zw, octDot_zero_left]
      change 1 - p0.1 0 - t⁻¹ * tracePairing zw p0 = 0
      rw [hzw, octDot_self]
      have hsharp0 := congrArg (fun a : Albert => a.1 0) (albertSharp_of_isAtom hp0)
      rw [albertSharp_fst_0, albert_zero_fst, sub_eq_zero] at hsharp0
      rw [← hsharp0]
      have h12sum : p0.1 1 + p0.1 2 = t := by linarith
      field_simp [ht_pos.ne']; rw [← ht_val, ← h12sum]; ring
    exact (support_of_atom_zero_pairing acceptedAtomAndRankOneBridge hfr_atom ⟨p, hp.1.symm⟩ htp).1
  have hfB : f ∈ B.carrier := B.carrier.sub_mem B.unit_mem hqB
  have hwB : w ∈ B.carrier := (peirce_components_mem_subalgebra B hqB hpB).2.2
  have hrB : r ∈ B.carrier := B.carrier.smul_mem _ hwB
  have hfrB : fr ∈ B.carrier := B.carrier.sub_mem hfB hrB
  let Frm : NativeJordanFrame :=
    { atom := ![fr, q, r]
      atoms := fun m => by fin_cases m <;> dsimp <;> [exact hfr_atom; exact hq; exact hr_atom]
      orthogonal := fun i j hij => by
        fin_cases i <;> fin_cases j <;> dsimp
        · exact absurd rfl hij
        · rw [jordanMul_comm]; exact hqfr
        · rw [jordanMul_comm]; exact hrfr
        · exact hqfr
        · exact absurd rfl hij
        · exact hqr
        · exact hrfr
        · rw [jordanMul_comm]; exact hqr
        · exact absurd rfl hij
      sum_unit := by rw [Fin.sum_univ_three]; change fr + q + r = albertUnit; dsimp [fr, f]; abel }
  have hFrm_mem : ∀ m : Fin 3, Frm.atom m ∈ (H3Subalgebra k).carrier := fun m => by
    fin_cases m <;> dsimp [Frm] <;> [exact hBk hfrB; exact hqK; exact hBk hrB]
  obtain ⟨α₀, hα₀⟩ := H3Auto.frame k Frm hFrm_mem
  obtain ⟨α₁, hα₁_diag, r1, hr1_nn, hα₁_slot12⟩ :=
    H3Auto.frameStab_slot12_real k (α₀.toIso.toLinearEquiv ⟨p, hpK⟩).1 (α₀.toIso.toLinearEquiv ⟨p, hpK⟩).2
  let α01 := α₀.trans α₁
  let pushSub : H3Auto k → NativeJordanSubalgebra := fun γ =>
    { carrier :=
        { carrier := {y : Albert | ∃ hy : y ∈ (H3Subalgebra k).carrier,
            (γ.toIso.toLinearEquiv.symm ⟨y, hy⟩).1 ∈ B.carrier}
          add_mem' := fun {a b} ⟨ha, ha'⟩ ⟨hb, hb'⟩ =>
            ⟨(H3Subalgebra k).carrier.add_mem ha hb, by
              have h : (⟨a + b, (H3Subalgebra k).carrier.add_mem ha hb⟩ : (H3Subalgebra k).carrier) =
                  ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
              rw [h, map_add, Submodule.coe_add]
              exact B.carrier.add_mem ha' hb'⟩
          zero_mem' := ⟨(H3Subalgebra k).carrier.zero_mem, by
            have h : (⟨0, (H3Subalgebra k).carrier.zero_mem⟩ : (H3Subalgebra k).carrier) = 0 := rfl
            rw [h, map_zero, Submodule.coe_zero]
            exact B.carrier.zero_mem⟩
          smul_mem' := fun c {a} ⟨ha, ha'⟩ =>
            ⟨(H3Subalgebra k).carrier.smul_mem c ha, by
              have h : (⟨c • a, (H3Subalgebra k).carrier.smul_mem c ha⟩ : (H3Subalgebra k).carrier) =
                  c • ⟨a, ha⟩ := rfl
              rw [h, map_smul, Submodule.coe_smul]
              exact B.carrier.smul_mem c ha'⟩ }
      unit_mem := ⟨(H3Subalgebra k).unit_mem, by
        have h : (γ.toIso.symm.toLinearEquiv ⟨albertUnit, (H3Subalgebra k).unit_mem⟩).1 ∈ B.carrier := by
          rw [γ.toIso.symm.map_unit]; exact B.unit_mem
        exact h⟩
      product_mem := fun a ⟨ha, ha'⟩ b ⟨hb, hb'⟩ =>
        ⟨(H3Subalgebra k).product_mem a ha b hb, by
          change (γ.toIso.symm.toLinearEquiv ⟨jordanMul a b, (H3Subalgebra k).product_mem a ha b hb⟩).1 ∈ B.carrier
          rw [γ.toIso.symm.map_jordan ⟨a, ha⟩ ⟨b, hb⟩]
          exact B.product_mem _ ha' _ hb'⟩ }
  have mem_pushSub : ∀ (γ : H3Auto k) (z : (H3Subalgebra k).carrier),
      z.1 ∈ B.carrier → (γ.toIso.toLinearEquiv z).1 ∈ (pushSub γ).carrier := fun γ z hz =>
    ⟨(γ.toIso.toLinearEquiv z).2, by
      have heq : (⟨(γ.toIso.toLinearEquiv z).1, (γ.toIso.toLinearEquiv z).2⟩ : (H3Subalgebra k).carrier) =
          γ.toIso.toLinearEquiv z := rfl
      rw [heq, LinearEquiv.symm_apply_apply]; exact hz⟩
  let B₂ := pushSub α01
  have hdiag0_2 : diagAtom 0 ∈ B₂.carrier := by
    have h := mem_pushSub α01 ⟨fr, hBk hfrB⟩ hfrB
    rw [H3Auto.toIso_trans] at h
    have h0 : α₀.toIso.toLinearEquiv ⟨fr, hBk hfrB⟩ = ⟨diagAtom 0, diagAtom_mem_H3Subalgebra k 0⟩ :=
      Subtype.ext (hα₀ 0)
    rw [h0, hα₁_diag 0] at h; exact h
  have hdiag1_2 : diagAtom 1 ∈ B₂.carrier := by
    have h := mem_pushSub α01 ⟨q, hqK⟩ hqB
    rw [H3Auto.toIso_trans] at h
    have h0 : α₀.toIso.toLinearEquiv ⟨q, hqK⟩ = ⟨diagAtom 1, diagAtom_mem_H3Subalgebra k 1⟩ :=
      Subtype.ext (hα₀ 1)
    rw [h0, hα₁_diag 1] at h; exact h
  have hdiag2_2 : diagAtom 2 ∈ B₂.carrier := by
    have h := mem_pushSub α01 ⟨r, hBk hrB⟩ hrB
    rw [H3Auto.toIso_trans] at h
    have h0 : α₀.toIso.toLinearEquiv ⟨r, hBk hrB⟩ = ⟨diagAtom 2, diagAtom_mem_H3Subalgebra k 2⟩ :=
      Subtype.ext (hα₀ 2)
    rw [h0, hα₁_diag 2] at h; exact h
  have hp1_in : (α01.toIso.toLinearEquiv ⟨p, hpK⟩).1 ∈ B₂.carrier := mem_pushSub α01 ⟨p, hpK⟩ hpB
  have hp1_atom : IsAtom (α01.toIso.toLinearEquiv ⟨p, hpK⟩).1 := iso_maps_atom α01.toIso ⟨p, hpK⟩ hp
  have hp1_slot12 : (α01.toIso.toLinearEquiv ⟨p, hpK⟩).1.2 2 = octonionScalar r1 := by
    rw [H3Auto.toIso_trans]; exact hα₁_slot12
  have hp1_fr : jordanMul (diagAtom 0) (α01.toIso.toLinearEquiv ⟨p, hpK⟩).1 = 0 := by
    have h0 : (α01.toIso.toLinearEquiv ⟨fr, hBk hfrB⟩).1 = diagAtom 0 := by
      rw [H3Auto.toIso_trans, show α₀.toIso.toLinearEquiv ⟨fr, hBk hfrB⟩ =
        ⟨diagAtom 0, diagAtom_mem_H3Subalgebra k 0⟩ from Subtype.ext (hα₀ 0)]
      exact hα₁_diag 0
    rw [← h0, ← α01.toIso.map_jordanMul_eq ⟨fr, hBk hfrB⟩ ⟨p, hpK⟩]
    have hzero : (⟨jordanMul fr p, (H3Subalgebra k).product_mem _ (hBk hfrB) _ hpK⟩ :
        (H3Subalgebra k).carrier) = 0 := Subtype.ext hfr_p
    rw [hzero, map_zero, Submodule.coe_zero]
  have hp1_coords := diag0_ortho_atom_coords hp1_atom hp1_fr
  have hr1_pos : 0 < r1 := by
    have hr1_ne0 : r1 ≠ 0 := by
      intro hr0
      have hprod0 : (α01.toIso.toLinearEquiv ⟨p, hpK⟩).1.1 1 *
          (α01.toIso.toLinearEquiv ⟨p, hpK⟩).1.1 2 = 0 := by
        have hns := hp1_coords.2.2.2.2
        rw [hp1_slot12, hr0, octonionScalar_zero, (octNormSq_eq_zero 0).mpr rfl] at hns
        exact hns.symm
      rcases mul_eq_zero.mp hprod0 with h1 | h2
      · have hd2 : (α01.toIso.toLinearEquiv ⟨p, hpK⟩).1.1 2 = 1 := by linarith [hp1_coords.2.1]
        have hp_d2 : (α01.toIso.toLinearEquiv ⟨p, hpK⟩).1 = diagAtom 2 := by
          apply albert_ext <;> simp [diagAtom_fst, diagAtom_snd, hp1_coords.1, h1, hd2,
            hp1_coords.2.2.1, hp1_coords.2.2.2.1, hp1_slot12, hr0, octonionScalar_zero]
        have hpr : p = r := by
          have hsub : α01.toIso.toLinearEquiv ⟨p, hpK⟩ = α01.toIso.toLinearEquiv ⟨r, hBk hrB⟩ :=
            Subtype.ext (by
              rw [hp_d2, H3Auto.toIso_trans, show α₀.toIso.toLinearEquiv ⟨r, hBk hrB⟩ =
                ⟨diagAtom 2, diagAtom_mem_H3Subalgebra k 2⟩ from Subtype.ext (hα₀ 2), hα₁_diag 2])
          exact congrArg Subtype.val (α01.toIso.toLinearEquiv.injective hsub)
        apply hp_off; rw [mem_lineSubalgebra_iff, hpr, hqr, ← hpr]
        rw [show tracePairing q p = 0 by unfold tracePairing; rw [hpr, hqr, albertTrace_zero], zero_smul]
      · have hd1 : (α01.toIso.toLinearEquiv ⟨p, hpK⟩).1.1 1 = 1 := by linarith [hp1_coords.2.1]
        have hp_d1 : (α01.toIso.toLinearEquiv ⟨p, hpK⟩).1 = diagAtom 1 := by
          apply albert_ext <;> simp [diagAtom_fst, diagAtom_snd, hp1_coords.1, hd1, h2,
            hp1_coords.2.2.1, hp1_coords.2.2.2.1, hp1_slot12, hr0, octonionScalar_zero]
        have hpq : p = q := by
          have hsub : α01.toIso.toLinearEquiv ⟨p, hpK⟩ = α01.toIso.toLinearEquiv ⟨q, hqK⟩ :=
            Subtype.ext (by
              rw [hp_d1, H3Auto.toIso_trans, show α₀.toIso.toLinearEquiv ⟨q, hqK⟩ =
                ⟨diagAtom 1, diagAtom_mem_H3Subalgebra k 1⟩ from Subtype.ext (hα₀ 1), hα₁_diag 1])
          exact congrArg Subtype.val (α01.toIso.toLinearEquiv.injective hsub)
        apply hp_off; rw [hpq]
        exact (mem_lineSubalgebra_iff q hq q).mpr (by rw [hq.1]; unfold tracePairing; rw [hq.1, hq.2, one_smul])
    exact lt_of_le_of_ne hr1_nn (Ne.symm hr1_ne0)
  have hs12_2 : slotElem12 octOne ∈ B₂.carrier := by
    have hpe : (4 : ℝ) • jordanMul (diagAtom 1)
        (jordanMul (diagAtom 2) (α01.toIso.toLinearEquiv ⟨p, hpK⟩).1) =
        slotElem12 (octonionScalar r1) := by
      rw [peirce12_extract, hp1_slot12]
    have hmem : slotElem12 (octonionScalar r1) ∈ B₂.carrier := by
      rw [← hpe]
      exact B₂.carrier.smul_mem _ (B₂.product_mem _ hdiag1_2 _ (B₂.product_mem _ hdiag2_2 _ hp1_in))
    have hsm : slotElem12 octOne = r1⁻¹ • slotElem12 (octonionScalar r1) := by
      rw [octonionScalar_eq_smul r1, ← octOne_eq_scalar]
      apply albert_ext <;> simp [slotElem12_fst, slotElem12_snd_0, slotElem12_snd_1, slotElem12_snd_2,
        albert_smul_fst, albert_smul_snd]
      rw [smul_smul, inv_mul_cancel₀ hr1_pos.ne', one_smul]
    rw [hsm]; exact B₂.carrier.smul_mem _ hmem
  have hB₂_not_line : ¬ B₂.carrier ≤ (lineSubalgebra (diagAtom 0) (diagAtom_isAtom 0)).carrier := by
    intro hle
    apply hnotline
    let q' := (α01.toIso.toLinearEquiv.symm ⟨diagAtom 0, diagAtom_mem_H3Subalgebra k 0⟩).1
    have hq' : IsAtom q' :=
      iso_maps_atom α01.toIso.symm ⟨diagAtom 0, diagAtom_mem_H3Subalgebra k 0⟩ (diagAtom_isAtom 0)
    have hq'K : q' ∈ (H3Subalgebra k).carrier :=
      (α01.toIso.toLinearEquiv.symm ⟨diagAtom 0, diagAtom_mem_H3Subalgebra k 0⟩).2
    refine ⟨q', hq', hq'K, fun x hx => ?_⟩
    have hx2 := hle (mem_pushSub α01 ⟨x, hBk hx⟩ hx)
    rw [mem_lineSubalgebra_iff_idem] at hx2 ⊢
    have h0 : (α01.toIso.toLinearEquiv ⟨q', hq'K⟩).1 = diagAtom 0 := by
      have hsub : (⟨q', hq'K⟩ : (H3Subalgebra k).carrier) =
          α01.toIso.toLinearEquiv.symm ⟨diagAtom 0, diagAtom_mem_H3Subalgebra k 0⟩ := rfl
      rw [hsub, LinearEquiv.apply_symm_apply]
    have hmul1 : (α01.toIso.toLinearEquiv ⟨jordanMul q' (jordanMul q' x),
        (H3Subalgebra k).product_mem _ hq'K _ ((H3Subalgebra k).product_mem _ hq'K _ (hBk hx))⟩) =
        α01.toIso.toLinearEquiv ⟨jordanMul q' x,
          (H3Subalgebra k).product_mem _ hq'K _ (hBk hx)⟩ := by
      apply Subtype.ext
      have hm1 := α01.toIso.map_jordanMul_eq ⟨q', hq'K⟩
        ⟨jordanMul q' x, (H3Subalgebra k).product_mem _ hq'K _ (hBk hx)⟩
      have hm2 := α01.toIso.map_jordanMul_eq ⟨q', hq'K⟩ ⟨x, hBk hx⟩
      rw [hm1, hm2, h0, hx2]
    exact congrArg Subtype.val (α01.toIso.toLinearEquiv.injective hmul1)
  obtain ⟨p', hp'B, hp'_atom, hp'_out⟩ :=
    subalgebra_exists_atom_outside_line B₂ (diagAtom 0) (diagAtom_isAtom 0) hB₂_not_line
  have hp'_slots : p'.2 0 ≠ 0 ∨ p'.2 1 ≠ 0 := by
    by_contra hnot
    push Not at hnot
    apply hp'_out
    rw [mem_lineSubalgebra_iff]
    exact (mem_line_diag0_iff p').mpr hnot
  have hex_w : ∃ w : Octonion, w ≠ 0 ∧ slotElem02 w ∈ B₂.carrier := by
    rcases hp'_slots with h0 | h1
    · refine ⟨p'.2 0, h0, ?_⟩
      have hs01 : slotElem01 (p'.2 0) ∈ B₂.carrier := by
        rw [← peirce01_extract p']
        exact B₂.carrier.smul_mem _ (B₂.product_mem _ hdiag0_2 _ (B₂.product_mem _ hdiag1_2 _ hp'B))
      exact slotElem01_mem_02_of_mem hs12_2 hs01
    · refine ⟨p'.2 1, h1, ?_⟩
      rw [← peirce02_extract p']
      exact B₂.carrier.smul_mem _ (B₂.product_mem _ hdiag0_2 _ (B₂.product_mem _ hdiag2_2 _ hp'B))
  obtain ⟨w0, hw0_ne, hw0_mem⟩ := hex_w
  have hw0_K : slotElem02 w0 ∈ (H3Subalgebra k).carrier := hw0_mem.1
  obtain ⟨α₂, hα₂_diag, hα₂_12, r2, hr2_nn, hα₂_slot02⟩ :=
    H3Auto.frameAnd12OneStab_slot02_real k (slotElem02 w0) hw0_K
  let α := α01.trans α₂
  let B₃ := pushSub α
  have hdiag_B₃ : ∀ m : Fin 3, diagAtom m ∈ B₃.carrier := fun m => by
    have hm : diagAtom m ∈ B₂.carrier := by fin_cases m <;> [exact hdiag0_2; exact hdiag1_2; exact hdiag2_2]
    have hmem : (α₂.toIso.toLinearEquiv ⟨diagAtom m, diagAtom_mem_H3Subalgebra k m⟩).1 ∈ B₃.carrier := by
      have hsrc := hm.2
      have hstep : (α.toIso.toLinearEquiv (α01.toIso.toLinearEquiv.symm
          ⟨diagAtom m, diagAtom_mem_H3Subalgebra k m⟩)).1 =
          (α₂.toIso.toLinearEquiv ⟨diagAtom m, diagAtom_mem_H3Subalgebra k m⟩).1 := by
        rw [H3Auto.toIso_trans, LinearEquiv.apply_symm_apply]
      rw [← hstep]
      exact mem_pushSub α _ hsrc
    rwa [hα₂_diag m] at hmem
  have hs12_B₃ : slotElem12 octOne ∈ B₃.carrier := by
    have hmem : (α₂.toIso.toLinearEquiv ⟨slotElem12 octOne, slotElem12_octOne_mem_H3Subalgebra k⟩).1 ∈ B₃.carrier := by
      have hsrc := hs12_2.2
      have hstep : (α.toIso.toLinearEquiv (α01.toIso.toLinearEquiv.symm
          ⟨slotElem12 octOne, slotElem12_octOne_mem_H3Subalgebra k⟩)).1 =
          (α₂.toIso.toLinearEquiv ⟨slotElem12 octOne, slotElem12_octOne_mem_H3Subalgebra k⟩).1 := by
        rw [H3Auto.toIso_trans, LinearEquiv.apply_symm_apply]
      rw [← hstep]
      exact mem_pushSub α _ hsrc
    rwa [hα₂_12 (slotElem12_octOne_mem_H3Subalgebra k)] at hmem
  have hpe_w : (α₂.toIso.toLinearEquiv ⟨slotElem02 w0, hw0_K⟩).1 = slotElem02 (octonionScalar r2) := by
    have h1 : slotElem02 w0 = (4 : ℝ) • jordanMul (diagAtom 0) (jordanMul (diagAtom 2) (slotElem02 w0)) :=
      (peirce02_extract (slotElem02 w0)).symm
    have h1_sub : (⟨slotElem02 w0, hw0_K⟩ : (H3Subalgebra k).carrier) =
        (4 : ℝ) • ⟨jordanMul (diagAtom 0) (jordanMul (diagAtom 2) (slotElem02 w0)),
          (H3Subalgebra k).product_mem _ (diagAtom_mem_H3Subalgebra k 0) _
            ((H3Subalgebra k).product_mem _ (diagAtom_mem_H3Subalgebra k 2) _ hw0_K)⟩ :=
      Subtype.ext h1
    have hm1 := α₂.toIso.map_jordanMul_eq ⟨diagAtom 0, diagAtom_mem_H3Subalgebra k 0⟩
      ⟨jordanMul (diagAtom 2) (slotElem02 w0),
        (H3Subalgebra k).product_mem _ (diagAtom_mem_H3Subalgebra k 2) _ hw0_K⟩
    have hm2 := α₂.toIso.map_jordanMul_eq ⟨diagAtom 2, diagAtom_mem_H3Subalgebra k 2⟩
      ⟨slotElem02 w0, hw0_K⟩
    calc
      (α₂.toIso.toLinearEquiv ⟨slotElem02 w0, hw0_K⟩).1
          = (4 : ℝ) • jordanMul (diagAtom 0) (jordanMul (diagAtom 2)
              (α₂.toIso.toLinearEquiv ⟨slotElem02 w0, hw0_K⟩).1) := by
            conv_lhs => rw [h1_sub, map_smul, Submodule.coe_smul, hm1, hm2, hα₂_diag 0, hα₂_diag 2]
      _ = slotElem02 (octonionScalar r2) := by
            rw [peirce02_extract, hα₂_slot02]
  have hr2_pos : 0 < r2 := by
    have hr2_ne0 : r2 ≠ 0 := by
      intro hr0
      have hzero : α₂.toIso.toLinearEquiv ⟨slotElem02 w0, hw0_K⟩ = 0 := Subtype.ext (by
        rw [hpe_w, hr0, octonionScalar_zero]; apply albert_ext <;> rfl)
      have hw0_z : (⟨slotElem02 w0, hw0_K⟩ : (H3Subalgebra k).carrier) = 0 :=
        α₂.toIso.toLinearEquiv.injective (by rw [hzero, map_zero])
      have hslot0 : w0 = 0 := by
        simpa [slotElem02_snd_1, albert_zero_snd] using
          congrArg (fun z : (H3Subalgebra k).carrier => z.1.2 1) hw0_z
      exact hw0_ne hslot0
    exact lt_of_le_of_ne hr2_nn (Ne.symm hr2_ne0)
  have hs02_B₃ : slotElem02 octOne ∈ B₃.carrier := by
    have hmem : slotElem02 (octonionScalar r2) ∈ B₃.carrier := by
      rw [← hpe_w]
      have hstep : (α.toIso.toLinearEquiv (α01.toIso.toLinearEquiv.symm ⟨slotElem02 w0, hw0_K⟩)).1 =
          (α₂.toIso.toLinearEquiv ⟨slotElem02 w0, hw0_K⟩).1 := by
        rw [H3Auto.toIso_trans, LinearEquiv.apply_symm_apply]
      rw [← hstep]
      exact mem_pushSub α _ hw0_mem.2
    have hsm : slotElem02 octOne = r2⁻¹ • slotElem02 (octonionScalar r2) := by
      rw [octonionScalar_eq_smul r2, ← octOne_eq_scalar]
      apply albert_ext <;> simp [slotElem02_fst, slotElem02_snd_0, slotElem02_snd_1, slotElem02_snd_2,
        albert_smul_fst, albert_smul_snd]
      rw [smul_smul, inv_mul_cancel₀ hr2_pos.ne', one_smul]
    rw [hsm]; exact B₃.carrier.smul_mem _ hmem
  obtain ⟨F, _, hB₃_eq, _⟩ := lem_five_coord B₃ (hdiag_B₃ 0) (hdiag_B₃ 1) (hdiag_B₃ 2)
    (Or.inr (Or.inr ⟨hs02_B₃, hs12_B₃⟩))
  have hF_le : F.carrier ≤ (octSubalgebraOfLevel k).carrier := by
    intro a ha
    have ha01 : slotElem01 a ∈ B₃.carrier := by
      rw [hB₃_eq]
      exact ⟨ha, F.carrier.zero_mem, F.carrier.zero_mem⟩
    exact ha01.1.1
  have hF_ne : F.carrier ≠ (octSubalgebraOfLevel k).carrier := by
    intro heq
    have hB₃_top : B₃.carrier = (H3Subalgebra k).carrier := by
      rw [hB₃_eq]; ext z; simp [jordanSubalgebraH3, H3Subalgebra, heq]
    apply hBk_lt.ne
    apply le_antisymm hBk
    intro x hx
    have hx3 : (α.toIso.toLinearEquiv ⟨x, hx⟩).1 ∈ B₃.carrier := by
      rw [hB₃_top]; exact (α.toIso.toLinearEquiv ⟨x, hx⟩).2
    obtain ⟨hxK, hxB⟩ := hx3
    have heq' : (⟨(α.toIso.toLinearEquiv ⟨x, hx⟩).1, hxK⟩ : (H3Subalgebra k).carrier) =
        α.toIso.toLinearEquiv ⟨x, hx⟩ := rfl
    rwa [heq', LinearEquiv.symm_apply_apply] at hxB
  refine ⟨α, F, lt_of_le_of_ne hF_le hF_ne, fun x => ?_⟩
  constructor
  · intro hxB
    refine ⟨hBk hxB, ?_⟩
    rw [← hB₃_eq]
    exact mem_pushSub α ⟨x, hBk hxB⟩ hxB
  · rintro ⟨hxK, hxF⟩
    have hx3 : (α.toIso.toLinearEquiv ⟨x, hxK⟩).1 ∈ B₃.carrier := by
      rw [hB₃_eq]; exact hxF
    obtain ⟨_, hxB⟩ := hx3
    have heq' : (⟨(α.toIso.toLinearEquiv ⟨x, hxK⟩).1,
        (α.toIso.toLinearEquiv ⟨x, hxK⟩).2⟩ : (H3Subalgebra k).carrier) =
        α.toIso.toLinearEquiv ⟨x, hxK⟩ := rfl
    rwa [heq', LinearEquiv.symm_apply_apply] at hxB

private theorem exists_unit_quat_conj_to_I (q : Quaternion ℝ)
    (hq_re : q.re = 0) (hq_ns : quatNormSq q = 1) :
    ∃ w : Quaternion ℝ, quatNormSq w = 1 ∧ w * q * star w = ⟨0, 1, 0, 0⟩ := by
  let qI : Quaternion ℝ := ⟨0, 1, 0, 0⟩
  have hq_sq : q * q = -1 := by
    apply Quaternion.ext
    · simp [hq_re]; unfold quatNormSq at hq_ns; simp only [sq, hq_re] at hq_ns; linarith
    · simp [hq_re]; ring
    · simp [hq_re]; ring
    · simp [hq_re]; ring
  have hqI_sq : qI * qI = -1 := by apply Quaternion.ext <;> norm_num [qI]
  by_cases hneg : q = -qI
  · refine ⟨⟨0, 0, 1, 0⟩, by norm_num [quatNormSq], ?_⟩
    rw [hneg]
    apply Quaternion.ext <;> norm_num [qI]
  · have hne0 : q + qI ≠ 0 := fun h => hneg (eq_neg_of_add_eq_zero_left h)
    have hpos : 0 < quatNormSq (q + qI) := by
      have hnn : 0 ≤ quatNormSq (q + qI) := by unfold quatNormSq; positivity
      exact lt_of_le_of_ne hnn (Ne.symm fun h => hne0 ((assocCD_H.normSq_eq_zero (q + qI)).mp h))
    let r := Real.sqrt (quatNormSq (q + qI))
    have hrpos : 0 < r := Real.sqrt_pos.mpr hpos
    have hr2 : r ^ 2 = quatNormSq (q + qI) := Real.sq_sqrt hpos.le
    let w := (1 / r) • (q + qI)
    have hw_ns : quatNormSq w = 1 := by
      have hsc : quatNormSq w = (1 / r) ^ 2 * quatNormSq (q + qI) := by
        dsimp [w]; unfold quatNormSq; simp; ring
      rw [hsc, div_pow, one_pow, hr2]; field_simp [hrpos.ne']
    have hw_star : w * star w = 1 := by
      have h := assocCD_H.mul_star_self w
      change w * star w = quatNormSq w • 1 at h
      rw [h, hw_ns, one_smul]
    have hcomm : (q + qI) * q = qI * (q + qI) := by
      rw [add_mul, mul_add, hq_sq, hqI_sq]; abel
    have hwq : w * q = qI * w := by
      dsimp [w]
      rw [Algebra.smul_mul_assoc, hcomm, ← Algebra.mul_smul_comm]
    refine ⟨w, hw_ns, ?_⟩
    rw [hwq, mul_assoc, hw_star, mul_one]

private theorem linearIndependent_four_orthonormal_oct {v : Fin 4 → Octonion}
    (hnorm : ∀ i, octNormSq (v i) = 1) (horth : ∀ i j, i ≠ j → octDot (v i) (v j) = 0) :
    LinearIndependent ℝ v := by
  rw [Fintype.linearIndependent_iff]
  intro c hc k
  have hdot := congrArg (fun z : Octonion => octDot z (v k)) hc
  rw [octDot_zero_left] at hdot
  have hsum : octDot (∑ i : Fin 4, c i • v i) (v k) =
      ∑ i : Fin 4, c i * octDot (v i) (v k) := by
    simp only [Fin.sum_univ_four, octDot_add_left, octDot_smul_left]
  rw [hsum, Finset.sum_eq_single k] at hdot
  · rw [octDot_self, hnorm k, mul_one] at hdot; exact hdot
  · intro i _ hi; rw [horth i k hi, mul_zero]
  · intro hk; exact False.elim (hk (Finset.mem_univ k))

private theorem exists_quatEmbedding_superset_of_lt_top (F : OctSubalgebra)
    (hF : F.carrier < ⊤) :
    ∃ φ : Quaternion ℝ →ₗ[ℝ] Octonion, IsQuatEmbedding φ ∧ F.carrier ≤ LinearMap.range φ := by
  let imF : Submodule ℝ Octonion :=
    { carrier := {x : Octonion | x ∈ F.carrier ∧ octonionReal x = 0}
      add_mem' := fun {a b} ha hb =>
        ⟨F.carrier.add_mem ha.1 hb.1, by rw [octonionReal_add, ha.2, hb.2, add_zero]⟩
      zero_mem' := ⟨F.carrier.zero_mem, octonionReal_zero⟩
      smul_mem' := fun r {a} ha =>
        ⟨F.carrier.smul_mem r ha.1, by rw [octonionReal_smul, ha.2, mul_zero]⟩ }
  have him_mem : ∀ y ∈ F.carrier, octIm y ∈ imF := fun y hy => by
    refine ⟨?_, octonionReal_octIm y⟩
    unfold octIm
    exact F.carrier.sub_mem hy (by
      rw [octonionScalar_eq_smul, ← octOne_eq_scalar]
      exact F.carrier.smul_mem _ F.one_mem)
  by_cases hbot : imF = ⊥
  · refine ⟨quatEmbed1, quatEmbed1_isQuatEmbedding, fun y hy => ?_⟩
    have him0 : octIm y = 0 := by
      have hm := him_mem y hy
      rw [hbot, Submodule.mem_bot] at hm
      exact hm
    refine ⟨⟨octonionReal y, 0, 0, 0⟩, ?_⟩
    rw [oct_eq_scalar_add_octIm y, him0, add_zero]
    rw [quatEmbed1_apply]; rfl
  · obtain ⟨x0, hx0_mem, hx0_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    have hnx0 : 0 < octNormSq x0 :=
      lt_of_le_of_ne (octNormSq_nonneg _) (Ne.symm fun h => hx0_ne ((octNormSq_eq_zero _).mp h))
    let ru := Real.sqrt (octNormSq x0)
    let u := (1 / ru) • x0
    have hu_mem : u ∈ imF := imF.smul_mem _ hx0_mem
    have hu_norm : octNormSq u = 1 := by
      rw [octNormSq_smul, one_div, inv_pow, Real.sq_sqrt hnx0.le]; field_simp [(Real.sqrt_pos.mpr hnx0).ne']
    by_cases hspan : imF ≤ Submodule.span ℝ {u}
    · obtain ⟨φ, hφ, hu_rng, _⟩ := exists_quatEmbedding_containing_pair u u
      refine ⟨φ, hφ, fun y hy => ?_⟩
      have him_span := hspan (him_mem y hy)
      rw [Submodule.mem_span_singleton] at him_span
      obtain ⟨c, hc⟩ := him_span
      rw [oct_eq_scalar_add_octIm y, ← hc, octonionScalar_eq_smul, ← hφ.map_one]
      rcases hu_rng with ⟨qu, hqu⟩
      exact ⟨octonionReal y • (1 : Quaternion ℝ) + c • qu, by rw [map_add, map_smul, map_smul, hqu]⟩
    · obtain ⟨y, hy_mem, hy_not⟩ := Set.not_subset.mp hspan
      let v0 := y - octDot y u • u
      have hv0_mem : v0 ∈ imF := imF.sub_mem hy_mem (imF.smul_mem _ hu_mem)
      have hv0_ne : v0 ≠ 0 := by
        intro h
        apply hy_not
        rw [show y = octDot y u • u from sub_eq_zero.mp h]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
      have hnv0 : 0 < octNormSq v0 :=
        lt_of_le_of_ne (octNormSq_nonneg _) (Ne.symm fun h => hv0_ne ((octNormSq_eq_zero _).mp h))
      let rv := Real.sqrt (octNormSq v0)
      let v := (1 / rv) • v0
      have hv_mem : v ∈ imF := imF.smul_mem _ hv0_mem
      have hv_norm : octNormSq v = 1 := by
        rw [octNormSq_smul, one_div, inv_pow, Real.sq_sqrt hnv0.le]; field_simp [(Real.sqrt_pos.mpr hnv0).ne']
      have huv : octDot u v = 0 := by
        rw [octDot_smul_right, octDot_comm,
          show octDot v0 u = 0 from by simp [v0, octDot_sub_left, octDot_smul_left, octDot_self, hu_norm],
          mul_zero]
      obtain ⟨φ, hφ, ⟨qu, hqu⟩, ⟨qv, hqv⟩⟩ := exists_quatEmbedding_containing_pair u v
      let w := octonionMul u v
      have hw_mem : w ∈ F.carrier := F.mul_mem u hu_mem.1 v hv_mem.1
      have hw_rng : w ∈ LinearMap.range φ := ⟨qu * qv, by rw [hφ.map_mul, hqu, hqv]⟩
      have hw_re : octonionReal w = 0 := by
        rw [octonionReal_mul_imag_eq hu_mem.2 hv_mem.2, huv, neg_zero]
      have hw_norm : octNormSq w = 1 := by rw [octNormSq_mul, hu_norm, hv_norm, mul_one]
      have huw : octDot u w = 0 := by
        rw [octDot_comm, octDot_mul_left, octonionConj_eq_neg_of_real_zero hu_mem.2,
          octonionMul_neg_left, octonionMul_imag_sq hu_mem.2, hu_norm, neg_one_smul, neg_neg,
          octDot_comm, show octDot octOne v = 0 from by
            rw [octOne_eq_scalar, octDot_scalar_left, hv_mem.2, mul_zero]]
      have hvw : octDot v w = 0 := by
        rw [octDot_comm, octDot_mul_right, octonionConj_eq_neg_of_real_zero hv_mem.2,
          octonionMul_neg_right, octonionMul_imag_sq hv_mem.2, hv_norm, neg_one_smul, neg_neg,
          octDot_comm, show octDot octOne u = 0 from by
            rw [octOne_eq_scalar, octDot_scalar_left, hu_mem.2, mul_zero]]
      let basis4 : Fin 4 → Octonion := ![octOne, u, v, w]
      have hli : LinearIndependent ℝ basis4 :=
        linearIndependent_four_orthonormal_oct
          (fun i => by fin_cases i <;> dsimp [basis4] <;>
            [exact octNormSq_one; exact hu_norm; exact hv_norm; exact hw_norm])
          (fun i j hij => by
            fin_cases i <;> fin_cases j <;> dsimp [basis4] <;> try exact absurd rfl hij
            · rw [octOne_eq_scalar, octDot_scalar_left, hu_mem.2, mul_zero]
            · rw [octOne_eq_scalar, octDot_scalar_left, hv_mem.2, mul_zero]
            · rw [octOne_eq_scalar, octDot_scalar_left, hw_re, mul_zero]
            · rw [octDot_comm, octOne_eq_scalar, octDot_scalar_left, hu_mem.2, mul_zero]
            · exact huv
            · exact huw
            · rw [octDot_comm, octOne_eq_scalar, octDot_scalar_left, hv_mem.2, mul_zero]
            · rw [octDot_comm]; exact huv
            · exact hvw
            · rw [octDot_comm, octOne_eq_scalar, octDot_scalar_left, hw_re, mul_zero]
            · rw [octDot_comm]; exact huw
            · rw [octDot_comm]; exact hvw)
      have hspan_le_rng : Submodule.span ℝ (Set.range basis4) ≤ LinearMap.range φ := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        fin_cases i <;> dsimp [basis4]
        · exact ⟨1, hφ.map_one⟩
        · exact ⟨qu, hqu⟩
        · exact ⟨qv, hqv⟩
        · exact hw_rng
      have hspan_le_F : Submodule.span ℝ (Set.range basis4) ≤ F.carrier := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        fin_cases i <;> dsimp [basis4]
        · exact F.one_mem
        · exact hu_mem.1
        · exact hv_mem.1
        · exact hw_mem
      have : Module.Finite ℝ Octonion :=
        inferInstanceAs (FiniteDimensional ℝ (Quaternion ℝ × Quaternion ℝ))
      have hfinφ : Module.finrank ℝ (LinearMap.range φ) = 4 := by
        rw [(LinearEquiv.ofInjective φ hφ.injective).symm.finrank_eq, Quaternion.finrank_eq_four]
      have hfin_span : Module.finrank ℝ (Submodule.span ℝ (Set.range basis4)) = 4 := by
        rw [finrank_span_eq_card hli, Fintype.card_fin]
      have hrng_eq : LinearMap.range φ = Submodule.span ℝ (Set.range basis4) :=
        (Submodule.eq_of_le_of_finrank_eq hspan_le_rng (by rw [hfin_span, hfinφ])).symm
      have hrng_le_F : LinearMap.range φ ≤ F.carrier := by rw [hrng_eq]; exact hspan_le_F
      have heq_F : LinearMap.range φ = F.carrier := by
        by_contra hne
        have hlt : LinearMap.range φ < F.carrier := lt_of_le_of_ne hrng_le_F hne
        exact hF.ne (octSubalgebra_strict_gt_quatEmbedding_eq_top F φ hφ hlt)
      exact ⟨φ, hφ, by rw [heq_F]⟩

theorem lem_five_sub (k : CDLevel) (B : NativeJordanSubalgebra)
    (hBk : B.carrier < (H3Subalgebra k).carrier) :
  (∃ (q : Albert) (hq : IsAtom q), q ∈ (H3Subalgebra k).carrier ∧ B.carrier ≤ (lineSubalgebra q hq).carrier) ∨
  match k with
  | .R => False
  | .C => ∃ U : Matrix.unitaryGroup (Fin 3) ℂ, B.carrier ≤ (unitaryConjSubalgebraC U (H3Subalgebra .R)).carrier
  | .H => ∃ Q : NativeJordanSubalgebra, Q.carrier ≤ (H3Subalgebra .H).carrier ∧
            Nonempty (JordanSubalgebraIso (H3Subalgebra .C) Q) ∧ B.carrier ≤ Q.carrier
  | .O => ∃ Q : QuaternionicWindow, B.carrier ≤ Q.subalgebra.carrier := by
  by_cases hline : ∃ (q : Albert) (hq : IsAtom q), q ∈ (H3Subalgebra k).carrier ∧
      B.carrier ≤ (lineSubalgebra q hq).carrier
  · exact Or.inl hline
  · right
    obtain ⟨α, F, hFlt, hBchar⟩ := lem_five_sub_core k B hBk hline
    have : Module.Finite ℝ Octonion :=
      inferInstanceAs (FiniteDimensional ℝ (Quaternion ℝ × Quaternion ℝ))
    cases k with
    | R =>
      have h1_le : octRealSubalgebra.carrier ≤ F.carrier := by
        intro x hx
        obtain ⟨r, rfl⟩ := (assocCD_R.range_embed ▸ hx : x ∈ LinearMap.range assocCD_R.embed)
        change octonionScalar r ∈ F.carrier
        rw [octonionScalar_eq_smul, ← octOne_eq_scalar]
        exact F.carrier.smul_mem _ F.one_mem
      exact hFlt.ne (le_antisymm hFlt.le h1_le)
    | C =>
      have hfin_lt : Module.finrank ℝ F.carrier < Module.finrank ℝ octComplexISubalgebra.carrier :=
        Submodule.finrank_lt_finrank_of_lt hFlt
      have hfinC : Module.finrank ℝ octComplexISubalgebra.carrier = 2 := octSubalgebraOfLevel_finrank .C
      have h1_le : octRealSubalgebra.carrier ≤ F.carrier := by
        intro x hx
        obtain ⟨r, rfl⟩ := (assocCD_R.range_embed ▸ hx : x ∈ LinearMap.range assocCD_R.embed)
        change octonionScalar r ∈ F.carrier
        rw [octonionScalar_eq_smul, ← octOne_eq_scalar]
        exact F.carrier.smul_mem _ F.one_mem
      have hfinR : Module.finrank ℝ octRealSubalgebra.carrier = 1 := octSubalgebraOfLevel_finrank .R
      have hfinF_ge1 : 1 ≤ Module.finrank ℝ F.carrier := by
        rw [← hfinR]; exact Submodule.finrank_mono h1_le
      have hfinF1 : Module.finrank ℝ F.carrier = 1 := by omega
      have hFR : F.carrier = octRealSubalgebra.carrier :=
        (Submodule.eq_of_le_of_finrank_eq h1_le (by rw [hfinR, hfinF1])).symm
      refine ⟨α, fun x hxB => ?_⟩
      obtain ⟨hxC, hxF⟩ := (hBchar x).mp hxB
      change ∃ hx : x ∈ (H3Subalgebra .C).carrier, _
      refine ⟨hxC, ?_⟩
      change ((α.toIso.toLinearEquiv ⟨x, hxC⟩).1) ∈ (H3Subalgebra .R).carrier
      exact ⟨hFR ▸ hxF.1, hFR ▸ hxF.2.1, hFR ▸ hxF.2.2⟩
    | H =>
      have hF_rng : F.carrier ≤ LinearMap.range quatEmbed1 := by
        change F.carrier ≤ LinearMap.range assocCD_H.embed
        rw [assocCD_H.range_embed]; exact hFlt.le
      have hfin_cases := octSubalgebra_le_quatEmbedding_finrank F quatEmbed1 quatEmbed1_isQuatEmbedding hF_rng
      have hfin_lt : Module.finrank ℝ F.carrier < 4 := by
        have h4 : Module.finrank ℝ (octSubalgebraOfLevel .H).carrier = 4 := by
          simpa using octSubalgebraOfLevel_finrank .H
        rw [← h4]
        exact Submodule.finrank_lt_finrank_of_lt hFlt
      have hmakeQ : ∀ (ψ : JordanSubalgebraIso (H3Subalgebra .H) (H3Subalgebra .H)),
          (∀ x : Albert, x ∈ B.carrier →
            ∃ hx : x ∈ (H3Subalgebra .H).carrier, (ψ.toLinearEquiv ⟨x, hx⟩).1 ∈ (H3Subalgebra .C).carrier) →
          ∃ Q : NativeJordanSubalgebra, Q.carrier ≤ (H3Subalgebra .H).carrier ∧
            Nonempty (JordanSubalgebraIso (H3Subalgebra .C) Q) ∧ B.carrier ≤ Q.carrier := by
        intro ψ hBψ
        have hCH : (H3Subalgebra .C).carrier ≤ (H3Subalgebra .H).carrier :=
          H3Subalgebra_mono (by simp)
        let Q : NativeJordanSubalgebra :=
          { carrier :=
              { carrier := {x : Albert | ∃ hx : x ∈ (H3Subalgebra .H).carrier,
                  (ψ.toLinearEquiv ⟨x, hx⟩).1 ∈ (H3Subalgebra .C).carrier}
                add_mem' := fun {a b} ⟨ha, ha'⟩ ⟨hb, hb'⟩ =>
                  ⟨(H3Subalgebra .H).carrier.add_mem ha hb, by
                    have h : (⟨a + b, (H3Subalgebra .H).carrier.add_mem ha hb⟩ : (H3Subalgebra .H).carrier) =
                        ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
                    rw [h, map_add, Submodule.coe_add]
                    exact (H3Subalgebra .C).carrier.add_mem ha' hb'⟩
                zero_mem' := ⟨(H3Subalgebra .H).carrier.zero_mem, by
                  have h : (⟨0, (H3Subalgebra .H).carrier.zero_mem⟩ : (H3Subalgebra .H).carrier) = 0 := rfl
                  rw [h, map_zero, Submodule.coe_zero]
                  exact (H3Subalgebra .C).carrier.zero_mem⟩
                smul_mem' := fun r {a} ⟨ha, ha'⟩ =>
                  ⟨(H3Subalgebra .H).carrier.smul_mem r ha, by
                    have h : (⟨r • a, (H3Subalgebra .H).carrier.smul_mem r ha⟩ : (H3Subalgebra .H).carrier) =
                        r • ⟨a, ha⟩ := rfl
                    rw [h, map_smul, Submodule.coe_smul]
                    exact (H3Subalgebra .C).carrier.smul_mem r ha'⟩ }
            unit_mem := ⟨(H3Subalgebra .H).unit_mem, by
              rw [ψ.map_unit]; exact (H3Subalgebra .C).unit_mem⟩
            product_mem := fun a ⟨ha, ha'⟩ b ⟨hb, hb'⟩ =>
              ⟨(H3Subalgebra .H).product_mem a ha b hb, by
                rw [ψ.map_jordan ⟨a, ha⟩ ⟨b, hb⟩]
                exact (H3Subalgebra .C).product_mem _ ha' _ hb'⟩ }
        have hBQ : B.carrier ≤ Q.carrier := fun x hx => hBψ x hx
        have hQH : Q.carrier ≤ (H3Subalgebra .H).carrier := fun _ h => h.1
        let isoCQ : JordanSubalgebraIso (H3Subalgebra .C) Q :=
          { toLinearEquiv :=
              { toFun := fun y =>
                  let z := ψ.toLinearEquiv.symm ⟨y.1, hCH y.2⟩
                  ⟨z.1, z.2, by
                    have hz : (⟨z.1, z.2⟩ : (H3Subalgebra .H).carrier) = z := rfl
                    rw [hz, LinearEquiv.apply_symm_apply]; exact y.2⟩
                invFun := fun q => ⟨(ψ.toLinearEquiv ⟨q.1, q.2.1⟩).1, q.2.2⟩
                left_inv := fun y => Subtype.ext (by
                  change (ψ.toLinearEquiv ⟨(ψ.toLinearEquiv.symm ⟨y.1, hCH y.2⟩).1, _⟩).1 = y.1
                  have hz : (⟨(ψ.toLinearEquiv.symm ⟨y.1, hCH y.2⟩).1,
                      (ψ.toLinearEquiv.symm ⟨y.1, hCH y.2⟩).2⟩ : (H3Subalgebra .H).carrier) =
                      ψ.toLinearEquiv.symm ⟨y.1, hCH y.2⟩ := rfl
                  rw [hz, LinearEquiv.apply_symm_apply])
                right_inv := fun q => Subtype.ext (by
                  change (ψ.toLinearEquiv.symm ⟨(ψ.toLinearEquiv ⟨q.1, q.2.1⟩).1, _⟩).1 = q.1
                  have hz : (⟨(ψ.toLinearEquiv ⟨q.1, q.2.1⟩).1,
                      (ψ.toLinearEquiv ⟨q.1, q.2.1⟩).2⟩ : (H3Subalgebra .H).carrier) =
                      ψ.toLinearEquiv ⟨q.1, q.2.1⟩ := rfl
                  rw [hz, LinearEquiv.symm_apply_apply])
                map_add' := fun y₁ y₂ => Subtype.ext (by
                  have h : (⟨(y₁ + y₂).1, hCH (y₁ + y₂).2⟩ : (H3Subalgebra .H).carrier) =
                      ⟨y₁.1, hCH y₁.2⟩ + ⟨y₂.1, hCH y₂.2⟩ := rfl
                  change (ψ.toLinearEquiv.symm ⟨(y₁ + y₂).1, hCH (y₁ + y₂).2⟩).1 = _
                  rw [h, map_add, Submodule.coe_add]; rfl)
                map_smul' := fun r y => Subtype.ext (by
                  have h : (⟨(r • y).1, hCH (r • y).2⟩ : (H3Subalgebra .H).carrier) =
                      r • ⟨y.1, hCH y.2⟩ := rfl
                  change (ψ.toLinearEquiv.symm ⟨(r • y).1, hCH (r • y).2⟩).1 = _
                  rw [h, map_smul, Submodule.coe_smul]; rfl) }
            map_unit := Subtype.ext (by
              change (ψ.symm.toLinearEquiv ⟨albertUnit, (H3Subalgebra .H).unit_mem⟩).1 = albertUnit
              rw [ψ.symm.map_unit])
            map_jordan := fun y₁ y₂ => Subtype.ext (by
              change (ψ.symm.toLinearEquiv ⟨jordanMul y₁.1 y₂.1,
                (H3Subalgebra .H).product_mem _ (hCH y₁.2) _ (hCH y₂.2)⟩).1 = _
              rw [ψ.symm.map_jordan ⟨y₁.1, hCH y₁.2⟩ ⟨y₂.1, hCH y₂.2⟩]; rfl) }
        exact ⟨Q, hQH, ⟨isoCQ⟩, hBQ⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hfin_cases
      rcases hfin_cases with hfin1 | hfin2 | hfin4
      · have hFR : F.carrier = Submodule.span ℝ {octOne} :=
          (octSubalgebra_le_quatEmbedding_finrank_one_iff F quatEmbed1 quatEmbed1_isQuatEmbedding hF_rng).mp hfin1
        apply hmakeQ α.toIso
        intro x hxB
        obtain ⟨hxH, hxF⟩ := (hBchar x).mp hxB
        refine ⟨hxH, ?_⟩
        have hRC : octRealSubalgebra.carrier ≤ (octSubalgebraOfLevel .C).carrier :=
          octSubalgebraOfLevel_mono (k₁ := .R) (k₂ := .C) (by simp)
        have hF_sub : F.carrier ≤ octRealSubalgebra.carrier := by
          rw [hFR, Submodule.span_le, Set.singleton_subset_iff]; exact octRealSubalgebra.one_mem
        exact ⟨hRC (hF_sub hxF.1), hRC (hF_sub hxF.2.1), hRC (hF_sub hxF.2.2)⟩
      · obtain ⟨u, hu_re, hu_ns, ⟨q, hqu⟩, hFu⟩ :=
          (octSubalgebra_le_quatEmbedding_finrank_two_iff F quatEmbed1 quatEmbed1_isQuatEmbedding hF_rng).mp hfin2
        have hq_re : q.re = 0 := by rw [← quatEmbed1_isQuatEmbedding.map_re q, hqu, hu_re]
        have hq_ns : quatNormSq q = 1 := by
          change assocCD_H.normSq q = 1
          rw [← assocCD_H.embed_normSq q]
          change octNormSq (quatEmbed1 q) = 1
          rw [hqu, hu_ns]
        obtain ⟨w, hw_ns, hw_conj⟩ := exists_unit_quat_conj_to_I q hq_re hq_ns
        let d : Fin 3 → Quaternion ℝ := ![star w, star w, star w]
        have hd : ∀ i, assocCD_H.normSq (d i) = 1 := fun i => by
          fin_cases i <;> dsimp [d] <;>
            rw [← assocCD_H.embed_normSq, ← assocCD_H.embed_star, octNormSq_conj, assocCD_H.embed_normSq] <;>
            exact hw_ns
        let U := Matrix.diagonal d
        have hU := assocCD_diag_unitary assocCD_H d hd
        let αw : JordanSubalgebraIso (H3Subalgebra .H) (H3Subalgebra .H) :=
          assocCD_unitaryIso assocCD_H U hU.1 hU.2
        apply hmakeQ (α.toIso.trans αw)
        intro x hxB
        obtain ⟨hxH, hxF⟩ := (hBchar x).mp hxB
        refine ⟨hxH, ?_⟩
        let y : (H3Subalgebra .H).carrier := α.toIso.toLinearEquiv ⟨x, hxH⟩
        let y' : (jordanSubalgebraH3 assocCD_H.subalgebra).carrier := y
        have hy_C : (αw.toLinearEquiv y).1 ∈ (H3Subalgebra .C).carrier := by
          let M := (assocHermEquiv assocCD_H).symm y'
          have hMeq : assocMatToAlbert assocCD_H M.1 = y.1 :=
            congrArg Subtype.val ((assocHermEquiv assocCD_H).apply_symm_apply y')
          have hw_star : w * star w = 1 := by
            have h := assocCD_H.mul_star_self w
            change w * star w = quatNormSq w • 1 at h
            rw [h, hw_ns, one_smul]
          have hconj_mem : ∀ b : Octonion, b ∈ F.carrier →
              ∀ p0 : Quaternion ℝ, assocCD_H.embed p0 = b →
              assocCD_H.embed (w * p0 * star w) ∈ octComplexISubalgebra.carrier := by
            intro b hb p0 hp0
            rw [hFu, Submodule.mem_span_insert] at hb
            obtain ⟨c₁, z, hz_span, hzb⟩ := hb
            rw [Submodule.mem_span_singleton] at hz_span
            obtain ⟨c₂, rfl⟩ := hz_span
            have hp0_eq : p0 = c₁ • (1 : Quaternion ℝ) + c₂ • q := assocCD_embed_injective assocCD_H (by
              rw [hp0, hzb, map_add, map_smul, map_smul, assocCD_H.embed_one]
              change _ = c₁ • octOne + c₂ • quatEmbed1 q
              rw [hqu])
            have hw_eq : w * p0 * star w = c₁ • (1 : Quaternion ℝ) + c₂ • (⟨0, 1, 0, 0⟩ : Quaternion ℝ) := by
              rw [hp0_eq, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, hw_star,
                mul_smul_comm, smul_mul_assoc, hw_conj]
            rw [hw_eq, map_add, map_smul, map_smul, assocCD_H.embed_one]
            refine octComplexISubalgebra.carrier.add_mem
              (octComplexISubalgebra.carrier.smul_mem _ octComplexISubalgebra.one_mem)
              (octComplexISubalgebra.carrier.smul_mem _ ?_)
            change quatEmbed1 ⟨0, 1, 0, 0⟩ ∈ assocCD_C.subalgebra.carrier
            rw [← assocCD_C.range_embed]
            refine ⟨Complex.I, ?_⟩
            change complexToOctonion Complex.I = (⟨0, 1, 0, 0⟩, 0)
            rw [complexToOctonion_apply]; rfl
          have h01_eq : (αw.toLinearEquiv y).1.2 0 = assocCD_H.embed (w * M.1 0 1 * star w) := by
            change ((assocCD_unitaryIso assocCD_H U hU.1 hU.2).toLinearEquiv y').1.2 0 = _
            rw [assocCD_diag_unitaryIso_apply assocCD_H d hd, assocMatToAlbert_snd_0, diag_conj_entry]
            simp [d]; rfl
          have h02_eq : (αw.toLinearEquiv y).1.2 1 = assocCD_H.embed (w * M.1 0 2 * star w) := by
            change ((assocCD_unitaryIso assocCD_H U hU.1 hU.2).toLinearEquiv y').1.2 1 = _
            rw [assocCD_diag_unitaryIso_apply assocCD_H d hd, assocMatToAlbert_snd_1, diag_conj_entry]
            simp [d]; rfl
          have h12_eq : (αw.toLinearEquiv y).1.2 2 = assocCD_H.embed (w * M.1 1 2 * star w) := by
            change ((assocCD_unitaryIso assocCD_H U hU.1 hU.2).toLinearEquiv y').1.2 2 = _
            rw [assocCD_diag_unitaryIso_apply assocCD_H d hd, assocMatToAlbert_snd_2, diag_conj_entry]
            simp [d]; rfl
          refine ⟨?_, ?_, ?_⟩
          · rw [h01_eq]
            exact hconj_mem (y.1.2 0) hxF.1 (M.1 0 1)
              (by rw [← hMeq, assocMatToAlbert_snd_0])
          · rw [h02_eq]
            exact hconj_mem (y.1.2 1) hxF.2.1 (M.1 0 2)
              (by rw [← hMeq, assocMatToAlbert_snd_1])
          · rw [h12_eq]
            exact hconj_mem (y.1.2 2) hxF.2.2 (M.1 1 2)
              (by rw [← hMeq, assocMatToAlbert_snd_2])
        exact hy_C
      · omega
    | O =>
      let g : NativeAlbertAutomorphism := α
      obtain ⟨φ, hφ, hFφ⟩ := exists_quatEmbedding_superset_of_lt_top F hFlt
      let Q0 := quaternionicWindowOfQuatEmbedding φ hφ
      let Q := Q0.transport (autoSymm g)
      refine ⟨Q, fun x hxB => ?_⟩
      obtain ⟨_, hxF⟩ := (hBchar x).mp hxB
      have hxQ0 : g.linearEquiv x ∈ Q0.subalgebra.carrier := by
        have h0 : (g.linearEquiv x).2 0 ∈ LinearMap.range φ := hFφ hxF.1
        have h1 : (g.linearEquiv x).2 1 ∈ LinearMap.range φ := hFφ hxF.2.1
        have h2 : (g.linearEquiv x).2 2 ∈ LinearMap.range φ := hFφ hxF.2.2
        obtain ⟨q0, hq0⟩ := h0
        obtain ⟨q1, hq1⟩ := h1
        obtain ⟨q2, hq2⟩ := h2
        rw [← Q0.range_eq]
        refine ⟨quatHermitian3Equiv.symm ((g.linearEquiv x).1, ![q0, q1, q2]), ?_⟩
        change quatMatrixToAlbert φ (quatHermitian3Equiv.symm ((g.linearEquiv x).1, ![q0, q1, q2]) : QuatMatrix3) =
          g.linearEquiv x
        have hp' := quatHermitian3Equiv.apply_symm_apply ((g.linearEquiv x).1, ![q0, q1, q2])
        have hq01 : (quatHermitian3Equiv.symm ((g.linearEquiv x).1, ![q0, q1, q2]) : QuatMatrix3) 0 1 = q0 :=
          congrArg (fun p : (Fin 3 → ℝ) × (Fin 3 → Quaternion ℝ) => p.2 0) hp'
        have hq02 : (quatHermitian3Equiv.symm ((g.linearEquiv x).1, ![q0, q1, q2]) : QuatMatrix3) 0 2 = q1 :=
          congrArg (fun p : (Fin 3 → ℝ) × (Fin 3 → Quaternion ℝ) => p.2 1) hp'
        have hq12 : (quatHermitian3Equiv.symm ((g.linearEquiv x).1, ![q0, q1, q2]) : QuatMatrix3) 1 2 = q2 :=
          congrArg (fun p : (Fin 3 → ℝ) × (Fin 3 → Quaternion ℝ) => p.2 2) hp'
        apply albert_ext
        · exact congrArg (fun p : (Fin 3 → ℝ) × (Fin 3 → Quaternion ℝ) => p.1 0) hp'
        · exact congrArg (fun p : (Fin 3 → ℝ) × (Fin 3 → Quaternion ℝ) => p.1 1) hp'
        · exact congrArg (fun p : (Fin 3 → ℝ) × (Fin 3 → Quaternion ℝ) => p.1 2) hp'
        · change φ ((quatHermitian3Equiv.symm _ : QuatMatrix3) 0 1) = _
          rw [hq01]; exact hq0
        · change φ ((quatHermitian3Equiv.symm _ : QuatMatrix3) 0 2) = _
          rw [hq02]; exact hq1
        · change φ ((quatHermitian3Equiv.symm _ : QuatMatrix3) 1 2) = _
          rw [hq12]; exact hq2
      refine ⟨g.linearEquiv x, hxQ0, ?_⟩
      change (autoSymm g).linearEquiv (g.linearEquiv x) = x
      exact g.linearEquiv.symm_apply_apply x

private theorem not_iso_H3_le_lineSubalgebra (k : CDLevel) (B : NativeJordanSubalgebra)
    (hiso : Nonempty (JordanSubalgebraIso (H3Subalgebra k) B))
    (q : Albert) (hq : IsAtom q) : ¬ B.carrier ≤ (lineSubalgebra q hq).carrier := by
  intro hle
  obtain ⟨ψ⟩ := hiso
  obtain ⟨g, hg⟩ := atom_to_diagAtom0 q hq
  let χ : Albert → ℝ := fun x => tracePairing q x
  have hχ_mul : ∀ x y : Albert,
      x ∈ (lineSubalgebra q hq).carrier → y ∈ (lineSubalgebra q hq).carrier →
      χ (jordanMul x y) = χ x * χ y := by
    intro x y hx hy
    have hxg : g.linearEquiv x ∈ (lineSubalgebra (diagAtom 0) (diagAtom_isAtom 0)).carrier := by
      rw [mem_lineSubalgebra_iff] at hx ⊢
      rw [← hg, ← g.preserves_product, hx, map_smul, g.map_tracePairing]
    have hyg : g.linearEquiv y ∈ (lineSubalgebra (diagAtom 0) (diagAtom_isAtom 0)).carrier := by
      rw [mem_lineSubalgebra_iff] at hy ⊢
      rw [← hg, ← g.preserves_product, hy, map_smul, g.map_tracePairing]
    have hx0 := (mem_line_diag0_iff _).mp ((mem_lineSubalgebra_iff _ _ _).mp hxg)
    have hy0 := (mem_line_diag0_iff _).mp ((mem_lineSubalgebra_iff _ _ _).mp hyg)
    have hcx : χ x = (g.linearEquiv x).1 0 := by
      change tracePairing q x = (g.linearEquiv x).1 0
      rw [← tracePairing_diagAtom0, ← hg, g.map_tracePairing]
    have hcy : χ y = (g.linearEquiv y).1 0 := by
      change tracePairing q y = (g.linearEquiv y).1 0
      rw [← tracePairing_diagAtom0, ← hg, g.map_tracePairing]
    have hcxy : χ (jordanMul x y) = (jordanMul (g.linearEquiv x) (g.linearEquiv y)).1 0 := by
      change tracePairing q (jordanMul x y) = _
      rw [← tracePairing_diagAtom0, ← hg, ← g.preserves_product, g.map_tracePairing]
    rw [hcxy, hcx, hcy, jordanMul_diag_0, hx0.1, hx0.2, hy0.1, hy0.2, octDot_zero_left]
    ring
  let e : Fin 3 → Albert := fun i => (ψ.toLinearEquiv ⟨diagAtom i, diagAtom_mem_H3Subalgebra k i⟩).1
  have he_mem : ∀ i, e i ∈ (lineSubalgebra q hq).carrier := fun i =>
    hle (ψ.toLinearEquiv ⟨diagAtom i, diagAtom_mem_H3Subalgebra k i⟩).2
  have he_sum : e 0 + e 1 + e 2 = albertUnit := by
    have hs : ⟨diagAtom 0, diagAtom_mem_H3Subalgebra k 0⟩ +
        ⟨diagAtom 1, diagAtom_mem_H3Subalgebra k 1⟩ +
        ⟨diagAtom 2, diagAtom_mem_H3Subalgebra k 2⟩ =
        (⟨albertUnit, (H3Subalgebra k).unit_mem⟩ : (H3Subalgebra k).carrier) :=
      Subtype.ext (by simpa [Fin.sum_univ_three] using diagAtom_sum_eq_unit)
    have hmap := congrArg (fun z => (ψ.toLinearEquiv z).1) hs
    rw [map_add, map_add, Submodule.coe_add, Submodule.coe_add, ψ.map_unit] at hmap
    exact hmap
  have he_id : ∀ i, jordanMul (e i) (e i) = e i := fun i => by
    rw [← ψ.map_jordanMul_eq]
    exact congrArg (fun z => (ψ.toLinearEquiv z).1) (Subtype.ext (diagAtom_isAtom i).1)
  have hχ_e_bool : ∀ i, χ (e i) = 0 ∨ χ (e i) = 1 := fun i => by
    have h := congrArg χ (he_id i)
    rw [hχ_mul (e i) (e i) (he_mem i) (he_mem i)] at h
    have hsq : χ (e i) * (χ (e i) - 1) = 0 := by linarith
    rcases mul_eq_zero.mp hsq with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  have hχ_sum : χ (e 0) + χ (e 1) + χ (e 2) = 1 := by
    have h := congrArg χ he_sum
    change tracePairing q (e 0 + e 1 + e 2) = tracePairing q albertUnit at h
    rw [tracePairing_add_right, tracePairing_add_right] at h
    have h1 : tracePairing q albertUnit = 1 := by
      unfold tracePairing; rw [jordanMul_albertUnit_right, hq.2]
    linarith
  let f01 := (ψ.toLinearEquiv ⟨slotElem01 octOne, slotElem01_octOne_mem_H3Subalgebra k⟩).1
  let f02 := (ψ.toLinearEquiv ⟨slotElem02 octOne, slotElem02_octOne_mem_H3Subalgebra k⟩).1
  have hf01_mem : f01 ∈ (lineSubalgebra q hq).carrier :=
    hle (ψ.toLinearEquiv ⟨slotElem01 octOne, slotElem01_octOne_mem_H3Subalgebra k⟩).2
  have hf02_mem : f02 ∈ (lineSubalgebra q hq).carrier :=
    hle (ψ.toLinearEquiv ⟨slotElem02 octOne, slotElem02_octOne_mem_H3Subalgebra k⟩).2
  have hm01 : jordanMul (e 0) f01 = (1 / 2 : ℝ) • f01 := by
    rw [← ψ.map_jordanMul_eq]
    have hrel : jordanMul (diagAtom 0) (slotElem01 octOne) = (1 / 2 : ℝ) • slotElem01 octOne := by
      apply albert_ext <;> simp [jordanMul_diagAtom0, slotElem01_fst, slotElem01_snd_0,
        slotElem01_snd_1, slotElem01_snd_2, albert_smul_fst, albert_smul_snd]
    have hsub : (⟨jordanMul (diagAtom 0) (slotElem01 octOne),
        (H3Subalgebra k).product_mem _ (diagAtom_mem_H3Subalgebra k 0) _ (slotElem01_octOne_mem_H3Subalgebra k)⟩ :
        (H3Subalgebra k).carrier) =
        (1 / 2 : ℝ) • ⟨slotElem01 octOne, slotElem01_octOne_mem_H3Subalgebra k⟩ := Subtype.ext hrel
    rw [hsub, map_smul, Submodule.coe_smul]
  have hm02 : jordanMul (e 2) f02 = (1 / 2 : ℝ) • f02 := by
    rw [← ψ.map_jordanMul_eq]
    have hrel : jordanMul (diagAtom 2) (slotElem02 octOne) = (1 / 2 : ℝ) • slotElem02 octOne := by
      apply albert_ext <;> simp [jordanMul_diagAtom2, slotElem02_fst, slotElem02_snd_0,
        slotElem02_snd_1, slotElem02_snd_2, albert_smul_fst, albert_smul_snd]
    have hsub : (⟨jordanMul (diagAtom 2) (slotElem02 octOne),
        (H3Subalgebra k).product_mem _ (diagAtom_mem_H3Subalgebra k 2) _ (slotElem02_octOne_mem_H3Subalgebra k)⟩ :
        (H3Subalgebra k).carrier) =
        (1 / 2 : ℝ) • ⟨slotElem02 octOne, slotElem02_octOne_mem_H3Subalgebra k⟩ := Subtype.ext hrel
    rw [hsub, map_smul, Submodule.coe_smul]
  have hsq01 : jordanMul f01 f01 = e 0 + e 1 := by
    rw [← ψ.map_jordanMul_eq]
    have hrel : jordanMul (slotElem01 octOne) (slotElem01 octOne) = diagAtom 0 + diagAtom 1 := by
      apply albert_ext
      · rw [jordanMul_diag_0, slotElem01_fst, slotElem01_snd_0, slotElem01_snd_1,
          octDot_zero_left, octDot_self, octNormSq_one, albert_add_fst, diagAtom_fst, diagAtom_fst]; norm_num
      · rw [jordanMul_diag_1, slotElem01_fst, slotElem01_snd_0, slotElem01_snd_2,
          octDot_zero_left, octDot_self, octNormSq_one, albert_add_fst, diagAtom_fst, diagAtom_fst]; norm_num
      · rw [jordanMul_diag_2, slotElem01_fst, slotElem01_snd_1, slotElem01_snd_2,
          octDot_zero_left, albert_add_fst, diagAtom_fst, diagAtom_fst]; norm_num
      · simp [jordanMul_off_0, slotElem01_fst, slotElem01_snd_0, slotElem01_snd_1, slotElem01_snd_2,
          octonionConj_zero, octonionMul_zero_right, albert_add_snd, diagAtom_snd]
      · simp [jordanMul_off_1, slotElem01_fst, slotElem01_snd_0, slotElem01_snd_1, slotElem01_snd_2,
          octonionMul_zero_right, albert_add_snd, diagAtom_snd]
      · simp [jordanMul_off_2, slotElem01_fst, slotElem01_snd_0, slotElem01_snd_1, slotElem01_snd_2,
          octonionMul_zero_right, albert_add_snd, diagAtom_snd]
    have hsub : (⟨jordanMul (slotElem01 octOne) (slotElem01 octOne),
        (H3Subalgebra k).product_mem _ (slotElem01_octOne_mem_H3Subalgebra k) _
          (slotElem01_octOne_mem_H3Subalgebra k)⟩ : (H3Subalgebra k).carrier) =
        ⟨diagAtom 0, diagAtom_mem_H3Subalgebra k 0⟩ +
        ⟨diagAtom 1, diagAtom_mem_H3Subalgebra k 1⟩ := Subtype.ext hrel
    rw [hsub, map_add, Submodule.coe_add]
  have hsq02 : jordanMul f02 f02 = e 0 + e 2 := by
    rw [← ψ.map_jordanMul_eq]
    have hrel : jordanMul (slotElem02 octOne) (slotElem02 octOne) = diagAtom 0 + diagAtom 2 := by
      apply albert_ext
      · rw [jordanMul_diag_0, slotElem02_fst, slotElem02_snd_0, slotElem02_snd_1,
          octDot_zero_left, octDot_self, octNormSq_one, albert_add_fst, diagAtom_fst, diagAtom_fst]; norm_num
      · rw [jordanMul_diag_1, slotElem02_fst, slotElem02_snd_0, slotElem02_snd_2,
          octDot_zero_left, albert_add_fst, diagAtom_fst, diagAtom_fst]; norm_num
      · rw [jordanMul_diag_2, slotElem02_fst, slotElem02_snd_1, slotElem02_snd_2,
          octDot_zero_left, octDot_self, octNormSq_one, albert_add_fst, diagAtom_fst, diagAtom_fst]; norm_num
      · simp [jordanMul_off_0, slotElem02_fst, slotElem02_snd_0, slotElem02_snd_1, slotElem02_snd_2,
          octonionConj_zero, octonionMul_zero_right, albert_add_snd, diagAtom_snd]
      · simp [jordanMul_off_1, slotElem02_fst, slotElem02_snd_0, slotElem02_snd_1, slotElem02_snd_2,
          octonionMul_zero_right, albert_add_snd, diagAtom_snd]
      · simp [jordanMul_off_2, slotElem02_fst, slotElem02_snd_0, slotElem02_snd_1, slotElem02_snd_2,
          octonionConj_zero, octonionMul_zero_left, albert_add_snd, diagAtom_snd]
    have hsub : (⟨jordanMul (slotElem02 octOne) (slotElem02 octOne),
        (H3Subalgebra k).product_mem _ (slotElem02_octOne_mem_H3Subalgebra k) _
          (slotElem02_octOne_mem_H3Subalgebra k)⟩ : (H3Subalgebra k).carrier) =
        ⟨diagAtom 0, diagAtom_mem_H3Subalgebra k 0⟩ +
        ⟨diagAtom 2, diagAtom_mem_H3Subalgebra k 2⟩ := Subtype.ext hrel
    rw [hsub, map_add, Submodule.coe_add]
  have hχ01 : χ f01 = 0 := by
    have h := congrArg χ hm01
    rw [hχ_mul (e 0) f01 (he_mem 0) hf01_mem] at h
    change χ (e 0) * χ f01 = tracePairing q ((1 / 2 : ℝ) • f01) at h
    rw [tracePairing_smul_right] at h
    rcases hχ_e_bool 0 with h0 | h1 <;> [rw [h0] at h; rw [h1] at h] <;> linarith
  have hχ02 : χ f02 = 0 := by
    have h := congrArg χ hm02
    rw [hχ_mul (e 2) f02 (he_mem 2) hf02_mem] at h
    change χ (e 2) * χ f02 = tracePairing q ((1 / 2 : ℝ) • f02) at h
    rw [tracePairing_smul_right] at h
    rcases hχ_e_bool 2 with h0 | h1 <;> [rw [h0] at h; rw [h1] at h] <;> linarith
  have h01_sum : χ (e 0) + χ (e 1) = 0 := by
    have h := congrArg χ hsq01
    rw [hχ_mul f01 f01 hf01_mem hf01_mem, hχ01, zero_mul] at h
    change 0 = tracePairing q (e 0 + e 1) at h
    rw [tracePairing_add_right] at h; linarith
  have h02_sum : χ (e 0) + χ (e 2) = 0 := by
    have h := congrArg χ hsq02
    rw [hχ_mul f02 f02 hf02_mem hf02_mem, hχ02, zero_mul] at h
    change 0 = tracePairing q (e 0 + e 2) at h
    rw [tracePairing_add_right] at h; linarith
  rcases hχ_e_bool 0 with h0 | h1 <;> linarith

theorem subalgebra_iso_H3R_or_H3C_in_quatWindow (B : NativeJordanSubalgebra)
    (hiso : Nonempty (JordanSubalgebraIso (H3Subalgebra .R) B) ∨ Nonempty (JordanSubalgebraIso (H3Subalgebra .C) B)) :
    ∃ Q : QuaternionicWindow, B.carrier ≤ Q.subalgebra.carrier := by
  have : Module.Finite ℝ Octonion :=
    inferInstanceAs (FiniteDimensional ℝ (Quaternion ℝ × Quaternion ℝ))
  have hlt : B.carrier < (H3Subalgebra .O).carrier := by
    rw [H3Subalgebra_O_eq_top]
    refine lt_of_le_of_ne le_top fun heq => ?_
    have h27 : Module.finrank ℝ B.carrier = 27 := by
      have h := finrank_H3Subalgebra .O
      rw [H3Subalgebra_O_eq_top] at h
      rw [heq]; exact h
    rcases hiso with hR | hC
    · obtain ⟨ψ⟩ := hR
      have h6 : Module.finrank ℝ B.carrier = 6 := by
        rw [← ψ.toLinearEquiv.finrank_eq]; exact finrank_H3Subalgebra .R
      omega
    · obtain ⟨ψ⟩ := hC
      have h9 : Module.finrank ℝ B.carrier = 9 := by
        rw [← ψ.toLinearEquiv.finrank_eq]; exact finrank_H3Subalgebra .C
      omega
  rcases lem_five_sub .O B hlt with ⟨q, hq, _, hline⟩ | hQ
  · exfalso
    rcases hiso with hR | hC
    · exact not_iso_H3_le_lineSubalgebra .R B hR q hq hline
    · exact not_iso_H3_le_lineSubalgebra .C B hC q hq hline
  · exact hQ

theorem subalgebra_H3C_iso_H3R_unitary_conj (B : NativeJordanSubalgebra)
    (hBC : B.carrier ≤ (H3Subalgebra .C).carrier)
    (hiso : Nonempty (JordanSubalgebraIso (H3Subalgebra .R) B)) :
    ∃ U : Matrix.unitaryGroup (Fin 3) ℂ, B.carrier = (unitaryConjSubalgebraC U (H3Subalgebra .R)).carrier := by
  have : Module.Finite ℝ Octonion :=
    inferInstanceAs (FiniteDimensional ℝ (Quaternion ℝ × Quaternion ℝ))
  have : Module.Finite ℝ Albert :=
    inferInstanceAs (FiniteDimensional ℝ ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
  obtain ⟨ψ⟩ := hiso
  have hfinB : Module.finrank ℝ B.carrier = 6 := by
    rw [← ψ.toLinearEquiv.finrank_eq]; exact finrank_H3Subalgebra .R
  have hfinC : Module.finrank ℝ (H3Subalgebra .C).carrier = 9 := finrank_H3Subalgebra .C
  have hlt : B.carrier < (H3Subalgebra .C).carrier := by
    refine lt_of_le_of_ne hBC fun heq => ?_
    rw [heq, hfinC] at hfinB; norm_num at hfinB
  rcases lem_five_sub .C B hlt with ⟨q, hq, _, hline⟩ | ⟨U, hU⟩
  · exact absurd hline (not_iso_H3_le_lineSubalgebra .R B ⟨ψ⟩ q hq)
  · have hfinU : Module.finrank ℝ (unitaryConjSubalgebraC U (H3Subalgebra .R)).carrier = 6 := by
      rw [finrank_unitaryConjSubalgebraC U (H3Subalgebra .R) (H3Subalgebra_mono (by simp))]
      exact finrank_H3Subalgebra .R
    exact ⟨U, Submodule.eq_of_le_of_finrank_eq hU (by rw [hfinB, hfinU])⟩

/-! ## Section 5: Explicit Hermitian Matrix Embeddings, State Transport, and `proper_iff_special` -/

/-! ### Section 5.1: `M_6(ℂ)` Symplectic Embedding for Any `QuaternionicWindow` -/

def quatMat2 (q : Quaternion ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![⟨q.re, q.imI⟩, ⟨q.imJ, q.imK⟩], ![⟨-q.imJ, q.imK⟩, ⟨q.re, -q.imI⟩]]

theorem quatMat2_one : quatMat2 (1 : Quaternion ℝ) = 1 := by
  funext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [quatMat2]

theorem quatMat2_add (a b : Quaternion ℝ) :
    quatMat2 (a + b) = quatMat2 a + quatMat2 b := by
  ext i j
  rw [Matrix.add_apply]
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> (simp [quatMat2]; try ring)

theorem quatMat2_smul (r : ℝ) (a : Quaternion ℝ) :
    quatMat2 (r • a) = r • quatMat2 a := by
  ext i j
  rw [Matrix.smul_apply]
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [quatMat2, Complex.real_smul]

theorem quatMat2_mul (a b : Quaternion ℝ) :
    quatMat2 (a * b) = quatMat2 a * quatMat2 b := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    (rw [Matrix.mul_apply, Fin.sum_univ_two]; apply Complex.ext <;> simp [quatMat2] <;> ring)

theorem quatMat2_star (a : Quaternion ℝ) :
    quatMat2 (star a) = (quatMat2 a).conjTranspose := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [quatMat2]

theorem quatMat2_injective : Function.Injective quatMat2 := by
  intro a b hab
  have h00 := congrFun (congrFun hab 0) 0
  have h01 := congrFun (congrFun hab 0) 1
  dsimp only [quatMat2, Matrix.cons_val_zero, Matrix.cons_val_one] at h00 h01
  apply Quaternion.ext
  · simpa using congrArg Complex.re h00
  · simpa using congrArg Complex.im h00
  · simpa using congrArg Complex.re h01
  · simpa using congrArg Complex.im h01

theorem quatMat2_trace_re (q : Quaternion ℝ) :
    (Matrix.trace (quatMat2 q)).re = 2 * q.re := by
  rw [Matrix.trace_fin_two]
  simp [quatMat2]
  ring

def fin3ProdFin2Equiv6 : Fin 3 × Fin 2 ≃ Fin 6 where
  toFun p := ⟨2 * p.1.1 + p.2.1, by omega⟩
  invFun k := (⟨k.1 / 2, by omega⟩, ⟨k.1 % 2, by omega⟩)
  left_inv p := by rcases p with ⟨i, j⟩; fin_cases i <;> fin_cases j <;> decide
  right_inv k := by fin_cases k <;> decide

def symplecticQuatMat6 (M : QuatMatrix3) : HermitianEmbeddingMatrix 6 :=
  Matrix.of fun r c =>
    let rp := fin3ProdFin2Equiv6.symm r
    let cp := fin3ProdFin2Equiv6.symm c
    quatMat2 (M rp.1 cp.1) rp.2 cp.2

theorem symplecticQuatMat6_one : symplecticQuatMat6 1 = 1 := by
  funext r c
  rcases hp : fin3ProdFin2Equiv6.symm r with ⟨r1, r2⟩
  rcases hq : fin3ProdFin2Equiv6.symm c with ⟨c1, c2⟩
  have hrc_eq : r = c ↔ r1 = c1 ∧ r2 = c2 := by
    rw [← fin3ProdFin2Equiv6.symm.injective.eq_iff, hp, hq, Prod.mk.injEq]
  simp only [symplecticQuatMat6, Matrix.of_apply, hp, hq, Matrix.one_apply]
  by_cases h1 : r1 = c1
  · subst c1
    fin_cases r2 <;> fin_cases c2 <;> (simp [quatMat2, hrc_eq]; apply Complex.ext <;> simp)
  · fin_cases r2 <;> fin_cases c2 <;> (simp [quatMat2, h1, hrc_eq]; apply Complex.ext <;> simp)

theorem symplecticQuatMat6_add (M N : QuatMatrix3) :
    symplecticQuatMat6 (M + N) = symplecticQuatMat6 M + symplecticQuatMat6 N := by
  funext r c; simp [symplecticQuatMat6, quatMat2_add]

theorem symplecticQuatMat6_smul (r : ℝ) (M : QuatMatrix3) :
    symplecticQuatMat6 (r • M) = r • symplecticQuatMat6 M := by
  funext a b; simp [symplecticQuatMat6, quatMat2_smul]

theorem symplecticQuatMat6_mul (M N : QuatMatrix3) :
    symplecticQuatMat6 (M * N) = symplecticQuatMat6 M * symplecticQuatMat6 N := by
  funext r c
  let rp := fin3ProdFin2Equiv6.symm r
  let cp := fin3ProdFin2Equiv6.symm c
  change quatMat2 ((M * N) rp.1 cp.1) rp.2 cp.2 =
    ∑ k : Fin 6, quatMat2 (M rp.1 (fin3ProdFin2Equiv6.symm k).1) rp.2 (fin3ProdFin2Equiv6.symm k).2 *
      quatMat2 (N (fin3ProdFin2Equiv6.symm k).1 cp.1) (fin3ProdFin2Equiv6.symm k).2 cp.2
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  simp only [quatMat2_add, Matrix.add_apply, quatMat2_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have hsum := Fintype.sum_equiv fin3ProdFin2Equiv6.symm
    (fun k : Fin 6 =>
      quatMat2 (M rp.1 (fin3ProdFin2Equiv6.symm k).1) rp.2 (fin3ProdFin2Equiv6.symm k).2 *
        quatMat2 (N (fin3ProdFin2Equiv6.symm k).1 cp.1) (fin3ProdFin2Equiv6.symm k).2 cp.2)
    (fun p : Fin 3 × Fin 2 =>
      quatMat2 (M rp.1 p.1) rp.2 p.2 * quatMat2 (N p.1 cp.1) p.2 cp.2)
    (fun _ => rfl)
  rw [hsum, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_three, Fin.sum_univ_two]

theorem symplecticQuatMat6_star (M : QuatMatrix3) :
    symplecticQuatMat6 (star M) = (symplecticQuatMat6 M).conjTranspose := by
  funext r c
  change quatMat2 (star (M (fin3ProdFin2Equiv6.symm c).1 (fin3ProdFin2Equiv6.symm r).1))
      (fin3ProdFin2Equiv6.symm r).2 (fin3ProdFin2Equiv6.symm c).2 =
    star (quatMat2 (M (fin3ProdFin2Equiv6.symm c).1 (fin3ProdFin2Equiv6.symm r).1)
      (fin3ProdFin2Equiv6.symm c).2 (fin3ProdFin2Equiv6.symm r).2)
  rw [quatMat2_star, Matrix.conjTranspose_apply]

theorem symplecticQuatMat6_injective : Function.Injective symplecticQuatMat6 := by
  intro M N hMN
  funext i j
  apply quatMat2_injective
  funext a b
  have h := congrFun (congrFun hMN (fin3ProdFin2Equiv6 (i, a))) (fin3ProdFin2Equiv6 (j, b))
  simpa [symplecticQuatMat6] using h

theorem symplecticQuatMat6_trace_re (M : QuatMatrix3) :
    (Matrix.trace (symplecticQuatMat6 M)).re = 2 * ∑ i : Fin 3, (M i i).re := by
  have htr : Matrix.trace (symplecticQuatMat6 M) = ∑ i : Fin 3, Matrix.trace (quatMat2 (M i i)) := by
    simp only [Matrix.trace, Matrix.diag_apply]
    have hsum := Fintype.sum_equiv fin3ProdFin2Equiv6.symm
      (fun r : Fin 6 => symplecticQuatMat6 M r r)
      (fun p : Fin 3 × Fin 2 => quatMat2 (M p.1 p.1) p.2 p.2)
      (fun _ => rfl)
    rw [hsum, Fintype.sum_prod_type]
  rw [htr, Complex.re_sum]
  simp only [quatMat2_trace_re, ← Finset.mul_sum]

def quatWindowEquiv (Q : QuaternionicWindow) : Q.subalgebra.carrier ≃ₗ[ℝ] QuatHermitian3 :=
  ((LinearEquiv.ofInjective Q.embedding Q.injective).trans
    (LinearEquiv.ofEq _ _ Q.range_eq)).symm

theorem quatWindowEquiv_apply_eq (Q : QuaternionicWindow) (x : Q.subalgebra.carrier) :
    Q.embedding (quatWindowEquiv Q x) = x.1 := by
  exact congrArg Subtype.val
    (((LinearEquiv.ofInjective Q.embedding Q.injective).trans
      (LinearEquiv.ofEq _ _ Q.range_eq)).apply_symm_apply x)

def symplecticQuatEmbed (Q : QuaternionicWindow) : SuppliedHermitianEmbedding Q.subalgebra 6 where
  map :=
    { toFun := fun x => symplecticQuatMat6 ((quatWindowEquiv Q x : QuatHermitian3) : QuatMatrix3)
      map_add' := fun x y => by
        rw [map_add]
        exact symplecticQuatMat6_add _ _
      map_smul' := fun r x => by
        rw [map_smul, RingHom.id_apply]
        exact symplecticQuatMat6_smul _ _ }
  injective := fun x y h => by
    apply (quatWindowEquiv Q).injective
    apply Subtype.ext
    exact symplecticQuatMat6_injective h
  hermitian := fun x => by
    change (symplecticQuatMat6 ((quatWindowEquiv Q x : QuatHermitian3) : QuatMatrix3)).IsHermitian
    rw [Matrix.IsHermitian, ← symplecticQuatMat6_star, (quatWindowEquiv Q x).prop]
  unit := by
    have h1 : quatWindowEquiv Q ⟨albertUnit, Q.subalgebra.unit_mem⟩ = 1 :=
      Q.injective (by rw [quatWindowEquiv_apply_eq, Q.unit])
    change symplecticQuatMat6 ((quatWindowEquiv Q ⟨albertUnit, Q.subalgebra.unit_mem⟩ : QuatHermitian3) : QuatMatrix3) = 1
    rw [h1]
    exact symplecticQuatMat6_one
  jordan := fun x y => by
    let A := quatWindowEquiv Q x
    let B := quatWindowEquiv Q y
    obtain ⟨C, hC⟩ := quatHermitian_product_closed A B
    have hemb : Q.embedding C = jordanMul x.1 y.1 := by
      rw [Q.preserves_product A B C hC, quatWindowEquiv_apply_eq, quatWindowEquiv_apply_eq]
    have hqC : quatWindowEquiv Q ⟨jordanMul x.1 y.1, Q.subalgebra.product_mem _ x.2 _ y.2⟩ = C :=
      Q.injective (by rw [quatWindowEquiv_apply_eq, hemb])
    change symplecticQuatMat6 ((quatWindowEquiv Q ⟨jordanMul x.1 y.1, _⟩ : QuatHermitian3) : QuatMatrix3) =
      (1 / 2 : ℝ) • (symplecticQuatMat6 (A : QuatMatrix3) * symplecticQuatMat6 (B : QuatMatrix3) +
        symplecticQuatMat6 (B : QuatMatrix3) * symplecticQuatMat6 (A : QuatMatrix3))
    rw [hqC, hC, symplecticQuatMat6_smul, symplecticQuatMat6_add, symplecticQuatMat6_mul, symplecticQuatMat6_mul]

theorem symplecticQuatEmbed_tracePairing (Q : QuaternionicWindow) (x y : Q.subalgebra.carrier) :
    (Matrix.trace ((symplecticQuatEmbed Q).map x * (symplecticQuatEmbed Q).map y)).re =
      2 * tracePairing x.1 y.1 := by
  let A := quatWindowEquiv Q x
  let B := quatWindowEquiv Q y
  obtain ⟨C, hC⟩ := quatHermitian_product_closed A B
  have htr_re : (Matrix.trace (symplecticQuatMat6 (A : QuatMatrix3) *
      symplecticQuatMat6 (B : QuatMatrix3))).re =
      2 * ∑ i : Fin 3, (((A : QuatMatrix3) * (B : QuatMatrix3)) i i).re := by
    rw [← symplecticQuatMat6_mul, symplecticQuatMat6_trace_re]
  have hre_sum : ∀ (s : Finset (Fin 3)) (f : Fin 3 → Quaternion ℝ),
      (∑ k ∈ s, f k).re = ∑ k ∈ s, (f k).re := fun s f => by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha]; exact congrArg (_ + ·) ih
  have hcomm : ∑ i : Fin 3, (((B : QuatMatrix3) * (A : QuatMatrix3)) i i).re =
      ∑ i : Fin 3, (((A : QuatMatrix3) * (B : QuatMatrix3)) i i).re := by
    simp only [Matrix.mul_apply, hre_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    exact quaternion_real_mul_comm _ _
  have hpair : tracePairing x.1 y.1 = ∑ i : Fin 3, (((A : QuatMatrix3) * (B : QuatMatrix3)) i i).re := by
    unfold tracePairing
    rw [← quatWindowEquiv_apply_eq Q x, ← quatWindowEquiv_apply_eq Q y,
      ← Q.preserves_product A B C hC, Q.preserves_trace C]
    have hC0 : ((C : QuatMatrix3) 0 0).re =
        (1 / 2 : ℝ) * ((((A : QuatMatrix3) * (B : QuatMatrix3)) 0 0).re +
          (((B : QuatMatrix3) * (A : QuatMatrix3)) 0 0).re) :=
      congrArg (fun M : QuatMatrix3 => (M 0 0).re) hC
    have hC1 : ((C : QuatMatrix3) 1 1).re =
        (1 / 2 : ℝ) * ((((A : QuatMatrix3) * (B : QuatMatrix3)) 1 1).re +
          (((B : QuatMatrix3) * (A : QuatMatrix3)) 1 1).re) :=
      congrArg (fun M : QuatMatrix3 => (M 1 1).re) hC
    have hC2 : ((C : QuatMatrix3) 2 2).re =
        (1 / 2 : ℝ) * ((((A : QuatMatrix3) * (B : QuatMatrix3)) 2 2).re +
          (((B : QuatMatrix3) * (A : QuatMatrix3)) 2 2).re) :=
      congrArg (fun M : QuatMatrix3 => (M 2 2).re) hC
    rw [hC0, hC1, hC2]
    have hsumA : ∑ i : Fin 3, (((A : QuatMatrix3) * (B : QuatMatrix3)) i i).re =
        (((A : QuatMatrix3) * (B : QuatMatrix3)) 0 0).re +
          (((A : QuatMatrix3) * (B : QuatMatrix3)) 1 1).re +
          (((A : QuatMatrix3) * (B : QuatMatrix3)) 2 2).re := by
      rw [Fin.sum_univ_three]
    have hsumB : ∑ i : Fin 3, (((B : QuatMatrix3) * (A : QuatMatrix3)) i i).re =
        (((B : QuatMatrix3) * (A : QuatMatrix3)) 0 0).re +
          (((B : QuatMatrix3) * (A : QuatMatrix3)) 1 1).re +
          (((B : QuatMatrix3) * (A : QuatMatrix3)) 2 2).re := by
      rw [Fin.sum_univ_three]
    linarith
  change (Matrix.trace (symplecticQuatMat6 (A : QuatMatrix3) *
    symplecticQuatMat6 (B : QuatMatrix3))).re = 2 * tracePairing x.1 y.1
  rw [htr_re, hpair]

/-! ### Section 5.2: `M_{24}(ℂ)` Clifford Embedding for Any `lineSubalgebra q hq` -/

def pauliMat : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => !![1, 0; 0, 1]
  | 1 => !![0, 1; 1, 0]
  | 2 => !![0, -Complex.I; Complex.I, 0]
  | 3 => !![1, 0; 0, -1]

theorem pauliMat_zero : pauliMat 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat]

theorem pauliMat_herm (a : Fin 4) : (pauliMat a).conjTranspose = pauliMat a := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliMat, Matrix.conjTranspose_apply]

theorem pauliMat_sq (a : Fin 4) : pauliMat a * pauliMat a = 1 := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliMat, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauliMat_anticomm (a b : Fin 4) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    pauliMat a * pauliMat b = -(pauliMat b * pauliMat a) := by
  fin_cases a <;> fin_cases b
  all_goals first
    | exact absurd rfl ha
    | exact absurd rfl hb
    | exact absurd rfl hab
    | (ext i j; fin_cases i <;> fin_cases j <;>
        (simp [pauliMat, Matrix.mul_apply, Fin.sum_univ_two]; try ring))

theorem pauliMat_trace_ne0 (a : Fin 4) (ha : a ≠ 0) : Matrix.trace (pauliMat a) = 0 := by
  fin_cases a
  · exact absurd rfl ha
  · simp [pauliMat, Matrix.trace_fin_two]
  · simp [pauliMat, Matrix.trace_fin_two]
  · simp [pauliMat, Matrix.trace_fin_two]

def fin16Equiv : Fin 16 ≃ Fin 2 × Fin 2 × Fin 2 × Fin 2 where
  toFun k := (⟨k.1 / 8, by omega⟩, ⟨(k.1 / 4) % 2, by omega⟩, ⟨(k.1 / 2) % 2, by omega⟩, ⟨k.1 % 2, by omega⟩)
  invFun p := ⟨8 * p.1.1 + 4 * p.2.1.1 + 2 * p.2.2.1.1 + p.2.2.2.1, by omega⟩
  left_inv k := by fin_cases k <;> decide
  right_inv p := by
    rcases p with ⟨a, b, c, d⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide

def kron4 (A₀ A₁ A₂ A₃ : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 16) (Fin 16) ℂ :=
  Matrix.of fun i j =>
    let ip := fin16Equiv i
    let jp := fin16Equiv j
    A₀ ip.1 jp.1 * A₁ ip.2.1 jp.2.1 * A₂ ip.2.2.1 jp.2.2.1 * A₃ ip.2.2.2 jp.2.2.2

theorem kron4_one : kron4 1 1 1 1 = 1 := by
  ext i j
  simp only [kron4, Matrix.of_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst j; simp
  · have hne : fin16Equiv i ≠ fin16Equiv j := fun h => hij (fin16Equiv.injective h)
    by_cases h1 : (fin16Equiv i).1 = (fin16Equiv j).1
    · by_cases h2 : (fin16Equiv i).2.1 = (fin16Equiv j).2.1
      · by_cases h3 : (fin16Equiv i).2.2.1 = (fin16Equiv j).2.2.1
        · have h4 : (fin16Equiv i).2.2.2 ≠ (fin16Equiv j).2.2.2 := fun h =>
            hne (Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h)))
          simp [hij, h4]
        · simp [hij, h3]
      · simp [hij, h2]
    · simp [hij, h1]

theorem kron4_conjTranspose (A₀ A₁ A₂ A₃ : Matrix (Fin 2) (Fin 2) ℂ) :
    (kron4 A₀ A₁ A₂ A₃).conjTranspose =
      kron4 A₀.conjTranspose A₁.conjTranspose A₂.conjTranspose A₃.conjTranspose := by
  ext i j
  simp only [kron4, Matrix.conjTranspose_apply, Matrix.of_apply, star_mul]
  ring

theorem kron4_mul (A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : Matrix (Fin 2) (Fin 2) ℂ) :
    kron4 A₀ A₁ A₂ A₃ * kron4 B₀ B₁ B₂ B₃ =
      kron4 (A₀ * B₀) (A₁ * B₁) (A₂ * B₂) (A₃ * B₃) := by
  ext i j
  rw [Matrix.mul_apply, ← Equiv.sum_comp fin16Equiv.symm]
  simp only [Fintype.sum_prod_type, kron4, Matrix.of_apply, Matrix.mul_apply,
    Equiv.apply_symm_apply, Fin.sum_univ_two]
  ring

theorem kron4_trace (A₀ A₁ A₂ A₃ : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (kron4 A₀ A₁ A₂ A₃) =
      Matrix.trace A₀ * Matrix.trace A₁ * Matrix.trace A₂ * Matrix.trace A₃ := by
  rw [Matrix.trace, ← Equiv.sum_comp fin16Equiv.symm]
  simp only [Fintype.sum_prod_type, kron4, Matrix.diag_apply, Matrix.of_apply,
    Equiv.apply_symm_apply, Matrix.trace, Fin.sum_univ_two]
  ring

def cliffordCode : Fin 9 → Fin 4 × Fin 4 × Fin 4 × Fin 4
  | 0 => (1, 1, 1, 1)
  | 1 => (1, 1, 1, 2)
  | 2 => (1, 1, 1, 3)
  | 3 => (1, 1, 3, 0)
  | 4 => (1, 1, 2, 0)
  | 5 => (1, 3, 0, 0)
  | 6 => (1, 2, 0, 0)
  | 7 => (3, 0, 0, 0)
  | 8 => (2, 0, 0, 0)

def cliffordGamma (k : Fin 9) : Matrix (Fin 16) (Fin 16) ℂ :=
  let c := cliffordCode k
  kron4 (pauliMat c.1) (pauliMat c.2.1) (pauliMat c.2.2.1) (pauliMat c.2.2.2)

theorem cliffordGamma_herm (k : Fin 9) : (cliffordGamma k).IsHermitian := by
  rw [Matrix.IsHermitian, cliffordGamma, kron4_conjTranspose, pauliMat_herm, pauliMat_herm,
    pauliMat_herm, pauliMat_herm]

theorem cliffordGamma_sq (k : Fin 9) : cliffordGamma k * cliffordGamma k = 1 := by
  rw [cliffordGamma, kron4_mul, pauliMat_sq, pauliMat_sq, pauliMat_sq, pauliMat_sq, kron4_one]

theorem cliffordGamma_trace (k : Fin 9) : Matrix.trace (cliffordGamma k) = 0 := by
  have h1 : (cliffordCode k).1 ≠ 0 := by fin_cases k <;> decide
  rw [cliffordGamma, kron4_trace, pauliMat_trace_ne0 _ h1, zero_mul, zero_mul, zero_mul]

private theorem kron4_anti_of_factors (A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : Matrix (Fin 2) (Fin 2) ℂ)
    (s0 s1 s2 s3 : ℂ)
    (h0 : A₀ * B₀ = s0 • (B₀ * A₀)) (h1 : A₁ * B₁ = s1 • (B₁ * A₁))
    (h2 : A₂ * B₂ = s2 • (B₂ * A₂)) (h3 : A₃ * B₃ = s3 • (B₃ * A₃))
    (hs : s0 * s1 * s2 * s3 = -1) :
    kron4 A₀ A₁ A₂ A₃ * kron4 B₀ B₁ B₂ B₃ = -(kron4 B₀ B₁ B₂ B₃ * kron4 A₀ A₁ A₂ A₃) := by
  rw [kron4_mul, kron4_mul, h0, h1, h2, h3]
  ext i j
  simp only [kron4, Matrix.of_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
  calc
    (s0 * (B₀ * A₀) (fin16Equiv i).1 (fin16Equiv j).1) *
        (s1 * (B₁ * A₁) (fin16Equiv i).2.1 (fin16Equiv j).2.1) *
        (s2 * (B₂ * A₂) (fin16Equiv i).2.2.1 (fin16Equiv j).2.2.1) *
        (s3 * (B₃ * A₃) (fin16Equiv i).2.2.2 (fin16Equiv j).2.2.2)
      = (s0 * s1 * s2 * s3) *
          ((B₀ * A₀) (fin16Equiv i).1 (fin16Equiv j).1 *
            (B₁ * A₁) (fin16Equiv i).2.1 (fin16Equiv j).2.1 *
            (B₂ * A₂) (fin16Equiv i).2.2.1 (fin16Equiv j).2.2.1 *
            (B₃ * A₃) (fin16Equiv i).2.2.2 (fin16Equiv j).2.2.2) := by ring
    _ = _ := by rw [hs]; ring

private theorem pauli_comm_sign (a b : Fin 4) :
    pauliMat a * pauliMat b =
      (if a = 0 ∨ b = 0 ∨ a = b then (1 : ℂ) else -1) • (pauliMat b * pauliMat a) := by
  split_ifs with h0
  · rw [one_smul]
    rcases h0 with rfl | rfl | rfl
    · rw [pauliMat_zero, one_mul, mul_one]
    · rw [pauliMat_zero, one_mul, mul_one]
    · rfl
  · rw [neg_one_smul]
    push Not at h0
    exact pauliMat_anticomm a b h0.1 h0.2.1 h0.2.2

theorem cliffordGamma_anticomm (j k : Fin 9) (hjk : j ≠ k) :
    cliffordGamma j * cliffordGamma k = -(cliffordGamma k * cliffordGamma j) := by
  let c := cliffordCode j
  let d := cliffordCode k
  let s (a b : Fin 4) : ℂ := if a = 0 ∨ b = 0 ∨ a = b then 1 else -1
  have hs : s c.1 d.1 * s c.2.1 d.2.1 * s c.2.2.1 d.2.2.1 * s c.2.2.2 d.2.2.2 = -1 := by
    dsimp only [s, c, d]
    fin_cases j <;> fin_cases k <;>
      first | exact absurd rfl hjk | (simp [cliffordCode]; try ring)
  exact kron4_anti_of_factors _ _ _ _ _ _ _ _
    (s c.1 d.1) (s c.2.1 d.2.1) (s c.2.2.1 d.2.2.1) (s c.2.2.2 d.2.2.2)
    (pauli_comm_sign c.1 d.1) (pauli_comm_sign c.2.1 d.2.1)
    (pauli_comm_sign c.2.2.1 d.2.2.1) (pauli_comm_sign c.2.2.2 d.2.2.2) hs

def fin8SumFin16Equiv : Fin 8 ⊕ Fin 16 ≃ Fin 24 where
  toFun
    | Sum.inl i => ⟨i.1, by omega⟩
    | Sum.inr j => ⟨8 + j.1, by omega⟩
  invFun k := if h : k.1 < 8 then Sum.inl ⟨k.1, h⟩ else Sum.inr ⟨k.1 - 8, by omega⟩
  left_inv s := by cases s with
    | inl i => simp [i.isLt]
    | inr j => simp
  right_inv k := by
    dsimp only
    split_ifs with h
    · rfl
    · exact Fin.ext (by dsimp; omega)

def block8x16 (A : Matrix (Fin 8) (Fin 8) ℂ) (B : Matrix (Fin 16) (Fin 16) ℂ) :
    HermitianEmbeddingMatrix 24 :=
  Matrix.reindex fin8SumFin16Equiv fin8SumFin16Equiv (Matrix.fromBlocks A 0 0 B)

theorem block8x16_one : block8x16 1 1 = 1 := by
  simp only [block8x16, Matrix.fromBlocks_one]
  exact (Matrix.reindexAlgEquiv ℂ ℂ fin8SumFin16Equiv).map_one

theorem block8x16_add (A₁ A₂ : Matrix (Fin 8) (Fin 8) ℂ) (B₁ B₂ : Matrix (Fin 16) (Fin 16) ℂ) :
    block8x16 (A₁ + A₂) (B₁ + B₂) = block8x16 A₁ B₁ + block8x16 A₂ B₂ := by
  simp only [block8x16]
  have h : Matrix.fromBlocks (A₁ + A₂) (0 : Matrix (Fin 8) (Fin 16) ℂ) 0 (B₁ + B₂) =
      Matrix.fromBlocks A₁ 0 0 B₁ + Matrix.fromBlocks A₂ 0 0 B₂ := by
    ext (i | i) (j | j) <;> simp
  rw [h]
  exact (Matrix.reindexAlgEquiv ℂ ℂ fin8SumFin16Equiv).map_add _ _

theorem block8x16_smul (r : ℝ) (A : Matrix (Fin 8) (Fin 8) ℂ) (B : Matrix (Fin 16) (Fin 16) ℂ) :
    block8x16 (r • A) (r • B) = r • block8x16 A B := by
  simp only [block8x16]
  have h : Matrix.fromBlocks (r • A) (0 : Matrix (Fin 8) (Fin 16) ℂ) 0 (r • B) =
      r • Matrix.fromBlocks A 0 0 B := by
    ext (i | i) (j | j) <;> simp
  rw [h]
  ext i j
  simp [Matrix.reindex_apply]

theorem block8x16_mul (A₁ A₂ : Matrix (Fin 8) (Fin 8) ℂ) (B₁ B₂ : Matrix (Fin 16) (Fin 16) ℂ) :
    block8x16 (A₁ * A₂) (B₁ * B₂) = block8x16 A₁ B₁ * block8x16 A₂ B₂ := by
  simp only [block8x16]
  have h : Matrix.fromBlocks (A₁ * A₂) (0 : Matrix (Fin 8) (Fin 16) ℂ) 0 (B₁ * B₂) =
      Matrix.fromBlocks A₁ 0 0 B₁ * Matrix.fromBlocks A₂ 0 0 B₂ := by
    rw [Matrix.fromBlocks_multiply]; simp
  rw [h]
  exact (Matrix.reindexAlgEquiv ℂ ℂ fin8SumFin16Equiv).map_mul _ _

theorem block8x16_conjTranspose (A : Matrix (Fin 8) (Fin 8) ℂ) (B : Matrix (Fin 16) (Fin 16) ℂ) :
    (block8x16 A B).conjTranspose = block8x16 A.conjTranspose B.conjTranspose := by
  ext i j
  simp only [block8x16, Matrix.conjTranspose_apply, Matrix.reindex_apply]
  have h := congrFun (congrFun
    (Matrix.fromBlocks_conjTranspose A (0 : Matrix (Fin 8) (Fin 16) ℂ) 0 B)
    (fin8SumFin16Equiv.symm i)) (fin8SumFin16Equiv.symm j)
  simpa [Matrix.conjTranspose_apply] using h

theorem block8x16_trace (A : Matrix (Fin 8) (Fin 8) ℂ) (B : Matrix (Fin 16) (Fin 16) ℂ) :
    Matrix.trace (block8x16 A B) = Matrix.trace A + Matrix.trace B := by
  rw [Matrix.trace, ← Equiv.sum_comp fin8SumFin16Equiv]
  simp [Fintype.sum_sum_type, block8x16, Matrix.diag_apply, Matrix.reindex_apply, Matrix.trace]

def octCoordFin8 (z : Octonion) : Fin 8 → ℝ :=
  ![z.1.re, z.1.imI, z.1.imJ, z.1.imK, z.2.re, z.2.imI, z.2.imJ, z.2.imK]

def lineVecFin9 (y : Albert) : Fin 9 → ℝ :=
  ![(1 / 2 : ℝ) * (y.1 1 - y.1 2),
    (y.2 2).1.re, (y.2 2).1.imI, (y.2 2).1.imJ, (y.2 2).1.imK,
    (y.2 2).2.re, (y.2 2).2.imI, (y.2 2).2.imJ, (y.2 2).2.imK]

private theorem lineVecFin9_dot (x y : Albert) :
    ∑ k : Fin 9, lineVecFin9 x k * lineVecFin9 y k =
      ((1 / 2 : ℝ) * (x.1 1 - x.1 2)) * ((1 / 2 : ℝ) * (y.1 1 - y.1 2)) +
        octDot (x.2 2) (y.2 2) := by
  rw [Fin.sum_univ_succ, octDot_eq_coords]
  simp [lineVecFin9, Fin.sum_univ_eight]

def lineDiag0Mat : Albert →ₗ[ℝ] HermitianEmbeddingMatrix 24 where
  toFun y :=
    let r : ℝ := y.1 0
    let a : ℝ := (1 / 2 : ℝ) * (y.1 1 + y.1 2)
    let v : Fin 9 → ℝ := lineVecFin9 y
    block8x16 (r • (1 : Matrix (Fin 8) (Fin 8) ℂ))
      (a • (1 : Matrix (Fin 16) (Fin 16) ℂ) + ∑ k : Fin 9, (v k : ℝ) • cliffordGamma k)
  map_add' x y := by
    have hv : ∀ k : Fin 9, lineVecFin9 (x + y) k = lineVecFin9 x k + lineVecFin9 y k := fun k => by
      fin_cases k <;> (simp [lineVecFin9, albert_add_fst, albert_add_snd, oct_add_fst, oct_add_snd]; try ring)
    dsimp only
    rw [← block8x16_add]
    congr 1
    · ext i j
      by_cases hij : i = j
      · subst hij; simp [albert_add_fst, Complex.real_smul]
      · simp [albert_add_fst, hij]
    · have hsum : (∑ k : Fin 9, lineVecFin9 (x + y) k • cliffordGamma k) =
          (∑ k : Fin 9, lineVecFin9 x k • cliffordGamma k) +
            (∑ k : Fin 9, lineVecFin9 y k • cliffordGamma k) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hv k, add_smul]
      rw [hsum]
      ext i j
      by_cases hij : i = j
      · subst hij; simp [albert_add_fst, Complex.real_smul]; ring
      · simp [albert_add_fst, hij]
  map_smul' r x := by
    have hv : ∀ k : Fin 9, lineVecFin9 (r • x) k = r * lineVecFin9 x k := fun k => by
      fin_cases k <;> (simp [lineVecFin9, albert_smul_fst, albert_smul_snd, oct_smul_fst, oct_smul_snd]; try ring)
    dsimp only
    rw [← block8x16_smul, RingHom.id_apply]
    congr 1
    · ext i j
      by_cases hij : i = j
      · subst hij; simp [albert_smul_fst, Complex.real_smul]
      · simp [albert_smul_fst, hij]
    · have hsum : (∑ k : Fin 9, lineVecFin9 (r • x) k • cliffordGamma k) =
          r • (∑ k : Fin 9, lineVecFin9 x k • cliffordGamma k) := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hv k, mul_smul]
      rw [hsum, smul_add]
      ext i j
      by_cases hij : i = j
      · subst hij; simp [albert_smul_fst, Complex.real_smul]; ring
      · simp [albert_smul_fst, hij]

theorem lineDiag0Mat_herm (y : Albert) : (lineDiag0Mat y).IsHermitian := by
  rw [Matrix.IsHermitian, lineDiag0Mat, LinearMap.coe_mk, AddHom.coe_mk, block8x16_conjTranspose]
  congr 1
  · ext i j
    by_cases hij : i = j
    · subst hij; apply Complex.ext <;> simp [Matrix.conjTranspose_apply, Complex.real_smul]
    · apply Complex.ext <;> simp [Matrix.conjTranspose_apply, hij, Ne.symm hij]
  · rw [Matrix.conjTranspose_add, Matrix.conjTranspose_sum]
    congr 1
    · ext i j
      by_cases hij : i = j
      · subst hij; apply Complex.ext <;> simp [Matrix.conjTranspose_apply, Complex.real_smul]
      · apply Complex.ext <;> simp [Matrix.conjTranspose_apply, hij, Ne.symm hij]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.conjTranspose_smul, (cliffordGamma_herm k).eq, star_trivial]

theorem lineDiag0Mat_unit : lineDiag0Mat albertUnit = 1 := by
  have hv0 : ∀ k : Fin 9, lineVecFin9 albertUnit k = 0 := fun k => by
    fin_cases k <;> simp [lineVecFin9, albertUnit_fst, albertUnit_snd, oct_zero_fst, oct_zero_snd]
  change block8x16 ((1 : ℝ) • 1) (((1 / 2 : ℝ) * (1 + 1)) • 1 + ∑ k : Fin 9, lineVecFin9 albertUnit k • cliffordGamma k) = 1
  simp only [hv0, zero_smul, Finset.sum_const_zero, add_zero, one_smul]
  rw [show (1 / 2 : ℝ) * (1 + 1) = 1 by norm_num, one_smul]
  exact block8x16_one

theorem lineDiag0Mat_trace_mul_re (x y : Albert) (hx : x.2 0 = 0 ∧ x.2 1 = 0)
    (hy : y.2 0 = 0 ∧ y.2 1 = 0) :
    (Matrix.trace (lineDiag0Mat x * lineDiag0Mat y)).re = 8 * tracePairing x y := by
  dsimp only [lineDiag0Mat, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← block8x16_mul, block8x16_trace]
  let rx := x.1 0
  let ry := y.1 0
  let ax := (1 / 2 : ℝ) * (x.1 1 + x.1 2)
  let ay := (1 / 2 : ℝ) * (y.1 1 + y.1 2)
  let vx := lineVecFin9 x
  let vy := lineVecFin9 y
  have h8 : Matrix.trace ((rx • (1 : Matrix (Fin 8) (Fin 8) ℂ)) *
      (ry • (1 : Matrix (Fin 8) (Fin 8) ℂ))) = ((8 * (rx * ry) : ℝ) : ℂ) := by
    have hsm : (rx • (1 : Matrix (Fin 8) (Fin 8) ℂ)) * (ry • (1 : Matrix (Fin 8) (Fin 8) ℂ)) =
        (rx * ry) • (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
      rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, one_mul, smul_smul]
    rw [hsm, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, Complex.real_smul]
    push_cast; ring
  have h16_cross : ∀ (j k : Fin 9), Matrix.trace (cliffordGamma j * cliffordGamma k) =
      if j = k then 16 else 0 := fun j k => by
    by_cases hjk : j = k
    · subst k; simp [cliffordGamma_sq, Matrix.trace_one, Fintype.card_fin]
    · rw [ite_eq_right_iff.mpr (fun h => absurd h hjk)]
      have htr : Matrix.trace (cliffordGamma j * cliffordGamma k) =
          -Matrix.trace (cliffordGamma j * cliffordGamma k) := by
        calc
          Matrix.trace (cliffordGamma j * cliffordGamma k)
            = Matrix.trace (-(cliffordGamma k * cliffordGamma j)) := by rw [cliffordGamma_anticomm j k hjk]
          _ = -Matrix.trace (cliffordGamma k * cliffordGamma j) := Matrix.trace_neg _
          _ = -Matrix.trace (cliffordGamma j * cliffordGamma k) := by rw [Matrix.trace_mul_comm]
      have h2 : 2 * Matrix.trace (cliffordGamma j * cliffordGamma k) = 0 := by
        rw [two_mul]
        conv_lhs => rhs; rw [htr]
        exact add_neg_cancel _
      exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  have h16 : Matrix.trace
      ((ax • (1 : Matrix (Fin 16) (Fin 16) ℂ) + ∑ k : Fin 9, vx k • cliffordGamma k) *
       (ay • (1 : Matrix (Fin 16) (Fin 16) ℂ) + ∑ k : Fin 9, vy k • cliffordGamma k)) =
      ((16 * (ax * ay + ∑ k : Fin 9, vx k * vy k) : ℝ) : ℂ) := by
    rw [mul_add, add_mul, add_mul, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add]
    have ht1 : Matrix.trace ((ax • (1 : Matrix (Fin 16) (Fin 16) ℂ)) *
        (ay • (1 : Matrix (Fin 16) (Fin 16) ℂ))) = ((16 * (ax * ay) : ℝ) : ℂ) := by
      have hsm : (ax • (1 : Matrix (Fin 16) (Fin 16) ℂ)) * (ay • (1 : Matrix (Fin 16) (Fin 16) ℂ)) =
          (ax * ay) • (1 : Matrix (Fin 16) (Fin 16) ℂ) := by
        rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, one_mul, smul_smul]
      rw [hsm, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, Complex.real_smul]
      push_cast; ring
    have ht2 : Matrix.trace ((ax • (1 : Matrix (Fin 16) (Fin 16) ℂ)) *
        ∑ k : Fin 9, vy k • cliffordGamma k) = 0 := by
      rw [Finset.mul_sum, Matrix.trace_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      have hsm : (ax • (1 : Matrix (Fin 16) (Fin 16) ℂ)) * (vy k • cliffordGamma k) =
          (ax * vy k) • cliffordGamma k := by
        rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, one_mul, smul_smul]
      rw [hsm, Matrix.trace_smul, cliffordGamma_trace, smul_zero]
    have ht3 : Matrix.trace ((∑ k : Fin 9, vx k • cliffordGamma k) *
        (ay • (1 : Matrix (Fin 16) (Fin 16) ℂ))) = 0 := by
      rw [Finset.sum_mul, Matrix.trace_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      have hsm : (vx k • cliffordGamma k) * (ay • (1 : Matrix (Fin 16) (Fin 16) ℂ)) =
          (vx k * ay) • cliffordGamma k := by
        rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, mul_one, smul_smul]
      rw [hsm, Matrix.trace_smul, cliffordGamma_trace, smul_zero]
    have ht4 : Matrix.trace ((∑ j : Fin 9, vx j • cliffordGamma j) *
        ∑ k : Fin 9, vy k • cliffordGamma k) = ((16 * ∑ k : Fin 9, vx k * vy k : ℝ) : ℂ) := by
      rw [Finset.sum_mul, Matrix.trace_sum]
      simp_rw [Finset.mul_sum, Matrix.trace_sum]
      have hterm : ∀ j k : Fin 9, Matrix.trace ((vx j • cliffordGamma j) * (vy k • cliffordGamma k)) =
          if j = k then (((16 * (vx j * vy k) : ℝ) : ℂ)) else 0 := fun j k => by
        rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, Matrix.trace_smul, h16_cross j k]
        split_ifs
        · simp [Complex.real_smul]; ring
        · simp
      simp_rw [hterm, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      push_cast; rfl
    rw [ht1, ht2, ht3, ht4, add_zero, zero_add]
    push_cast; ring
  dsimp only [rx, ry, ax, ay, vx, vy] at h8 h16 ⊢
  rw [h8, h16]
  simp only [Complex.add_re, Complex.ofReal_re]
  rw [lineVecFin9_dot]
  have htp : tracePairing x y =
      x.1 0 * y.1 0 + x.1 1 * y.1 1 + x.1 2 * y.1 2 + 2 * octDot (x.2 2) (y.2 2) := by
    simp only [tracePairing_eq_coords, hx.1, hx.2, hy.1, hy.2, octDot_zero_left]
    ring
  rw [htp]
  ring

theorem lineDiag0Mat_jordan (x y : Albert) (hx : x.2 0 = 0 ∧ x.2 1 = 0)
    (hy : y.2 0 = 0 ∧ y.2 1 = 0) :
    lineDiag0Mat (jordanMul x y) =
      (1 / 2 : ℝ) • (lineDiag0Mat x * lineDiag0Mat y + lineDiag0Mat y * lineDiag0Mat x) := by
  let rx := x.1 0; let ry := y.1 0
  let ax := (1 / 2 : ℝ) * (x.1 1 + x.1 2); let ay := (1 / 2 : ℝ) * (y.1 1 + y.1 2)
  let dx := (1 / 2 : ℝ) * (x.1 1 - x.1 2); let dy := (1 / 2 : ℝ) * (y.1 1 - y.1 2)
  let vx := lineVecFin9 x; let vy := lineVecFin9 y
  have hj0 : (jordanMul x y).1 0 = rx * ry := by
    rw [jordanMul_diag_0, hx.1, hx.2, hy.1, hy.2, octDot_zero_left]; ring
  have hj1 : (jordanMul x y).1 1 = x.1 1 * y.1 1 + octDot (x.2 2) (y.2 2) := by
    rw [jordanMul_diag_1, hx.1, hy.1, octDot_zero_left]; ring
  have hj2 : (jordanMul x y).1 2 = x.1 2 * y.1 2 + octDot (x.2 2) (y.2 2) := by
    rw [jordanMul_diag_2, hx.2, hy.2, octDot_zero_left]; ring
  have hj12 : (jordanMul x y).2 2 = ax • y.2 2 + ay • x.2 2 := by
    rw [jordanMul_off_2, hx.1, hx.2, hy.1, hy.2, octonionConj_zero, octonionMul_zero_left,
      add_zero, add_zero, smul_add, smul_smul, smul_smul]
  have ha_eq : (1 / 2 : ℝ) * ((jordanMul x y).1 1 + (jordanMul x y).1 2) =
      ax * ay + ∑ k : Fin 9, vx k * vy k := by
    rw [hj1, hj2, lineVecFin9_dot]; dsimp only [ax, ay]; ring
  have hv_eq : ∀ k : Fin 9, lineVecFin9 (jordanMul x y) k = ax * vy k + ay * vx k := fun k => by
    dsimp only [vx, vy, lineVecFin9]
    fin_cases k
    · dsimp; simp only [hj1, hj2]; dsimp only [ax, ay]; ring
    all_goals
      (simp [hj12, oct_add_fst, oct_add_snd, oct_smul_fst, oct_smul_snd]; try ring)
  dsimp only [lineDiag0Mat, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← block8x16_mul, ← block8x16_mul, ← block8x16_add, ← block8x16_smul]
  congr 1
  · rw [hj0]
    simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, one_mul, smul_smul]
    rw [← add_smul, smul_smul]
    congr 1
    ring
  · have hsum_diag : (∑ k : Fin 9, (vx k * vy k) • (1 : Matrix (Fin 16) (Fin 16) ℂ)) =
        (∑ k : Fin 9, vx k * vy k) • (1 : Matrix (Fin 16) (Fin 16) ℂ) := by
      rw [← Finset.sum_smul]
    have hgamma_anti : ∀ j k : Fin 9,
        (vx j • cliffordGamma j) * (vy k • cliffordGamma k) +
          (vy k • cliffordGamma k) * (vx j • cliffordGamma j) =
        if j = k then (2 * (vx j * vy k)) • (1 : Matrix (Fin 16) (Fin 16) ℂ) else 0 := fun j k => by
      rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul,
        Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
      by_cases hjk : j = k
      · subst k
        simp only [↓reduceIte, cliffordGamma_sq, mul_comm (vy j) (vx j)]
        rw [← add_smul, ← two_mul]
      · simp only [ite_eq_right_iff.mpr (fun h => absurd h hjk), cliffordGamma_anticomm j k hjk,
          mul_comm (vy k) (vx j), smul_neg]
        exact neg_add_cancel _
    have hanti_sum :
        (1 / 2 : ℝ) • ((∑ j : Fin 9, vx j • cliffordGamma j) * (∑ k : Fin 9, vy k • cliffordGamma k) +
          (∑ k : Fin 9, vy k • cliffordGamma k) * (∑ j : Fin 9, vx j • cliffordGamma j)) =
        (∑ k : Fin 9, vx k * vy k) • (1 : Matrix (Fin 16) (Fin 16) ℂ) := by
      rw [Finset.sum_mul, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      have hcomm_sum : (∑ x_1 : Fin 9, ∑ x_2 : Fin 9,
          (vy x_1 • cliffordGamma x_1) * (vx x_2 • cliffordGamma x_2)) =
          (∑ j : Fin 9, ∑ k : Fin 9, (vy k • cliffordGamma k) * (vx j • cliffordGamma j)) :=
        Finset.sum_comm
      rw [hcomm_sum, ← Finset.sum_add_distrib]
      have hpair_sum : (∑ j : Fin 9,
          ((∑ k : Fin 9, (vx j • cliffordGamma j) * (vy k • cliffordGamma k)) +
            (∑ k : Fin 9, (vy k • cliffordGamma k) * (vx j • cliffordGamma j)))) =
          ∑ j : Fin 9, (2 * (vx j * vy j)) • (1 : Matrix (Fin 16) (Fin 16) ℂ) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.sum_add_distrib]
        simp_rw [hgamma_anti j]
        simp [Finset.sum_ite_eq]
      rw [hpair_sum, Finset.smul_sum]
      simp_rw [smul_smul]
      rw [← Finset.sum_smul]
      congr 1
      refine Finset.sum_congr rfl fun j _ => by ring
    have hcross : ∀ (r0 : ℝ) (u : Fin 9 → ℝ),
        (r0 • (1 : Matrix (Fin 16) (Fin 16) ℂ)) * (∑ k : Fin 9, u k • cliffordGamma k) =
          ∑ k : Fin 9, (r0 * u k) • cliffordGamma k := fun r0 u => by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, one_mul, smul_smul]
    have hcross' : ∀ (r0 : ℝ) (u : Fin 9 → ℝ),
        (∑ k : Fin 9, u k • cliffordGamma k) * (r0 • (1 : Matrix (Fin 16) (Fin 16) ℂ)) =
          ∑ k : Fin 9, (r0 * u k) • cliffordGamma k := fun r0 u => by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, mul_one, smul_smul, mul_comm]
    have hmain : (ax • (1 : Matrix (Fin 16) (Fin 16) ℂ) + ∑ k : Fin 9, vx k • cliffordGamma k) *
        (ay • (1 : Matrix (Fin 16) (Fin 16) ℂ) + ∑ k : Fin 9, vy k • cliffordGamma k) +
        (ay • (1 : Matrix (Fin 16) (Fin 16) ℂ) + ∑ k : Fin 9, vy k • cliffordGamma k) *
        (ax • (1 : Matrix (Fin 16) (Fin 16) ℂ) + ∑ k : Fin 9, vx k • cliffordGamma k) =
        (2 * (ax * ay)) • (1 : Matrix (Fin 16) (Fin 16) ℂ) +
        ((2 : ℝ) • ∑ k : Fin 9, (ax * vy k + ay * vx k) • cliffordGamma k) +
        ((∑ j : Fin 9, vx j • cliffordGamma j) * (∑ k : Fin 9, vy k • cliffordGamma k) +
          (∑ k : Fin 9, vy k • cliffordGamma k) * (∑ j : Fin 9, vx j • cliffordGamma j)) := by
      have ha_prod : (ax • (1 : Matrix (Fin 16) (Fin 16) ℂ)) * (ay • (1 : Matrix (Fin 16) (Fin 16) ℂ)) +
          (ay • (1 : Matrix (Fin 16) (Fin 16) ℂ)) * (ax • (1 : Matrix (Fin 16) (Fin 16) ℂ)) =
          (2 * (ax * ay)) • (1 : Matrix (Fin 16) (Fin 16) ℂ) := by
        simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, one_mul, smul_smul]
        rw [← add_smul]
        congr 1
        ring
      rw [mul_add, add_mul, add_mul, mul_add, add_mul, add_mul,
        hcross ax vy, hcross' ay vx, hcross ay vx, hcross' ax vy]
      have hsums : (∑ k : Fin 9, (ax * vy k) • cliffordGamma k) +
          (∑ k : Fin 9, (ay * vx k) • cliffordGamma k) +
          ((∑ k : Fin 9, (ay * vx k) • cliffordGamma k) +
          (∑ k : Fin 9, (ax * vy k) • cliffordGamma k)) =
          (2 : ℝ) • ∑ k : Fin 9, (ax * vy k + ay * vx k) • cliffordGamma k := by
        rw [Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← add_smul, ← add_smul, ← add_smul, smul_smul]; ring_nf
      calc
        ((ax • (1 : Matrix (Fin 16) (Fin 16) ℂ)) * (ay • 1) + ∑ k : Fin 9, (ay * vx k) • cliffordGamma k +
          (∑ k : Fin 9, (ax * vy k) • cliffordGamma k + (∑ j, vx j • cliffordGamma j) * ∑ k, vy k • cliffordGamma k)) +
          ((ay • 1) * (ax • 1) + ∑ k : Fin 9, (ax * vy k) • cliffordGamma k +
          (∑ k : Fin 9, (ay * vx k) • cliffordGamma k + (∑ k, vy k • cliffordGamma k) * ∑ j, vx j • cliffordGamma j))
          = ((ax • 1) * (ay • 1) + (ay • 1) * (ax • 1)) +
            ((∑ k : Fin 9, (ax * vy k) • cliffordGamma k) + (∑ k : Fin 9, (ay * vx k) • cliffordGamma k) +
              ((∑ k : Fin 9, (ay * vx k) • cliffordGamma k) + (∑ k : Fin 9, (ax * vy k) • cliffordGamma k))) +
            ((∑ j, vx j • cliffordGamma j) * ∑ k, vy k • cliffordGamma k +
              (∑ k, vy k • cliffordGamma k) * ∑ j, vx j • cliffordGamma j) := by abel
        _ = _ := by rw [ha_prod, hsums]
    rw [hmain, smul_add, smul_add, smul_smul, smul_smul, hanti_sum]
    have hc1 : (1 / 2 : ℝ) * (2 * (ax * ay)) = ax * ay := by ring
    have hc2 : (1 / 2 : ℝ) * 2 = 1 := by ring
    rw [hc1, hc2, one_smul, ha_eq, add_smul]
    simp_rw [hv_eq]
    abel

def lineCliffordEmbed (q : Albert) (hq : IsAtom q) :
    SuppliedHermitianEmbedding (lineSubalgebra q hq) 24 :=
  let g := Classical.choose (atom_to_diagAtom0 q hq)
  let hg : g.linearEquiv q = diagAtom 0 := Classical.choose_spec (atom_to_diagAtom0 q hq)
  let toDiag0 : (lineSubalgebra q hq).carrier →ₗ[ℝ] Albert :=
    g.linearEquiv.toLinearMap.comp (lineSubalgebra q hq).carrier.subtype
  have hdiag_coords : ∀ x : (lineSubalgebra q hq).carrier,
      (g.linearEquiv x.1).2 0 = 0 ∧ (g.linearEquiv x.1).2 1 = 0 := fun x => by
    have hmem := (mem_lineSubalgebra_iff q hq x.1).mp x.2
    have hm : jordanMul (diagAtom 0) (g.linearEquiv x.1) =
        tracePairing (diagAtom 0) (g.linearEquiv x.1) • diagAtom 0 := by
      rw [← hg, ← g.preserves_product, hmem, map_smul, g.map_tracePairing]
    exact (mem_line_diag0_iff _).mp ((mem_lineSubalgebra_iff (diagAtom 0) (diagAtom_isAtom 0) _).mpr hm)
  let mapLM : (lineSubalgebra q hq).carrier →ₗ[ℝ] HermitianEmbeddingMatrix 24 :=
    lineDiag0Mat.comp toDiag0
  { map := mapLM
    injective := fun x y hxy => by
      have hdiff : mapLM (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      have hpair0 : tracePairing (g.linearEquiv (x.1 - y.1)) (g.linearEquiv (x.1 - y.1)) = 0 := by
        have hx0 := hdiag_coords (x - y)
        have htr := lineDiag0Mat_trace_mul_re (g.linearEquiv (x - y).1) (g.linearEquiv (x - y).1) hx0 hx0
        have hm0 : lineDiag0Mat (g.linearEquiv (x - y).1) = 0 := hdiff
        rw [hm0, zero_mul, Matrix.trace_zero, Complex.zero_re] at htr
        have hsub : (x - y).1 = x.1 - y.1 := rfl
        rw [hsub] at htr
        linarith [tracePairing_self_nonneg (g.linearEquiv (x.1 - y.1))]
      have hgy : g.linearEquiv (x.1 - y.1) = 0 := (tracePairing_self_eq_zero _).mp hpair0
      have hxy0 : x.1 - y.1 = 0 := g.linearEquiv.injective (by rw [hgy, map_zero])
      exact Subtype.ext (sub_eq_zero.mp hxy0)
    hermitian := fun x => lineDiag0Mat_herm (g.linearEquiv x.1)
    unit := by
      change lineDiag0Mat (g.linearEquiv albertUnit) = 1
      rw [g.preserves_unit]
      exact lineDiag0Mat_unit
    jordan := fun x y => by
      change lineDiag0Mat (g.linearEquiv (jordanMul x.1 y.1)) =
        (1 / 2 : ℝ) • (lineDiag0Mat (g.linearEquiv x.1) * lineDiag0Mat (g.linearEquiv y.1) +
          lineDiag0Mat (g.linearEquiv y.1) * lineDiag0Mat (g.linearEquiv x.1))
      rw [g.preserves_product]
      exact lineDiag0Mat_jordan _ _ (hdiag_coords x) (hdiag_coords y) }

theorem lineCliffordEmbed_tracePairing (q : Albert) (hq : IsAtom q)
    (x y : (lineSubalgebra q hq).carrier) :
    (Matrix.trace ((lineCliffordEmbed q hq).map x * (lineCliffordEmbed q hq).map y)).re =
      8 * tracePairing x.1 y.1 := by
  let g := Classical.choose (atom_to_diagAtom0 q hq)
  let hg : g.linearEquiv q = diagAtom 0 := Classical.choose_spec (atom_to_diagAtom0 q hq)
  have hdiag_coords : ∀ z : (lineSubalgebra q hq).carrier,
      (g.linearEquiv z.1).2 0 = 0 ∧ (g.linearEquiv z.1).2 1 = 0 := fun z => by
    have hmem := (mem_lineSubalgebra_iff q hq z.1).mp z.2
    have hm : jordanMul (diagAtom 0) (g.linearEquiv z.1) =
        tracePairing (diagAtom 0) (g.linearEquiv z.1) • diagAtom 0 := by
      rw [← hg, ← g.preserves_product, hmem, map_smul, g.map_tracePairing]
    exact (mem_line_diag0_iff _).mp ((mem_lineSubalgebra_iff (diagAtom 0) (diagAtom_isAtom 0) _).mpr hm)
  change (Matrix.trace (lineDiag0Mat (g.linearEquiv x.1) * lineDiag0Mat (g.linearEquiv y.1))).re =
    8 * tracePairing x.1 y.1
  rw [lineDiag0Mat_trace_mul_re _ _ (hdiag_coords x) (hdiag_coords y), g.map_tracePairing]

/-! ### Section 5.3: Unconditional State Transport and `proper_iff_special` -/

private def evalSubalgFactors (B : NativeJordanSubalgebra) : List ℝ → B.carrier → B.carrier
  | [], _ => ⟨albertUnit, B.unit_mem⟩
  | r :: rs, z =>
    let fac : B.carrier := z - r • ⟨albertUnit, B.unit_mem⟩
    let rest := evalSubalgFactors B rs z
    ⟨jordanMul fac.1 rest.1, B.product_mem _ fac.2 _ rest.2⟩

private theorem evalSubalgFactors_map_spec {B : NativeJordanSubalgebra} {d : ℕ}
    (ι : SuppliedHermitianEmbedding B d) (L : List ℝ) (z : B.carrier)
    (U : HermitianEmbeddingMatrix d) (μ : Fin d → ℝ)
    (hspec : ι.map z = U * Matrix.diagonal (fun i => (μ i : ℂ)) * U.conjTranspose)
    (hUU : U.conjTranspose * U = 1) (hUUt : U * U.conjTranspose = 1) :
    ι.map (evalSubalgFactors B L z) =
      U * Matrix.diagonal (fun i => ((L.map (fun r => μ i - r)).prod : ℂ)) * U.conjTranspose := by
  induction L with
  | nil =>
    simp only [evalSubalgFactors, List.map_nil, List.prod_nil, Complex.ofReal_one, Matrix.diagonal_one,
      Matrix.mul_one]
    rw [ι.unit]
    exact hUUt.symm
  | cons r rs ih =>
    dsimp only [evalSubalgFactors]
    have hfac : ι.map (z - r • ⟨albertUnit, B.unit_mem⟩) =
        U * Matrix.diagonal (fun i => ((μ i - r : ℝ) : ℂ)) * U.conjTranspose := by
      rw [map_sub, map_smul, ι.unit, hspec]
      have hr : r • (1 : HermitianEmbeddingMatrix d) =
          U * Matrix.diagonal (fun _ => (r : ℂ)) * U.conjTranspose := by
        have hdiag : Matrix.diagonal (fun _ : Fin d => (r : ℂ)) =
            (r : ℝ) • (1 : HermitianEmbeddingMatrix d) := by
          ext i j
          by_cases hij : i = j
          · subst hij; simp [Complex.real_smul]
          · simp [hij]
        rw [hdiag, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, Matrix.mul_one, hUUt]
      rw [hr]
      rw [← Matrix.sub_mul, ← Matrix.mul_sub]
      congr 1; congr 1
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [ι.jordan, hfac, ih]
    have hprod_mul : ∀ (α β : Fin d → ℝ),
        (U * Matrix.diagonal (fun i => (α i : ℂ)) * U.conjTranspose) *
          (U * Matrix.diagonal (fun i => (β i : ℂ)) * U.conjTranspose) =
        U * Matrix.diagonal (fun i => ((α i * β i : ℝ) : ℂ)) * U.conjTranspose := fun α β => by
      calc
        (U * Matrix.diagonal (fun i => (α i : ℂ)) * U.conjTranspose) *
            (U * Matrix.diagonal (fun i => (β i : ℂ)) * U.conjTranspose)
          = U * Matrix.diagonal (fun i => (α i : ℂ)) * (U.conjTranspose * U) *
              Matrix.diagonal (fun i => (β i : ℂ)) * U.conjTranspose := by
                simp only [Matrix.mul_assoc]
        _ = U * (Matrix.diagonal (fun i => (α i : ℂ)) *
              Matrix.diagonal (fun i => (β i : ℂ))) * U.conjTranspose := by
                rw [hUU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = U * Matrix.diagonal (fun i => ((α i * β i : ℝ) : ℂ)) * U.conjTranspose := by
              rw [Matrix.diagonal_mul_diagonal]
              congr 1; congr 1; ext i; push_cast; ring
    have hcomm : (fun i => ((((List.map (fun r => μ i - r) rs).prod * (μ i - r) : ℝ) : ℂ))) =
        (fun i => ((((μ i - r) * (List.map (fun r => μ i - r) rs).prod : ℝ) : ℂ))) := by
      ext i; push_cast; ring
    rw [hprod_mul, hprod_mul, hcomm]
    have h2 : ∀ M : HermitianEmbeddingMatrix d, (1 / 2 : ℝ) • (M + M) = M := fun M => by module
    rw [h2]
    simp only [List.map_cons, List.prod_cons]

private theorem wordAmplitude_cons {ι : Type*} {A : Type*} [Ring A] (P : ι → A)
    (a : Outcome ι) (ws : Word ι) :
    wordAmplitude P (a :: ws) = wordAmplitude P ws * algebraicOutcome P a := by
  have h : ∀ (l : Word ι) (x : A),
      List.foldl (fun acc b => algebraicOutcome P b * acc) (x * algebraicOutcome P a) l =
        List.foldl (fun acc b => algebraicOutcome P b * acc) x l * algebraicOutcome P a := by
    intro l
    induction l with
    | nil => intro x; rfl
    | cons b bs ih =>
      intro x
      simp only [List.foldl_cons, ← mul_assoc]
      exact ih (algebraicOutcome P b * x)
  simpa [wordAmplitude] using h ws 1

private theorem suppliedEmbedding_wordOperator_eq {B : NativeJordanSubalgebra} {d : ℕ}
    (ι : SuppliedHermitianEmbedding B d) {n : ℕ} (p : Fin n → Albert) (hp : ∀ i, p i ∈ B.carrier)
    (w : Word (Fin n)) :
    ∃ hw : nativeWordEffect p w ∈ B.carrier,
      ι.map ⟨nativeWordEffect p w, hw⟩ = wordOperator (fun i => ι.map ⟨p i, hp i⟩) w := by
  let P : Fin n → HermitianEmbeddingMatrix d := fun i => ι.map ⟨p i, hp i⟩
  induction w with
  | nil =>
    refine ⟨B.unit_mem, ?_⟩
    simp [nativeWordEffect, wordOperator, wordAmplitude, ι.unit]
  | cons a ws ih =>
    obtain ⟨hws, ih_eq⟩ := ih
    have haB : nativeOutcome p a ∈ B.carrier := by
      cases a with
      | mk i b =>
        cases b
        · exact B.carrier.sub_mem B.unit_mem (hp i)
        · exact hp i
    have hq_mem : quadraticMap (nativeOutcome p a) (nativeWordEffect p ws) ∈ B.carrier := by
      rw [quadraticMap, two_nsmul]
      exact B.carrier.sub_mem
        (B.carrier.add_mem
          (B.product_mem _ haB _ (B.product_mem _ haB _ hws))
          (B.product_mem _ haB _ (B.product_mem _ haB _ hws)))
        (B.product_mem _ (B.product_mem _ haB _ haB) _ hws)
    refine ⟨?_, ?_⟩
    · exact hq_mem
    · have ha_map : ι.map ⟨nativeOutcome p a, haB⟩ = algebraicOutcome P a := by
        cases a with
        | mk i b =>
          cases b
          · change ι.map (⟨albertUnit, B.unit_mem⟩ - ⟨p i, hp i⟩) = 1 - P i
            rw [map_sub, ι.unit]
          · rfl
      have hU_herm : star (algebraicOutcome P a) = algebraicOutcome P a := by
        rw [← ha_map, Matrix.star_eq_conjTranspose, (ι.hermitian _).eq]
      have hw_cons : wordAmplitude P (a :: ws) = wordAmplitude P ws * algebraicOutcome P a :=
        wordAmplitude_cons P a ws
      have hw_op : wordOperator P (a :: ws) =
          algebraicOutcome P a * wordOperator P ws * algebraicOutcome P a := by
        unfold wordOperator
        rw [hw_cons, star_mul, hU_herm]
        simp only [Matrix.mul_assoc]
      rw [hw_op]
      have hquad : ι.map ⟨quadraticMap (nativeOutcome p a) (nativeWordEffect p ws), hq_mem⟩ =
          algebraicOutcome P a * wordOperator P ws * algebraicOutcome P a := by
        let a' : B.carrier := ⟨nativeOutcome p a, haB⟩
        let w' : B.carrier := ⟨nativeWordEffect p ws, hws⟩
        let aw' : B.carrier := ⟨jordanMul a'.1 w'.1, B.product_mem _ haB _ hws⟩
        let aa' : B.carrier := ⟨jordanMul a'.1 a'.1, B.product_mem _ haB _ haB⟩
        have hj1 := ι.jordan a' aw'
        have hj2 := ι.jordan a' w'
        have hj3 := ι.jordan aa' w'
        have hj4 := ι.jordan a' a'
        have hsub : (⟨quadraticMap (nativeOutcome p a) (nativeWordEffect p ws), hq_mem⟩ : B.carrier) =
            2 • ⟨jordanMul a'.1 aw'.1, B.product_mem _ haB _ aw'.2⟩ -
              ⟨jordanMul aa'.1 w'.1, B.product_mem _ aa'.2 _ hws⟩ := rfl
        rw [hsub, map_sub, map_nsmul, hj1, hj2, hj3, hj4]
        have ha_eq : ι.map a' = algebraicOutcome P a := ha_map
        have hw_eq : ι.map w' = wordOperator P ws := ih_eq
        rw [ha_eq, hw_eq]
        set U := algebraicOutcome P a
        set Y := wordOperator P ws
        simp only [two_nsmul, smul_add, smul_smul, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
          mul_add, add_mul, Matrix.mul_assoc]
        module
      exact hquad

private theorem tracePairing_sum_right {ι : Type*} (s : Finset ι) (x : Albert) (f : ι → Albert) :
    tracePairing x (∑ i ∈ s, f i) = ∑ i ∈ s, tracePairing x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using tracePairing_smul_right (0 : ℝ) x 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, tracePairing_add_right, ih]

theorem suppliedEmbedding_scaled_state_transport (B : NativeJordanSubalgebra) (d : ℕ)
    (ι : SuppliedHermitianEmbedding B d) (c : ℝ) (hc : 0 < c)
    (htr : ∀ x y : B.carrier,
      (Matrix.trace (ι.map x * ι.map y)).re = c * tracePairing x.1 y.1)
    (ρ : Albert) (hρ : IsDensity ρ) :
    ∃ σ : HermitianEmbeddingMatrix d, IsEmbeddingDensity d σ ∧
      ∀ (n : ℕ) (p : Fin n → Albert) (hp : ∀ i, p i ∈ B.carrier) (w : Word (Fin n)),
        (Matrix.trace (σ * wordOperator (fun i => ι.map ⟨p i, hp i⟩) w)).re =
          nativeWordProbability p ρ w := by
  have : Module.Finite ℝ Octonion :=
    inferInstanceAs (FiniteDimensional ℝ (Quaternion ℝ × Quaternion ℝ))
  have : Module.Finite ℝ Albert :=
    inferInstanceAs (FiniteDimensional ℝ ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
  let r : ℕ := Module.finrank ℝ B.carrier
  let b : Module.Basis (Fin r) ℝ B.carrier := Module.finBasis ℝ B.carrier
  let T : B.carrier →ₗ[ℝ] (Fin r → ℝ) :=
    { toFun := fun x i => tracePairing x.1 (b i).1
      map_add' := fun x y => by ext i; exact tracePairing_add_left _ _ _
      map_smul' := fun s x => by ext i; exact tracePairing_smul_left _ _ _ }
  have hcoe_sum : ∀ (f : Fin r → B.carrier), (∑ i : Fin r, f i).1 = ∑ i : Fin r, (f i).1 := fun f => by
    classical
    have hs : ∀ s : Finset (Fin r), (∑ i ∈ s, f i).1 = ∑ i ∈ s, (f i).1 := fun s => by
      induction s using Finset.induction_on with
      | empty => rfl
      | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha]; exact congrArg (_ + ·) ih
    exact hs Finset.univ
  have hT_inj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hxi : ∀ i : Fin r, tracePairing x.1 (b i).1 = 0 := fun i => congrFun hx i
    have hx_self : tracePairing x.1 x.1 = 0 := by
      have hrepr := (b.sum_repr x).symm
      calc
        tracePairing x.1 x.1
          = tracePairing x.1 ((∑ i : Fin r, b.repr x i • b i).1) := by rw [← hrepr]
        _ = ∑ i : Fin r, b.repr x i * tracePairing x.1 (b i).1 := by
              rw [hcoe_sum, tracePairing_sum_right]
              refine Finset.sum_congr rfl fun i _ => ?_
              exact tracePairing_smul_right (b.repr x i) x.1 (b i).1
        _ = 0 := Finset.sum_eq_zero fun i _ => by rw [hxi i, mul_zero]
    exact Subtype.ext ((tracePairing_self_eq_zero x.1).mp hx_self)
  have hfin_eq : Module.finrank ℝ B.carrier = Module.finrank ℝ (Fin r → ℝ) := by
    rw [Module.finrank_fin_fun]
  have hT_surj : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin_eq).mp hT_inj
  obtain ⟨z, hz_coords⟩ := hT_surj (fun i => tracePairing ρ (b i).1)
  have hzi : ∀ i : Fin r, tracePairing z.1 (b i).1 = tracePairing ρ (b i).1 :=
    fun i => congrFun hz_coords i
  have hz_pair : ∀ y : B.carrier, tracePairing z.1 y.1 = tracePairing ρ y.1 := by
    intro y
    have hrepr := (b.sum_repr y).symm
    calc
      tracePairing z.1 y.1
        = tracePairing z.1 ((∑ i : Fin r, b.repr y i • b i).1) := by rw [← hrepr]
      _ = ∑ i : Fin r, b.repr y i * tracePairing z.1 (b i).1 := by
            rw [hcoe_sum, tracePairing_sum_right]
            refine Finset.sum_congr rfl fun i _ => ?_
            exact tracePairing_smul_right (b.repr y i) z.1 (b i).1
      _ = ∑ i : Fin r, b.repr y i * tracePairing ρ (b i).1 := by
            refine Finset.sum_congr rfl fun i _ => by rw [hzi i]
      _ = tracePairing ρ ((∑ i : Fin r, b.repr y i • b i).1) := by
            rw [hcoe_sum, tracePairing_sum_right]
            refine Finset.sum_congr rfl fun i _ => (tracePairing_smul_right (b.repr y i) ρ (b i).1).symm
      _ = tracePairing ρ y.1 := by rw [← hrepr]
  let A : HermitianEmbeddingMatrix d := ι.map z
  have hA_herm : A.IsHermitian := ι.hermitian z
  let U : HermitianEmbeddingMatrix d := hA_herm.eigenvectorUnitary
  let μ : Fin d → ℝ := hA_herm.eigenvalues
  have hUU : U.conjTranspose * U = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self hA_herm.eigenvectorUnitary
  have hUUt : U * U.conjTranspose = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using
      Unitary.coe_mul_star_self hA_herm.eigenvectorUnitary
  have hspec : A = U * Matrix.diagonal (fun i => (μ i : ℂ)) * U.conjTranspose := by
    simpa [U, μ, Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.star_eq_conjTranspose] using
      hA_herm.spectral_theorem
  have hμ_nonneg : ∀ k : Fin d, 0 ≤ μ k := by
    intro k
    let L : List ℝ := (List.finRange d).filterMap (fun j => if μ j = μ k then none else some (μ j))
    let yF := evalSubalgFactors B L z
    let ySq : B.carrier := ⟨jordanMul yF.1 yF.1, B.product_mem _ yF.2 _ yF.2⟩
    have hyF_spec := evalSubalgFactors_map_spec ι L z U μ hspec hUU hUUt
    let val : Fin d → ℝ := fun i => (L.map (fun r0 => μ i - r0)).prod
    have hySq_spec : ι.map ySq =
        U * Matrix.diagonal (fun i => ((val i ^ 2 : ℝ) : ℂ)) * U.conjTranspose := by
      rw [ι.jordan, hyF_spec]
      calc
        (1 / 2 : ℝ) •
            ((U * Matrix.diagonal (fun i => (val i : ℂ)) * U.conjTranspose) *
                (U * Matrix.diagonal (fun i => (val i : ℂ)) * U.conjTranspose) +
              (U * Matrix.diagonal (fun i => (val i : ℂ)) * U.conjTranspose) *
                (U * Matrix.diagonal (fun i => (val i : ℂ)) * U.conjTranspose))
          = (U * Matrix.diagonal (fun i => (val i : ℂ)) * (U.conjTranspose * U) *
              Matrix.diagonal (fun i => (val i : ℂ)) * U.conjTranspose) := by
                have h2 : ∀ M : HermitianEmbeddingMatrix d, (1 / 2 : ℝ) • (M + M) = M := fun M => by module
                rw [h2]; simp only [Matrix.mul_assoc]
        _ = U * Matrix.diagonal (fun i => ((val i ^ 2 : ℝ) : ℂ)) * U.conjTranspose := by
              have hd2 : Matrix.diagonal (fun i => (val i : ℂ)) * Matrix.diagonal (fun i => (val i : ℂ)) =
                  Matrix.diagonal (fun i => ((val i ^ 2 : ℝ) : ℂ)) := by
                rw [Matrix.diagonal_mul_diagonal]
                congr 1; ext i; push_cast; ring
              rw [hUU, Matrix.mul_one, Matrix.mul_assoc U (Matrix.diagonal _) (Matrix.diagonal _), hd2]
    have hnonneg_pair : 0 ≤ (Matrix.trace (A * ι.map ySq)).re := by
      rw [htr z ySq, hz_pair ySq]
      exact mul_nonneg hc.le (tracePairing_positive_nonnegative ρ ySq.1 hρ.1 ⟨yF.1, rfl⟩)
    have htr_eval : (Matrix.trace (A * ι.map ySq)).re = ∑ i : Fin d, μ i * val i ^ 2 := by
      have hmul : A * ι.map ySq =
          U * Matrix.diagonal (fun i => ((μ i * val i ^ 2 : ℝ) : ℂ)) * U.conjTranspose := by
        rw [hspec, hySq_spec]
        calc
          (U * Matrix.diagonal (fun i => (μ i : ℂ)) * U.conjTranspose) *
              (U * Matrix.diagonal (fun i => ((val i ^ 2 : ℝ) : ℂ)) * U.conjTranspose)
            = U * Matrix.diagonal (fun i => (μ i : ℂ)) * (U.conjTranspose * U) *
                Matrix.diagonal (fun i => ((val i ^ 2 : ℝ) : ℂ)) * U.conjTranspose := by
                  simp only [Matrix.mul_assoc]
          _ = U * (Matrix.diagonal (fun i => (μ i : ℂ)) *
                Matrix.diagonal (fun i => ((val i ^ 2 : ℝ) : ℂ))) * U.conjTranspose := by
                  rw [hUU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
          _ = U * Matrix.diagonal (fun i => ((μ i * val i ^ 2 : ℝ) : ℂ)) * U.conjTranspose := by
                rw [Matrix.diagonal_mul_diagonal]
                congr 1; congr 1; ext i; push_cast; ring
      rw [hmul, Matrix.trace_mul_cycle, hUU, Matrix.one_mul, Matrix.trace_diagonal, Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.ofReal_re]
    have hzero_other : ∀ i : Fin d, μ i ≠ μ k → val i = 0 := by
      intro i hne
      dsimp only [val]
      rw [List.prod_eq_zero_iff, List.mem_map]
      refine ⟨μ i, ?_, sub_self _⟩
      rw [List.mem_filterMap]
      exact ⟨i, List.mem_finRange i, by simp [hne]⟩
    have hprod_eq : ∀ i : Fin d, μ i * val i ^ 2 = μ k * val i ^ 2 := fun i => by
      by_cases heq : μ i = μ k
      · rw [heq]
      · rw [hzero_other i heq]; ring
    have hvalk_ne : val k ≠ 0 := by
      dsimp only [val]
      apply List.prod_ne_zero
      intro h0
      rw [List.mem_map] at h0
      rcases h0 with ⟨r0, hr0, hr_eq⟩
      rw [List.mem_filterMap] at hr0
      rcases hr0 with ⟨j, _hj, hif⟩
      by_cases hjk : μ j = μ k
      · simp [hjk] at hif
      · simp [hjk] at hif; subst r0; exact hjk (sub_eq_zero.mp hr_eq).symm
    have hsum_pos : 0 < ∑ i : Fin d, val i ^ 2 := by
      have hk_pos : 0 < val k ^ 2 := sq_pos_iff.mpr hvalk_ne
      have hle : val k ^ 2 ≤ ∑ i : Fin d, val i ^ 2 :=
        Finset.single_le_sum (fun i _ => sq_nonneg (val i)) (Finset.mem_univ k)
      linarith
    have hfinal : 0 ≤ μ k * ∑ i : Fin d, val i ^ 2 := by
      rw [Finset.mul_sum]
      calc
        0 ≤ (Matrix.trace (A * ι.map ySq)).re := hnonneg_pair
        _ = ∑ i : Fin d, μ i * val i ^ 2 := htr_eval
        _ = ∑ i : Fin d, μ k * val i ^ 2 := Finset.sum_congr rfl fun i _ => hprod_eq i
    exact nonneg_of_mul_nonneg_left hfinal hsum_pos
  have hA_psd : A.PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨hA_herm, fun v => ?_⟩
    let D := Matrix.diagonal (fun i => (Real.sqrt (μ i) : ℂ))
    have hD2 : D * D = Matrix.diagonal (fun i => (μ i : ℂ)) := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1; ext i; exact_mod_cast Real.mul_self_sqrt (hμ_nonneg i)
    have hD_herm : D.conjTranspose = D := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp [D]
      · simp [D, hij, Ne.symm hij]
    have hAA : A = (U * D) * (U * D).conjTranspose := by
      rw [Matrix.conjTranspose_mul, hD_herm, hspec, ← hD2]
      simp only [Matrix.mul_assoc]
    rw [hAA]
    let wv := Matrix.mulVec (U * D).conjTranspose v
    have hval : star v ⬝ᵥ Matrix.mulVec ((U * D) * (U * D).conjTranspose) v =
        ∑ i : Fin d, star (wv i) * wv i := by
      have hw : star wv = Matrix.vecMul (star v) (U * D) := by
        dsimp only [wv]; rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← hw]
      rfl
    rw [hval]
    refine Finset.sum_nonneg fun i _ => ?_
    have hz : star (wv i) * wv i = (((wv i).re ^ 2 + (wv i).im ^ 2 : ℝ) : ℂ) := by
      apply Complex.ext
      · simp [sq]
      · simp
        rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, Complex.ofReal_im, Complex.ofReal_im]
        ring
    rw [hz]
    exact_mod_cast add_nonneg (sq_nonneg (wv i).re) (sq_nonneg (wv i).im)
  let σ : HermitianEmbeddingMatrix d := (1 / c) • A
  have hσ_psd : σ.PosSemidef := hA_psd.smul (div_nonneg zero_le_one hc.le)
  have hσ_tr : Matrix.trace σ = 1 := by
    have htr_re : (Matrix.trace A).re = c := by
      have h1 := htr z ⟨albertUnit, B.unit_mem⟩
      rw [ι.unit, Matrix.mul_one, hz_pair, tracePairing_unit_right, hρ.2, mul_one] at h1
      exact h1
    have htr_im : (Matrix.trace A).im = 0 := by
      rw [Matrix.trace]
      have him_sum : ∀ s : Finset (Fin d),
          (∑ i ∈ s, A.diag i).im = ∑ i ∈ s, (A i i).im := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp
        | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Complex.add_im, ih]; rfl
      rw [him_sum Finset.univ]
      refine Finset.sum_eq_zero fun i _ => ?_
      have hi := congrFun (congrFun hA_herm.eq i) i
      have him := congrArg Complex.im hi
      simp [Matrix.conjTranspose_apply] at him
      linarith
    have htr_A : Matrix.trace A = (c : ℂ) := Complex.ext htr_re htr_im
    dsimp only [σ]
    rw [Matrix.trace_smul, htr_A, Complex.real_smul, ← Complex.ofReal_mul,
      one_div_mul_cancel hc.ne', Complex.ofReal_one]
  refine ⟨σ, ⟨hσ_psd, hσ_tr⟩, fun n p hp w => ?_⟩
  obtain ⟨hw_mem, hw_eq⟩ := suppliedEmbedding_wordOperator_eq ι p hp w
  rw [← hw_eq]
  dsimp only [σ, A]
  rw [Matrix.smul_mul, Matrix.trace_smul, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    htr z ⟨nativeWordEffect p w, hw_mem⟩, hz_pair]
  have hne : (1 / c) * (c * tracePairing ρ (nativeWordEffect p w)) =
      tracePairing ρ (nativeWordEffect p w) := by
    field_simp [hc.ne']
  rw [hne, ← nativeWordProbability_eq_pairing]

def IsSpecialSubalgebra (B : NativeJordanSubalgebra) : Prop :=
  ∃ (d : ℕ), 0 < d ∧ Nonempty (SuppliedHermitianEmbedding B d)

private def restrictEmbedding {B₁ B₂ : NativeJordanSubalgebra} (hle : B₁.carrier ≤ B₂.carrier)
    {d : ℕ} (ι : SuppliedHermitianEmbedding B₂ d) : SuppliedHermitianEmbedding B₁ d where
  map :=
    { toFun := fun x => ι.map ⟨x.1, hle x.2⟩
      map_add' := fun x y => ι.map.map_add ⟨x.1, hle x.2⟩ ⟨y.1, hle y.2⟩
      map_smul' := fun r x => ι.map.map_smul r ⟨x.1, hle x.2⟩ }
  injective := fun x y h => by
    change ι.map ⟨x.1, hle x.2⟩ = ι.map ⟨y.1, hle y.2⟩ at h
    exact Subtype.ext (congrArg (Subtype.val : B₂.carrier → Albert) (ι.injective h))
  hermitian := fun x => ι.hermitian ⟨x.1, hle x.2⟩
  unit := ι.unit
  jordan := fun x y => ι.jordan ⟨x.1, hle x.2⟩ ⟨y.1, hle y.2⟩

theorem proper_iff_special (B : NativeJordanSubalgebra) :
    B ≠ ⊤ ↔ IsSpecialSubalgebra B := by
  constructor
  · intro hne
    have hlt : B.carrier < (H3Subalgebra .O).carrier := by
      rw [H3Subalgebra_O_eq_top]
      refine lt_of_le_of_ne le_top fun heq => hne ?_
      cases B
      congr
    rcases lem_five_sub .O B hlt with ⟨q, hq, _, hline⟩ | ⟨Q, hQ⟩
    · exact ⟨24, by norm_num, ⟨restrictEmbedding hline (lineCliffordEmbed q hq)⟩⟩
    · exact ⟨6, by norm_num, ⟨restrictEmbedding hQ (symplecticQuatEmbed Q)⟩⟩
  · rintro ⟨d, _hd, ⟨ι⟩⟩ htop
    have hmem : ∀ x : Albert, x ∈ B.carrier := fun x => by rw [htop]; trivial
    let η : Albert →ₗ[ℝ] HermitianEmbeddingMatrix d :=
      { toFun := fun x => ι.map ⟨x, hmem x⟩
        map_add' := fun x y => ι.map.map_add ⟨x, hmem x⟩ ⟨y, hmem y⟩
        map_smul' := fun r x => ι.map.map_smul r ⟨x, hmem x⟩ }
    have hη : IsJordanHom η := fun x y => ι.jordan ⟨x, hmem x⟩ ⟨y, hmem y⟩
    have hzero : η = 0 := albertJordanHom_eq_zero (HermitianEmbeddingMatrix d) η hη
    have hunit0 : ι.map ⟨albertUnit, B.unit_mem⟩ = 0 := by
      change η albertUnit = 0
      rw [hzero]; rfl
    have hunit_eq0 : (⟨albertUnit, B.unit_mem⟩ : B.carrier) = 0 :=
      ι.injective (by rw [hunit0, map_zero])
    have hau : albertUnit = 0 := congrArg Subtype.val hunit_eq0
    have htr := congrArg albertTrace hau
    have h3 : albertTrace albertUnit = 3 := by simp [albertTrace, albertUnit]
    have h0 : albertTrace 0 = 0 := by simp [albertTrace, albert_zero_fst]
    rw [h3, h0] at htr
    norm_num at htr

end AlbertSequential
