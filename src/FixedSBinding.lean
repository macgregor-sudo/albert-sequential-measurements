module

public import Defs
public import DiagPeirceAnchor
public import NativePeircePropagation
public import Interfaces.AlgebraicReconstruction
public import JordanHomTransport
public import JordanTripleTransport
public import NativeAlbertLaws
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Finite-`S` Native Corner Binding

Proves the literal rational `fixedS` configuration (`atomA, atomB, atomC, atomD`
in upper slots `[01, 02, 12]`), all four `IsAtom` identities, all 12 ordered
distinct R1 equations (10 via the two explicit quaternion dyad embeddings
`quatEmbed1`, `quatEmbed2` and 2 via the explicit 6-slot `(C, D)` contraction),
exact `nativeOverlaps` and `nativeTriangles` values and symmetries across all
64 `Fin 4` triples, all 4 native R2 equations, all 3 native R3 equations in
exact `nativeCornerQ` order `123, 231, 312`, target-side `fixedS_cornerRelations`,
and the exact denominator-free discriminant `fixedS_discriminant = 1 / 104976`.
-/

@[expose] public section
noncomputable section

namespace AlbertSequential

/-! ## Section 1: Literal Rational Configuration `fixedS` -/

def atomA : Albert := diagAtom 0

def atomC : Albert :=
  (1 / 3 : ℝ) • (![1, 1, 1], ![-octI, octonionScalar 1, octI])

def atomD : Albert :=
  (1 / 3 : ℝ) • (![1, 1, 1], ![-octJ, -octL, -octonionMul octJ octL])

def fixedS : Fin 4 → Albert := ![atomA, atomB, atomC, atomD]

theorem fixedS_zero : fixedS 0 = diagAtom 0 := rfl
theorem fixedS_one : fixedS 1 = atomB := rfl
theorem fixedS_two : fixedS 2 = atomC := rfl
theorem fixedS_three : fixedS 3 = atomD := rfl

/-! ## Section 2: Component Accessors & Quaternion Dyad Identifications -/

@[local simp] private theorem q_smul_re (r : ℝ) (q : Quaternion ℝ) : (r • q).re = r * q.re := rfl
@[local simp] private theorem q_smul_imI (r : ℝ) (q : Quaternion ℝ) : (r • q).imI = r * q.imI := rfl
@[local simp] private theorem q_smul_imJ (r : ℝ) (q : Quaternion ℝ) : (r • q).imJ = r * q.imJ := rfl
@[local simp] private theorem q_smul_imK (r : ℝ) (q : Quaternion ℝ) : (r • q).imK = r * q.imK := rfl

@[local simp] private theorem oct_zero_fst : (0 : Octonion).1 = 0 := rfl
@[local simp] private theorem oct_zero_snd : (0 : Octonion).2 = 0 := rfl
@[local simp] private theorem oct_smul_fst (r : ℝ) (x : Octonion) : (r • x).1 = r • x.1 := rfl
@[local simp] private theorem oct_smul_snd (r : ℝ) (x : Octonion) : (r • x).2 = r • x.2 := rfl
@[local simp] private theorem oct_add_fst (x y : Octonion) : (x + y).1 = x.1 + y.1 := rfl
@[local simp] private theorem oct_add_snd (x y : Octonion) : (x + y).2 = x.2 + y.2 := rfl
@[local simp] private theorem oct_sub_fst (x y : Octonion) : (x - y).1 = x.1 - y.1 := rfl
@[local simp] private theorem oct_sub_snd (x y : Octonion) : (x - y).2 = x.2 - y.2 := rfl
@[local simp] private theorem oct_neg_fst (x : Octonion) : (-x).1 = -x.1 := rfl
@[local simp] private theorem oct_neg_snd (x : Octonion) : (-x).2 = -x.2 := rfl
@[local simp] private theorem oct_mul_fst (x y : Octonion) :
    (octonionMul x y).1 = x.1 * y.1 - star y.2 * x.2 := rfl
@[local simp] private theorem oct_mul_snd (x y : Octonion) :
    (octonionMul x y).2 = y.2 * x.1 + x.2 * star y.1 := rfl
@[local simp] private theorem oct_conj_fst (x : Octonion) : (octonionConj x).1 = star x.1 := rfl
@[local simp] private theorem oct_conj_snd (x : Octonion) : (octonionConj x).2 = -x.2 := rfl
@[local simp] private theorem oct_scalar_fst (r : ℝ) : (octonionScalar r).1 = ⟨r, 0, 0, 0⟩ := rfl
@[local simp] private theorem oct_scalar_snd (r : ℝ) : (octonionScalar r).2 = 0 := rfl
@[local simp] private theorem octReal_eq (x : Octonion) : octonionReal x = x.1.re := rfl

@[local simp] private theorem octI_fst : octI.1 = ⟨0, 1, 0, 0⟩ := rfl
@[local simp] private theorem octI_snd : octI.2 = 0 := rfl
@[local simp] private theorem octJ_fst : octJ.1 = ⟨0, 0, 1, 0⟩ := rfl
@[local simp] private theorem octJ_snd : octJ.2 = 0 := rfl
@[local simp] private theorem octK_fst : octK.1 = ⟨0, 0, 0, 1⟩ := rfl
@[local simp] private theorem octK_snd : octK.2 = 0 := rfl
@[local simp] private theorem octL_fst : octL.1 = 0 := rfl
@[local simp] private theorem octL_snd : octL.2 = ⟨1, 0, 0, 0⟩ := rfl
@[local simp] private theorem octS_fst : octS.1 = 0 := rfl
@[local simp] private theorem octS_snd : octS.2 = ⟨0, 1, 0, 0⟩ := rfl
@[local simp] private theorem octR_fst : octR.1 = 0 := rfl
@[local simp] private theorem octR_snd : octR.2 = ⟨0, 0, 1, 0⟩ := rfl
@[local simp] private theorem octT_fst : octT.1 = 0 := rfl
@[local simp] private theorem octT_snd : octT.2 = ⟨0, 0, 0, 1⟩ := rfl

@[local simp] private theorem alb_smul_fst (r : ℝ) (x : Albert) (i : Fin 3) : (r • x).1 i = r * x.1 i := rfl
@[local simp] private theorem alb_smul_snd (r : ℝ) (x : Albert) (i : Fin 3) : (r • x).2 i = r • x.2 i := rfl
@[local simp] private theorem alb_add_fst (x y : Albert) (i : Fin 3) : (x + y).1 i = x.1 i + y.1 i := rfl
@[local simp] private theorem alb_add_snd (x y : Albert) (i : Fin 3) : (x + y).2 i = x.2 i + y.2 i := rfl
@[local simp] private theorem alb_sub_fst (x y : Albert) (i : Fin 3) : (x - y).1 i = x.1 i - y.1 i := rfl
@[local simp] private theorem alb_sub_snd (x y : Albert) (i : Fin 3) : (x - y).2 i = x.2 i - y.2 i := rfl

private theorem atomB_d0 : atomB.1 0 = 1 / 2 := by
  change (1 / 2 : ℝ) * 1 = 1 / 2; norm_num
private theorem atomB_d1 : atomB.1 1 = 1 / 2 := by
  change (1 / 2 : ℝ) * 1 = 1 / 2; norm_num
private theorem atomB_d2 : atomB.1 2 = 0 := by
  change (1 / 2 : ℝ) * 0 = 0; norm_num
private theorem atomB_u0 : atomB.2 0 = (1 / 2 : ℝ) • octonionScalar 1 := rfl
private theorem atomB_u1 : atomB.2 1 = 0 := by
  change (1 / 2 : ℝ) • (0 : Octonion) = 0; exact smul_zero _
private theorem atomB_u2 : atomB.2 2 = 0 := by
  change (1 / 2 : ℝ) • (0 : Octonion) = 0; exact smul_zero _

private theorem atomC_d0 : atomC.1 0 = 1 / 3 := by
  change (1 / 3 : ℝ) * 1 = 1 / 3; norm_num
private theorem atomC_d1 : atomC.1 1 = 1 / 3 := by
  change (1 / 3 : ℝ) * 1 = 1 / 3; norm_num
private theorem atomC_d2 : atomC.1 2 = 1 / 3 := by
  change (1 / 3 : ℝ) * 1 = 1 / 3; norm_num
private theorem atomC_u0 : atomC.2 0 = (1 / 3 : ℝ) • (-octI) := rfl
private theorem atomC_u1 : atomC.2 1 = (1 / 3 : ℝ) • octonionScalar 1 := rfl
private theorem atomC_u2 : atomC.2 2 = (1 / 3 : ℝ) • octI := rfl

private theorem atomD_d0 : atomD.1 0 = 1 / 3 := by
  change (1 / 3 : ℝ) * 1 = 1 / 3; norm_num
private theorem atomD_d1 : atomD.1 1 = 1 / 3 := by
  change (1 / 3 : ℝ) * 1 = 1 / 3; norm_num
private theorem atomD_d2 : atomD.1 2 = 1 / 3 := by
  change (1 / 3 : ℝ) * 1 = 1 / 3; norm_num
private theorem atomD_u0 : atomD.2 0 = (1 / 3 : ℝ) • (-octJ) := rfl
private theorem atomD_u1 : atomD.2 1 = (1 / 3 : ℝ) • (-octL) := rfl
private theorem atomD_u2 : atomD.2 2 = (1 / 3 : ℝ) • (-octR) := by
  change (1 / 3 : ℝ) • (-octonionMul octJ octL) = _; rw [octR_eq_mul]

private theorem quatDyad_d (ι : Quaternion ℝ →ₗ[ℝ] Octonion)
    (u : Fin 3 → Quaternion ℝ) (n : ℝ) (i : Fin 3) :
    (quatDyad ι u n).1 i = (1 / n : ℝ) * (u i * star (u i)).re := rfl
private theorem quatDyad_u0 (ι : Quaternion ℝ →ₗ[ℝ] Octonion)
    (u : Fin 3 → Quaternion ℝ) (n : ℝ) :
    (quatDyad ι u n).2 0 = (1 / n : ℝ) • ι (u 0 * star (u 1)) := rfl
private theorem quatDyad_u1 (ι : Quaternion ℝ →ₗ[ℝ] Octonion)
    (u : Fin 3 → Quaternion ℝ) (n : ℝ) :
    (quatDyad ι u n).2 1 = (1 / n : ℝ) • ι (u 0 * star (u 2)) := rfl
private theorem quatDyad_u2 (ι : Quaternion ℝ →ₗ[ℝ] Octonion)
    (u : Fin 3 → Quaternion ℝ) (n : ℝ) :
    (quatDyad ι u n).2 2 = (1 / n : ℝ) • ι (u 1 * star (u 2)) := rfl

private theorem albert_ext {x y : Albert}
    (h0 : x.1 0 = y.1 0) (h1 : x.1 1 = y.1 1) (h2 : x.1 2 = y.1 2)
    (u0 : x.2 0 = y.2 0) (u1 : x.2 1 = y.2 1) (u2 : x.2 2 = y.2 2) : x = y := by
  apply Prod.ext <;> funext idx <;> fin_cases idx
  · exact h0
  · exact h1
  · exact h2
  · exact u0
  · exact u1
  · exact u2

private theorem octonion_ext {x y : Octonion}
    (h1 : x.1.re = y.1.re) (h2 : x.1.imI = y.1.imI)
    (h3 : x.1.imJ = y.1.imJ) (h4 : x.1.imK = y.1.imK)
    (h5 : x.2.re = y.2.re) (h6 : x.2.imI = y.2.imI)
    (h7 : x.2.imJ = y.2.imJ) (h8 : x.2.imK = y.2.imK) : x = y := by
  apply Prod.ext <;> apply Quaternion.ext <;> assumption

private def qI : Quaternion ℝ := ⟨0, 1, 0, 0⟩
private def qJ : Quaternion ℝ := ⟨0, 0, 1, 0⟩

private def qVecA : Fin 3 → Quaternion ℝ := ![1, 0, 0]
private def qVecB : Fin 3 → Quaternion ℝ := ![1, 1, 0]
private def qVecC : Fin 3 → Quaternion ℝ := ![1, qI, 1]
private def qVecD : Fin 3 → Quaternion ℝ := ![1, qI, qJ]

private theorem qVecA_normSq : ∑ i : Fin 3, quatNormSq (qVecA i) = 1 := by
  simp [Fin.sum_univ_three, quatNormSq, qVecA]

private theorem qVecB_normSq : ∑ i : Fin 3, quatNormSq (qVecB i) = 2 := by
  simp [Fin.sum_univ_three, quatNormSq, qVecB]
  norm_num

private theorem qVecC_normSq : ∑ i : Fin 3, quatNormSq (qVecC i) = 3 := by
  simp [Fin.sum_univ_three, quatNormSq, qVecC, qI]
  norm_num

private theorem qVecD_normSq : ∑ i : Fin 3, quatNormSq (qVecD i) = 3 := by
  simp [Fin.sum_univ_three, quatNormSq, qVecD, qI, qJ]
  norm_num

private theorem atomA_eq_quatDyad (ι : Quaternion ℝ →ₗ[ℝ] Octonion) :
    atomA = quatDyad ι qVecA 1 := by
  apply albert_ext <;> simp [atomA, diagAtom, quatDyad, qVecA]

private theorem ite_of_pos {α : Type*} {p : Prop} [Decidable p] {a b : α} (h : p) :
    (if p then a else b) = a := by simp [h]

private theorem ite_of_neg {α : Type*} {p : Prop} [Decidable p] {a b : α} (h : ¬ p) :
    (if p then a else b) = b := by simp [h]

private theorem atomB_eq_quatDyad (ι : Quaternion ℝ →ₗ[ℝ] Octonion)
    (hι : IsQuatEmbedding ι) :
    atomB = quatDyad ι qVecB 2 := by
  apply albert_ext
  · rw [atomB_d0, quatDyad_d]; simp [qVecB]
  · rw [atomB_d1, quatDyad_d]; simp [qVecB]
  · rw [atomB_d2, quatDyad_d]; simp [qVecB]
  · rw [atomB_u0, quatDyad_u0]; simp [qVecB, hι.map_one]
  · rw [atomB_u1, quatDyad_u1]; simp [qVecB]
  · rw [atomB_u2, quatDyad_u2]; simp [qVecB]

private theorem atomC_eq_quatDyad1 :
    atomC = quatDyad quatEmbed1 qVecC 3 := by
  apply albert_ext
  · rw [atomC_d0, quatDyad_d]; simp [qVecC]
  · rw [atomC_d1, quatDyad_d]; simp [qVecC, qI]
  · rw [atomC_d2, quatDyad_d]; simp [qVecC]
  · rw [atomC_u0, quatDyad_u0]; congr 1; apply octonion_ext <;> simp [qVecC, qI, quatEmbed1_apply]
  · rw [atomC_u1, quatDyad_u1]; congr 1; apply octonion_ext <;> simp [qVecC, quatEmbed1_apply]
  · rw [atomC_u2, quatDyad_u2]; congr 1; apply octonion_ext <;> simp [qVecC, qI, quatEmbed1_apply]

private theorem atomD_eq_quatDyad2 :
    atomD = quatDyad quatEmbed2 qVecD 3 := by
  apply albert_ext
  · rw [atomD_d0, quatDyad_d]; simp [qVecD]
  · rw [atomD_d1, quatDyad_d]; simp [qVecD, qI]
  · rw [atomD_d2, quatDyad_d]; simp [qVecD, qJ]
  · rw [atomD_u0, quatDyad_u0]; congr 1; apply octonion_ext <;> simp [qVecD, qI, quatEmbed2_apply]
  · rw [atomD_u1, quatDyad_u1]; congr 1; apply octonion_ext <;> simp [qVecD, qJ, quatEmbed2_apply]
  · rw [atomD_u2, quatDyad_u2]; congr 1; apply octonion_ext <;> simp [qVecD, qI, qJ, quatEmbed2_apply]

theorem fixedS_isAtom (a : Fin 4) : IsAtom (fixedS a) := by
  fin_cases a
  · exact diagAtom_isAtom 0
  · change IsAtom atomB
    rw [atomB_eq_quatDyad quatEmbed1 quatEmbed1_isQuatEmbedding]
    exact quatDyad_isAtom quatEmbed1 quatEmbed1_isQuatEmbedding qVecB 2 (by norm_num) qVecB_normSq
  · change IsAtom atomC
    rw [atomC_eq_quatDyad1]
    exact quatDyad_isAtom quatEmbed1 quatEmbed1_isQuatEmbedding qVecC 3 (by norm_num) qVecC_normSq
  · change IsAtom atomD
    rw [atomD_eq_quatDyad2]
    exact quatDyad_isAtom quatEmbed2 quatEmbed2_isQuatEmbedding qVecD 3 (by norm_num) qVecD_normSq

/-! ## Section 3: Ten Easy R1 Equations via Quaternion Subalgebras -/

private theorem quatDyad_R1_eval
    (ι : Quaternion ℝ →ₗ[ℝ] Octonion) (hι : IsQuatEmbedding ι)
    (u v : Fin 3 → Quaternion ℝ) (nu nv c : ℝ)
    (hnu : nu ≠ 0) (hu : ∑ i : Fin 3, quatNormSq (u i) = nu)
    (hc : quatNormSq (∑ i : Fin 3, star (u i) * v i) / (nu * nv) = c) :
    quadraticMap (quatDyad ι u nu) (quatDyad ι v nv) = c • quatDyad ι u nu := by
  rw [quadraticMap_quatDyad ι hι u v nu nv hnu hu, hc]

private theorem quadraticMap_atomA_atomB :
    quadraticMap atomA atomB = (1 / 2 : ℝ) • atomA := by
  rw [atomA_eq_quatDyad quatEmbed1, atomB_eq_quatDyad quatEmbed1 quatEmbed1_isQuatEmbedding]
  exact quatDyad_R1_eval quatEmbed1 quatEmbed1_isQuatEmbedding qVecA qVecB 1 2 (1 / 2)
    (by norm_num) qVecA_normSq (by
      simp [Fin.sum_univ_three, quatNormSq, qVecA, qVecB])

private theorem quadraticMap_atomB_atomA :
    quadraticMap atomB atomA = (1 / 2 : ℝ) • atomB := by
  rw [atomB_eq_quatDyad quatEmbed1 quatEmbed1_isQuatEmbedding, atomA_eq_quatDyad quatEmbed1]
  exact quatDyad_R1_eval quatEmbed1 quatEmbed1_isQuatEmbedding qVecB qVecA 2 1 (1 / 2)
    (by norm_num) qVecB_normSq (by
      simp [Fin.sum_univ_three, quatNormSq, qVecA, qVecB])

private theorem quadraticMap_atomA_atomC :
    quadraticMap atomA atomC = (1 / 3 : ℝ) • atomA := by
  rw [atomA_eq_quatDyad quatEmbed1, atomC_eq_quatDyad1]
  exact quatDyad_R1_eval quatEmbed1 quatEmbed1_isQuatEmbedding qVecA qVecC 1 3 (1 / 3)
    (by norm_num) qVecA_normSq (by
      simp [Fin.sum_univ_three, quatNormSq, qVecA, qVecC])

private theorem quadraticMap_atomC_atomA :
    quadraticMap atomC atomA = (1 / 3 : ℝ) • atomC := by
  rw [atomC_eq_quatDyad1, atomA_eq_quatDyad quatEmbed1]
  exact quatDyad_R1_eval quatEmbed1 quatEmbed1_isQuatEmbedding qVecC qVecA 3 1 (1 / 3)
    (by norm_num) qVecC_normSq (by
      simp [Fin.sum_univ_three, quatNormSq, qVecA, qVecC])

private theorem quadraticMap_atomA_atomD :
    quadraticMap atomA atomD = (1 / 3 : ℝ) • atomA := by
  rw [atomA_eq_quatDyad quatEmbed2, atomD_eq_quatDyad2]
  exact quatDyad_R1_eval quatEmbed2 quatEmbed2_isQuatEmbedding qVecA qVecD 1 3 (1 / 3)
    (by norm_num) qVecA_normSq (by
      simp [Fin.sum_univ_three, quatNormSq, qVecA, qVecD])

private theorem quadraticMap_atomD_atomA :
    quadraticMap atomD atomA = (1 / 3 : ℝ) • atomD := by
  rw [atomD_eq_quatDyad2, atomA_eq_quatDyad quatEmbed2]
  exact quatDyad_R1_eval quatEmbed2 quatEmbed2_isQuatEmbedding qVecD qVecA 3 1 (1 / 3)
    (by norm_num) qVecD_normSq (by
      simp [Fin.sum_univ_three, quatNormSq, qVecA, qVecD])

private theorem quadraticMap_atomB_atomC :
    quadraticMap atomB atomC = (1 / 3 : ℝ) • atomB := by
  rw [atomB_eq_quatDyad quatEmbed1 quatEmbed1_isQuatEmbedding, atomC_eq_quatDyad1]
  exact quatDyad_R1_eval quatEmbed1 quatEmbed1_isQuatEmbedding qVecB qVecC 2 3 (1 / 3)
    (by norm_num) qVecB_normSq (by
      simp [Fin.sum_univ_three, quatNormSq, qVecB, qVecC, qI]
      norm_num)

private theorem quadraticMap_atomC_atomB :
    quadraticMap atomC atomB = (1 / 3 : ℝ) • atomC := by
  rw [atomC_eq_quatDyad1, atomB_eq_quatDyad quatEmbed1 quatEmbed1_isQuatEmbedding]
  exact quatDyad_R1_eval quatEmbed1 quatEmbed1_isQuatEmbedding qVecC qVecB 3 2 (1 / 3)
    (by norm_num) qVecC_normSq (by
      simp [Fin.sum_univ_three, quatNormSq, qVecB, qVecC, qI]
      norm_num)

private theorem quadraticMap_atomB_atomD :
    quadraticMap atomB atomD = (1 / 3 : ℝ) • atomB := by
  rw [atomB_eq_quatDyad quatEmbed2 quatEmbed2_isQuatEmbedding, atomD_eq_quatDyad2]
  exact quatDyad_R1_eval quatEmbed2 quatEmbed2_isQuatEmbedding qVecB qVecD 2 3 (1 / 3)
    (by norm_num) qVecB_normSq (by
      simp [Fin.sum_univ_three, quatNormSq, qVecB, qVecD, qI]
      norm_num)

private theorem quadraticMap_atomD_atomB :
    quadraticMap atomD atomB = (1 / 3 : ℝ) • atomD := by
  rw [atomD_eq_quatDyad2, atomB_eq_quatDyad quatEmbed2 quatEmbed2_isQuatEmbedding]
  exact quatDyad_R1_eval quatEmbed2 quatEmbed2_isQuatEmbedding qVecD qVecB 3 2 (1 / 3)
    (by norm_num) qVecD_normSq (by
      simp [Fin.sum_univ_three, quatNormSq, qVecB, qVecD, qI]
      norm_num)

/-! ## Section 4: Explicit 6-Slot `(C, D)` Contraction & All 12 Ordered R1s -/

private theorem jordanMul_off01 (x y : Albert) :
    (jordanMul x y).2 0 = (1 / 2 : ℝ) •
      ((x.1 0 • y.2 0 + y.1 1 • x.2 0 + octonionMul (x.2 1) (octonionConj (y.2 2))) +
       (y.1 0 • x.2 0 + x.1 1 • y.2 0 + octonionMul (y.2 1) (octonionConj (x.2 2)))) := by
  unfold jordanMul albertCoordinates octonionMatrixMul
  simp only [Fin.sum_univ_three, Pi.add_apply]
  change (1 / 2 : ℝ) •
      ((octonionMul (octonionScalar (x.1 0)) (y.2 0) +
          octonionMul (x.2 0) (octonionScalar (y.1 1)) +
          octonionMul (x.2 1) (octonionConj (y.2 2))) +
        (octonionMul (octonionScalar (y.1 0)) (x.2 0) +
          octonionMul (y.2 0) (octonionScalar (x.1 1)) +
          octonionMul (y.2 1) (octonionConj (x.2 2)))) = _
  rw [octonionMul_scalar_left, octonionMul_scalar_right,
    octonionMul_scalar_left, octonionMul_scalar_right]

private theorem jordanMul_off02 (x y : Albert) :
    (jordanMul x y).2 1 = (1 / 2 : ℝ) •
      ((x.1 0 • y.2 1 + octonionMul (x.2 0) (y.2 2) + y.1 2 • x.2 1) +
       (y.1 0 • x.2 1 + octonionMul (y.2 0) (x.2 2) + x.1 2 • y.2 1)) := by
  unfold jordanMul albertCoordinates octonionMatrixMul
  simp only [Fin.sum_univ_three, Pi.add_apply]
  change (1 / 2 : ℝ) •
      ((octonionMul (octonionScalar (x.1 0)) (y.2 1) +
          octonionMul (x.2 0) (y.2 2) +
          octonionMul (x.2 1) (octonionScalar (y.1 2))) +
        (octonionMul (octonionScalar (y.1 0)) (x.2 1) +
          octonionMul (y.2 0) (x.2 2) +
          octonionMul (y.2 1) (octonionScalar (x.1 2)))) = _
  rw [octonionMul_scalar_left, octonionMul_scalar_right,
    octonionMul_scalar_left, octonionMul_scalar_right]

private theorem jordanMul_off12 (x y : Albert) :
    (jordanMul x y).2 2 = (1 / 2 : ℝ) •
      ((octonionMul (octonionConj (x.2 0)) (y.2 1) + x.1 1 • y.2 2 + y.1 2 • x.2 2) +
       (octonionMul (octonionConj (y.2 0)) (x.2 1) + y.1 1 • x.2 2 + x.1 2 • y.2 2)) := by
  unfold jordanMul albertCoordinates octonionMatrixMul
  simp only [Fin.sum_univ_three, Pi.add_apply]
  change (1 / 2 : ℝ) •
      ((octonionMul (octonionConj (x.2 0)) (y.2 1) +
          octonionMul (octonionScalar (x.1 1)) (y.2 2) +
          octonionMul (x.2 2) (octonionScalar (y.1 2))) +
        (octonionMul (octonionConj (y.2 0)) (x.2 1) +
          octonionMul (octonionScalar (y.1 1)) (x.2 2) +
          octonionMul (y.2 2) (octonionScalar (x.1 2)))) = _
  rw [octonionMul_scalar_left, octonionMul_scalar_right,
    octonionMul_scalar_left, octonionMul_scalar_right]

def offC : Albert := (0, ![-octI, octonionScalar 1, octI])
def offD : Albert := (0, ![-octJ, -octL, -octR])
def offCD : Albert :=
  (0, ![(1 / 2 : ℝ) • (octR - octS), (1 / 2 : ℝ) • (octK - octT), (1 / 2 : ℝ) • (octJ - octS)])

private theorem offC_d (i : Fin 3) : offC.1 i = 0 := rfl
private theorem offD_d (i : Fin 3) : offD.1 i = 0 := rfl
private theorem offCD_d (i : Fin 3) : offCD.1 i = 0 := rfl
private theorem offC_u0 : offC.2 0 = -octI := rfl
private theorem offC_u1 : offC.2 1 = octonionScalar 1 := rfl
private theorem offC_u2 : offC.2 2 = octI := rfl
private theorem offD_u0 : offD.2 0 = -octJ := rfl
private theorem offD_u1 : offD.2 1 = -octL := rfl
private theorem offD_u2 : offD.2 2 = -octR := rfl
private theorem offCD_u0 : offCD.2 0 = (1 / 2 : ℝ) • (octR - octS) := rfl
private theorem offCD_u1 : offCD.2 1 = (1 / 2 : ℝ) • (octK - octT) := rfl
private theorem offCD_u2 : offCD.2 2 = (1 / 2 : ℝ) • (octJ - octS) := rfl

private theorem three_smul_atomC : (3 : ℝ) • atomC = albertUnit + offC := by
  have h3 : (3 : ℝ) * (1 / 3 : ℝ) = 1 := by norm_num
  apply albert_ext
  · rw [alb_smul_fst, atomC_d0, alb_add_fst, offC_d]; simp [albertUnit]
  · rw [alb_smul_fst, atomC_d1, alb_add_fst, offC_d]; simp [albertUnit]
  · rw [alb_smul_fst, atomC_d2, alb_add_fst, offC_d]; simp [albertUnit]
  · rw [alb_smul_snd, atomC_u0, alb_add_snd, smul_smul, h3, one_smul, offC_u0]; simp [albertUnit]
  · rw [alb_smul_snd, atomC_u1, alb_add_snd, smul_smul, h3, one_smul, offC_u1]; simp [albertUnit]
  · rw [alb_smul_snd, atomC_u2, alb_add_snd, smul_smul, h3, one_smul, offC_u2]; simp [albertUnit]

private theorem three_smul_atomD : (3 : ℝ) • atomD = albertUnit + offD := by
  have h3 : (3 : ℝ) * (1 / 3 : ℝ) = 1 := by norm_num
  apply albert_ext
  · rw [alb_smul_fst, atomD_d0, alb_add_fst, offD_d]; simp [albertUnit]
  · rw [alb_smul_fst, atomD_d1, alb_add_fst, offD_d]; simp [albertUnit]
  · rw [alb_smul_fst, atomD_d2, alb_add_fst, offD_d]; simp [albertUnit]
  · rw [alb_smul_snd, atomD_u0, alb_add_snd, smul_smul, h3, one_smul, offD_u0]; simp [albertUnit]
  · rw [alb_smul_snd, atomD_u1, alb_add_snd, smul_smul, h3, one_smul, offD_u1]; simp [albertUnit]
  · rw [alb_smul_snd, atomD_u2, alb_add_snd, smul_smul, h3, one_smul, offD_u2]; simp [albertUnit]

private theorem off_mul_self_of_three_atom {p m : Albert}
    (hp : jordanMul p p = p) (hpm : (3 : ℝ) • p = albertUnit + m) :
    jordanMul m m = (2 : ℝ) • albertUnit + m := by
  have hsq : jordanMul (albertUnit + m) (albertUnit + m) = (3 : ℝ) • (albertUnit + m) := by
    calc
      jordanMul (albertUnit + m) (albertUnit + m)
          = jordanMul ((3 : ℝ) • p) ((3 : ℝ) • p) := by rw [← hpm]
      _ = ((3 : ℝ) * 3) • jordanMul p p := by
          rw [jordanMul_smul_left, jordanMul_smul_right, smul_smul]
      _ = (3 : ℝ) • ((3 : ℝ) • p) := by rw [hp, smul_smul]
      _ = (3 : ℝ) • (albertUnit + m) := by rw [hpm]
  simp only [jordanMul_add_left, jordanMul_add_right,
    jordanMul_albertUnit_left, jordanMul_albertUnit_right] at hsq
  have hsolve : jordanMul m m =
      (3 : ℝ) • (albertUnit + m) - (albertUnit + m + m) := by
    rw [← hsq]
    abel
  rw [hsolve]
  module

private theorem offC_mul_self : jordanMul offC offC = (2 : ℝ) • albertUnit + offC :=
  off_mul_self_of_three_atom (fixedS_isAtom 2).1 three_smul_atomC

private theorem offD_mul_self : jordanMul offD offD = (2 : ℝ) • albertUnit + offD :=
  off_mul_self_of_three_atom (fixedS_isAtom 3).1 three_smul_atomD

theorem jordanMul_offC_offD : jordanMul offC offD = offCD := by
  apply albert_ext
  · rw [jordanMul_diag_0, offC_d, offD_d, offCD_d, offC_u0, offC_u1, offD_u0, offD_u1]
    simp [octDot_eq_coords]
  · rw [jordanMul_diag_1, offC_d, offD_d, offCD_d, offC_u0, offC_u2, offD_u0, offD_u2]
    simp [octDot_eq_coords]
  · rw [jordanMul_diag_2, offC_d, offD_d, offCD_d, offC_u1, offC_u2, offD_u1, offD_u2]
    simp [octDot_eq_coords]
  · rw [jordanMul_off01, offC_d, offC_d, offD_d, offD_d, offC_u1, offC_u2, offD_u1, offD_u2, offCD_u0]
    apply octonion_ext <;> simp
  · rw [jordanMul_off02, offC_d, offC_d, offD_d, offD_d, offC_u0, offC_u2, offD_u0, offD_u2, offCD_u1]
    apply octonion_ext <;> simp
  · rw [jordanMul_off12, offC_d, offC_d, offD_d, offD_d, offC_u0, offC_u1, offD_u0, offD_u1, offCD_u2]
    apply octonion_ext <;> simp

theorem two_smul_offC_mul_offCD : (2 : ℝ) • jordanMul offC offCD = offD - offCD := by
  apply albert_ext
  · simp only [alb_smul_fst, alb_sub_fst, jordanMul_diag_0, offC_d, offD_d, offCD_d,
      offC_u0, offC_u1, offCD_u0, offCD_u1]
    simp [octDot_eq_coords]
  · simp only [alb_smul_fst, alb_sub_fst, jordanMul_diag_1, offC_d, offD_d, offCD_d,
      offC_u0, offC_u2, offCD_u0, offCD_u2]
    simp [octDot_eq_coords]
  · simp only [alb_smul_fst, alb_sub_fst, jordanMul_diag_2, offC_d, offD_d, offCD_d,
      offC_u1, offC_u2, offCD_u1, offCD_u2]
    simp [octDot_eq_coords]
  · simp only [alb_smul_snd, alb_sub_snd, jordanMul_off01, offC_d, offCD_d,
      offC_u1, offC_u2, offD_u0, offCD_u0, offCD_u1, offCD_u2]
    (apply octonion_ext <;> simp); norm_num
  · simp only [alb_smul_snd, alb_sub_snd, jordanMul_off02, offC_d, offCD_d,
      offC_u0, offC_u2, offD_u1, offCD_u0, offCD_u1, offCD_u2]
    (apply octonion_ext <;> simp); norm_num
  · simp only [alb_smul_snd, alb_sub_snd, jordanMul_off12, offC_d, offCD_d,
      offC_u0, offC_u1, offD_u2, offCD_u0, offCD_u1, offCD_u2]
    (apply octonion_ext <;> simp); norm_num

theorem two_smul_offD_mul_offCD : (2 : ℝ) • jordanMul offD offCD = offC - offCD := by
  apply albert_ext
  · simp only [alb_smul_fst, alb_sub_fst, jordanMul_diag_0, offC_d, offD_d, offCD_d,
      offD_u0, offD_u1, offCD_u0, offCD_u1]
    simp [octDot_eq_coords]
  · simp only [alb_smul_fst, alb_sub_fst, jordanMul_diag_1, offC_d, offD_d, offCD_d,
      offD_u0, offD_u2, offCD_u0, offCD_u2]
    simp [octDot_eq_coords]
  · simp only [alb_smul_fst, alb_sub_fst, jordanMul_diag_2, offC_d, offD_d, offCD_d,
      offD_u1, offD_u2, offCD_u1, offCD_u2]
    simp [octDot_eq_coords]
  · simp only [alb_smul_snd, alb_sub_snd, jordanMul_off01, offD_d, offCD_d,
      offD_u1, offD_u2, offC_u0, offCD_u0, offCD_u1, offCD_u2]
    (apply octonion_ext <;> simp); norm_num
  · simp only [alb_smul_snd, alb_sub_snd, jordanMul_off02, offD_d, offCD_d,
      offD_u0, offD_u2, offC_u1, offCD_u0, offCD_u1, offCD_u2]
    (apply octonion_ext <;> simp); norm_num
  · simp only [alb_smul_snd, alb_sub_snd, jordanMul_off12, offD_d, offCD_d,
      offD_u0, offD_u1, offC_u2, offCD_u0, offCD_u1, offCD_u2]
    (apply octonion_ext <;> simp); norm_num

private theorem quadraticMap_unit_plus_off
    {m n h : Albert}
    (hm : jordanMul m m = (2 : ℝ) • albertUnit + m)
    (hh : jordanMul m n = h)
    (hcd : (2 : ℝ) • jordanMul m h = n - h) :
    quadraticMap (albertUnit + m) (albertUnit + n) = (3 : ℝ) • (albertUnit + m) := by
  have hmm : jordanMul (albertUnit + m) (albertUnit + m) = (3 : ℝ) • (albertUnit + m) := by
    simp only [jordanMul_add_left, jordanMul_add_right,
      jordanMul_albertUnit_left, jordanMul_albertUnit_right, hm]
    module
  have hmn : jordanMul (albertUnit + m) (albertUnit + n) = albertUnit + m + n + h := by
    simp only [jordanMul_add_left, jordanMul_add_right,
      jordanMul_albertUnit_left, jordanMul_albertUnit_right, hh]
    abel
  unfold quadraticMap
  rw [hmm, hmn, jordanMul_smul_left, hmn]
  have hstep : jordanMul (albertUnit + m) (albertUnit + m + n + h) =
      (3 : ℝ) • albertUnit + (3 : ℝ) • m + n + (2 : ℝ) • h + jordanMul m h := by
    simp only [jordanMul_add_left, jordanMul_add_right,
      jordanMul_albertUnit_left, jordanMul_albertUnit_right, hm, hh]
    module
  rw [hstep, two_smul]
  have hcast :
      (3 : ℝ) • albertUnit + (3 : ℝ) • m + n + (2 : ℝ) • h + jordanMul m h +
        ((3 : ℝ) • albertUnit + (3 : ℝ) • m + n + (2 : ℝ) • h + jordanMul m h) -
        (3 : ℝ) • (albertUnit + m + n + h) =
      (3 : ℝ) • (albertUnit + m) + ((2 : ℝ) • jordanMul m h - (n - h)) := by
    module
  rw [hcast, hcd, sub_self, add_zero]

private theorem quadraticMap_CD_of_off
    {p q m n h : Albert}
    (hp3 : (3 : ℝ) • p = albertUnit + m)
    (hq3 : (3 : ℝ) • q = albertUnit + n)
    (hm : jordanMul m m = (2 : ℝ) • albertUnit + m)
    (hh : jordanMul m n = h)
    (hcd : (2 : ℝ) • jordanMul m h = n - h) :
    quadraticMap p q = (1 / 3 : ℝ) • p := by
  have hU := quadraticMap_unit_plus_off hm hh hcd
  rw [← hp3, ← hq3, quadraticMap_smul_left, quadraticMap_smul_right, smul_smul, hp3] at hU
  calc
    quadraticMap p q
        = (1 / 27 : ℝ) • (((3 : ℝ) ^ 2 * 3) • quadraticMap p q) := by
          rw [smul_smul]; norm_num
    _ = (1 / 27 : ℝ) • ((3 : ℝ) • (albertUnit + m)) := by rw [hU]
    _ = (1 / 27 : ℝ) • ((3 : ℝ) • ((3 : ℝ) • p)) := by rw [← hp3]
    _ = (1 / 3 : ℝ) • p := by rw [smul_smul, smul_smul]; norm_num

theorem quadraticMap_atomC_atomD :
    quadraticMap atomC atomD = (1 / 3 : ℝ) • atomC :=
  quadraticMap_CD_of_off three_smul_atomC three_smul_atomD
    offC_mul_self jordanMul_offC_offD two_smul_offC_mul_offCD

theorem quadraticMap_atomD_atomC :
    quadraticMap atomD atomC = (1 / 3 : ℝ) • atomD :=
  quadraticMap_CD_of_off three_smul_atomD three_smul_atomC
    offD_mul_self ((jordanMul_comm offD offC).trans jordanMul_offC_offD)
    two_smul_offD_mul_offCD

theorem nativeOverlaps_fixedS_eq (a b : Fin 4) :
    nativeOverlaps fixedS a b =
      if a = b then 1
      else if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) then 1 / 2
      else 1 / 3 := by
  by_cases hab : a = b
  · subst hab
    rw [ite_of_pos rfl, nativeOverlaps, tracePairing, (fixedS_isAtom a).1, (fixedS_isAtom a).2]
  · rw [ite_of_neg hab]
    have h01 : nativeOverlaps fixedS 0 1 = 1 / 2 := by
      unfold nativeOverlaps
      rw [fixedS_zero, fixedS_one, tracePairing_diagAtom 0, atomB_d0]
    have h02 : nativeOverlaps fixedS 0 2 = 1 / 3 := by
      unfold nativeOverlaps
      rw [fixedS_zero, fixedS_two, tracePairing_diagAtom 0, atomC_d0]
    have h03 : nativeOverlaps fixedS 0 3 = 1 / 3 := by
      unfold nativeOverlaps
      rw [fixedS_zero, fixedS_three, tracePairing_diagAtom 0, atomD_d0]
    have h12 : nativeOverlaps fixedS 1 2 = 1 / 3 := by
      unfold nativeOverlaps
      rw [fixedS_one, fixedS_two, tracePairing_atomB, atomC_d0, atomC_d1, atomC_u0]
      simp
    have h13 : nativeOverlaps fixedS 1 3 = 1 / 3 := by
      unfold nativeOverlaps
      rw [fixedS_one, fixedS_three, tracePairing_atomB, atomD_d0, atomD_d1, atomD_u0]
      simp
    have h23 : nativeOverlaps fixedS 2 3 = 1 / 3 := by
      unfold nativeOverlaps
      rw [fixedS_two, fixedS_three, tracePairing_eq_coords,
        atomC_d0, atomC_d1, atomC_d2, atomC_u0, atomC_u1, atomC_u2,
        atomD_d0, atomD_d1, atomD_d2, atomD_u0, atomD_u1, atomD_u2]
      simp [octDot_eq_coords]; norm_num
    fin_cases a <;> fin_cases b <;>
      try exact absurd rfl hab
    · rw [ite_of_pos (by decide)]; exact h01
    · rw [ite_of_neg (by decide)]; exact h02
    · rw [ite_of_neg (by decide)]; exact h03
    · rw [ite_of_pos (by decide), nativeOverlaps, tracePairing_comm]; exact h01
    · rw [ite_of_neg (by decide)]; exact h12
    · rw [ite_of_neg (by decide)]; exact h13
    · rw [ite_of_neg (by decide), nativeOverlaps, tracePairing_comm]; exact h02
    · rw [ite_of_neg (by decide), nativeOverlaps, tracePairing_comm]; exact h12
    · rw [ite_of_neg (by decide)]; exact h23
    · rw [ite_of_neg (by decide), nativeOverlaps, tracePairing_comm]; exact h03
    · rw [ite_of_neg (by decide), nativeOverlaps, tracePairing_comm]; exact h13
    · rw [ite_of_neg (by decide), nativeOverlaps, tracePairing_comm]; exact h23

theorem fixedS_overlap_symmetric (a b : Fin 4) :
    nativeOverlaps fixedS a b = nativeOverlaps fixedS b a :=
  tracePairing_comm (fixedS a) (fixedS b)

theorem fixedS_native_R1 (a b : Fin 4) (hab : a ≠ b) :
    quadraticMap (fixedS a) (fixedS b) = nativeOverlaps fixedS a b • fixedS a := by
  rw [nativeOverlaps_fixedS_eq a b, ite_of_neg hab]
  fin_cases a <;> fin_cases b <;>
    try exact absurd rfl hab
  · rw [ite_of_pos (by decide)]; exact quadraticMap_atomA_atomB
  · rw [ite_of_neg (by decide)]; exact quadraticMap_atomA_atomC
  · rw [ite_of_neg (by decide)]; exact quadraticMap_atomA_atomD
  · rw [ite_of_pos (by decide)]; exact quadraticMap_atomB_atomA
  · rw [ite_of_neg (by decide)]; exact quadraticMap_atomB_atomC
  · rw [ite_of_neg (by decide)]; exact quadraticMap_atomB_atomD
  · rw [ite_of_neg (by decide)]; exact quadraticMap_atomC_atomA
  · rw [ite_of_neg (by decide)]; exact quadraticMap_atomC_atomB
  · rw [ite_of_neg (by decide)]; exact quadraticMap_atomC_atomD
  · rw [ite_of_neg (by decide)]; exact quadraticMap_atomD_atomA
  · rw [ite_of_neg (by decide)]; exact quadraticMap_atomD_atomB
  · rw [ite_of_neg (by decide)]; exact quadraticMap_atomD_atomC

/-! ## Section 5: Small Pair Table `(P)` & Actual Triangle Symmetry on All 64 Triples -/

private theorem jordanMul_diagAtom0_apply (y : Albert) :
    jordanMul (diagAtom 0) y =
      (![y.1 0, 0, 0], ![(1 / 2 : ℝ) • y.2 0, (1 / 2 : ℝ) • y.2 1, 0]) := by
  apply albert_ext
  · rw [jordanMul_diag_0]; simp [diagAtom, octDot_zero_left]
  · rw [jordanMul_diag_1]; simp [diagAtom, octDot_zero_left]
  · rw [jordanMul_diag_2]; simp [diagAtom, octDot_zero_left]
  · rw [jordanMul_off01]; simp [diagAtom, octonionMul_zero_left, octonionMul_zero_right, octonionConj_zero]
  · rw [jordanMul_off02]; simp [diagAtom, octonionMul_zero_left, octonionMul_zero_right]
  · rw [jordanMul_off12]; simp [diagAtom, octonionConj_zero, octonionMul_zero_left, octonionMul_zero_right]

private def pairAB : Albert := (1 / 4 : ℝ) • (![2, 0, 0], ![octonionScalar 1, 0, 0])
private def pairAC : Albert := (1 / 6 : ℝ) • (![2, 0, 0], ![-octI, octonionScalar 1, 0])
private def pairAD : Albert := (1 / 6 : ℝ) • (![2, 0, 0], ![-octJ, -octL, 0])
private def pairBC : Albert :=
  (1 / 12 : ℝ) • (![2, 2, 0], ![octonionScalar 2 - (2 : ℝ) • octI, octonionScalar 1 + octI, octonionScalar 1 + octI])
private def pairBD : Albert :=
  (1 / 12 : ℝ) • (![2, 2, 0], ![octonionScalar 2 - (2 : ℝ) • octJ, -octL - octR, -octL - octR])
private def pairCD : Albert := (1 / 9 : ℝ) • (albertUnit + offC + offD + offCD)

private theorem pairAB_d0 : pairAB.1 0 = 1 / 2 := by
  change (1 / 4 : ℝ) * 2 = 1 / 2; norm_num
private theorem pairAB_d1 : pairAB.1 1 = 0 := by
  change (1 / 4 : ℝ) * 0 = 0; norm_num
private theorem pairAB_d2 : pairAB.1 2 = 0 := by
  change (1 / 4 : ℝ) * 0 = 0; norm_num
private theorem pairAB_u0 : pairAB.2 0 = (1 / 4 : ℝ) • octonionScalar 1 := rfl
private theorem pairAB_u1 : pairAB.2 1 = 0 := by
  change (1 / 4 : ℝ) • (0 : Octonion) = 0; exact smul_zero _
private theorem pairAB_u2 : pairAB.2 2 = 0 := by
  change (1 / 4 : ℝ) • (0 : Octonion) = 0; exact smul_zero _

private theorem pairAC_d0 : pairAC.1 0 = 1 / 3 := by
  change (1 / 6 : ℝ) * 2 = 1 / 3; norm_num
private theorem pairAC_d1 : pairAC.1 1 = 0 := by
  change (1 / 6 : ℝ) * 0 = 0; norm_num
private theorem pairAC_d2 : pairAC.1 2 = 0 := by
  change (1 / 6 : ℝ) * 0 = 0; norm_num
private theorem pairAC_u0 : pairAC.2 0 = (1 / 6 : ℝ) • (-octI) := rfl
private theorem pairAC_u1 : pairAC.2 1 = (1 / 6 : ℝ) • octonionScalar 1 := rfl
private theorem pairAC_u2 : pairAC.2 2 = 0 := by
  change (1 / 6 : ℝ) • (0 : Octonion) = 0; exact smul_zero _

private theorem pairAD_d0 : pairAD.1 0 = 1 / 3 := by
  change (1 / 6 : ℝ) * 2 = 1 / 3; norm_num
private theorem pairAD_d1 : pairAD.1 1 = 0 := by
  change (1 / 6 : ℝ) * 0 = 0; norm_num
private theorem pairAD_d2 : pairAD.1 2 = 0 := by
  change (1 / 6 : ℝ) * 0 = 0; norm_num
private theorem pairAD_u0 : pairAD.2 0 = (1 / 6 : ℝ) • (-octJ) := rfl
private theorem pairAD_u1 : pairAD.2 1 = (1 / 6 : ℝ) • (-octL) := rfl
private theorem pairAD_u2 : pairAD.2 2 = 0 := by
  change (1 / 6 : ℝ) • (0 : Octonion) = 0; exact smul_zero _

private theorem pairBC_d0 : pairBC.1 0 = 1 / 6 := by
  change (1 / 12 : ℝ) * 2 = 1 / 6; norm_num
private theorem pairBC_d1 : pairBC.1 1 = 1 / 6 := by
  change (1 / 12 : ℝ) * 2 = 1 / 6; norm_num
private theorem pairBC_d2 : pairBC.1 2 = 0 := by
  change (1 / 12 : ℝ) * 0 = 0; norm_num
private theorem pairBC_u0 : pairBC.2 0 = (1 / 12 : ℝ) • (octonionScalar 2 - (2 : ℝ) • octI) := rfl
private theorem pairBC_u1 : pairBC.2 1 = (1 / 12 : ℝ) • (octonionScalar 1 + octI) := rfl
private theorem pairBC_u2 : pairBC.2 2 = (1 / 12 : ℝ) • (octonionScalar 1 + octI) := rfl

private theorem pairBD_d0 : pairBD.1 0 = 1 / 6 := by
  change (1 / 12 : ℝ) * 2 = 1 / 6; norm_num
private theorem pairBD_d1 : pairBD.1 1 = 1 / 6 := by
  change (1 / 12 : ℝ) * 2 = 1 / 6; norm_num
private theorem pairBD_d2 : pairBD.1 2 = 0 := by
  change (1 / 12 : ℝ) * 0 = 0; norm_num
private theorem pairBD_u0 : pairBD.2 0 = (1 / 12 : ℝ) • (octonionScalar 2 - (2 : ℝ) • octJ) := rfl
private theorem pairBD_u1 : pairBD.2 1 = (1 / 12 : ℝ) • (-octL - octR) := rfl
private theorem pairBD_u2 : pairBD.2 2 = (1 / 12 : ℝ) • (-octL - octR) := rfl

private theorem pairCD_d0 : pairCD.1 0 = 1 / 9 := by
  change (1 / 9 : ℝ) * (1 + 0 + 0 + 0) = 1 / 9; norm_num
private theorem pairCD_d1 : pairCD.1 1 = 1 / 9 := by
  change (1 / 9 : ℝ) * (1 + 0 + 0 + 0) = 1 / 9; norm_num
private theorem pairCD_d2 : pairCD.1 2 = 1 / 9 := by
  change (1 / 9 : ℝ) * (1 + 0 + 0 + 0) = 1 / 9; norm_num
private theorem pairCD_u0 : pairCD.2 0 = (1 / 9 : ℝ) • (0 + -octI + -octJ + (1 / 2 : ℝ) • (octR - octS)) := rfl
private theorem pairCD_u1 : pairCD.2 1 = (1 / 9 : ℝ) • (0 + octonionScalar 1 + -octL + (1 / 2 : ℝ) • (octK - octT)) := rfl
private theorem pairCD_u2 : pairCD.2 2 = (1 / 9 : ℝ) • (0 + octI + -octR + (1 / 2 : ℝ) • (octJ - octS)) := rfl

private theorem jordanMul_atomA_atomB : jordanMul atomA atomB = pairAB := by
  rw [atomA, jordanMul_diagAtom0_apply]
  apply albert_ext
  · simp [atomB_d0, pairAB_d0]
  · simp [pairAB_d1]
  · simp [pairAB_d2]
  · simp [atomB_u0, pairAB_u0, smul_smul]; norm_num
  · simp [atomB_u1, pairAB_u1]
  · exact pairAB_u2.symm

private theorem jordanMul_atomA_atomC : jordanMul atomA atomC = pairAC := by
  rw [atomA, jordanMul_diagAtom0_apply]
  apply albert_ext
  · simp [atomC_d0, pairAC_d0]
  · simp [pairAC_d1]
  · simp [pairAC_d2]
  · simp [atomC_u0, pairAC_u0, smul_smul]; norm_num
  · simp [atomC_u1, pairAC_u1, smul_smul]; norm_num
  · simp [pairAC_u2]

private theorem jordanMul_atomA_atomD : jordanMul atomA atomD = pairAD := by
  rw [atomA, jordanMul_diagAtom0_apply]
  apply albert_ext
  · simp [atomD_d0, pairAD_d0]
  · simp [pairAD_d1]
  · simp [pairAD_d2]
  · simp [atomD_u0, pairAD_u0, smul_smul]; norm_num
  · simp [atomD_u1, pairAD_u1, smul_smul]; norm_num
  · simp [pairAD_u2]

private theorem jordanMul_atomB_atomC : jordanMul atomB atomC = pairBC := by
  apply albert_ext
  · rw [jordanMul_diag_0, atomB_d0, atomB_u0, atomB_u1, atomC_d0, atomC_u0, atomC_u1, pairBC_d0]
    simp [octDot_eq_coords]; norm_num
  · rw [jordanMul_diag_1, atomB_d1, atomB_u0, atomB_u2, atomC_d1, atomC_u0, atomC_u2, pairBC_d1]
    simp [octDot_eq_coords]; norm_num
  · rw [jordanMul_diag_2, atomB_d2, atomB_u1, atomB_u2, atomC_d2, pairBC_d2]
    simp only [octDot_zero_left]; norm_num
  · rw [jordanMul_off01, atomB_d0, atomB_d1, atomB_u0, atomB_u1, atomB_u2,
      atomC_d0, atomC_d1, atomC_u0, atomC_u1, atomC_u2, pairBC_u0]
    apply octonion_ext <;> simp <;> norm_num
  · rw [jordanMul_off02, atomB_d0, atomB_d2, atomB_u0, atomB_u1, atomB_u2,
      atomC_d0, atomC_d2, atomC_u0, atomC_u1, atomC_u2, pairBC_u1]
    apply octonion_ext <;> simp <;> norm_num
  · rw [jordanMul_off12, atomB_d1, atomB_d2, atomB_u0, atomB_u1, atomB_u2,
      atomC_d1, atomC_d2, atomC_u0, atomC_u1, atomC_u2, pairBC_u2]
    apply octonion_ext <;> simp <;> norm_num

private theorem jordanMul_atomB_atomD : jordanMul atomB atomD = pairBD := by
  apply albert_ext
  · rw [jordanMul_diag_0, atomB_d0, atomB_u0, atomB_u1, atomD_d0, atomD_u0, atomD_u1, pairBD_d0]
    simp [octDot_eq_coords]; norm_num
  · rw [jordanMul_diag_1, atomB_d1, atomB_u0, atomB_u2, atomD_d1, atomD_u0, atomD_u2, pairBD_d1]
    simp [octDot_eq_coords]; norm_num
  · rw [jordanMul_diag_2, atomB_d2, atomB_u1, atomB_u2, atomD_d2, pairBD_d2]
    simp only [octDot_zero_left]; norm_num
  · rw [jordanMul_off01, atomB_d0, atomB_d1, atomB_u0, atomB_u1, atomB_u2,
      atomD_d0, atomD_d1, atomD_u0, atomD_u1, atomD_u2, pairBD_u0]
    apply octonion_ext <;> simp <;> norm_num
  · rw [jordanMul_off02, atomB_d0, atomB_d2, atomB_u0, atomB_u1, atomB_u2,
      atomD_d0, atomD_d2, atomD_u0, atomD_u1, atomD_u2, pairBD_u1]
    apply octonion_ext <;> simp <;> norm_num
  · rw [jordanMul_off12, atomB_d1, atomB_d2, atomB_u0, atomB_u1, atomB_u2,
      atomD_d1, atomD_d2, atomD_u0, atomD_u1, atomD_u2, pairBD_u2]
    apply octonion_ext <;> simp <;> norm_num

private theorem jordanMul_atomC_atomD : jordanMul atomC atomD = pairCD := by
  have h9 : (9 : ℝ) • jordanMul atomC atomD = albertUnit + offC + offD + offCD := by
    calc
      (9 : ℝ) • jordanMul atomC atomD
          = jordanMul ((3 : ℝ) • atomC) ((3 : ℝ) • atomD) := by
            rw [jordanMul_smul_left, jordanMul_smul_right, smul_smul]; norm_num
      _ = jordanMul (albertUnit + offC) (albertUnit + offD) := by
            rw [three_smul_atomC, three_smul_atomD]
      _ = albertUnit + offC + offD + offCD := by
            simp only [jordanMul_add_left, jordanMul_add_right,
              jordanMul_albertUnit_left, jordanMul_albertUnit_right, jordanMul_offC_offD]
            abel
  calc
    jordanMul atomC atomD = (1 / 9 : ℝ) • ((9 : ℝ) • jordanMul atomC atomD) := by
      rw [smul_smul]; norm_num
    _ = pairCD := by rw [h9]; rfl

private theorem tracePairing_jordanMul_self_left {p q : Albert}
    (hp : IsAtom p) (hU : quadraticMap p q = tracePairing p q • p) :
    tracePairing p (jordanMul p q) = tracePairing p q := by
  unfold quadraticMap at hU
  rw [hp.1] at hU
  have htr := congrArg albertTrace hU
  rw [albertTrace_sub, two_smul, albertTrace_add, albertTrace_smul, hp.2, mul_one] at htr
  change tracePairing p (jordanMul p q) + tracePairing p (jordanMul p q) -
      tracePairing p q = tracePairing p q at htr
  linarith

private theorem nativeTriangles_012 : nativeTriangles fixedS 0 1 2 = 1 / 6 := by
  unfold nativeTriangles
  rw [fixedS_zero, fixedS_one, fixedS_two, tracePairing_diagAtom 0, jordanMul_atomB_atomC, pairBC_d0]

private theorem nativeTriangles_102 : nativeTriangles fixedS 1 0 2 = 1 / 6 := by
  unfold nativeTriangles
  have hA : fixedS 0 = atomA := rfl
  rw [fixedS_one, hA, fixedS_two, tracePairing_atomB, jordanMul_atomA_atomC,
    pairAC_d0, pairAC_d1, pairAC_u0]
  simp; norm_num

private theorem nativeTriangles_201 : nativeTriangles fixedS 2 0 1 = 1 / 6 := by
  unfold nativeTriangles
  have hA : fixedS 0 = atomA := rfl
  rw [fixedS_two, hA, fixedS_one, tracePairing_eq_coords, jordanMul_atomA_atomB,
    atomC_d0, atomC_d1, atomC_d2, atomC_u0, atomC_u1, atomC_u2,
    pairAB_d0, pairAB_d1, pairAB_d2, pairAB_u0, pairAB_u1, pairAB_u2]
  simp [octDot_eq_coords]; norm_num

private theorem nativeTriangles_013 : nativeTriangles fixedS 0 1 3 = 1 / 6 := by
  unfold nativeTriangles
  rw [fixedS_zero, fixedS_one, fixedS_three, tracePairing_diagAtom 0, jordanMul_atomB_atomD, pairBD_d0]

private theorem nativeTriangles_103 : nativeTriangles fixedS 1 0 3 = 1 / 6 := by
  unfold nativeTriangles
  have hA : fixedS 0 = atomA := rfl
  rw [fixedS_one, hA, fixedS_three, tracePairing_atomB, jordanMul_atomA_atomD,
    pairAD_d0, pairAD_d1, pairAD_u0]
  simp; norm_num

private theorem nativeTriangles_301 : nativeTriangles fixedS 3 0 1 = 1 / 6 := by
  unfold nativeTriangles
  have hA : fixedS 0 = atomA := rfl
  rw [fixedS_three, hA, fixedS_one, tracePairing_eq_coords, jordanMul_atomA_atomB,
    atomD_d0, atomD_d1, atomD_d2, atomD_u0, atomD_u1, atomD_u2,
    pairAB_d0, pairAB_d1, pairAB_d2, pairAB_u0, pairAB_u1, pairAB_u2]
  simp [octDot_eq_coords]; norm_num

private theorem nativeTriangles_023 : nativeTriangles fixedS 0 2 3 = 1 / 9 := by
  unfold nativeTriangles
  rw [fixedS_zero, fixedS_two, fixedS_three, tracePairing_diagAtom 0, jordanMul_atomC_atomD, pairCD_d0]

private theorem nativeTriangles_203 : nativeTriangles fixedS 2 0 3 = 1 / 9 := by
  unfold nativeTriangles
  have hA : fixedS 0 = atomA := rfl
  rw [fixedS_two, hA, fixedS_three, tracePairing_eq_coords, jordanMul_atomA_atomD,
    atomC_d0, atomC_d1, atomC_d2, atomC_u0, atomC_u1, atomC_u2,
    pairAD_d0, pairAD_d1, pairAD_d2, pairAD_u0, pairAD_u1, pairAD_u2]
  simp [octDot_eq_coords]; norm_num

private theorem nativeTriangles_302 : nativeTriangles fixedS 3 0 2 = 1 / 9 := by
  unfold nativeTriangles
  have hA : fixedS 0 = atomA := rfl
  rw [fixedS_three, hA, fixedS_two, tracePairing_eq_coords, jordanMul_atomA_atomC,
    atomD_d0, atomD_d1, atomD_d2, atomD_u0, atomD_u1, atomD_u2,
    pairAC_d0, pairAC_d1, pairAC_d2, pairAC_u0, pairAC_u1, pairAC_u2]
  simp [octDot_eq_coords]; norm_num

private theorem nativeTriangles_123 : nativeTriangles fixedS 1 2 3 = 1 / 9 := by
  unfold nativeTriangles
  rw [fixedS_one, fixedS_two, fixedS_three, tracePairing_atomB, jordanMul_atomC_atomD,
    pairCD_d0, pairCD_d1, pairCD_u0]
  simp

private theorem nativeTriangles_213 : nativeTriangles fixedS 2 1 3 = 1 / 9 := by
  unfold nativeTriangles
  rw [fixedS_two, fixedS_one, fixedS_three, tracePairing_eq_coords, jordanMul_atomB_atomD,
    atomC_d0, atomC_d1, atomC_d2, atomC_u0, atomC_u1, atomC_u2,
    pairBD_d0, pairBD_d1, pairBD_d2, pairBD_u0, pairBD_u1, pairBD_u2]
  simp [octDot_eq_coords]; norm_num

private theorem nativeTriangles_312 : nativeTriangles fixedS 3 1 2 = 1 / 9 := by
  unfold nativeTriangles
  rw [fixedS_three, fixedS_one, fixedS_two, tracePairing_eq_coords, jordanMul_atomB_atomC,
    atomD_d0, atomD_d1, atomD_d2, atomD_u0, atomD_u1, atomD_u2,
    pairBC_d0, pairBC_d1, pairBC_d2, pairBC_u0, pairBC_u1, pairBC_u2]
  simp [octDot_eq_coords]; norm_num

def fixedSTriangleVal (a b c : Fin 4) : ℝ :=
  if a = b ∧ b = c then 1
  else if a = b then nativeOverlaps fixedS a c
  else if a = c then nativeOverlaps fixedS a b
  else if b = c then nativeOverlaps fixedS b a
  else if a.val + b.val + c.val ≤ 4 then 1 / 6
  else 1 / 9

theorem nativeTriangles_fixedS_eq (a b c : Fin 4) :
    nativeTriangles fixedS a b c = fixedSTriangleVal a b c := by
  by_cases hab : a = b
  · subst hab
    by_cases hac : a = c
    · subst hac
      unfold fixedSTriangleVal
      rw [ite_of_pos ⟨rfl, rfl⟩, nativeTriangles, tracePairing,
        (fixedS_isAtom a).1, (fixedS_isAtom a).1, (fixedS_isAtom a).2]
    · unfold fixedSTriangleVal
      rw [ite_of_neg (fun h => hac h.2), ite_of_pos rfl]
      exact tracePairing_jordanMul_self_left (fixedS_isAtom a) (fixedS_native_R1 a c hac)
  · by_cases hac : a = c
    · subst hac
      unfold fixedSTriangleVal
      rw [ite_of_neg (fun h => hab h.1), ite_of_neg hab, ite_of_pos rfl,
        nativeTriangles, jordanMul_comm]
      exact tracePairing_jordanMul_self_left (fixedS_isAtom a) (fixedS_native_R1 a b hab)
    · by_cases hbc : b = c
      · subst hbc
        unfold fixedSTriangleVal
        rw [ite_of_neg (fun h => hab h.1), ite_of_neg hab, ite_of_neg hac, ite_of_pos rfl,
          nativeTriangles, (fixedS_isAtom b).1, tracePairing_comm]
        rfl
      · have hcomm : ∀ x y z : Fin 4,
            nativeTriangles fixedS x y z = nativeTriangles fixedS x z y := by
          intro x y z; rw [nativeTriangles, nativeTriangles, jordanMul_comm]
        fin_cases a <;> fin_cases b <;> fin_cases c <;>
          (try exact absurd rfl hab) <;>
          (try exact absurd rfl hac) <;>
          (try exact absurd rfl hbc) <;>
          (unfold fixedSTriangleVal;
           rw [ite_of_neg (fun h => hab h.1), ite_of_neg hab, ite_of_neg hac, ite_of_neg hbc])
        · rw [ite_of_pos (by decide)]; exact nativeTriangles_012
        · rw [ite_of_pos (by decide)]; exact nativeTriangles_013
        · rw [ite_of_pos (by decide)]; exact (hcomm 0 2 1).trans nativeTriangles_012
        · rw [ite_of_neg (by decide)]; exact nativeTriangles_023
        · rw [ite_of_pos (by decide)]; exact (hcomm 0 3 1).trans nativeTriangles_013
        · rw [ite_of_neg (by decide)]; exact (hcomm 0 3 2).trans nativeTriangles_023
        · rw [ite_of_pos (by decide)]; exact nativeTriangles_102
        · rw [ite_of_pos (by decide)]; exact nativeTriangles_103
        · rw [ite_of_pos (by decide)]; exact (hcomm 1 2 0).trans nativeTriangles_102
        · rw [ite_of_neg (by decide)]; exact nativeTriangles_123
        · rw [ite_of_pos (by decide)]; exact (hcomm 1 3 0).trans nativeTriangles_103
        · rw [ite_of_neg (by decide)]; exact (hcomm 1 3 2).trans nativeTriangles_123
        · rw [ite_of_pos (by decide)]; exact nativeTriangles_201
        · rw [ite_of_neg (by decide)]; exact nativeTriangles_203
        · rw [ite_of_pos (by decide)]; exact (hcomm 2 1 0).trans nativeTriangles_201
        · rw [ite_of_neg (by decide)]; exact nativeTriangles_213
        · rw [ite_of_neg (by decide)]; exact (hcomm 2 3 0).trans nativeTriangles_203
        · rw [ite_of_neg (by decide)]; exact (hcomm 2 3 1).trans nativeTriangles_213
        · rw [ite_of_pos (by decide)]; exact nativeTriangles_301
        · rw [ite_of_neg (by decide)]; exact nativeTriangles_302
        · rw [ite_of_pos (by decide)]; exact (hcomm 3 1 0).trans nativeTriangles_301
        · rw [ite_of_neg (by decide)]; exact nativeTriangles_312
        · rw [ite_of_neg (by decide)]; exact (hcomm 3 2 0).trans nativeTriangles_302
        · rw [ite_of_neg (by decide)]; exact (hcomm 3 2 1).trans nativeTriangles_312

private theorem fixedSTriangleVal_swap12 (a b c : Fin 4) :
    fixedSTriangleVal a b c = fixedSTriangleVal b a c := by
  by_cases hab : a = b
  · subst hab; rfl
  · by_cases hac : a = c
    · subst hac
      simp only [fixedSTriangleVal, hab, Ne.symm hab, false_and, ↓reduceIte]
    · by_cases hbc : b = c
      · subst hbc
        simp only [fixedSTriangleVal, hab, Ne.symm hab, false_and, ↓reduceIte]
      · simp only [fixedSTriangleVal, hab, hac, hbc, Ne.symm hab, false_and, ↓reduceIte,
          Nat.add_comm a.val b.val]

theorem fixedS_triangle_swap (a b c : Fin 4) :
    nativeTriangles fixedS a b c = nativeTriangles fixedS b a c ∧
      nativeTriangles fixedS a b c = nativeTriangles fixedS a c b := by
  constructor
  · rw [nativeTriangles_fixedS_eq a b c, nativeTriangles_fixedS_eq b a c]
    exact fixedSTriangleVal_swap12 a b c
  · unfold nativeTriangles
    rw [jordanMul_comm (fixedS b) (fixedS c)]

/-! ## Section 6: Four Native R2s and Three Native R3s (`123, 231, 312`) -/

theorem fixedS_native_R2_baseA (b c : Fin 4) :
    quadraticMap (fixedS 0) (jordanMul (fixedS b) (fixedS c)) =
      nativeTriangles fixedS 0 b c • fixedS 0 := by
  rw [fixedS_zero, quadraticMap_diagAtom 0]
  congr 1
  exact (tracePairing_diagAtom 0 _).symm

theorem fixedS_native_R2_012 :
    quadraticMap (fixedS 0) (jordanMul (fixedS 1) (fixedS 2)) = (1 / 6 : ℝ) • fixedS 0 := by
  rw [fixedS_native_R2_baseA 1 2, nativeTriangles_012]

theorem fixedS_native_R2_023 :
    quadraticMap (fixedS 0) (jordanMul (fixedS 2) (fixedS 3)) = (1 / 9 : ℝ) • fixedS 0 := by
  rw [fixedS_native_R2_baseA 2 3, nativeTriangles_023]

theorem fixedS_native_R2_031 :
    quadraticMap (fixedS 0) (jordanMul (fixedS 3) (fixedS 1)) = (1 / 6 : ℝ) • fixedS 0 := by
  rw [fixedS_native_R2_baseA 3 1, nativeTriangles, jordanMul_comm, ← nativeTriangles]
  rw [nativeTriangles_013]

theorem fixedS_native_R2_123 :
    quadraticMap (fixedS 1) (jordanMul (fixedS 2) (fixedS 3)) = (1 / 9 : ℝ) • fixedS 1 := by
  rw [fixedS_one, quadraticMap_atomB]
  change nativeTriangles fixedS 1 2 3 • fixedS 1 = (1 / 9 : ℝ) • fixedS 1
  rw [nativeTriangles_123]

private theorem nested_alpha_coord :
    (jordanMul (jordanMul atomB atomC) atomD).1 0 = 1 / 18 := by
  rw [jordanMul_atomB_atomC, jordanMul_diag_0,
    pairBC_d0, pairBC_u0, pairBC_u1, atomD_d0, atomD_u0, atomD_u1]
  simp [octDot_eq_coords]; norm_num

private theorem nested_beta_coord :
    (jordanMul (jordanMul atomC atomD) atomB).1 0 = 1 / 18 := by
  rw [jordanMul_atomC_atomD, jordanMul_diag_0,
    pairCD_d0, pairCD_u0, pairCD_u1, atomB_d0, atomB_u0, atomB_u1, octDot_zero_right]
  simp [octDot_eq_coords]; norm_num

private theorem nested_gamma_coord :
    (jordanMul (jordanMul atomB atomD) atomC).1 0 = 1 / 18 := by
  rw [jordanMul_atomB_atomD, jordanMul_diag_0,
    pairBD_d0, pairBD_u0, pairBD_u1, atomC_d0, atomC_u0, atomC_u1]
  simp [octDot_eq_coords]; norm_num

theorem nativeCornerQ_fixedS :
    nativeCornerQ fixedS = ![1 / 18, 1 / 18, 1 / 18] := by
  unfold nativeCornerQ
  funext k
  fin_cases k
  · change tracePairing (diagAtom 0) (jordanTriple atomB atomC atomD) = 1 / 18
    rw [tracePairing_diagAtom 0, jordanTriple, alb_sub_fst, alb_add_fst,
      jordanMul_comm atomD atomC, nested_alpha_coord, nested_beta_coord, nested_gamma_coord]
    norm_num
  · change tracePairing (diagAtom 0) (jordanTriple atomC atomD atomB) = 1 / 18
    rw [tracePairing_diagAtom 0, jordanTriple, alb_sub_fst, alb_add_fst,
      jordanMul_comm atomC atomB, nested_beta_coord, nested_gamma_coord, nested_alpha_coord]
    norm_num
  · change tracePairing (diagAtom 0) (jordanTriple atomD atomB atomC) = 1 / 18
    rw [tracePairing_diagAtom 0, jordanTriple, alb_sub_fst, alb_add_fst,
      jordanMul_comm atomD atomB, jordanMul_comm atomC atomB, jordanMul_comm atomD atomC,
      nested_gamma_coord, nested_alpha_coord, nested_beta_coord]
    norm_num

theorem fixedS_native_R3_123 :
    quadraticMap (fixedS 0) (jordanTriple (fixedS 1) (fixedS 2) (fixedS 3)) =
      nativeCornerQ fixedS 0 • fixedS 0 := by
  rw [fixedS_zero, quadraticMap_diagAtom 0]
  congr 1
  exact (tracePairing_diagAtom 0 _).symm

theorem fixedS_native_R3_231 :
    quadraticMap (fixedS 0) (jordanTriple (fixedS 2) (fixedS 3) (fixedS 1)) =
      nativeCornerQ fixedS 1 • fixedS 0 := by
  rw [fixedS_zero, quadraticMap_diagAtom 0]
  congr 1
  exact (tracePairing_diagAtom 0 _).symm

theorem fixedS_native_R3_312 :
    quadraticMap (fixedS 0) (jordanTriple (fixedS 3) (fixedS 1) (fixedS 2)) =
      nativeCornerQ fixedS 2 • fixedS 0 := by
  rw [fixedS_zero, quadraticMap_diagAtom 0]
  congr 1
  exact (tracePairing_diagAtom 0 _).symm

private theorem tracePairing_atomB_ACD :
    tracePairing atomB (jordanMul (jordanMul atomA atomC) atomD) = 1 / 18 := by
  rw [tracePairing_atomB, jordanMul_atomA_atomC, jordanMul_diag_0, jordanMul_diag_1, jordanMul_off01,
    pairAC_d0, pairAC_d1, pairAC_u0, pairAC_u1, pairAC_u2,
    atomD_d0, atomD_d1, atomD_u0, atomD_u1, atomD_u2, octDot_zero_left]
  simp [octDot_eq_coords]; norm_num

private theorem tracePairing_atomB_CDA :
    tracePairing atomB (jordanMul (jordanMul atomC atomD) atomA) = 1 / 18 := by
  rw [tracePairing_atomB, jordanMul_atomC_atomD, jordanMul_comm pairCD atomA, atomA,
    jordanMul_diagAtom0_apply, pairCD_d0, pairCD_u0]
  simp; norm_num

private theorem tracePairing_atomB_ADC :
    tracePairing atomB (jordanMul (jordanMul atomA atomD) atomC) = 1 / 18 := by
  rw [tracePairing_atomB, jordanMul_atomA_atomD, jordanMul_diag_0, jordanMul_diag_1, jordanMul_off01,
    pairAD_d0, pairAD_d1, pairAD_u0, pairAD_u1, pairAD_u2,
    atomC_d0, atomC_d1, atomC_u0, atomC_u1, atomC_u2, octDot_zero_left]
  simp [octDot_eq_coords]; norm_num

theorem fixedS_native_R3_baseB_023 :
    quadraticMap (fixedS 1) (jordanTriple (fixedS 0) (fixedS 2) (fixedS 3)) =
      (1 / 18 : ℝ) • fixedS 1 := by
  have hA : fixedS 0 = atomA := rfl
  rw [fixedS_one, hA, fixedS_two, fixedS_three, quadraticMap_atomB]
  congr 1
  unfold jordanTriple
  rw [tracePairing_sub_right, tracePairing_add_right, jordanMul_comm atomD atomC,
    tracePairing_atomB_ACD, tracePairing_atomB_CDA, tracePairing_atomB_ADC]
  norm_num

theorem fixedS_native_R3_baseB_230 :
    quadraticMap (fixedS 1) (jordanTriple (fixedS 2) (fixedS 3) (fixedS 0)) =
      (1 / 18 : ℝ) • fixedS 1 := by
  have hA : fixedS 0 = atomA := rfl
  rw [fixedS_one, hA, fixedS_two, fixedS_three, quadraticMap_atomB]
  congr 1
  unfold jordanTriple
  rw [tracePairing_sub_right, tracePairing_add_right, jordanMul_comm atomC atomA,
    tracePairing_atomB_CDA, tracePairing_atomB_ADC, tracePairing_atomB_ACD]
  norm_num

theorem fixedS_native_R3_baseB_302 :
    quadraticMap (fixedS 1) (jordanTriple (fixedS 3) (fixedS 0) (fixedS 2)) =
      (1 / 18 : ℝ) • fixedS 1 := by
  have hA : fixedS 0 = atomA := rfl
  rw [fixedS_one, hA, fixedS_two, fixedS_three, quadraticMap_atomB]
  congr 1
  unfold jordanTriple
  rw [tracePairing_sub_right, tracePairing_add_right, jordanMul_comm atomD atomA,
    jordanMul_comm atomC atomA, jordanMul_comm atomD atomC,
    tracePairing_atomB_ADC, tracePairing_atomB_ACD, tracePairing_atomB_CDA]
  norm_num

/-! ## Section 7: Target Homomorphism Transport and Exact Discriminant -/

private theorem target_R2_of_native
    {T : Type*} [NonUnitalRing T] [Module ℝ T]
    [IsScalarTower ℝ T T] [SMulCommClass ℝ T T]
    (η : Albert →ₗ[ℝ] T) (hη : IsJordanHom η)
    (a b c : Fin 4)
    (hnat : quadraticMap (fixedS a) (jordanMul (fixedS b) (fixedS c)) =
      nativeTriangles fixedS a b c • fixedS a) :
    η (fixedS a) * (η (fixedS b) * η (fixedS c) + η (fixedS c) * η (fixedS b)) *
        η (fixedS a) =
      (2 * nativeTriangles fixedS a b c) • η (fixedS a) := by
  have hcomp := jordanHom_map_compression η hη (fixedS a)
    (jordanMul (fixedS b) (fixedS c)) (nativeTriangles fixedS a b c) hnat
  rw [hη (fixedS b) (fixedS c), mul_smul_comm, smul_mul_assoc] at hcomp
  have htwo := congrArg (fun z : T => (2 : ℝ) • z) hcomp
  simpa only [smul_smul, show (2 : ℝ) * (1 / 2 : ℝ) = 1 by norm_num, one_smul] using htwo

private theorem target_R3_of_native
    {T : Type*} [NonUnitalRing T] [Module ℝ T]
    [IsScalarTower ℝ T T] [SMulCommClass ℝ T T]
    (η : Albert →ₗ[ℝ] T) (hη : IsJordanHom η)
    (b c d : Fin 4) (q : ℝ)
    (hnat : quadraticMap (fixedS 0) (jordanTriple (fixedS b) (fixedS c) (fixedS d)) =
      q • fixedS 0) :
    η (fixedS 0) * (η (fixedS b) * η (fixedS c) * η (fixedS d) +
        η (fixedS d) * η (fixedS c) * η (fixedS b)) * η (fixedS 0) =
      (2 * q) • η (fixedS 0) := by
  have hcomp := jordanHom_map_compression η hη (fixedS 0)
    (jordanTriple (fixedS b) (fixedS c) (fixedS d)) q hnat
  rw [jordanHom_map_triple η hη (fixedS b) (fixedS c) (fixedS d),
    mul_smul_comm, smul_mul_assoc] at hcomp
  have htwo := congrArg (fun z : T => (2 : ℝ) • z) hcomp
  simpa only [smul_smul, show (2 : ℝ) * (1 / 2 : ℝ) = 1 by norm_num, one_smul] using htwo

theorem fixedS_cornerRelations
    {T : Type*} [NonUnitalRing T] [Module ℝ T]
    [IsScalarTower ℝ T T] [SMulCommClass ℝ T T]
    (η : Albert →ₗ[ℝ] T) (hη : IsJordanHom η) :
    CornerRelations (fun i => η (fixedS i))
      (nativeOverlaps fixedS) (nativeTriangles fixedS) (nativeCornerQ fixedS) where
  idempotent a := jordanHom_map_atom_idempotent η hη (fixedS a) (fixedS_isAtom a)
  overlap_symmetric := fixedS_overlap_symmetric
  triangle_swap := fixedS_triangle_swap
  pair a b hab := jordanHom_map_compression η hη (fixedS a) (fixedS b)
    (nativeOverlaps fixedS a b) (fixedS_native_R1 a b hab)
  triangle_012 := target_R2_of_native η hη 0 1 2 (fixedS_native_R2_baseA 1 2)
  triangle_023 := target_R2_of_native η hη 0 2 3 (fixedS_native_R2_baseA 2 3)
  triangle_031 := target_R2_of_native η hη 0 3 1 (fixedS_native_R2_baseA 3 1)
  triangle_123 := target_R2_of_native η hη 1 2 3 (by
    rw [fixedS_native_R2_123, nativeTriangles_123])
  quadruple_123 := target_R3_of_native η hη 1 2 3 (nativeCornerQ fixedS 0) fixedS_native_R3_123
  quadruple_231 := target_R3_of_native η hη 2 3 1 (nativeCornerQ fixedS 1) fixedS_native_R3_231
  quadruple_312 := target_R3_of_native η hη 3 1 2 (nativeCornerQ fixedS 2) fixedS_native_R3_312

theorem fixedS_discriminant :
    tetrahedronDiscriminant (nativeOverlaps fixedS)
      (nativeTriangles fixedS) (nativeCornerQ fixedS) = 1 / 104976 := by
  have o01 : nativeOverlaps fixedS 0 1 = 1 / 2 := by
    rw [nativeOverlaps_fixedS_eq, ite_of_neg (by decide), ite_of_pos (by decide)]
  have o10 : nativeOverlaps fixedS 1 0 = 1 / 2 := by
    rw [nativeOverlaps_fixedS_eq, ite_of_neg (by decide), ite_of_pos (by decide)]
  have o02 : nativeOverlaps fixedS 0 2 = 1 / 3 := by
    rw [nativeOverlaps_fixedS_eq, ite_of_neg (by decide), ite_of_neg (by decide)]
  have o20 : nativeOverlaps fixedS 2 0 = 1 / 3 := by
    rw [nativeOverlaps_fixedS_eq, ite_of_neg (by decide), ite_of_neg (by decide)]
  have o03 : nativeOverlaps fixedS 0 3 = 1 / 3 := by
    rw [nativeOverlaps_fixedS_eq, ite_of_neg (by decide), ite_of_neg (by decide)]
  have o30 : nativeOverlaps fixedS 3 0 = 1 / 3 := by
    rw [nativeOverlaps_fixedS_eq, ite_of_neg (by decide), ite_of_neg (by decide)]
  have o12 : nativeOverlaps fixedS 1 2 = 1 / 3 := by
    rw [nativeOverlaps_fixedS_eq, ite_of_neg (by decide), ite_of_neg (by decide)]
  have o23 : nativeOverlaps fixedS 2 3 = 1 / 3 := by
    rw [nativeOverlaps_fixedS_eq, ite_of_neg (by decide), ite_of_neg (by decide)]
  have o31 : nativeOverlaps fixedS 3 1 = 1 / 3 := by
    rw [nativeOverlaps_fixedS_eq, ite_of_neg (by decide), ite_of_neg (by decide)]
  have t031 : nativeTriangles fixedS 0 3 1 = 1 / 6 :=
    (fixedS_triangle_swap 0 3 1).2.trans nativeTriangles_013
  unfold tetrahedronDiscriminant
  rw [nativeTriangles_012, nativeTriangles_023, t031, nativeTriangles_123,
    o01, o12, o20, o02, o23, o30, o03, o31, o10, nativeCornerQ_fixedS]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  norm_num

end AlbertSequential
