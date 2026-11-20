/- SPDX-License-Identifier: Apache-2.0 -/
module

public import QuaternionicHellySix
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp

/-! The maximal proper unital subalgebras in the four standard rank-three algebras. -/

@[expose] public section
noncomputable section

namespace AlbertSequential

/-- The line through an atom, taken relative to the specified native ambient algebra. -/
def relativeLine (A : NativeJordanSubalgebra) (q : Albert) (hq : IsAtom q) :
    NativeJordanSubalgebra where
  carrier := A.carrier ⊓ (lineSubalgebra q hq).carrier
  unit_mem := ⟨A.unit_mem, (lineSubalgebra q hq).unit_mem⟩
  product_mem x hx y hy :=
    ⟨A.product_mem x hx.1 y hy.1, (lineSubalgebra q hq).product_mem x hx.2 y hy.2⟩

theorem atom_mem_relativeLine {A : NativeJordanSubalgebra} {q : Albert} (hq : IsAtom q)
    (hqA : q ∈ A.carrier) : q ∈ (relativeLine A q hq).carrier :=
  ⟨hqA, (mem_lineSubalgebra_iff_idem q hq q).mpr (by rw [hq.1]; exact hq.1)⟩

/-- The actual Peirce-zero corner in the native ambient algebra. -/
def relativePeirceZero (A : NativeJordanSubalgebra) (q : Albert) : Submodule ℝ Albert where
  carrier := {x | x ∈ A.carrier ∧ jordanMul q x = 0}
  zero_mem' := ⟨A.carrier.zero_mem, jordanMul_zero_right q⟩
  add_mem' := fun hx hy => ⟨A.carrier.add_mem hx.1 hy.1, by
    rw [jordanMul_add_right, hx.2, hy.2, add_zero]⟩
  smul_mem' := fun a _ hx => ⟨A.carrier.smul_mem a hx.1, by
    rw [jordanMul_smul_right, hx.2, smul_zero]⟩

/-- The relative line is the internal direct sum of the scalar atom and its Peirce-zero corner. -/
theorem relativeLine_directSum (A : NativeJordanSubalgebra) {q : Albert}
    (hq : IsAtom q) (hqA : q ∈ A.carrier) :
    (relativeLine A q hq).carrier = Submodule.span ℝ {q} ⊔ relativePeirceZero A q ∧
      Disjoint (Submodule.span ℝ {q}) (relativePeirceZero A q) := by
  constructor
  · apply le_antisymm
    · intro x hx
      have hxA : x ∈ A.carrier := hx.1
      let t := tracePairing q x
      have hqmul : jordanMul q x = t • q := (mem_lineSubalgebra_iff q hq x).mp hx.2
      apply Submodule.mem_sup.mpr
      refine ⟨t • q, Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton q)), x - t • q,
        ⟨A.carrier.sub_mem hxA (A.carrier.smul_mem _ hqA), ?_⟩, by abel⟩
      rw [jordanMul_sub_right, jordanMul_smul_right, hqmul, hq.1, sub_self]
    · apply sup_le
      · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (atom_mem_relativeLine hq hqA))
      · intro x hx
        exact ⟨hx.1, (mem_lineSubalgebra_iff_idem q hq x).mpr (by
          rw [hx.2, jordanMul_zero_right])⟩
  · rw [disjoint_iff_inf_le]
    intro x hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx.1
    have h := hx.2.2
    rw [jordanMul_smul_right, hq.1] at h
    exact h

private theorem h3AtomToStandard (k : CDLevel) {q : Albert} (hq : IsAtom q)
    (hqA : q ∈ (H3Subalgebra k).carrier) :
    ∃ f : JordanSubalgebraIso (H3Subalgebra k) (H3Subalgebra k),
      (f.toLinearEquiv ⟨q, hqA⟩).1 = diagAtom 0 := by
  let A := H3Subalgebra k
  let f := albertUnit - q
  let c (i : Fin 3) := quadraticMap f (diagAtom i)
  have hcA (i : Fin 3) : c i ∈ A.carrier :=
    (peirce_components_mem_subalgebra A hqA (diagAtom_mem_H3Subalgebra k i)).2.2
  have hlin : ∑ i : Fin 3, c i = quadraticMap f (∑ i : Fin 3, diagAtom i) := by
    simp only [c, quadraticMap, two_nsmul, Fin.sum_univ_three, jordanMul_add_right]
    abel
  have hf : jordanMul f f = f := by
    simp only [f, jordanMul_sub_left, jordanMul_sub_right, jordanMul_albertUnit_left,
      jordanMul_albertUnit_right, hq.1]
    abel
  have hsum : ∑ i : Fin 3, albertTrace (c i) = 2 := by
    have htr : ∑ i : Fin 3, albertTrace (c i) = albertTrace (∑ i : Fin 3, c i) := by
      simp [Fin.sum_univ_three, albertTrace_add]
    have hunit : albertTrace albertUnit = 3 := by simp [albertTrace, albertUnit]
    rw [htr, hlin, diagAtom_sum_eq_unit]
    have hcomp : quadraticMap f albertUnit = f := by
      unfold quadraticMap
      simp only [jordanMul_albertUnit_right, hf, two_nsmul]
      abel
    rw [hcomp]
    change albertTrace (albertUnit - q) = 2
    rw [albertTrace_sub, hunit, hq.2]
    norm_num
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, 0 < albertTrace (c i) := by
    by_contra h
    push Not at h
    have hle : ∑ i : Fin 3, albertTrace (c i) ≤ 0 := Finset.sum_nonpos (fun i _ => h i)
    linarith
  have hw := complementAtomCompression hq (diagAtom_isAtom i)
  let t := albertTrace (c i)
  let r := t⁻¹ • c i
  let s := f - r
  have hnc : t ≠ 0 := hi.ne'
  have hrA : r ∈ A.carrier := A.carrier.smul_mem _ (hcA i)
  have hsA : s ∈ A.carrier := A.carrier.sub_mem (A.carrier.sub_mem A.unit_mem hqA) hrA
  have hr : IsAtom r := by
    constructor
    · change jordanMul (t⁻¹ • c i) (t⁻¹ • c i) = t⁻¹ • c i
      rw [jordanMul_smul_left, jordanMul_smul_right, show jordanMul (c i) (c i) = t • c i from hw.1]
      congr 1
      rw [smul_smul, inv_mul_cancel₀ hnc, one_smul]
    · change albertTrace (t⁻¹ • c i) = 1
      rw [albertTrace_smul, inv_mul_cancel₀ hnc]
  have hqr : jordanMul q r = 0 := by
    change jordanMul q (t⁻¹ • c i) = 0
    rw [jordanMul_smul_right, show jordanMul q (c i) = 0 from hw.2.2.2, smul_zero]
  have hrq : jordanMul r q = 0 := by rw [jordanMul_comm, hqr]
  have hqs : jordanMul q s = 0 := by
    simp only [s, f, jordanMul_sub_right, jordanMul_albertUnit_right, hq.1, hqr, sub_self]
  have hrs : jordanMul r s = 0 := by
    simp only [s, f, jordanMul_sub_right, jordanMul_albertUnit_right, hr.1, hrq, sub_self, sub_zero]
  have hs : IsAtom s := by
    constructor
    · simp only [s, f, jordanMul_sub_left, jordanMul_sub_right, jordanMul_albertUnit_left,
        jordanMul_albertUnit_right, hq.1, hr.1, hqr, hrq]
      abel
    · change albertTrace (albertUnit - q - r) = 1
      have hunit : albertTrace albertUnit = 3 := by simp [albertTrace, albertUnit]
      rw [albertTrace_sub, albertTrace_sub, hunit, hq.2, hr.2]
      norm_num
  let F : NativeJordanFrame :=
    { atom := ![q, r, s]
      atoms := fun j => by fin_cases j <;> first | exact hq | exact hr | exact hs
      orthogonal := fun j m hne => by
        fin_cases j <;> fin_cases m
        · exact absurd rfl hne
        · exact hqr
        · exact hqs
        · exact hrq
        · exact absurd rfl hne
        · exact hrs
        · exact (jordanMul_comm s q).trans hqs
        · exact (jordanMul_comm s r).trans hrs
        · exact absurd rfl hne
      sum_unit := by
        rw [Fin.sum_univ_three]
        change q + r + (albertUnit - q - r) = albertUnit
        abel }
  have hF (j : Fin 3) : F.atom j ∈ A.carrier := by
    fin_cases j <;> first | exact hqA | exact hrA | exact hsA
  obtain ⟨g, hg⟩ := h3FrameToStandard k F hF
  exact ⟨g, hg 0⟩

private theorem line_mem_transport {A B : NativeJordanSubalgebra}
    (f : JordanSubalgebraIso A B) (p : A.carrier) (hp : IsAtom p.1)
    (hq : IsAtom (f.toLinearEquiv p).1) (x : A.carrier) :
    x.1 ∈ (relativeLine A p.1 hp).carrier ↔
      (f.toLinearEquiv x).1 ∈ (relativeLine B (f.toLinearEquiv p).1 hq).carrier := by
  let j : A.carrier → A.carrier := fun y => ⟨jordanMul p.1 y.1, A.product_mem _ p.2 _ y.2⟩
  have f_j (y : A.carrier) := f.map_jordanMul_eq p y
  have fp :
      (f.toLinearEquiv (j (j x))).1 = jordanMul (f.toLinearEquiv p).1
        (jordanMul (f.toLinearEquiv p).1 (f.toLinearEquiv x).1) := by
    rw [show (f.toLinearEquiv (j (j x))).1 =
      jordanMul (f.toLinearEquiv p).1 (f.toLinearEquiv (j x)).1 from f_j (j x), ← f_j x]
  constructor
  · intro h
    refine ⟨(f.toLinearEquiv x).2, (mem_lineSubalgebra_iff_idem _ hq _).mpr ?_⟩
    rw [← fp, ← f_j x]
    exact congrArg (fun z => (f.toLinearEquiv z).1)
      (Subtype.ext ((mem_lineSubalgebra_iff_idem _ hp _).mp h.2) : j (j x) = j x)
  · intro h
    refine ⟨x.2, (mem_lineSubalgebra_iff_idem _ hp _).mpr ?_⟩
    apply congrArg Subtype.val (f.toLinearEquiv.injective (Subtype.ext ?_) : j (j x) = j x)
    rw [fp, f_j x]
    exact (mem_lineSubalgebra_iff_idem _ hq _).mp h.2

private theorem relativeLine_congr (A : NativeJordanSubalgebra) {p q : Albert}
    (h : p = q) (hp : IsAtom p) (hq : IsAtom q) :
    relativeLine A p hp = relativeLine A q hq := by
  subst q
  rfl

private def relativeLineIso {A B : NativeJordanSubalgebra}
    (f : JordanSubalgebraIso A B) (p : A.carrier) (hp : IsAtom p.1)
    (hq : IsAtom (f.toLinearEquiv p).1) :
    JordanSubalgebraIso (relativeLine A p.1 hp)
      (relativeLine B (f.toLinearEquiv p).1 hq) := by
  let g : (relativeLine A p.1 hp).carrier →ₗ[ℝ]
      (relativeLine B (f.toLinearEquiv p).1 hq).carrier :=
    { toFun := fun x => ⟨(f.toLinearEquiv ⟨x.1,x.2.1⟩).1,
        (line_mem_transport f p hp hq ⟨x.1,x.2.1⟩).mp x.2⟩
      map_add' := fun x y => by
        apply Subtype.ext
        exact congrArg (fun z : B.carrier => z.1)
          (f.toLinearEquiv.map_add ⟨x.1,x.2.1⟩ ⟨y.1,y.2.1⟩)
      map_smul' := fun a x => by
        apply Subtype.ext
        exact congrArg (fun z : B.carrier => z.1)
          (f.toLinearEquiv.map_smul a ⟨x.1,x.2.1⟩) }
  have hg : Function.Bijective g := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      have hval := congrArg (fun z : (relativeLine B (f.toLinearEquiv p).1 hq).carrier => z.1) hxy
      have he : f.toLinearEquiv ⟨x.1,x.2.1⟩ = f.toLinearEquiv ⟨y.1,y.2.1⟩ :=
        Subtype.ext hval
      exact congrArg (fun z : A.carrier => z.1) (f.toLinearEquiv.injective he)
    · intro z
      let y := f.toLinearEquiv.symm ⟨z.1,z.2.1⟩
      have hy : f.toLinearEquiv y = ⟨z.1,z.2.1⟩ := f.toLinearEquiv.apply_symm_apply _
      refine ⟨⟨y.1, (line_mem_transport f p hp hq y).mpr (by rw [hy]; exact z.2)⟩, ?_⟩
      exact Subtype.ext (congrArg (fun w : B.carrier => w.1) hy)
  exact ⟨LinearEquiv.ofBijective g hg, Subtype.ext (congrArg (fun z : B.carrier => z.1) f.map_unit),
    fun x y => Subtype.ext (f.map_jordanMul_eq ⟨x.1,x.2.1⟩ ⟨y.1,y.2.1⟩)⟩

private def diagonalLineCoordinates (k : CDLevel) :
    (relativeLine (H3Subalgebra k) (diagAtom 0) (diagAtom_isAtom 0)).carrier ≃ₗ[ℝ]
      (Fin 3 → ℝ) × (octSubalgebraOfLevel k).carrier where
  toFun x := (x.1.1, ⟨x.1.2 2, x.2.1.2.2⟩)
  invFun x := ⟨(x.1, ![0, 0, x.2.1]),
    ⟨⟨(octSubalgebraOfLevel k).carrier.zero_mem, (octSubalgebraOfLevel k).carrier.zero_mem, x.2.2⟩,
      (mem_lineSubalgebra_diagAtom0 _).mpr ⟨rfl,rfl⟩⟩⟩
  left_inv x := by
    obtain ⟨h0, h1⟩ := (mem_lineSubalgebra_diagAtom0 x.1).mp x.2.2
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext i
      fin_cases i
      · exact h0.symm
      · exact h1.symm
      · rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Each ambient line is unital Jordan-isomorphic to the standard block line. -/
theorem relativeLine_standardIso (k : CDLevel) {q : Albert} (hq : IsAtom q)
    (hqA : q ∈ (H3Subalgebra k).carrier) :
    Nonempty (JordanSubalgebraIso (relativeLine (H3Subalgebra k) q hq)
      (relativeLine (H3Subalgebra k) (diagAtom 0) (diagAtom_isAtom 0))) := by
  obtain ⟨f,hf⟩ := h3AtomToStandard k hq hqA
  let p : (H3Subalgebra k).carrier := ⟨q,hqA⟩
  have hf' : (f.toLinearEquiv p).1 = diagAtom 0 := hf
  have hq' : IsAtom (f.toLinearEquiv p).1 := hf'.symm ▸ diagAtom_isAtom 0
  have hi : Nonempty (JordanSubalgebraIso (relativeLine (H3Subalgebra k) q hq)
      (relativeLine (H3Subalgebra k) (f.toLinearEquiv p).1 hq')) :=
    ⟨relativeLineIso f p hq hq'⟩
  rwa [relativeLine_congr (H3Subalgebra k) hf hq' (diagAtom_isAtom 0)] at hi

theorem relativeLine_finrank (k : CDLevel) {q : Albert} (hq : IsAtom q)
    (hqA : q ∈ (H3Subalgebra k).carrier) :
    Module.finrank ℝ (relativeLine (H3Subalgebra k) q hq).carrier =
      3 + Module.finrank ℝ (octSubalgebraOfLevel k).carrier := by
  let : Module.Finite ℝ Octonion :=
    inferInstanceAs (FiniteDimensional ℝ (Quaternion ℝ × Quaternion ℝ))
  obtain ⟨f⟩ := relativeLine_standardIso k hq hqA
  rw [f.toLinearEquiv.finrank_eq, (diagonalLineCoordinates k).finrank_eq, Module.finrank_prod]
  simp

private def complexConjugateCopyIso (U : Matrix.unitaryGroup (Fin 3) ℂ) :
    JordanSubalgebraIso (H3Subalgebra .R)
      (unitaryConjSubalgebraC U (H3Subalgebra .R)) := by
  let A := H3Subalgebra .C
  let B := H3Subalgebra .R
  let C := unitaryConjSubalgebraC U B
  let ψ : JordanSubalgebraIso A A :=
    assocCD_unitaryIso assocCD_C U.1
      (Matrix.mem_unitaryGroup_iff'.mp U.prop) (Matrix.mem_unitaryGroup_iff.mp U.prop)
  have hBA : B.carrier ≤ A.carrier := H3Subalgebra_mono (by decide)
  let forward : C.carrier →ₗ[ℝ] B.carrier :=
    { toFun := fun x => ⟨(ψ.toLinearEquiv ⟨x.1,x.2.1⟩).1, x.2.2⟩
      map_add' := fun x y => by
        apply Subtype.ext
        exact congrArg (fun z : A.carrier => z.1)
          (ψ.toLinearEquiv.map_add ⟨x.1,x.2.1⟩ ⟨y.1,y.2.1⟩)
      map_smul' := fun a x => by
        apply Subtype.ext
        exact congrArg (fun z : A.carrier => z.1)
          (ψ.toLinearEquiv.map_smul a ⟨x.1,x.2.1⟩) }
  let equiv : C.carrier ≃ₗ[ℝ] B.carrier := LinearEquiv.ofBijective forward (by
    constructor
    · intro x y hxy
      apply Subtype.ext
      have hval := congrArg (fun z : B.carrier => z.1) hxy
      have he : ψ.toLinearEquiv ⟨x.1,x.2.1⟩ = ψ.toLinearEquiv ⟨y.1,y.2.1⟩ :=
        Subtype.ext hval
      exact congrArg (fun z : A.carrier => z.1) (ψ.toLinearEquiv.injective he)
    · intro z
      let w := ψ.toLinearEquiv.symm ⟨z.1, hBA z.2⟩
      have hy : ψ.toLinearEquiv w = ⟨z.1, hBA z.2⟩ := ψ.toLinearEquiv.apply_symm_apply _
      exact ⟨⟨w.1, w.2, by change (ψ.toLinearEquiv w).1 ∈ B.carrier; rw [hy]; exact z.2⟩,
        Subtype.ext (congrArg (fun v : A.carrier => v.1) hy)⟩)
  exact (⟨equiv,
    Subtype.ext (congrArg (fun z : A.carrier => z.1) ψ.map_unit),
    fun x y => Subtype.ext (ψ.map_jordanMul_eq ⟨x.1,x.2.1⟩ ⟨y.1,y.2.1⟩)⟩ :
      JordanSubalgebraIso C B).symm

private theorem h3Copy_pullback_atom {k : CDLevel} {B : NativeJordanSubalgebra}
    (ψ : JordanSubalgebraIso (H3Subalgebra k) B) (q : B.carrier) (hq : IsAtom q.1) :
    IsAtom (ψ.toLinearEquiv.symm q).1 := by
  let A := H3Subalgebra k
  let p := ψ.toLinearEquiv.symm q
  have hqp : ψ.toLinearEquiv p = q := ψ.toLinearEquiv.apply_symm_apply q
  have hp_id : jordanMul p.1 p.1 = p.1 := by
    have hm := ψ.symm.map_jordanMul_eq q q
    rw [show (⟨jordanMul q.1 q.1, B.product_mem _ q.2 _ q.2⟩ : B.carrier) = q
      from Subtype.ext hq.1] at hm
    exact hm.symm
  have hunit : albertTrace albertUnit = 3 := by simp [albertTrace, albertUnit]
  rcases idempotent_dichotomy p.1 hp_id with ⟨h0,_⟩ | ⟨ha,_⟩ | ⟨⟨r,hr,hpr⟩,_⟩ | ⟨h1,_⟩
  · have hz : p = 0 := Subtype.ext h0
    rw [hz, map_zero] at hqp
    have hq0 : q.1 = 0 := congrArg Subtype.val hqp.symm
    have hh := hq.2
    rw [hq0] at hh
    have hztrace : albertTrace (0 : Albert) = 0 := by
      simp only [albertTrace, Fin.sum_univ_three]
      change (0 : ℝ) + 0 + 0 = 0
      norm_num
    rw [hztrace] at hh
    norm_num at hh
  · exact ha
  · have he : albertUnit - p.1 = r := by rw [hpr]; abel
    have hrA : r ∈ A.carrier := he ▸ A.carrier.sub_mem A.unit_mem p.2
    have hrq : (ψ.toLinearEquiv ⟨r,hrA⟩).1 = albertUnit - q.1 := by
      rw [show (⟨r,hrA⟩ : A.carrier) = ⟨albertUnit,A.unit_mem⟩ - p from Subtype.ext he.symm,
        map_sub, ψ.map_unit, hqp]
      rfl
    have ha := (iso_maps_atom ψ ⟨r,hrA⟩ hr).2
    rw [hrq, albertTrace_sub, hunit, hq.2] at ha
    norm_num at ha
  · have he : p = ⟨albertUnit,A.unit_mem⟩ := Subtype.ext h1
    rw [he, ψ.map_unit] at hqp
    have hq1 : q.1 = albertUnit := congrArg Subtype.val hqp.symm
    have hh := hq.2
    rw [hq1,hunit] at hh
    norm_num at hh

private theorem line_not_le_h3Copy {k j : CDLevel} {B : NativeJordanSubalgebra}
    (h : Module.finrank ℝ (octSubalgebraOfLevel j).carrier <
      Module.finrank ℝ (octSubalgebraOfLevel k).carrier)
    (ψ : JordanSubalgebraIso (H3Subalgebra j) B)
    (hBA : B.carrier ≤ (H3Subalgebra k).carrier)
    {q : Albert} (hq : IsAtom q) (hqA : q ∈ (H3Subalgebra k).carrier) :
    ¬ (relativeLine (H3Subalgebra k) q hq).carrier ≤ B.carrier := by
  intro hle
  let p : B.carrier := ⟨q, hle (atom_mem_relativeLine hq hqA)⟩
  let x := ψ.toLinearEquiv.symm p
  have hx : IsAtom x.1 := h3Copy_pullback_atom ψ p hq
  have hxp : (ψ.toLinearEquiv x).1 = q :=
    congrArg Subtype.val (ψ.toLinearEquiv.apply_symm_apply p)
  have hy : IsAtom (ψ.toLinearEquiv x).1 := hxp.symm ▸ hq
  have hdim := (relativeLineIso ψ x hx hy).toLinearEquiv.finrank_eq
  rw [relativeLine_congr B hxp hy hq, relativeLine_finrank j hx x.2] at hdim
  have heq : relativeLine B q hq = relativeLine (H3Subalgebra k) q hq := by
    apply nativeJordanSubalgebra_ext
    exact le_antisymm (fun _ hz => ⟨hBA hz.1,hz.2⟩) (fun _ hz => ⟨hle hz,hz.2⟩)
  rw [heq, relativeLine_finrank k hq hqA] at hdim
  omega

def precedingCDLevel : CDLevel → CDLevel
  | .R => .R
  | .C => .R
  | .H => .C
  | .O => .H

/-- The previous scalar level in the table of maximal proper subalgebras. -/
def IsPrecedingRankThreeCopy (k : CDLevel) (B : NativeJordanSubalgebra) : Prop :=
  k ≠ .R ∧ Nonempty (JordanSubalgebraIso (H3Subalgebra (precedingCDLevel k)) B)

/-- Maximality among the actual proper native unital subalgebras of a fixed ambient algebra. -/
def IsMaximalProperNative (A B : NativeJordanSubalgebra) : Prop :=
  B.carrier < A.carrier ∧
    ∀ C : NativeJordanSubalgebra, B.carrier ≤ C.carrier → C.carrier < A.carrier → B = C

private theorem maximalContainment (k : CDLevel) (B : NativeJordanSubalgebra)
    (hB : B.carrier < (H3Subalgebra k).carrier) :
    (∃ (q : Albert) (hq : IsAtom q), q ∈ (H3Subalgebra k).carrier ∧
      B.carrier ≤ (relativeLine (H3Subalgebra k) q hq).carrier) ∨
    (∃ C : NativeJordanSubalgebra, C.carrier ≤ (H3Subalgebra k).carrier ∧
      IsPrecedingRankThreeCopy k C ∧ B.carrier ≤ C.carrier) := by
  rcases lem_five_sub k B hB with ⟨q,hq,hqA,hline⟩ | hcopy
  · exact Or.inl ⟨q,hq,hqA,le_inf hB.le hline⟩
  right
  cases k with
  | R => exact False.elim hcopy
  | C =>
    obtain ⟨U,hU⟩ := hcopy
    refine ⟨unitaryConjSubalgebraC U (H3Subalgebra .R), ?_, ⟨by decide, ⟨complexConjugateCopyIso U⟩⟩, hU⟩
    intro x hx
    obtain ⟨hxA, _⟩ := hx
    exact hxA
  | H =>
    obtain ⟨C,hCA,hiso,hBC⟩ := hcopy
    exact ⟨C,hCA,⟨by decide,hiso⟩,hBC⟩
  | O =>
    obtain ⟨C,hiso,hBC⟩ :=
      (quaternionicContainment_iff_iso (B.carrier : Set Albert)).mp hcopy
    exact ⟨C, by rw [H3Subalgebra_O_eq_top]; exact fun _ _ => trivial, ⟨by decide,hiso⟩, hBC⟩

private theorem relativeLine_proper (k : CDLevel) {q : Albert} (hq : IsAtom q)
    (hqA : q ∈ (H3Subalgebra k).carrier) :
    (relativeLine (H3Subalgebra k) q hq).carrier < (H3Subalgebra k).carrier := by
  refine lt_of_le_of_ne inf_le_left ?_
  intro he
  have hd := relativeLine_finrank k hq hqA
  rw [he,finrank_H3Subalgebra,octSubalgebraOfLevel_finrank] at hd
  cases k <;> norm_num at hd

private theorem precedingCopy_proper (k : CDLevel) (B : NativeJordanSubalgebra)
    (hBA : B.carrier ≤ (H3Subalgebra k).carrier) (hB : IsPrecedingRankThreeCopy k B) :
    B.carrier < (H3Subalgebra k).carrier := by
  obtain ⟨hne,⟨ψ⟩⟩ := hB
  refine lt_of_le_of_ne hBA ?_
  intro he
  have hd := ψ.toLinearEquiv.finrank_eq
  rw [he,finrank_H3Subalgebra,finrank_H3Subalgebra] at hd
  cases k <;> simp_all [precedingCDLevel]

/-- The four rows of the companion's maximal proper subalgebra table, in both directions. -/
theorem maximalProperNative_iff (k : CDLevel) (B : NativeJordanSubalgebra)
    (hBA : B.carrier ≤ (H3Subalgebra k).carrier) :
    IsMaximalProperNative (H3Subalgebra k) B ↔
      (∃ (q : Albert) (hq : IsAtom q), q ∈ (H3Subalgebra k).carrier ∧
        B = relativeLine (H3Subalgebra k) q hq) ∨ IsPrecedingRankThreeCopy k B := by
  let : Module.Finite ℝ Octonion :=
    inferInstanceAs (FiniteDimensional ℝ (Quaternion ℝ × Quaternion ℝ))
  let : Module.Finite ℝ Albert :=
    inferInstanceAs (FiniteDimensional ℝ ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
  constructor
  · rintro ⟨hB,hmax⟩
    rcases maximalContainment k B hB with ⟨q,hq,hqA,hline⟩ | ⟨C,hCA,hiso,hBC⟩
    · exact Or.inl ⟨q,hq,hqA,hmax _ hline (relativeLine_proper k hq hqA)⟩
    · right
      rwa [hmax C hBC (precedingCopy_proper k C hCA hiso)]
  · rintro (⟨q,hq,hqA,rfl⟩ | hcopy)
    · refine ⟨relativeLine_proper k hq hqA, ?_⟩
      intro C hLC hCA
      rcases maximalContainment k C hCA with ⟨r,hr,hrA,hrC⟩ | ⟨D,hDA,⟨hne,⟨ψ⟩⟩,hCD⟩
      · have he : (relativeLine (H3Subalgebra k) q hq).carrier =
            (relativeLine (H3Subalgebra k) r hr).carrier := by
          apply Submodule.eq_of_le_of_finrank_le (hLC.trans hrC)
          rw [relativeLine_finrank k hq hqA, relativeLine_finrank k hr hrA]
        exact nativeJordanSubalgebra_ext (le_antisymm hLC (he.symm ▸ hrC))
      · exact (line_not_le_h3Copy (by
          rw [octSubalgebraOfLevel_finrank,octSubalgebraOfLevel_finrank]
          cases k <;> simp_all [precedingCDLevel]) ψ hDA hq hqA (hLC.trans hCD)).elim
    · refine ⟨precedingCopy_proper k B hBA hcopy, ?_⟩
      intro C hBC hCA
      rcases maximalContainment k C hCA with ⟨q,hq,_,hline⟩ | ⟨D,_,hD,hCD⟩
      · exact (h3Copy_not_le_line _ B hcopy.2 q hq
          (hBC.trans (hline.trans inf_le_right))).elim
      · obtain ⟨ψ⟩ := hcopy.2
        obtain ⟨φ⟩ := hD.2
        have hBD : B.carrier = D.carrier := by
          apply Submodule.eq_of_le_of_finrank_le (hBC.trans hCD)
          rw [← ψ.toLinearEquiv.finrank_eq, ← φ.toLinearEquiv.finrank_eq]
        exact nativeJordanSubalgebra_ext (le_antisymm hBC (hBD.symm ▸ hCD))

end AlbertSequential
