/- SPDX-License-Identifier: Apache-2.0 -/
module

public import SubalgebraCoordsAndLine
public import SuppliedEmbeddingStateTransport
import Bridge.Atoms
public import NativeCornerSpectralCoordinates

/-! Literal scalar and primitive-idempotent consequences of the Appendix E line calculations. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace AlbertSequential

open NativeAnalysis

private theorem lineAtom_self_pairing (q : Albert) (hq : IsAtom q) : tracePairing q q = 1 := by
  unfold tracePairing
  rw [hq.1, hq.2]

private theorem linePairing_zero_of_mul_zero {q x : Albert} (h : jordanMul q x = 0) :
    tracePairing q x = 0 := by rw [tracePairing, h, albertTrace_zero]

private theorem lineComplement_mul (q x : Albert) (hx : jordanMul q x = 0) :
    jordanMul (albertUnit - q) x = x := by
  rw [jordanMul_sub_left, jordanMul_albertUnit_left, hx, sub_zero]

/-- The native line algebra is the sum of the atom scalar and its zero Peirce space. -/
theorem mem_lineSubalgebra_iff_scalar_add_corner (q : Albert) (hq : IsAtom q) (x : Albert) :
    x ∈ (lineSubalgebra q hq).carrier ↔
      ∃ (t : ℝ) (y : nativePeirceZero q), x = t • q + (y : Albert) := by
  constructor
  · intro h
    let t := tracePairing q x
    have he := (mem_lineSubalgebra_iff q hq x).mp h
    have hy : jordanMul q (x - t • q) = 0 := by rw [jordanMul_sub_right, jordanMul_smul_right, hq.1, he, sub_self]
    exact ⟨t, ⟨x - t • q, hy⟩, by change x = t • q + (x - t • q); abel⟩
  · rintro ⟨t, y, rfl⟩
    have hy := (mem_nativePeirceZero _ _).mp y.property
    rw [mem_lineSubalgebra_iff, jordanMul_add_right, jordanMul_smul_right, hq.1, hy,
      tracePairing_add_right, tracePairing_smul_right, lineAtom_self_pairing q hq,
      linePairing_zero_of_mul_zero hy, mul_one]
    simp only [add_zero]

private theorem corner_mem_lineSubalgebra {q x : Albert} (hq : IsAtom q) (hx : jordanMul q x = 0) :
    x ∈ (lineSubalgebra q hq).carrier :=
  (mem_lineSubalgebra_iff_scalar_add_corner q hq x).mpr ⟨0, ⟨x, hx⟩, by simp⟩

private theorem self_mem_lineSubalgebra (q : Albert) (hq : IsAtom q) :
    q ∈ (lineSubalgebra q hq).carrier := by
  rw [mem_lineSubalgebra_iff, hq.1, lineAtom_self_pairing q hq, one_smul]

/-- A primitive of the literal line algebra is precisely the pole or a native atom on its line. -/
theorem lineSubalgebra_primitive_iff (q : Albert) (hq : IsAtom q) (x : (lineSubalgebra q hq).carrier) :
    (lineSubalgebra q hq).restrictedProduct.IsPrimitive x ↔
      (x : Albert) = q ∨ (IsAtom (x : Albert) ∧ jordanMul q (x : Albert) = 0) := by
  let B := lineSubalgebra q hq
  let P := B.restrictedProduct
  have ha : P.IsPrimitive x ↔ IsAtom (x : Albert) := by
    constructor
    · obtain ⟨x, hxB⟩ := x
      rintro ⟨hi, hn, hs⟩
      have hx : jordanMul x x = x := congrArg Subtype.val hi
      have hx_ne : x ≠ 0 := fun he => hn (Subtype.ext he)
      have hsplit (v w : Albert) (hv : v ∈ B.carrier) (hw : w ∈ B.carrier)
          (hiv : jordanMul v v = v) (hiw : jordanMul w w = w)
          (hvw : jordanMul v w = 0) (he : v + w = x) : v = 0 ∨ w = 0 := by
        rcases hs ⟨v, hv⟩ ⟨w, hw⟩ (Subtype.ext hiv) (Subtype.ext hiw) (Subtype.ext hvw)
          (Subtype.ext he) with h | h
        · exact Or.inl (congrArg Subtype.val h)
        · exact Or.inr (congrArg Subtype.val h)
      let t := tracePairing q x
      have ht : jordanMul q x = t • q := (mem_lineSubalgebra_iff _ _ _).mp hxB
      have hts : t = t * t := by
        change tracePairing q x = t * t
        rw [← hx, ← tracePairing_associative, ht, tracePairing_smul_left]
      have hz : t = 0 ∨ t = 1 := by
        have hmul : t * (t - 1) = 0 := by nlinarith [hts]
        exact (mul_eq_zero.mp hmul).imp id sub_eq_zero.mp
      rcases hz with hz | hz
      · have hqx : jordanMul q x = 0 := by rw [ht, hz, zero_smul]
        let f := albertUnit - q
        have hfx : jordanMul f x = x := lineComplement_mul q x hqx
        have hxf : jordanMul x f = x := (jordanMul_comm x f).trans hfx
        have hf : jordanMul f f = f := complementary_idempotent q hq.1
        have hftr : albertTrace f = 2 := by unfold f; rw [albertTrace_sub, albertTrace_unit, hq.2]; norm_num
        have hcomp : jordanMul (f - x) (f - x) = f - x := by
          simp only [jordanMul_sub_left, jordanMul_sub_right, hf, hfx, hxf, hx]
          abel
        have ht₀ : 0 ≤ albertTrace (f - x) := isPositive_trace_nonnegative _ (isPositive_idempotent _ hcomp)
        rw [albertTrace_sub, hftr] at ht₀
        rcases native_idempotent_trace_cases x hx with h0 | h1 | h2 | h3
        · exact (hx_ne ((isPositive_trace_eq_zero _ (isPositive_idempotent _ hx)).mp h0)).elim
        · exact ⟨hx, h1⟩
        · have he : f - x = 0 := by
            apply (isPositive_trace_eq_zero _ (isPositive_idempotent _ hcomp)).mp
            rw [albertTrace_sub, hftr, h2, sub_self]
          obtain ⟨v, w, hv, hw, hvw, hsum, _⟩ :=
            nativeCorner_spectralAtoms q hq (nativeCornerUnit q hq.1)
          have heq : (v : Albert) + (w : Albert) = x :=
            (congrArg Subtype.val hsum).trans (sub_eq_zero.mp he)
          rcases hsplit v w (corner_mem_lineSubalgebra hq v.property)
            (corner_mem_lineSubalgebra hq w.property) hv.1 hw.1 hvw heq with h | h
          · exact ((NativeAnalysis.isAtom_iff_primitive _).mp hv).2.1 h |>.elim
          · exact ((NativeAnalysis.isAtom_iff_primitive _).mp hw).2.1 h |>.elim
        · linarith
      · have hqx : jordanMul q x = q := by rw [ht, hz, one_smul]
        have hxq := (jordanMul_comm x q).trans hqx
        have hr : jordanMul q (x - q) = 0 := by rw [jordanMul_sub_right, hqx, hq.1, sub_self]
        have he : jordanMul (x - q) (x - q) = x - q := by
          simp only [jordanMul_sub_left, jordanMul_sub_right, hx, hqx, hxq, hq.1]
          abel
        rcases hsplit q (x-q) (self_mem_lineSubalgebra q hq)
          (corner_mem_lineSubalgebra hq hr) hq.1 he hr (by abel) with hz | hz
        · exact ((NativeAnalysis.isAtom_iff_primitive _).mp hq).2.1 hz |>.elim
        · change IsAtom x
          rwa [sub_eq_zero.mp hz]
    · intro h
      obtain ⟨hi, hn, hs⟩ := (NativeAnalysis.isAtom_iff_primitive x.val).mp h
      refine ⟨Subtype.ext hi, fun hz => hn (congrArg Subtype.val hz), ?_⟩
      intro r s hr hs' horth hsum
      by_contra hc
      push Not at hc
      exact hs ⟨r.val, s.val, congrArg Subtype.val hr, congrArg Subtype.val hs',
        fun hz => hc.1 (Subtype.ext hz), fun hz => hc.2 (Subtype.ext hz),
        congrArg Subtype.val horth, (congrArg Subtype.val hsum).symm⟩
  rw [ha]
  constructor
  · intro hx
    exact (atom_of_mem_lineSubalgebra hq hx x.property).imp id (fun h => ⟨hx, h⟩)
  · rintro (h | h)
    · rwa [h]
    · exact h.1

/-- Actual centered atom coordinate in the line and its trace normalization. -/
theorem lineAtom_centered_coordinates (q a : Albert) (hq : IsAtom q) (ha : IsAtom a)
    (hqa : jordanMul q a = 0) :
    let u := (2 : ℝ) • a - (albertUnit - q)
    jordanMul q u = 0 ∧ albertTrace u = 0 ∧ a = (1 / 2 : ℝ) • ((albertUnit - q) + u) := by
  intro u
  refine ⟨?_, ?_, ?_⟩
  · change jordanMul q ((2 : ℝ) • a - (albertUnit - q)) = 0
    rw [jordanMul_sub_right, jordanMul_smul_right, hqa, smul_zero, jordanMul_sub_right,
      jordanMul_albertUnit_right, hq.1, sub_self, sub_zero]
  · change albertTrace ((2 : ℝ) • a - (albertUnit - q)) = 0
    rw [albertTrace_sub, albertTrace_sub, albertTrace_smul, albertTrace_unit, ha.2, hq.2]
    norm_num
  · dsimp only [u]
    module

/-- The pairing in the two centered coordinates has the displayed constant two. -/
theorem lineAtom_centered_pairing (q a b : Albert) (hq : IsAtom q) (ha : IsAtom a) (hb : IsAtom b)
    (hqa : jordanMul q a = 0) (hqb : jordanMul q b = 0) :
    let f := albertUnit - q
    let u := (2 : ℝ) • a - f
    let v := (2 : ℝ) • b - f
    tracePairing a b = (2 + tracePairing u v) / 4 := by
  intro f u v
  have hfa : tracePairing f a = 1 := by
    change tracePairing (albertUnit - q) a = 1
    rw [tracePairing_sub_left, tracePairing_comm albertUnit, tracePairing_unit_right,
      ha.2, linePairing_zero_of_mul_zero hqa, sub_zero]
  have hfb : tracePairing f b = 1 := by
    change tracePairing (albertUnit - q) b = 1
    rw [tracePairing_sub_left, tracePairing_comm albertUnit, tracePairing_unit_right,
      hb.2, linePairing_zero_of_mul_zero hqb, sub_zero]
  have hff : tracePairing f f = 2 := by
    change albertTrace (jordanMul (albertUnit-q) (albertUnit-q)) = 2
    rw [complementary_idempotent q hq.1, albertTrace_sub, albertTrace_unit, hq.2]
    norm_num
  have hraw (w : Albert) :
      tracePairing ((2 : ℝ) • a - w) ((2 : ℝ) • b - w) =
        4 * tracePairing a b - 2 * tracePairing a w - 2 * tracePairing w b + tracePairing w w := by
    simp only [tracePairing_sub_left, tracePairing_sub_right, tracePairing_smul_left,
      tracePairing_smul_right]
    ring
  change tracePairing a b = (2 + tracePairing ((2 : ℝ) • a - f) ((2 : ℝ) • b - f)) / 4
  rw [hraw, tracePairing_comm a f, hfa, hfb, hff]
  ring

/-- The un-divided support calculation holds also when the two atoms coincide. -/
theorem lineAtom_support_raw (q a b : Albert) (hq : IsAtom q) (ha : IsAtom a) (hb : IsAtom b)
    (hqa : jordanMul q a = 0) (hqb : jordanMul q b = 0) :
    a + b - (2 : ℝ) • jordanMul a b = (1 - tracePairing a b) • (albertUnit - q) := by
  by_cases hab : a = b
  · subst b
    rw [ha.1, lineAtom_self_pairing a ha, sub_self, zero_smul, two_smul, sub_self]
  · obtain ⟨hlt, he⟩ := eq_fiv_support q a b hq ha hb hqa hqb hab
    have h := congrArg (fun x : Albert => (1 - tracePairing a b) • x) he
    rw [smul_smul, mul_inv_cancel₀ (sub_ne_zero.mpr hlt.ne'), one_smul] at h
    exact h.symm

/-- The three literal off-diagonal squared norms of a native atom. -/
theorem atom_slot_norms (p : Albert) (hp : IsAtom p) :
    octNormSq (p.2 0) = p.1 0 * p.1 1 ∧
    octNormSq (p.2 1) = p.1 0 * p.1 2 ∧
    octNormSq (p.2 2) = p.1 1 * p.1 2 := by
  have h := albertSharp_of_isAtom hp
  have he (i : Fin 3) := congrArg (fun z : Albert => z.1 i) h
  have h₀ := he 0
  have h₁ := he 1
  have h₂ := he 2
  change p.1 1 * p.1 2 - octNormSq (p.2 2) = 0 at h₀
  change p.1 0 * p.1 2 - octNormSq (p.2 1) = 0 at h₁
  change p.1 0 * p.1 1 - octNormSq (p.2 0) = 0 at h₂
  exact ⟨(sub_eq_zero.mp h₂).symm, (sub_eq_zero.mp h₁).symm, (sub_eq_zero.mp h₀).symm⟩

/-- A unital Jordan isomorphism taking the pole to the second diagonal atom
identifies the actual overlap with the second diagonal coordinate. -/
theorem lineNormalForm_overlap {k : CDLevel} (α : JordanSubalgebraIso (H3Subalgebra k) (H3Subalgebra k))
    (q p : (H3Subalgebra k).carrier) (hq : IsAtom q.val)
    (hαq : (α.toLinearEquiv q).val = diagAtom 1) :
    (α.toLinearEquiv p).val.1 1 = tracePairing p.val q.val := by
  have hmem : quadraticMap q.val p.val ∈ (H3Subalgebra k).carrier := by
    rw [quadraticMap_atom _ _ hq]
    exact (H3Subalgebra k).carrier.smul_mem _ q.property
  have h := α.map_quadraticMap q p
  have hqeq : (⟨quadraticMap q.val p.val, hmem⟩ : (H3Subalgebra k).carrier) =
      tracePairing q.val p.val • q := Subtype.ext (quadraticMap_atom _ _ hq)
  rw [hqeq, map_smul, Submodule.coe_smul, hαq, quadraticMap_atom _ _ (diagAtom_isAtom 1),
    tracePairing_diagAtom] at h
  have ho := congrArg (fun x : Albert => x.1 1) h
  change tracePairing q.val p.val * 1 = (α.toLinearEquiv p).val.1 1 * 1 at ho
  rw [mul_one, mul_one] at ho
  exact ho.symm.trans (tracePairing_comm _ _)

/-- The third frame coordinate is forced by the two displayed diagonal coordinates. -/
theorem lineNormalForm_remainder {k : CDLevel} (α : JordanSubalgebraIso (H3Subalgebra k) (H3Subalgebra k))
    (q r : (H3Subalgebra k).carrier) (hαq : (α.toLinearEquiv q).val = diagAtom 1)
    (hαr : (α.toLinearEquiv r).val = diagAtom 2) :
    (α.toLinearEquiv (⟨albertUnit, (H3Subalgebra k).unit_mem⟩ - q - r)).val = diagAtom 0 := by
  rw [map_sub, map_sub, α.map_unit, Submodule.coe_sub, Submodule.coe_sub, hαq, hαr]
  have hs := diagAtom_sum_eq_unit
  rw [Fin.sum_univ_three] at hs
  change albertUnit - diagAtom 1 - diagAtom 2 = diagAtom 0
  rw [← hs]
  abel

/-- The native off-line compression has the paper's exact trace and a positive denominator. -/
theorem lineOffAtom_compression_trace (q p : Albert) (hq : IsAtom q) (hp : IsAtom p)
    (hp_off : p ∉ (lineSubalgebra q hq).carrier) :
    let a := tracePairing p q
    0 < a ∧ a < 1 ∧ albertTrace (quadraticMap (albertUnit - q) p) = 1 - a := by
  intro a
  have hb := atom_tracePairing_bounds p q hp hq
  have h₀ : a ≠ 0 := by
    intro h
    have h₁ : tracePairing q p = 0 := (tracePairing_comm p q).symm.trans h
    exact hp_off (corner_mem_lineSubalgebra hq ((atom_tracePairing_eq_zero_iff q p hq hp).mp h₁))
  have h₁ : a ≠ 1 := by
    intro h
    have he : p = q := (atom_tracePairing_eq_one_iff p q hp hq).mp h
    exact hp_off (he ▸ self_mem_lineSubalgebra q hq)
  refine ⟨lt_of_le_of_ne hb.1 h₀.symm, lt_of_le_of_ne hb.2 h₁, ?_⟩
  rw [← tracePairing_unit_right, quadraticMap_self_adjoint, quadraticMap_unit_argument,
    complementary_idempotent q hq.1, tracePairing_sub_right, tracePairing_unit_right, hp.2]

/-- The normalized compression and the two literal complements give the ordered frame in Appendix E. -/
theorem lineOffAtom_normalized_frame (q p : Albert) (hq : IsAtom q) (hp : IsAtom p)
    (hp_off : p ∉ (lineSubalgebra q hq).carrier) :
    let f := albertUnit - q
    let w := quadraticMap f p
    let r := (albertTrace w)⁻¹ • w
    ∃ F : NativeJordanFrame, F.atom = ![f - r, q, r] := by
  intro f w r
  let t := albertTrace w
  obtain ⟨_, hlt, htr⟩ := lineOffAtom_compression_trace q p hq hp hp_off
  have ht : 0 < t := by change 0 < albertTrace (quadraticMap (albertUnit - q) p); rw [htr]; linarith
  have hff : jordanMul f f = f := complementary_idempotent q hq.1
  have hpf : tracePairing p f = t := by
    change tracePairing p (albertUnit - q) = albertTrace (quadraticMap (albertUnit - q) p)
    rw [tracePairing_sub_right, tracePairing_unit_right, hp.2, htr]
  have hww : jordanMul w w = t • w := by
    change jordanMul (quadraticMap f p) (quadraticMap f p) = t • quadraticMap f p
    rw [← quadraticMap_unit_argument, quadraticMap_fundamental, quadraticMap_unit_argument, hff,
      quadraticMap_atom p f hp, hpf, quadraticMap_smul_right]
  have hr : IsAtom r := by
    refine ⟨?_, ?_⟩
    · change jordanMul (t⁻¹ • w) (t⁻¹ • w) = t⁻¹ • w
      rw [jordanMul_smul_left, jordanMul_smul_right, hww, smul_smul, smul_smul, mul_assoc, inv_mul_cancel₀ ht.ne', mul_one]
    · change albertTrace (t⁻¹ • w) = 1
      rw [albertTrace_smul, inv_mul_cancel₀ ht.ne']
  have hqr : jordanMul q r = 0 := by
    change jordanMul q (t⁻¹ • quadraticMap (albertUnit - q) p) = 0
    rw [jordanMul_smul_right, native_complement_quadratic_mem_zero q p hq.1, smul_zero]
  have hqf : jordanMul q f = 0 := by
    change jordanMul q (albertUnit-q) = 0
    rw [jordanMul_sub_right, jordanMul_albertUnit_right, hq.1, sub_self]
  have hfr : jordanMul f r = r := lineComplement_mul q r hqr
  have hrf : jordanMul r f = r := (jordanMul_comm _ _).trans hfr
  have hftr : albertTrace f = 2 := by unfold f; rw [albertTrace_sub, albertTrace_unit, hq.2]; norm_num
  have hfrAtom : IsAtom (f-r) := by
    constructor
    · simp only [jordanMul_sub_left, jordanMul_sub_right, hff, hfr, hrf, hr.1]
      abel
    · rw [albertTrace_sub, hftr, hr.2]
      norm_num
  have hqfr : jordanMul q (f-r) = 0 := by rw [jordanMul_sub_right, hqf, hqr, sub_self]
  have hrfr : jordanMul (f-r) r = 0 := by rw [jordanMul_sub_left, hfr, hr.1, sub_self]
  refine ⟨⟨![f-r,q,r], ?_, ?_, ?_⟩, rfl⟩
  · intro i
    fin_cases i
    · exact hfrAtom
    · exact hq
    · exact hr
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact (jordanMul_comm _ _).trans hqfr
    · exact hrfr
    · exact hqfr
    · exact (hij rfl).elim
    · exact hqr
    · exact (jordanMul_comm _ _).trans hrfr
    · exact (jordanMul_comm _ _).trans hqr
    · exact (hij rfl).elim
  · rw [Fin.sum_univ_three]
    change f-r+q+r = albertUnit
    dsimp only [f]
    abel

end AlbertSequential
