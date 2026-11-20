module

import PrintedLineCoordinates
import PrintedSlotLaws
import NativeCornerSpinorReflections

open AlbertSequential AlbertSequential.NativeAnalysis

noncomputable section

example (q : Albert) (hq : IsAtom q) (x : (lineSubalgebra q hq).carrier) :
    (lineSubalgebra q hq).restrictedProduct.IsPrimitive x ↔
      (x : Albert) = q ∨ (IsAtom (x : Albert) ∧ jordanMul q (x : Albert) = 0) :=
  lineSubalgebra_primitive_iff q hq x

example (q a b : Albert) (hq : IsAtom q) (ha : IsAtom a) (hb : IsAtom b)
    (hqa : jordanMul q a = 0) (hqb : jordanMul q b = 0) :
    let f := albertUnit - q
    let u := (2 : ℝ) • a - f
    let v := (2 : ℝ) • b - f
    tracePairing a b = (2 + tracePairing u v) / 4 ∧
      a + b - (2 : ℝ) • jordanMul a b = (1 - tracePairing a b) • f :=
  ⟨lineAtom_centered_pairing q a b hq ha hb hqa hqb, lineAtom_support_raw q a b hq ha hb hqa hqb⟩

example {k : CDLevel} (α : JordanSubalgebraIso (H3Subalgebra k) (H3Subalgebra k))
    (q p r : (H3Subalgebra k).carrier) (hq : IsAtom q.val)
    (hαq : (α.toLinearEquiv q).val = diagAtom 1)
    (hαr : (α.toLinearEquiv r).val = diagAtom 2) :
    (α.toLinearEquiv p).val.1 1 = tracePairing p.val q.val ∧
    (α.toLinearEquiv (⟨albertUnit, (H3Subalgebra k).unit_mem⟩ - q - r)).val = diagAtom 0 :=
  ⟨lineNormalForm_overlap α q p hq hαq, lineNormalForm_remainder α q r hαq hαr⟩

example (q p : Albert) (hq : IsAtom q) (hp : IsAtom p)
    (h : p ∉ (lineSubalgebra q hq).carrier) :
    0 < tracePairing p q ∧ tracePairing p q < 1 ∧
      albertTrace (quadraticMap (albertUnit - q) p) = 1 - tracePairing p q :=
  lineOffAtom_compression_trace q p hq hp h

example (q : Albert) (hq : IsAtom q) (u v : nativePeirceZero q)
    (hu : albertTrace u = 0) (hv : albertTrace v = 0) :
    jordanMul u v = (tracePairing u v / 2) • (albertUnit - q) :=
  congrArg Subtype.val (nativeCorner_traceless_product q hq u v hu hv)

example (q p : Albert) (hq : IsAtom q) (hp : IsAtom p)
    (h : p ∉ (lineSubalgebra q hq).carrier) :
    let f := albertUnit - q
    let w := quadraticMap f p
    let r := (albertTrace w)⁻¹ • w
    ∃ F : NativeJordanFrame, F.atom = ![f - r, q, r] :=
  lineOffAtom_normalized_frame q p hq hp h

#print axioms nativeCorner_traceless_product
#print axioms lineOffAtom_normalized_frame
#print axioms mem_lineSubalgebra_iff_scalar_add_corner
#print axioms lineSubalgebra_primitive_iff
#print axioms lineAtom_centered_coordinates
#print axioms lineAtom_centered_pairing
#print axioms lineAtom_support_raw
#print axioms atom_slot_norms
#print axioms lineNormalForm_overlap
#print axioms lineNormalForm_remainder
#print axioms lineOffAtom_compression_trace
#print axioms peirce01_extract
#print axioms peirce02_extract
#print axioms peirce12_extract
#print axioms cyclicSlot_coefficientSubalgebra
#print axioms lem_five_coord_gen
#print axioms lem_five_line
