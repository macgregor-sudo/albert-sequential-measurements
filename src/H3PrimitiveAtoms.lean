/- SPDX-License-Identifier: Apache-2.0 -/
module

public import SubalgebraCoordsAndLine
public import SuppliedEmbeddingStateTransport
import Bridge.Atoms
import GeneralEJALowRankClassification
import NativeAlbertTableMixtures

public section
noncomputable section

namespace AlbertSequential

open scoped BigOperators

private theorem relativePrimitive_of_atom (B : NativeJordanSubalgebra) (p : B.carrier)
    (hp : IsAtom p.val) : B.restrictedProduct.IsPrimitive p := by
  obtain ⟨hi, hn, hs⟩ := (NativeAnalysis.isAtom_iff_primitive p.val).mp hp
  refine ⟨Subtype.ext hi, fun h => hn (congrArg Subtype.val h), ?_⟩
  intro r s hr hsr horth hsum
  by_contra h
  push Not at h
  exact hs ⟨r.val, s.val, congrArg Subtype.val hr, congrArg Subtype.val hsr,
    fun hz => h.1 (Subtype.ext hz), fun hz => h.2 (Subtype.ext hz),
    congrArg Subtype.val horth, (congrArg Subtype.val hsum).symm⟩

private theorem restrictedProduct_formallyReal (B : NativeJordanSubalgebra) : B.restrictedProduct.FormallyReal := by
  intro n x hx i
  apply Subtype.ext
  apply nativeAlbertProduct_formallyReal n (fun j => (x j).val) _ i
  have h := congrArg B.carrier.subtype hx
  rw [map_sum, map_zero] at h
  exact h

/-- The trace-one atom predicate in `Albert` agrees with intrinsic Jordan
primitivity in every standard rank-three Hermitian carrier. -/
theorem h3_primitive_iff_atom (k : CDLevel) (p : (H3Subalgebra k).carrier) :
    (H3Subalgebra k).restrictedProduct.IsPrimitive p ↔ IsAtom p.val := by
  let B := H3Subalgebra k
  let P := B.restrictedProduct
  change P.IsPrimitive p ↔ IsAtom p.val
  refine ⟨fun hp => ?_, relativePrimitive_of_atom B p⟩
  let : FiniteDimensional ℝ Albert := nativeAlbertModuleFinite
  let hfr := restrictedProduct_formallyReal B
  let τ := P.canonicalTraceOfFormallyReal hfr
  let d (i : Fin 3) : B.carrier := ⟨diagAtom i, diagAtom_mem_H3Subalgebra k i⟩
  have hd (i : Fin 3) : P.IsPrimitive (d i) := relativePrimitive_of_atom B (d i) (diagAtom_isAtom i)
  have hds : ∑ i, d i = P.unit := by
    apply Subtype.ext
    change B.carrier.subtype (∑ i, d i) = albertUnit
    rw [map_sum]
    exact diagAtom_sum_eq_unit
  have ht : τ P.unit = 3 := P.canonicalTrace_unit_eq_primitive_frame_length hfr d hd hds
  have htp : τ p = 1 := P.canonicalTraceOfFormallyReal_primitive hfr p hp
  have hcp : P.product (P.unit - p) (P.unit - p) = P.unit - p := by
    apply Subtype.ext
    exact NativeAnalysis.complementary_idempotent p.val (congrArg Subtype.val hp.1)
  obtain ⟨n, c, hc, _, _, hcs⟩ := P.primitive_refinement (P.unit - p) hcp
  have hnt : (n : ℝ) = 2 := by
    calc
      (n : ℝ) = ∑ i, τ (c i) := by
        simp only [show ∀ i, τ (c i) = 1 from fun i => P.canonicalTraceOfFormallyReal_primitive hfr _ (hc i)]
        simp
      _ = τ (P.unit - p) := by rw [← map_sum, hcs]
      _ = 2 := by rw [map_sub, ht, htp]; norm_num
  have hid : jordanMul p.val p.val = p.val := congrArg Subtype.val hp.1
  have hmin : 1 ≤ albertTrace p.val := NativeAnalysis.one_le_trace_of_idempotent hid
    (fun hz => hp.2.1 (Subtype.ext hz))
  have haux (i : Fin n) : 1 ≤ albertTrace (c i).val :=
    NativeAnalysis.one_le_trace_of_idempotent (congrArg Subtype.val (hc i).1)
      (fun hz => (hc i).2.1 (Subtype.ext hz))
  have hcalc : ∑ i, albertTrace (c i).val = 3 - albertTrace p.val := by
    let tr : B.carrier →ₗ[ℝ] ℝ :=
      { toFun := fun x => albertTrace x.val
        map_add' := fun x y => albertTrace_add x.val y.val
        map_smul' := fun a x => albertTrace_smul a x.val }
    change ∑ i, tr (c i) = _
    rw [← map_sum, hcs, map_sub]
    change albertTrace albertUnit - albertTrace p.val = _
    rw [NativeAnalysis.albertTrace_unit]
  have hle : (n : ℝ) ≤ ∑ i, albertTrace (c i).val := by
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => haux i)
  rw [hnt, hcalc] at hle
  exact ⟨hid, by linarith⟩

end AlbertSequential
