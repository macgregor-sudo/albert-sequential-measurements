/- SPDX-License-Identifier: Apache-2.0 -/
module
public import CyclicWordQuotient

public import Mathlib.LinearAlgebra.Span.Basic

/-!+Elementary linear descent used by reconstruction. A total single-valued
linear relation is the graph of a genuine linear map. The nontrivial
single-valuedness hypothesis is later proved from all-history square lifts;
it is not claimed here as an unconditional reconstruction result.
-/
@[expose] public section
noncomputable section
namespace AlbertSequential

section Relation
variable {J E : Type*} [AddCommGroup J] [Module ℝ J] [AddCommGroup E] [Module ℝ E]

theorem linearRelation_unique (R : Submodule ℝ (J × E))
    (hzero : ∀ y, (0, y) ∈ R → y = 0) {x : J} {y z : E}
    (hy : (x, y) ∈ R) (hz : (x, z) ∈ R) : y = z := by
  apply sub_eq_zero.mp
  apply hzero
  simpa only [Prod.mk_sub_mk, sub_self] using R.sub_mem hy hz

def descendedLinearMap (R : Submodule ℝ (J × E))
    (htotal : ∀ x, ∃ y, (x, y) ∈ R)
    (hzero : ∀ y, (0, y) ∈ R → y = 0) : J →ₗ[ℝ] E where
  toFun x := (htotal x).choose
  map_add' x y := linearRelation_unique R hzero (htotal (x + y)).choose_spec
    (R.add_mem (htotal x).choose_spec (htotal y).choose_spec)
  map_smul' r x := linearRelation_unique R hzero (htotal (r • x)).choose_spec
    (R.smul_mem r (htotal x).choose_spec)

theorem descendedLinearMap_graph (R : Submodule ℝ (J × E))
    (htotal : ∀ x, ∃ y, (x, y) ∈ R)
    (hzero : ∀ y, (0, y) ∈ R → y = 0) (x : J) :
    (x, descendedLinearMap R htotal hzero x) ∈ R := (htotal x).choose_spec

theorem descendedLinearMap_eq_of_mem (R : Submodule ℝ (J × E))
    (htotal : ∀ x, ∃ y, (x, y) ∈ R)
    (hzero : ∀ y, (0, y) ∈ R → y = 0) {x : J} {y : E}
    (hxy : (x, y) ∈ R) : descendedLinearMap R htotal hzero x = y :=
  linearRelation_unique R hzero (descendedLinearMap_graph R htotal hzero x) hxy

/-- Paired generators with an explicit distinguished unit. -/
def unitAndAtomLabels {κ : Type*} (e : J) (q : κ → J) : Option κ → J
  | none => e
  | some i => q i

def unitAndAtomRelation {κ : Type*} (e : J) (q : κ → J) (u : E) (P : κ → E) :
    Submodule ℝ (J × E) :=
  Submodule.span ℝ (Set.range (fun i => (unitAndAtomLabels e q i, unitAndAtomLabels u P i)))

theorem unitAndAtomRelation_generator {κ : Type*} (e : J) (q : κ → J)
    (u : E) (P : κ → E) (i : Option κ) :
    (unitAndAtomLabels e q i, unitAndAtomLabels u P i) ∈ unitAndAtomRelation e q u P :=
  Submodule.subset_span ⟨i, rfl⟩

theorem unitAndAtomRelation_total {κ : Type*} (e : J) (q : κ → J)
    (u : E) (P : κ → E)
    (hspan : Submodule.span ℝ (Set.range (unitAndAtomLabels e q)) = ⊤) :
    ∀ x, ∃ y, (x, y) ∈ unitAndAtomRelation e q u P := by
  intro x
  have hx : x ∈ Submodule.span ℝ (Set.range (unitAndAtomLabels e q)) := by
    rw [hspan]
    trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨i, rfl⟩
      exact ⟨unitAndAtomLabels u P i, unitAndAtomRelation_generator e q u P i⟩
  | zero => exact ⟨0, (unitAndAtomRelation e q u P).zero_mem⟩
  | add x y hx hy ihx ihy =>
      rcases ihx with ⟨z, hz⟩
      rcases ihy with ⟨w, hw⟩
      exact ⟨z + w, (unitAndAtomRelation e q u P).add_mem hz hw⟩
  | smul r x hx ih =>
      rcases ih with ⟨z, hz⟩
      exact ⟨r • z, (unitAndAtomRelation e q u P).smul_mem r hz⟩

theorem unitAndAtomRelation_map {κ F : Type*} [AddCommGroup F] [Module ℝ F]
    (e : J) (q : κ → J) (u : E) (P : κ → E) (H : E →ₗ[ℝ] F)
    {x : J} {z : E} (hz : (x, z) ∈ unitAndAtomRelation e q u P) :
    (x, H z) ∈ unitAndAtomRelation e q (H u) (fun i => H (P i)) := by
  have hall : ∀ y ∈ unitAndAtomRelation e q u P,
      (y.1, H y.2) ∈ unitAndAtomRelation e q (H u) (fun i => H (P i)) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        rcases hy with ⟨i, rfl⟩
        cases i with
        | none => exact unitAndAtomRelation_generator _ _ _ _ none
        | some i => exact unitAndAtomRelation_generator _ _ _ _ (some i)
    | zero =>
        change (0, H (0 : E)) ∈ unitAndAtomRelation e q (H u) (fun i => H (P i))
        rw [map_zero]
        exact (unitAndAtomRelation e q (H u) (fun i => H (P i))).zero_mem
    | add y z hy hz ihy ihz =>
        simpa using
          (unitAndAtomRelation e q (H u) (fun i => H (P i))).add_mem ihy ihz
    | smul r y hy ih =>
        simpa using
          (unitAndAtomRelation e q (H u) (fun i => H (P i))).smul_mem r ih
  exact hall (x, z) hz

/-- Every finite relation in the image has a finite preimage relation.
No injectivity or global surjectivity of H is required. -/
theorem unitAndAtomRelation_map_lift {κ F : Type*} [AddCommGroup F] [Module ℝ F]
    (e : J) (q : κ → J) (u : E) (P : κ → E) (H : E →ₗ[ℝ] F)
    {x : J} {z : F} (hz : (x, z) ∈ unitAndAtomRelation e q (H u) (fun i => H (P i))) :
    ∃ y : E, (x, y) ∈ unitAndAtomRelation e q u P ∧ H y = z := by
  have hall : ∀ w ∈ unitAndAtomRelation e q (H u) (fun i => H (P i)),
      ∃ y : E, (w.1, y) ∈ unitAndAtomRelation e q u P ∧ H y = w.2 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
        rcases hw with ⟨i, rfl⟩
        cases i with
        | none => exact ⟨u, unitAndAtomRelation_generator _ _ _ _ none, rfl⟩
        | some i => exact ⟨P i, unitAndAtomRelation_generator _ _ _ _ (some i), rfl⟩
    | zero => exact ⟨0, (unitAndAtomRelation e q u P).zero_mem, map_zero H⟩
    | add w v hw hv ihw ihv =>
        rcases ihw with ⟨y, hy, he⟩
        rcases ihv with ⟨z, hz, hf⟩
        exact ⟨y + z, (unitAndAtomRelation e q u P).add_mem hy hz, by rw [map_add, he, hf]; rfl⟩
    | smul r w hw ih =>
        rcases ih with ⟨y, hy, he⟩
        exact ⟨r • y, (unitAndAtomRelation e q u P).smul_mem r hy, by rw [map_smul, he]; rfl⟩
  exact hall (x, z) hz

end Relation
end AlbertSequential
