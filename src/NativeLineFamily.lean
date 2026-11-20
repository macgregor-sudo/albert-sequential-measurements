/- SPDX-License-Identifier: Apache-2.0 -/
module
public import SubalgebraCoordsAndLine
import NativeOrbitLifts
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Module

@[expose] public section

namespace AlbertSequential

noncomputable section

local instance : Module.Finite ℝ Albert :=
  inferInstanceAs (Module.Finite ℝ ((Fin 3 → ℝ) × (Fin 3 → (Quaternion ℝ × Quaternion ℝ))))

/-- The Bloch vector, in native coordinates, of an atom on the line normal to q. -/
def lineBloch (q a : Albert) : Albert := (2 : ℝ) • a - (albertUnit - q)

theorem lineBloch_product {q a b : Albert} (hq : IsAtom q) (ha : IsAtom a) (hb : IsAtom b)
    (hqa : jordanMul q a = 0) (hqb : jordanMul q b = 0) :
    jordanMul (lineBloch q a) (lineBloch q b) =
      (2 * tracePairing a b - 1) • (albertUnit - q) := by
  let f := albertUnit - q
  have hfa : jordanMul a f = a := by
    simp [f, jordanMul_sub_right, jordanMul_albertUnit_right, jordanMul_comm a q, hqa]
  have hfb : jordanMul f b = b := by simp [f, jordanMul_sub_left, jordanMul_albertUnit_left, hqb]
  have hff : jordanMul f f = f := by
    simp [f, jordanMul_sub_left, jordanMul_sub_right, jordanMul_albertUnit_left,
      jordanMul_albertUnit_right, hq.1]
  change jordanMul ((2 : ℝ) • a - f) ((2 : ℝ) • b - f) = _ • f
  simp only [jordanMul_sub_left, jordanMul_sub_right, jordanMul_smul_left, jordanMul_smul_right,
    hfa, hfb, hff]
  by_cases hab : a = b
  · subst b
    rw [ha.1, show tracePairing a a = 1 by unfold tracePairing; rw [ha.1, ha.2]]
    module
  obtain ⟨hlt, hs⟩ := eq_fiv_support q a b hq ha hb hqa hqb hab
  have h := congrArg ((1 - tracePairing a b) • ·) hs
  change (1 - tracePairing a b) • f = _ at h
  rw [smul_smul, mul_inv_cancel₀ (by linarith), one_smul] at h
  linear_combination (norm := module) (2 : ℝ) • h

/-- Overlap is half of one plus the standard Bloch inner product.
The two Bloch vectors have the native trace metric scaled by one half. -/
theorem lineBloch_transition {q a b : Albert} (hq : IsAtom q) (ha : IsAtom a) (hb : IsAtom b)
    (hqa : jordanMul q a = 0) (hqb : jordanMul q b = 0) :
    tracePairing a b = (1 + tracePairing (lineBloch q a) (lineBloch q b) / 2) / 2 := by
  have h := congrArg albertTrace (lineBloch_product hq ha hb hqa hqb)
  have he : albertTrace albertUnit = 3 := by norm_num [albertTrace, albertUnit]
  rw [albertTrace_smul, albertTrace_sub, he, hq.2] at h
  change tracePairing (lineBloch q a) (lineBloch q b) = _ at h
  linarith

private theorem rank_insert {S : Set Albert} {a : Albert} (ha : a ∉ Submodule.span ℝ S) :
    Module.finrank ℝ (Submodule.span ℝ (insert a S)) = Module.finrank ℝ (Submodule.span ℝ S) + 1 := by
  rw [Submodule.span_insert, sup_comm, Submodule.finrank_sup_span_singleton ha]

/-- Any family on one native line containing two distinct atoms generates precisely
the two scalar directions and the span of its Bloch vectors. No independence or
orthogonality among those vectors is assumed. -/
theorem generatedLineFamily {ι : Type*} (p : ι → Albert) (q : Albert) (hq : IsAtom q)
    (hp : ∀ i, IsAtom (p i)) (ho : ∀ i, jordanMul q (p i) = 0)
    (hd : ∃ i j, p i ≠ p j) :
    let f := albertUnit - q
    let U := Set.range (fun i => lineBloch q (p i))
    let B := generatedSubalgebra (Set.range p)
    B.carrier = Submodule.span ℝ (insert q (insert f U)) ∧
      Module.finrank ℝ B.carrier = Module.finrank ℝ (Submodule.span ℝ U) + 2 := by
  classical
  let f := albertUnit - q
  let u := fun i => lineBloch q (p i)
  let U := Set.range u
  let T := insert q (insert f U)
  let W := Submodule.span ℝ T
  let B := generatedSubalgebra (Set.range p)
  have hqW : q ∈ W := Submodule.subset_span (by exact Set.mem_insert _ _)
  have hfW : f ∈ W := Submodule.subset_span (by exact Or.inr (Or.inl rfl))
  have huW (i) : u i ∈ W := Submodule.subset_span (by exact Or.inr (Or.inr ⟨i,rfl⟩))
  have hqf : jordanMul q f = 0 := by simp [f, jordanMul_sub_right, jordanMul_albertUnit_right, hq.1]
  have hff : jordanMul f f = f := by
    change jordanMul (albertUnit - q) f = f
    rw [jordanMul_sub_left, jordanMul_albertUnit_left, hqf, sub_zero]
  have hqu (i) : jordanMul q (u i) = 0 := by
    change jordanMul q ((2 : ℝ) • p i - f) = 0
    simp [jordanMul_sub_right, jordanMul_smul_right, ho, hqf]
  have hfu (i) : jordanMul f (u i) = u i := by
    change jordanMul (albertUnit - q) (u i) = u i
    rw [jordanMul_sub_left, jordanMul_albertUnit_left, hqu, sub_zero]
  have hprod : ∀ x ∈ T, ∀ y ∈ T, jordanMul x y ∈ W := by
    rintro x (rfl | rfl | ⟨i,rfl⟩) y (rfl | rfl | ⟨j,rfl⟩)
    · simpa only [hq.1] using hqW
    · rw [hqf]; exact W.zero_mem
    · rw [hqu]; exact W.zero_mem
    · rw [jordanMul_comm, hqf]; exact W.zero_mem
    · rwa [hff]
    · rw [hfu]; exact huW j
    · rw [jordanMul_comm, hqu]; exact W.zero_mem
    · rw [jordanMul_comm, hfu]; exact huW i
    · exact (lineBloch_product hq (hp i) (hp j) (ho i) (ho j)) ▸ W.smul_mem _ hfW
  let A : NativeJordanSubalgebra := {
    carrier := W
    unit_mem := by
      rw [show albertUnit = q + f by dsimp [f]; abel]
      exact W.add_mem hqW hfW
    product_mem := fun x hx y hy => LinearMap.BilinMap.apply_apply_mem_of_mem_span W T T
      nativeJordanProductLinear hprod x y hx hy }
  have hBW : B.carrier ≤ W := generatedSubalgebra_le (B := A) (by
    rintro _ ⟨i,rfl⟩
    have he : p i = (1 / 2 : ℝ) • (u i + f) := by dsimp [u,lineBloch,f]; module
    rw [he]; exact W.smul_mem _ (W.add_mem (huW i) hfW))
  have hpB (i) : p i ∈ B.carrier := subset_generatedSubalgebra _ ⟨i,rfl⟩
  obtain ⟨i,j,hij⟩ := hd
  have hfB : f ∈ B.carrier := by
    rw [show f = _ from (eq_fiv_support q _ _ hq (hp i) (hp j) (ho i) (ho j) hij).2]
    exact B.carrier.smul_mem _ (B.carrier.sub_mem (B.carrier.add_mem (hpB i) (hpB j))
      (B.carrier.smul_mem _ (B.product_mem _ (hpB i) _ (hpB j))))
  have hqB : q ∈ B.carrier := by
    rw [show q = albertUnit - f by dsimp [f]; abel]
    exact B.carrier.sub_mem B.unit_mem hfB
  have heq : B.carrier = W := le_antisymm hBW (Submodule.span_le.mpr (by
    rintro _ (rfl | rfl | ⟨k,rfl⟩)
    · exact hqB
    · exact hfB
    · exact B.carrier.sub_mem (B.carrier.smul_mem _ (hpB k)) hfB))
  have ht : albertTrace f = 2 := by
    change albertTrace (albertUnit - q) = 2
    rw [albertTrace_sub, hq.2]; norm_num [albertTrace, albertUnit]
  have hfout : f ∉ Submodule.span ℝ U := by
    intro h
    suffices ∀ x ∈ Submodule.span ℝ U, albertTrace x = 0 by linarith [this f h]
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k,rfl⟩ := hx
      change albertTrace ((2 : ℝ) • p k - f) = 0
      rw [albertTrace_sub, albertTrace_smul, (hp k).2, ht]; norm_num
    | zero => change (∑ _ : Fin 3, (0 : ℝ)) = 0; simp
    | add _ _ _ _ a b => rw [albertTrace_add,a,b,add_zero]
    | smul _ _ _ a => rw [albertTrace_smul,a,mul_zero]
  have hqout : q ∉ Submodule.span ℝ (insert f U) := by
    have hk : Submodule.span ℝ (insert f U) ≤ (nativeJordanProductLinear q).ker :=
      Submodule.span_le.mpr (by rintro _ (rfl | ⟨k,rfl⟩); exact hqf; exact hqu k)
    intro h
    have hz : q = 0 := hq.1.symm.trans (LinearMap.mem_ker.mp (hk h))
    have htq := hq.2
    rw [hz] at htq
    change (∑ _ : Fin 3, (0 : ℝ)) = 1 at htq
    simp at htq
  refine ⟨heq, ?_⟩
  change Module.finrank ℝ B.carrier = Module.finrank ℝ (Submodule.span ℝ U) + 2
  rw [heq, show W = Submodule.span ℝ (insert q (insert f U)) from rfl, rank_insert hqout,
    rank_insert hfout]

/-- The Jordan product on the entire vector summand is its Euclidean inner
product (one half of the native trace pairing) times the line unit. -/
theorem lineBloch_span_product {ι : Type*} (p : ι → Albert) (q : Albert) (hq : IsAtom q)
    (hp : ∀ i, IsAtom (p i)) (ho : ∀ i, jordanMul q (p i) = 0)
    {x y : Albert} (hx : x ∈ Submodule.span ℝ (Set.range (fun i => lineBloch q (p i))))
    (hy : y ∈ Submodule.span ℝ (Set.range (fun i => lineBloch q (p i)))) :
    jordanMul x y = (tracePairing x y / 2) • (albertUnit - q) := by
  let f := albertUnit - q
  let L := Submodule.span ℝ ({f} : Set Albert)
  have hf : f ∈ L := Submodule.mem_span_singleton_self _
  have hm : jordanMul x y ∈ L :=
    LinearMap.BilinMap.apply_apply_mem_of_mem_span L _ _ nativeJordanProductLinear (by
      rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
      change jordanMul (lineBloch q (p i)) (lineBloch q (p j)) ∈ L
      rw [lineBloch_product hq (hp i) (hp j) (ho i) (ho j)]
      exact L.smul_mem _ hf) x y hx hy
  obtain ⟨t,ht⟩ := Submodule.mem_span_singleton.mp hm
  have htr : albertTrace f = 2 := by
    change albertTrace (albertUnit - q) = 2
    rw [albertTrace_sub, hq.2]; norm_num [albertTrace, albertUnit]
  have h := congrArg albertTrace ht
  rw [albertTrace_smul, htr] at h
  have hscalar : tracePairing x y / 2 = t := by
    unfold tracePairing; linarith
  rw [hscalar]; exact ht.symm

/-- With just one atom, the unital algebra consists of the two scalar directions. -/
theorem generatedSingletonAtom (a : Albert) (ha : IsAtom a) :
    let B := generatedSubalgebra ({a} : Set Albert)
    B.carrier = Submodule.span ℝ ({albertUnit,a} : Set Albert) ∧
      Module.finrank ℝ B.carrier = 2 := by
  let T : Set Albert := {albertUnit,a}
  let W := Submodule.span ℝ T
  have he : albertUnit ∈ W := Submodule.subset_span (by exact Or.inl rfl)
  have hp : a ∈ W := Submodule.subset_span (by exact Or.inr rfl)
  let A : NativeJordanSubalgebra := {
    carrier := W
    unit_mem := he
    product_mem := fun x hx y hy =>
      LinearMap.BilinMap.apply_apply_mem_of_mem_span W T T nativeJordanProductLinear (by
        rintro x (hx | hx) y (hy | hy) <;> change _ = _ at hx hy <;> subst x <;> subst y
        all_goals change jordanMul _ _ ∈ W
        · simpa only [jordanMul_albertUnit_left] using he
        · simpa only [jordanMul_albertUnit_left] using hp
        · simpa only [jordanMul_albertUnit_right] using hp
        · simpa only [ha.1] using hp) x y hx hy }
  let B := generatedSubalgebra ({a} : Set Albert)
  have hB : B.carrier = W := le_antisymm
    (generatedSubalgebra_le (B := A) (Set.singleton_subset_iff.mpr hp))
    (Submodule.span_le.mpr (Set.insert_subset B.unit_mem (Set.singleton_subset_iff.mpr
      (subset_generatedSubalgebra _ rfl))))
  refine ⟨hB, ?_⟩
  have hne : a ≠ 0 := by
    intro e
    have h := ha.2
    rw [e] at h; change (∑ _ : Fin 3, (0 : ℝ)) = 1 at h; simp at h
  have hout : albertUnit ∉ Submodule.span ℝ ({a} : Set Albert) := by
    intro h
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp h
    have ht := congrArg albertTrace hc
    rw [albertTrace_smul,ha.2] at ht
    have he3 : albertTrace albertUnit = 3 := by norm_num [albertTrace,albertUnit]
    rw [he3,mul_one] at ht
    have hj := congrArg (jordanMul a) hc
    change jordanMul a (c • a) = jordanMul a albertUnit at hj
    rw [jordanMul_smul_right, ha.1,jordanMul_albertUnit_right,ht] at hj
    have hz : (2 : ℝ) • a = 0 := by linear_combination (norm := module) hj
    exact hne ((smul_eq_zero.mp hz).resolve_left (by norm_num))
  change Module.finrank ℝ B.carrier = 2
  rw [hB, show W = Submodule.span ℝ (insert albertUnit {a}) from rfl, rank_insert hout,
    finrank_span_singleton hne]

end

end AlbertSequential
