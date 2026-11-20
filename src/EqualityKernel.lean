/- SPDX-License-Identifier: Apache-2.0 -/
module

public import BlockA.SecondOrderResidual
public import BlockA.GlennieGeneral
public import FixedSBinding
public import NativeReachableDensity
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

@[expose] public section
noncomputable section

namespace AlbertSequential.AppF
open NativeAnalysis

private theorem tracePairing_square_nonzero_density (x : Albert) (hx : x ≠ 0) :
    ∃ ρ : Albert, IsDensity ρ ∧ tracePairing ρ x ≠ 0 := by
  by_contra! h
  have hsq (y : Albert) : tracePairing (jordanMul y y) x = 0 := by
    by_cases hy : y = 0
    · subst y
      simp only [jordanMul_zero_left]
      rw [tracePairing_comm, ← tracePairingLM_apply, map_zero]
    · have htr : 0 < albertTrace (jordanMul y y) :=
        lt_of_le_of_ne (tracePairing_self_nonneg y)
          (Ne.symm (mt (tracePairing_self_eq_zero y).mp hy))
      have hd := native_normalized_positive_density (jordanMul y y) ⟨y, rfl⟩ htr
      have hz := h _ hd
      rw [tracePairing_smul_left] at hz
      exact (mul_eq_zero.mp hz).resolve_left (inv_ne_zero htr.ne')
  have he : jordanMul (x + albertUnit) (x + albertUnit) -
      jordanMul (x - albertUnit) (x - albertUnit) = (4 : ℝ) • x := by
    simp only [jordanMul_add_left, jordanMul_add_right, jordanMul_sub_left, jordanMul_sub_right,
      jordanMul_albertUnit_left, jordanMul_albertUnit_right]
    module
  have hz := congrArg (fun y => tracePairing y x) he
  simp only [tracePairing_sub_left, tracePairing_smul_left, hsq, sub_self] at hz
  exact hx ((tracePairing_self_eq_zero x).mp ((mul_eq_zero.mp hz.symm).resolve_left (by norm_num)))

/-- The group-algebra homomorphism on a Jordan-term representative of a free element. -/
def idempotentJordanGroupValue {n : ℕ} (T : JTerm n) : GroupAlgebra n :=
  T.evalS (groupProj n)

theorem idempotentJordanGroupValue_wordCombination {n : ℕ} (c : Word (Fin n) →₀ ℝ) :
    idempotentJordanGroupValue (wordCombinationJTerm c) = freeProductImage c :=
  evalS_wordCombinationJTerm c (groupProj n)

/-- For a represented element of the word span, the two independent tests in 6.17(c)
are exactly the projective-equality and native-violation predicates. -/
theorem wordCombination_projectiveViolation_iff {n : ℕ}
    (p : Fin n → Albert) (c : Word (Fin n) →₀ ℝ) :
    (IsProjectiveEquality c ∧ ∃ ρ : Albert, IsDensity ρ ∧
      c.sum (fun w a => a * nativeWordProbability p ρ w) ≠ 0) ↔
    idempotentJordanGroupValue (wordCombinationJTerm c) = 0 ∧
      (wordCombinationJTerm c).evalAlbert p ≠ 0 := by
  rw [idempotentJordanGroupValue_wordCombination, isProjectiveEquality_iff_freeProductZero,
    evalAlbert_wordCombinationJTerm]
  constructor
  · rintro ⟨hc, ρ, _, hρ⟩
    refine ⟨hc, fun hz => hρ ?_⟩
    rw [← tracePairing_nativeWordCombinationEffect, hz]
    exact map_zero (tracePairingLM ρ)
  · rintro ⟨hc, hz⟩
    obtain ⟨ρ, hρ, htrace⟩ := tracePairing_square_nonzero_density _ hz
    exact ⟨hc, ρ, hρ, (tracePairing_nativeWordCombinationEffect c p ρ) ▸ htrace⟩

private theorem native_eval_surjective_of_generates {n : ℕ}
    (p : Fin n → Albert) (hp : GeneratesAlbert p) :
    Function.Surjective (JTerm.evalAlbert p) := by
  let B : NativeJordanSubalgebra :=
    { carrier :=
        { carrier := Set.range (JTerm.evalAlbert p)
          zero_mem' := ⟨.smul 0 .one, zero_smul ℝ albertUnit⟩
          add_mem' := by rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩; exact ⟨.add s t, rfl⟩
          smul_mem' := by rintro r _ ⟨t, rfl⟩; exact ⟨.smul r t, rfl⟩ }
      unit_mem := ⟨.one, rfl⟩
      product_mem := by rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩; exact ⟨.mul s t, rfl⟩ }
  intro x
  exact hp x B (fun k => ⟨.var k, rfl⟩)

private def termOps (n : ℕ) : JOps (JTerm n) where
  add := .add
  sub := fun x y => .add x (.smul (-1) y)
  mul := .mul

private theorem evalAlbert_termGlennie {n : ℕ} (p : Fin n → Albert) (a b c d : JTerm n) :
    (glennieF (termOps n) a b c d).evalAlbert p =
      nativeGlennieF (a.evalAlbert p) (b.evalAlbert p) (c.evalAlbert p) (d.evalAlbert p) := by
  apply map_glennieF
  · intro x y
    rfl
  · intro x y
    simp [termOps, JTerm.evalAlbert, nativeOps, sub_eq_add_neg]
  · intro x y
    rfl

private theorem groupValue_termGlennie {n : ℕ} (a b c d : JTerm n) :
    idempotentJordanGroupValue (glennieF (termOps n) a b c d) = 0 := by
  unfold idempotentJordanGroupValue
  rw [map_glennieF (o := termOps n) (o' := specialOps (GroupAlgebra n)) (JTerm.evalS (groupProj n))
    (fun _ _ => rfl) (fun x y => by simp [termOps, JTerm.evalS, specialOps, sub_eq_add_neg])
    (fun _ _ => rfl)]
  exact special_glennieF_eq_zero _ _ _ _

private theorem fixedSGlennie_ne :
    nativeGlennieF (symmetryOf (fixedS 0)) (symmetryOf (fixedS 1))
      (symmetryOf (fixedS 2)) (symmetryOf (fixedS 3)) ≠ 0 := by
  intro hz
  have hI := (thm_glennie_eq_zero_iff (fixedS 0) (fixedS 1) (fixedS 2) (fixedS 3)
    (fixedS_isAtom 0) (fixedS_isAtom 1) (fixedS_isAtom 2) (fixedS_isAtom 3)).mp hz
  have hη : ![fixedS 0, fixedS 1, fixedS 2, fixedS 3] = fixedS := by
    funext i
    fin_cases i <;> rfl
  rw [hη, fourPointInvariant_fixedS] at hI
  norm_num at hI

/-- The Albert–Paige obstruction used in 6.17(c): a special Jordan subalgebra
of an associative real algebra cannot map onto the native Albert algebra. -/
theorem specialJordanSubmodule_no_surjective_to_Albert
    {A : Type*} [NonUnitalRing A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    (C : Submodule ℝ A) (hC : ∀ x ∈ C, ∀ y ∈ C, (specialOps A).mul x y ∈ C)
    (f : C →ₗ[ℝ] Albert)
    (hf : ∀ x y : C, f ⟨(specialOps A).mul x y, hC _ x.2 _ y.2⟩ = jordanMul (f x) (f y)) :
    ¬ Function.Surjective f := by
  intro hsurj
  obtain ⟨a, ha⟩ := hsurj (symmetryOf (fixedS 0))
  obtain ⟨b, hb⟩ := hsurj (symmetryOf (fixedS 1))
  obtain ⟨c, hc⟩ := hsurj (symmetryOf (fixedS 2))
  obtain ⟨d, hd⟩ := hsurj (symmetryOf (fixedS 3))
  let o : JOps C := ⟨(· + ·), (· - ·), fun x y => ⟨(specialOps A).mul x y, hC _ x.2 _ y.2⟩⟩
  have hz : glennieF o a b c d = 0 := by
    apply Subtype.val_injective
    rw [map_glennieF (o := o) (o' := specialOps A) Subtype.val
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)]
    exact special_glennieF_eq_zero _ _ _ _
  have hmap := map_glennieF (o := o) (o' := nativeOps) f
    (fun x y => map_add f x y) (fun x y => map_sub f x y) hf a b c d
  rw [hz, map_zero, ha, hb, hc, hd] at hmap
  exact fixedSGlennie_ne hmap.symm

/-- The second assertion of 6.17(c) for arbitrary idempotent generators, in
term representatives. A Glennie term gives the kernel witness directly. -/
theorem exists_idempotentJordanKernel_of_generates {n : ℕ}
    (p : Fin n → Albert) (hp : GeneratesAlbert p) :
    ∃ T : JTerm n, idempotentJordanGroupValue T = 0 ∧ T.evalAlbert p ≠ 0 := by
  let s := fun i : Fin 4 => symmetryOf (fixedS i)
  have hsurj := native_eval_surjective_of_generates p hp
  obtain ⟨a, ha⟩ := hsurj (s 0)
  obtain ⟨b, hb⟩ := hsurj (s 1)
  obtain ⟨c, hc⟩ := hsurj (s 2)
  obtain ⟨d, hd⟩ := hsurj (s 3)
  refine ⟨glennieF (termOps n) a b c d, groupValue_termGlennie _ _ _ _, ?_⟩
  rw [evalAlbert_termGlennie, ha, hb, hc, hd]
  exact fixedSGlennie_ne

end AlbertSequential.AppF
