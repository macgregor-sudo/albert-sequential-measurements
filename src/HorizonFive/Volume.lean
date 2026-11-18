/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HorizonFive.Components

/-! # The Clifford volume functional `ℓ` (eq:cer:h5:volume) as a linear functional on `ℝ[G]`

A concrete representation of `Cl_{4,0}` on `ℝ^{Finset Test}` (`γ_i e_S = ± e_{S Δ {i}}`, sign
`(-1)^{#{k ∈ S, k < i}}`, matching `cliffMul`), the algebra map `cliffRep : ℝ[G] → End`, and
`volFun x = (cliffRep x e_∅)(univ)`:

* `volFun_groupElt`: `volFun (groupElt l) = cliffVol l`;
* `volFun_specialEval`: `volFun (σ̂ F) = 0` for every Jordan expression (from
  `clifford_eval_mem_span`). -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.HorizonFive

open AlbertSequential AlbertSequential.NativeAnalysis

/-- The space `ℝ^{Finset Test}`. -/
abbrev CV := Finset Test → ℝ

/-- Sign `(-1)^{#{k ∈ S, k < i}}`. -/
def csgn (i : Test) (S : Finset Test) : ℝ := (-1) ^ (S.filter (· < i)).card

theorem csgn_symmDiff (i : Test) (S : Finset Test) : csgn i (symmDiff S {i}) = csgn i S := by
  unfold csgn
  congr 2
  ext k
  simp only [Finset.mem_filter, Finset.mem_symmDiff, Finset.mem_singleton]
  constructor
  · rintro ⟨h | h, hk⟩
    · exact ⟨h.1, hk⟩
    · exact absurd (h.1 ▸ hk) (lt_irrefl _)
  · rintro ⟨h, hk⟩
    exact ⟨Or.inl ⟨h, fun e => lt_irrefl k (e ▸ hk)⟩, hk⟩

theorem csgn_sq (i : Test) (S : Finset Test) : csgn i S * csgn i S = 1 := by
  unfold csgn
  rw [← pow_add, ← two_mul, pow_mul]
  simp

theorem symmDiff_symmDiff_self' (S : Finset Test) (i : Test) :
    symmDiff (symmDiff S {i}) {i} = S := by
  rw [symmDiff_assoc, symmDiff_self, symmDiff_bot]

/-- The anticommutation sign identity, checked over all subsets of `Fin 4`. -/
theorem csgn_anti_parity : ∀ (T : Finset Test) (i k : Test), i ≠ k →
    ((symmDiff T {i}).filter (· < i)).card + ((symmDiff (symmDiff T {i}) {k}).filter (· < k)).card
      + ((symmDiff T {k}).filter (· < k)).card
      + ((symmDiff (symmDiff T {k}) {i}).filter (· < i)).card ≡ 1 [MOD 2] := by
  decide

theorem neg_one_pow_anti (a b c d : ℕ) (h : (a + b + c + d) % 2 = 1) :
    ((-1 : ℝ) ^ a) * (-1) ^ b = -((-1) ^ c * (-1) ^ d) := by
  rw [← pow_add, ← pow_add]
  rcases Nat.even_or_odd (a + b) with h1 | h1
  · have h2 : Odd (c + d) := by
      rw [Nat.odd_iff]; rw [Nat.even_iff] at h1; omega
    rw [h1.neg_one_pow, h2.neg_one_pow, neg_neg]
  · have h2 : Even (c + d) := by
      rw [Nat.even_iff]; rw [Nat.odd_iff] at h1; omega
    rw [h1.neg_one_pow, h2.neg_one_pow]

theorem csgn_anti (T : Finset Test) (i k : Test) (hik : i ≠ k) :
    csgn i (symmDiff T {i}) * csgn k (symmDiff (symmDiff T {i}) {k}) =
      -(csgn k (symmDiff T {k}) * csgn i (symmDiff (symmDiff T {k}) {i})) := by
  have h := csgn_anti_parity T i k hik
  unfold Nat.ModEq at h
  unfold csgn
  exact neg_one_pow_anti _ _ _ _ (by omega)

/-- `γ_i` on `ℝ^{Finset Test}`. -/
def gam (i : Test) : Module.End ℝ CV where
  toFun f T := csgn i (symmDiff T {i}) * f (symmDiff T {i})
  map_add' f g := by funext T; simp only [Pi.add_apply]; ring
  map_smul' r f := by funext T; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem gam_apply (i : Test) (f : CV) (T : Finset Test) :
    gam i f T = csgn i (symmDiff T {i}) * f (symmDiff T {i}) := rfl

theorem gam_sq (i : Test) : gam i * gam i = 1 := by
  apply LinearMap.ext; intro f; funext T
  simp only [mul_apply_eq_comp, gam_apply, symmDiff_symmDiff_self', csgn_symmDiff,
    one_apply_eq_self, ← mul_assoc, csgn_sq, one_mul]

theorem gam_anti (i k : Test) (hik : i ≠ k) : gam i * gam k = -(gam k * gam i) := by
  apply LinearMap.ext; intro f; funext T
  simp only [mul_apply_eq_comp, gam_apply, LinearMap.neg_apply, Pi.neg_apply, ← mul_assoc]
  rw [csgn_anti T i k hik]
  have : symmDiff (symmDiff T {i}) {k} = symmDiff (symmDiff T {k}) {i} := by
    rw [symmDiff_assoc, symmDiff_assoc, symmDiff_comm ({i} : Finset Test)]
  rw [this]
  ring

def cpop (i : Test) : Module.End ℝ CV := (1 / 2 : ℝ) • (1 + gam i)

theorem cpop_idem (i : Test) : cpop i * cpop i = cpop i := by
  simp only [cpop, smul_mul_assoc, mul_smul_comm, mul_add, add_mul, one_mul, mul_one, gam_sq,
    smul_smul, smul_add]
  module

/-- The Clifford representation of `ℝ[G]`. -/
def cliffRep : UniversalProjectionAlgebra 4 →ₐ[ℝ] Module.End ℝ CV :=
  RingQuot.liftAlgHom ℝ ⟨FreeAlgebra.lift ℝ cpop, by
    intro x y h
    cases h with
    | generator i =>
      simp only [map_mul, FreeAlgebra.lift_ι_apply]
      exact cpop_idem i⟩

theorem cliffRep_tests (i : Test) : cliffRep (universalTests i) = cpop i := by
  simp only [cliffRep, universalTests, universalProjection, projectionQuotient]
  rw [RingQuot.liftAlgHom_mkAlgHom_apply]
  simp only [FreeAlgebra.lift_ι_apply]

theorem cliffRep_symm (i : Test) : cliffRep (specialSymmetry i) = gam i := by
  simp only [specialSymmetry, map_sub, map_smul, map_one, cliffRep_tests, cpop, smul_smul]
  norm_num

/-- The basis vector `e_S`. -/
def ce (S : Finset Test) : CV := fun T => if T = S then 1 else 0

theorem gam_ce (i : Test) (S : Finset Test) :
    gam i (ce S) = csgn i S • ce (symmDiff S {i}) := by
  funext T
  simp only [gam_apply, ce, Pi.smul_apply, smul_eq_mul]
  by_cases h : symmDiff T {i} = S
  · have hT : T = symmDiff S {i} := by rw [← h, symmDiff_symmDiff_self']
    rw [ite_eq_left h, ite_eq_left hT, h]
  · have hT : T ≠ symmDiff S {i} := by
      intro hT; apply h; rw [hT, symmDiff_symmDiff_self']
    rw [ite_eq_right h, ite_eq_right hT, mul_zero, mul_zero]

theorem cliffRep_groupElt (l : List Test) :
    cliffRep (groupElt l) (ce ∅) = ((cliffImage l).1 : ℝ) • ce (cliffImage l).2 := by
  induction l with
  | nil => simp [groupElt, cliffImage]
  | cons a l ih =>
    rw [groupElt_cons, map_mul, mul_apply_eq_comp, ih, map_smul, cliffRep_symm, gam_ce,
      smul_smul]
    simp only [cliffImage, List.foldr_cons, cliffMul]
    congr 1
    simp only [csgn, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
    ring

/-- The volume functional. -/
def volFun : UniversalProjectionAlgebra 4 →ₗ[ℝ] ℝ :=
  (LinearMap.proj (R := ℝ) (φ := fun _ : Finset Test => ℝ) Finset.univ).comp
    ((LinearMap.applyₗ (ce ∅)).comp cliffRep.toLinearMap)

theorem volFun_apply (x : UniversalProjectionAlgebra 4) : volFun x = cliffRep x (ce ∅) Finset.univ :=
  rfl

theorem volFun_groupElt (l : List Test) : volFun (groupElt l) = (cliffVol l : ℝ) := by
  rw [volFun_apply, cliffRep_groupElt]
  simp only [Pi.smul_apply, ce, smul_eq_mul, cliffVol]
  by_cases h : (cliffImage l).2 = Finset.univ
  · rw [ite_eq_left h.symm, ite_eq_left h]; simp
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h]; simp

theorem volFun_specialEval (F : JPoly Test) : volFun (specialEval F) = 0 := by
  have hmem := clifford_eval_mem_span gam (fun i => gam_sq i) gam_anti F
  have h1 : cliffRep (specialEval F) = (specialTarget (Module.End ℝ CV)).eval gam F := by
    rw [specialEval, specialTarget_eval_hom]
    congr 1
    funext i
    exact cliffRep_symm i
  rw [volFun_apply, h1]
  let Φ : Module.End ℝ CV →ₗ[ℝ] ℝ :=
    (LinearMap.proj (R := ℝ) (φ := fun _ : Finset Test => ℝ) Finset.univ).comp
      (LinearMap.applyₗ (ce ∅))
  change Φ _ = 0
  have hle : Submodule.span ℝ (insert (1 : Module.End ℝ CV) (Set.range gam)) ≤ LinearMap.ker Φ := by
    refine Submodule.span_le.2 ?_
    rintro _ (rfl | ⟨i, rfl⟩)
    · change (1 : Module.End ℝ CV) (ce ∅) Finset.univ = 0
      simp only [one_apply_eq_self, ce]
      rw [ite_eq_right]
      exact Finset.univ_nonempty.ne_empty
    · change gam i (ce ∅) Finset.univ = 0
      rw [gam_ce]
      simp only [Pi.smul_apply, ce, smul_eq_mul]
      rw [ite_eq_right, mul_zero]
      intro h
      have := congrArg Finset.card h
      rw [Finset.card_univ, Fintype.card_fin] at this
      have h2 : (symmDiff (∅ : Finset Test) {i}).card = 1 := by
        rw [← Finset.bot_eq_empty, bot_symmDiff, Finset.card_singleton]
      omega
  exact hle hmem

end AlbertSequential.HorizonFive
