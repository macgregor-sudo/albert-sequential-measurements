/- SPDX-License-Identifier: Apache-2.0 -/
module

public import AppF.HigherJetCoefficientAlgebras
public import AppF.CoefficientRegularQuotient
import Mathlib.Tactic.Abel

/-! The precise two-sided ideal and faithful quotient for the real and quaternionic jets. -/
@[expose] public section
noncomputable section

namespace AlbertSequential.AppF.HigherJetCoefficients

def monomial (b : HigherJetBase) (m j : Fin 4) (h₀ : j ≠ 0) (hm : j ≤ m) :
    Octonion →ₗ[ℝ] HigherJetCoefficients b m where
  toFun x := ⟨fun i => if i = j then x else 0,
    ⟨by simp [Ne.symm h₀], fun i hi => by
      have hne : i ≠ j := fun h => (not_le_of_gt hi) (h ▸ hm)
      simp [hne]⟩⟩
  map_add' x y := by
    apply Subtype.ext
    funext i
    change (if i = j then x + y else 0) =
      (if i = j then x else 0) + (if i = j then y else 0)
    by_cases hi : i = j <;> simp [hi]
  map_smul' r x := by
    apply Subtype.ext
    funext i
    change (if i = j then r • x else 0) = r • (if i = j then x else 0)
    by_cases hi : i = j <;> simp [hi]

@[simp] theorem monomial_apply (b : HigherJetBase) (m j : Fin 4)
    (h₀ : j ≠ 0) (hm : j ≤ m) (x : Octonion) (i : Fin 4) :
    (monomial b m j h₀ hm x).val i = if i = j then x else 0 := rfl

def constant (b : HigherJetBase) (m : Fin 4) (x : Octonion) (hx : b.project x = x) :
    HigherJetCoefficients b m :=
  ⟨![x, 0, 0, 0], ⟨hx, fun i hi => by fin_cases i <;> simp_all [Fin.lt_def]⟩⟩

@[simp] theorem constant_apply (b : HigherJetBase) (m : Fin 4) (x : Octonion)
    (hx : b.project x = x) (i : Fin 4) :
    (constant b m x hx).val i = ![x, 0, 0, 0] i := rfl

def leadingMonomial (b : HigherJetBase) :
    Octonion →ₗ[ℝ] HigherJetCoefficients b b.threshold :=
  monomial b b.threshold b.threshold (by cases b <;> decide) le_rfl

@[simp] theorem leadingMonomial_apply (b : HigherJetBase) (x : Octonion) (i : Fin 4) :
    (leadingMonomial b x).val i = if i = b.threshold then x else 0 := rfl

theorem leadingMonomial_injective (b : HigherJetBase) : Function.Injective (leadingMonomial b) := by
  intro x y h
  simpa using congrArg (fun u : HigherJetCoefficients b b.threshold => u.val b.threshold) h

def leadingIdeal (b : HigherJetBase) : Submodule ℝ (HigherJetCoefficients b b.threshold) :=
  b.leadingSpace.map (leadingMonomial b)

theorem mem_leadingIdeal (b : HigherJetBase) (x : HigherJetCoefficients b b.threshold) :
    x ∈ leadingIdeal b ↔
      (∀ i, i ≠ b.threshold → x.val i = 0) ∧ x.val b.threshold ∈ b.leadingSpace := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨fun i hi => by simp [hi], by simpa⟩
  · rintro ⟨hz, ht⟩
    refine ⟨x.val b.threshold, ht, Subtype.ext (funext fun i => ?_)⟩
    by_cases hi : i = b.threshold
    · subst i
      simp
    · simp [hi, hz i hi]

theorem associator_mem_leadingIdeal (b : HigherJetBase)
    (x y z : HigherJetCoefficients b b.threshold) :
    associator x y z ∈ leadingIdeal b :=
  (mem_leadingIdeal b _).mpr (associator_at_threshold b x y z)

private theorem leadingAssociator_eq (b : HigherJetBase) (x y z : HigherJetCoefficients b b.threshold) :
    associator x y z = leadingMonomial b ((associator x y z).val b.threshold) := by
  apply Subtype.ext
  funext i
  by_cases hi : i = b.threshold
  · subst i
    simp
  · simp [hi, (associator_at_threshold b x y z).1 i hi]

section StandardCoordinates
set_option allowUnsafeReducibility true in
attribute [local reducible] Octonion

private def realFirst (x : Octonion) : HigherJetCoefficients .real 3 :=
  monomial .real 3 1 (by decide) (by decide) x

private theorem realFirst_associator (x y z : Octonion) :
    associator (realFirst x) (realFirst y) (realFirst z) =
      leadingMonomial .real (octAssociator x y z) := by
  rw [leadingAssociator_eq .real]
  congr 1
  rw [associator_apply (realFirst x) (realFirst y) (realFirst z) (3 : Fin 4) le_rfl]
  simp [realFirst, monomial, octonionJetAssociator_degreeThree,
    octAssociator_zero_mid, octAssociator_zero_right]
  abel

private def quatFirst (x : Octonion) : HigherJetCoefficients .quaternionic 1 :=
  monomial .quaternionic 1 1 (by decide) le_rfl x

private def quatZero (q : Quaternion ℝ) : HigherJetCoefficients .quaternionic 1 :=
  constant .quaternionic 1 (q, 0) rfl

private theorem quatFirst_associator (a b : Quaternion ℝ) (x : Octonion) :
    associator (quatZero a) (quatZero b) (quatFirst x) =
      leadingMonomial .quaternionic (octAssociator (a, 0) (b, 0) x) := by
  rw [leadingAssociator_eq .quaternionic]
  congr 1
  rw [associator_apply (quatZero a) (quatZero b) (quatFirst x) (1 : Fin 4) le_rfl]
  simp [quatZero, quatFirst, constant, monomial, octonionJetAssociator_degreeOne, octAssociator_zero_right]
  abel

/-- The exact leading ideal is spanned by the actual associators of the truncated algebra. -/
theorem span_associators_eq_leadingIdeal (b : HigherJetBase) :
    Submodule.span ℝ (Set.range (fun t :
      HigherJetCoefficients b b.threshold × HigherJetCoefficients b b.threshold ×
        HigherJetCoefficients b b.threshold => associator t.1 t.2.1 t.2.2)) = leadingIdeal b := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨x, y, z⟩, rfl⟩
    exact associator_mem_leadingIdeal b x y z
  · rintro _ ⟨⟨p, q⟩, hu, rfl⟩
    cases b
    · change p.re = 0 at hu
      obtain ⟨u, huv⟩ := realLeadingAssociator_decomposition p q hu
      let S := Submodule.span ℝ (Set.range (fun t :
        HigherJetCoefficients .real 3 × HigherJetCoefficients .real 3 ×
          HigherJetCoefficients .real 3 => associator t.1 t.2.1 t.2.2))
      have hgen (x y z : Octonion) : leadingMonomial .real (octAssociator x y z) ∈ S := by
        rw [← realFirst_associator]
        exact Submodule.subset_span ⟨(realFirst x, realFirst y, realFirst z), rfl⟩
      change leadingMonomial .real (p, q) ∈ S
      rw [huv, map_add, map_add, map_smul]
      exact S.add_mem (S.add_mem (S.smul_mem _ (hgen octJ octL (octonionMul octK octL)))
        (hgen octI octL (0, ⟨0, 0, -(p.imK / 2), p.imJ / 2⟩))) (hgen octI octJ (0, u))
    · change p = 0 at hu
      subst p
      obtain ⟨u, huv⟩ := quaternionicLeadingAssociator_representative q
      have he : octAssociator ((octI.1, 0) : Octonion) ((octJ.1, 0) : Octonion) (0, u) = (0, q) :=
        huv
      rw [← he, ← quatFirst_associator]
      exact Submodule.subset_span ⟨(quatZero octI.1, quatZero octJ.1, quatFirst (0, u)), rfl⟩

end StandardCoordinates

theorem product_leadingMonomial_left (b : HigherJetBase)
    (x : HigherJetCoefficients b b.threshold) (u : Octonion) :
    product (leadingMonomial b u) x = leadingMonomial b (octonionMul u (x.val 0)) := by
  apply Subtype.ext
  funext i
  cases b <;> fin_cases i <;>
    simp [product, octonionJetProduct, leadingMonomial, monomial, HigherJetBase.threshold,
      Fin.le_def, octonionMul_zero_left]

theorem product_leadingMonomial_right (b : HigherJetBase)
    (x : HigherJetCoefficients b b.threshold) (u : Octonion) :
    product x (leadingMonomial b u) = leadingMonomial b (octonionMul (x.val 0) u) := by
  apply Subtype.ext
  funext i
  cases b <;> fin_cases i <;>
    simp [product, octonionJetProduct, leadingMonomial, monomial, HigherJetBase.threshold,
      Fin.le_def, octonionMul_zero_right]

theorem leadingIdeal_twoSided (b : HigherJetBase)
    (x y : HigherJetCoefficients b b.threshold) (hy : y ∈ leadingIdeal b) :
    product x y ∈ leadingIdeal b ∧ product y x ∈ leadingIdeal b := by
  rcases hy with ⟨u, hu, rfl⟩
  rw [product_leadingMonomial_left, product_leadingMonomial_right]
  have hbase := (base x).symm
  constructor
  · apply Submodule.mem_map_of_mem
    cases b
    · change x.val 0 = octonionScalar (octonionReal (x.val 0)) at hbase
      rw [hbase, octonionMul_scalar_left]
      exact Submodule.smul_mem _ _ hu
    · change u.1 = 0 at hu
      have hp : (x.val 0).2 = 0 := congrArg Prod.snd hbase
      change (x.val 0).1 * u.1 - star u.2 * (x.val 0).2 = 0
      simp [hu, hp]
  · apply Submodule.mem_map_of_mem
    cases b
    · change x.val 0 = octonionScalar (octonionReal (x.val 0)) at hbase
      rw [hbase, octonionMul_scalar_right]
      exact Submodule.smul_mem _ _ hu
    · change u.1 = 0 at hu
      have hp : (x.val 0).2 = 0 := congrArg Prod.snd hbase
      change u.1 * (x.val 0).1 - star (x.val 0).2 * u.2 = 0
      simp [hu, hp]

def specialCoefficientMap (b : HigherJetBase) (m : Fin 4)
    (I : Submodule ℝ (HigherJetCoefficients b m))
    (hI : ∀ x y, y ∈ I → product x y ∈ I) :
    HigherJetCoefficients b m →ₗ[ℝ] Module.End ℝ (HigherJetCoefficients b m ⧸ I) :=
  leftRegularQuotient bilinear I hI

theorem exists_injective_specialCoefficientMap_below (b : HigherJetBase) (m : Fin 4)
    (hm : m < b.threshold) :
    ∃ f : HigherJetCoefficients b m →ₗ[ℝ]
        Module.End ℝ (HigherJetCoefficients b m ⧸ (⊥ : Submodule ℝ (HigherJetCoefficients b m))),
      Function.Injective f ∧ f (unit b m) = 1 ∧ ∀ x y, f (product x y) = f x * f y := by
  let hleft (x y : HigherJetCoefficients b m) (hy : y ∈ (⊥ : Submodule ℝ _)) :
      product x y ∈ (⊥ : Submodule ℝ _) := by
    rw [Submodule.mem_bot] at hy ⊢
    subst y
    exact map_zero (bilinear x)
  refine ⟨specialCoefficientMap b m ⊥ hleft, ?_, ?_, ?_⟩
  · apply LinearMap.ker_eq_bot.mp
    exact leftRegularQuotient_ker bilinear ⊥ hleft _ product_unit_right (fun x y hx => by
      rw [Submodule.mem_bot] at hx ⊢
      subst x
      exact LinearMap.congr_fun (map_zero (bilinear (b := b) (m := m))) y)
  · exact leftRegularQuotient_unit bilinear ⊥ hleft _ product_unit_left
  · apply leftRegularQuotient_product
    intro x y z
    rw [Submodule.mem_bot]
    exact associator_eq_zero_below b m hm x y z

theorem exists_specialCoefficientMap_at_threshold (b : HigherJetBase) :
    ∃ f : HigherJetCoefficients b b.threshold →ₗ[ℝ]
        Module.End ℝ (HigherJetCoefficients b b.threshold ⧸ leadingIdeal b),
      LinearMap.ker f = leadingIdeal b ∧ f (unit b b.threshold) = 1 ∧
      ∀ x y, f (product x y) = f x * f y := by
  let hl (x y : HigherJetCoefficients b b.threshold) (hy : y ∈ leadingIdeal b) :=
    (leadingIdeal_twoSided b x y hy).1
  refine ⟨specialCoefficientMap b b.threshold _ hl, ?_, ?_, ?_⟩
  · exact leftRegularQuotient_ker bilinear _ hl _ product_unit_right
      (fun x y hx => (leadingIdeal_twoSided b y x hx).2)
  · exact leftRegularQuotient_unit bilinear _ hl _ product_unit_left
  · exact leftRegularQuotient_product bilinear _ hl (associator_mem_leadingIdeal b)

end AlbertSequential.AppF.HigherJetCoefficients
