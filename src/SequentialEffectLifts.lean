/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CyclicWordQuotient

/-!
Finite formal-word combinations are represented by the span of paired model
operators and native effects. Membership means an actual finite linear
combination; it is not an assumed relation between quotient operators.
This module proves the all-history square-lift mechanism independently of
Albert-specific purity and reflection identities.
-/
@[expose] public section
noncomputable section
namespace AlbertSequential

section FiniteLifts
variable {ι A J : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
  [AddCommGroup J] [Module ℝ J]

local instance : Algebra ℝ A := Algebra.ofModule smul_mul_assoc mul_smul_comm

/-- A paired finite word combination, as a subspace of the literal two
evaluations. The native effect recursion remains a separate hypothesis. -/
def sequentialEffectLiftSpace (P : ι → A) (θ : Word ι → J) : Submodule ℝ (A × J) :=
  Submodule.span ℝ (Set.range (fun w => (wordOperator P w, θ w)))

def HasSequentialEffectLift (P : ι → A) (θ : Word ι → J) (Z : A) (x : J) : Prop :=
  (Z, x) ∈ sequentialEffectLiftSpace P θ

theorem wordAmplitude_star_reverse (P : ι → A) (hstar : ∀ i, star (P i) = P i)
    (w : Word ι) : star (wordAmplitude P w) = wordAmplitude P w.reverse := by
  induction w with
  | nil => simp only [wordAmplitude_nil, List.reverse_nil, star_one]
  | cons a w ih =>
      simp only [wordAmplitude_cons, star_mul, algebraicOutcome_star P hstar, ih,
        List.reverse_cons, wordAmplitude_append, wordAmplitude_singleton, wordAmplitude_nil, one_mul]

theorem wordOperator_mem_wordSubalgebra (P : ι → A) (hstar : ∀ i, star (P i) = P i)
    (w : Word ι) : wordOperator P w ∈ wordSubalgebra P := by
  change star (wordAmplitude P w) * wordAmplitude P w ∈ WordVectorSpan P
  rw [wordAmplitude_star_reverse P hstar]
  exact mul_mem_wordVectorSpan P (wordAmplitude_mem_wordVectorSpan P _) (wordAmplitude_mem_wordVectorSpan P _)

theorem sequentialEffectLift_operator_mem (P : ι → A) (θ : Word ι → J)
    (hstar : ∀ i, star (P i) = P i) {Z : A} {x : J}
    (hZ : HasSequentialEffectLift P θ Z x) : Z ∈ wordSubalgebra P := by
  have he : ∀ y ∈ sequentialEffectLiftSpace P θ, y.1 ∈ wordSubalgebra P := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        rcases hy with ⟨w, rfl⟩
        exact wordOperator_mem_wordSubalgebra P hstar w
    | zero => exact (wordSubalgebra P).zero_mem
    | add y z hy hz ihy ihz => exact (wordSubalgebra P).add_mem ihy ihz
    | smul r y hy ih => exact (WordVectorSpan P).smul_mem r ih
  exact he (Z, x) hZ

theorem hasSequentialEffectLift_word (P : ι → A) (θ : Word ι → J) (w : Word ι) :
    HasSequentialEffectLift P θ (wordOperator P w) (θ w) :=
  Submodule.subset_span ⟨w, rfl⟩

theorem hasSequentialEffectLift_zero (P : ι → A) (θ : Word ι → J) :
    HasSequentialEffectLift P θ 0 0 := (sequentialEffectLiftSpace P θ).zero_mem

theorem hasSequentialEffectLift_add (P : ι → A) (θ : Word ι → J)
    {Z Y : A} {x y : J} (hZ : HasSequentialEffectLift P θ Z x)
    (hY : HasSequentialEffectLift P θ Y y) : HasSequentialEffectLift P θ (Z + Y) (x + y) :=
  (sequentialEffectLiftSpace P θ).add_mem hZ hY

theorem hasSequentialEffectLift_smul (P : ι → A) (θ : Word ι → J) (r : ℝ)
    {Z : A} {x : J} (hZ : HasSequentialEffectLift P θ Z x) :
    HasSequentialEffectLift P θ (r • Z) (r • x) :=
  (sequentialEffectLiftSpace P θ).smul_mem r hZ

theorem hasSequentialEffectLift_sub (P : ι → A) (θ : Word ι → J)
    {Z Y : A} {x y : J} (hZ : HasSequentialEffectLift P θ Z x)
    (hY : HasSequentialEffectLift P θ Y y) : HasSequentialEffectLift P θ (Z - Y) (x - y) :=
  (sequentialEffectLiftSpace P θ).sub_mem hZ hY

/-- Matching on actual word probabilities extends to precisely the finite
paired span. This statement has no faithfulness or positivity premise. -/
theorem sequentialEffectLift_expectation (P : ι → A) (θ : Word ι → J)
    (φ : A →ₗ[ℝ] ℝ) (ω : J →ₗ[ℝ] ℝ)
    (hmatch : ∀ w, φ (wordOperator P w) = ω (θ w))
    {Z : A} {x : J} (hZ : HasSequentialEffectLift P θ Z x) : φ Z = ω x := by
  have he : ∀ y ∈ sequentialEffectLiftSpace P θ, φ y.1 = ω y.2 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        rcases hy with ⟨w, rfl⟩
        exact hmatch w
    | zero => simp only [Prod.fst_zero, Prod.snd_zero, map_zero]
    | add y z hy hz ihy ihz =>
        simpa only [Prod.fst_add, Prod.snd_add, map_add, ihy, ihz]
    | smul r y hy ih =>
        simpa only [Prod.smul_fst, Prod.smul_snd, map_smul, ih]
  exact he (Z, x) hZ

/-- One-outcome corner action on the paired evaluations. -/
def sequentialLiftCorner (P : ι → A) (U : Outcome ι → Module.End ℝ J)
    (a : Outcome ι) : Module.End ℝ (A × J) where
  toFun z := (algebraicOutcome P a * z.1 * algebraicOutcome P a, U a z.2)
  map_add' z w := by simp only [Prod.fst_add, Prod.snd_add, mul_add, add_mul, map_add, Prod.mk_add_mk]
  map_smul' r z := by simp [mul_smul_comm, smul_mul_assoc]

theorem hasSequentialEffectLift_prefix (P : ι → A) (θ : Word ι → J)
    (U : Outcome ι → Module.End ℝ J)
    (hstar : ∀ i, star (P i) = P i)
    (hθ : ∀ a w, θ (a :: w) = U a (θ w))
    (a : Outcome ι) {Z : A} {x : J} (hZ : HasSequentialEffectLift P θ Z x) :
    HasSequentialEffectLift P θ
      (algebraicOutcome P a * Z * algebraicOutcome P a) (U a x) := by
  have hclosed : ∀ z ∈ sequentialEffectLiftSpace P θ,
      sequentialLiftCorner P U a z ∈ sequentialEffectLiftSpace P θ := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
        rcases hz with ⟨w, rfl⟩
        change HasSequentialEffectLift P θ
          (algebraicOutcome P a * wordOperator P w * algebraicOutcome P a) (U a (θ w))
        rw [← wordOperator_cons P hstar, ← hθ]
        exact hasSequentialEffectLift_word P θ _
    | zero => simpa only [map_zero] using (sequentialEffectLiftSpace P θ).zero_mem
    | add z w hz hw ihz ihw =>
        rw [map_add]
        exact (sequentialEffectLiftSpace P θ).add_mem ihz ihw
    | smul r z hz ih =>
        rw [map_smul]
        exact (sequentialEffectLiftSpace P θ).smul_mem r ih
  exact hclosed (Z, x) hZ

/-- Native reflection expressed entirely through the two outcome updates. -/
def sequentialReflectionUpdate (U : Outcome ι → Module.End ℝ J) (i : ι) : Module.End ℝ J :=
  (2 : ℝ) • (U (i, true) + U (i, false)) - 1

def projectionReflection (P : ι → A) (i : ι) : A := (2 : ℝ) • P i - 1

theorem hasSequentialEffectLift_reflection (P : ι → A) (θ : Word ι → J)
    (U : Outcome ι → Module.End ℝ J)
    (hstar : ∀ i, star (P i) = P i)
    (hθ : ∀ a w, θ (a :: w) = U a (θ w))
    (i : ι) {Z : A} {x : J} (hZ : HasSequentialEffectLift P θ Z x) :
    HasSequentialEffectLift P θ
      (projectionReflection P i * Z * projectionReflection P i)
      (sequentialReflectionUpdate U i x) := by
  have hy := hasSequentialEffectLift_prefix P θ U hstar hθ (i, true) hZ
  have hn := hasSequentialEffectLift_prefix P θ U hstar hθ (i, false) hZ
  have h := hasSequentialEffectLift_sub P θ
    (hasSequentialEffectLift_smul P θ (2 : ℝ) (hasSequentialEffectLift_add P θ hy hn)) hZ
  have he : (2 : ℝ) •
      (algebraicOutcome P (i, true) * Z * algebraicOutcome P (i, true) +
        algebraicOutcome P (i, false) * Z * algebraicOutcome P (i, false)) - Z =
      projectionReflection P i * Z * projectionReflection P i := by
    simp only [algebraicOutcome, Bool.false_eq_true, ↓reduceIte, projectionReflection, two_smul]
    noncomm_ring
  rw [he] at h
  exact h

def projectionReflectionWord (P : ι → A) : List ι → A
  | [] => 1
  | i :: g => projectionReflection P i * projectionReflectionWord P g

def reflectionWordUpdate (U : Outcome ι → Module.End ℝ J) : List ι → Module.End ℝ J
  | [] => 1
  | i :: g => (sequentialReflectionUpdate U i).comp (reflectionWordUpdate U g)

theorem projectionReflectionWord_append (P : ι → A) (g h : List ι) :
    projectionReflectionWord P (g ++ h) = projectionReflectionWord P g * projectionReflectionWord P h := by
  induction g with
  | nil => simp only [List.nil_append, projectionReflectionWord, one_mul]
  | cons i g ih => simp only [List.cons_append, projectionReflectionWord, ih, mul_assoc]

theorem projectionReflection_star (P : ι → A) (hstar : ∀ i, star (P i) = P i)
    (i : ι) : star (projectionReflection P i) = projectionReflection P i := by
  simp only [projectionReflection, star_sub, star_smul, star_trivial, hstar, star_one]

theorem projectionReflectionWord_reverse (P : ι → A) (hstar : ∀ i, star (P i) = P i)
    (g : List ι) : projectionReflectionWord P g.reverse = star (projectionReflectionWord P g) := by
  induction g with
  | nil => simp only [List.reverse_nil, projectionReflectionWord, star_one]
  | cons i g ih =>
      simp only [List.reverse_cons, projectionReflectionWord_append, projectionReflectionWord,
        mul_one, star_mul, projectionReflection_star P hstar, ih]

theorem projectionReflection_square (P : ι → A) (hp : ∀ i, P i * P i = P i)
    (i : ι) : projectionReflection P i * projectionReflection P i = 1 := by
  simp only [projectionReflection, two_smul]
  noncomm_ring [hp i]

theorem projectionReflectionWord_star_mul (P : ι → A)
    (hp : ∀ i, P i * P i = P i) (hstar : ∀ i, star (P i) = P i) (g : List ι) :
    star (projectionReflectionWord P g) * projectionReflectionWord P g = 1 := by
  induction g with
  | nil => simp only [projectionReflectionWord, star_one, mul_one]
  | cons i g ih =>
      simp only [projectionReflectionWord, star_mul, projectionReflection_star P hstar]
      calc
        star (projectionReflectionWord P g) * projectionReflection P i *
            (projectionReflection P i * projectionReflectionWord P g) =
            star (projectionReflectionWord P g) *
              (projectionReflection P i * projectionReflection P i) * projectionReflectionWord P g := by
          simp only [mul_assoc]
        _ = 1 := by rw [projectionReflection_square P hp, mul_one, ih]

theorem projectionReflectionWord_mul_star (P : ι → A)
    (hp : ∀ i, P i * P i = P i) (hstar : ∀ i, star (P i) = P i) (g : List ι) :
    projectionReflectionWord P g * star (projectionReflectionWord P g) = 1 := by
  induction g with
  | nil => simp only [projectionReflectionWord, star_one, mul_one]
  | cons i g ih =>
      simp only [projectionReflectionWord, star_mul, projectionReflection_star P hstar]
      calc
        projectionReflection P i * projectionReflectionWord P g *
            (star (projectionReflectionWord P g) * projectionReflection P i) =
            projectionReflection P i *
              (projectionReflectionWord P g * star (projectionReflectionWord P g)) * projectionReflection P i := by
          simp only [mul_assoc]
        _ = 1 := by rw [ih, mul_one, projectionReflection_square P hp]

/-- Any finite orbit conjugation has a finite word lift. No native
automorphism, primitive-idempotent or fundamental-formula fact is assumed. -/
theorem hasSequentialEffectLift_reflection_word (P : ι → A) (θ : Word ι → J)
    (U : Outcome ι → Module.End ℝ J)
    (hstar : ∀ i, star (P i) = P i)
    (hθ : ∀ a w, θ (a :: w) = U a (θ w))
    (g : List ι) {Z : A} {x : J} (hZ : HasSequentialEffectLift P θ Z x) :
    HasSequentialEffectLift P θ
      (projectionReflectionWord P g * Z * star (projectionReflectionWord P g))
      (reflectionWordUpdate U g x) := by
  induction g with
  | nil => simpa only [projectionReflectionWord, reflectionWordUpdate, star_one,
      one_mul, mul_one, one_apply_eq_self] using hZ
  | cons i g ih =>
      have h := hasSequentialEffectLift_reflection P θ U hstar hθ i ih
      simpa only [projectionReflectionWord, reflectionWordUpdate, LinearMap.comp_apply,
        star_mul, projectionReflection_star P hstar, mul_assoc] using h

def orbitProjection (P : ι → A) (g : List ι) (i : ι) : A :=
  projectionReflectionWord P g * P i * star (projectionReflectionWord P g)

def orbitCornerUpdate (U : Outcome ι → Module.End ℝ J) (g : List ι) (i : ι) : Module.End ℝ J :=
  (reflectionWordUpdate U g).comp ((U (i, true)).comp (reflectionWordUpdate U g.reverse))

def orbitReflectionUpdate (U : Outcome ι → Module.End ℝ J) (g : List ι) (i : ι) : Module.End ℝ J :=
  (reflectionWordUpdate U g).comp
    ((sequentialReflectionUpdate U i).comp (reflectionWordUpdate U g.reverse))

theorem conjugate_projectionReflection (P : ι → A)
    (hp : ∀ i, P i * P i = P i) (hstar : ∀ i, star (P i) = P i) (g : List ι) (i : ι) :
    projectionReflectionWord P g * projectionReflection P i * star (projectionReflectionWord P g) =
      (2 : ℝ) • orbitProjection P g i - 1 := by
  unfold projectionReflection orbitProjection
  simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  rw [projectionReflectionWord_mul_star P hp hstar]

theorem orbitProjection_star (P : ι → A) (hstar : ∀ i, star (P i) = P i)
    (g : List ι) (i : ι) : star (orbitProjection P g i) = orbitProjection P g i := by
  simp only [orbitProjection, star_mul, star_star, hstar, mul_assoc]

theorem orbitProjection_idempotent (P : ι → A)
    (hp : ∀ i, P i * P i = P i) (hstar : ∀ i, star (P i) = P i)
    (g : List ι) (i : ι) : orbitProjection P g i * orbitProjection P g i = orbitProjection P g i := by
  unfold orbitProjection
  calc
    projectionReflectionWord P g * P i * star (projectionReflectionWord P g) *
        (projectionReflectionWord P g * P i * star (projectionReflectionWord P g)) =
        projectionReflectionWord P g * P i *
          (star (projectionReflectionWord P g) * projectionReflectionWord P g) *
          P i * star (projectionReflectionWord P g) := by simp only [mul_assoc]
    _ = _ := by
      rw [projectionReflectionWord_star_mul P hp hstar, mul_one]
      simpa only [mul_assoc] using congrArg
        (fun y => projectionReflectionWord P g * y * star (projectionReflectionWord P g)) (hp i)

theorem hasSequentialEffectLift_orbit_corner (P : ι → A) (θ : Word ι → J)
    (U : Outcome ι → Module.End ℝ J)
    (hstar : ∀ i, star (P i) = P i)
    (hθ : ∀ a w, θ (a :: w) = U a (θ w))
    (g : List ι) (i : ι) {Z : A} {x : J} (hZ : HasSequentialEffectLift P θ Z x) :
    HasSequentialEffectLift P θ (orbitProjection P g i * Z * orbitProjection P g i)
      (orbitCornerUpdate U g i x) := by
  have hi := hasSequentialEffectLift_prefix P θ U hstar hθ (i, true)
    (hasSequentialEffectLift_reflection_word P θ U hstar hθ g.reverse hZ)
  have hg := hasSequentialEffectLift_reflection_word P θ U hstar hθ g hi
  simpa only [projectionReflectionWord_reverse P hstar, star_star, algebraicOutcome,
    ↓reduceIte, orbitProjection, orbitCornerUpdate, LinearMap.comp_apply, mul_assoc] using hg

theorem hasSequentialEffectLift_orbit_reflection (P : ι → A) (θ : Word ι → J)
    (U : Outcome ι → Module.End ℝ J)
    (hp : ∀ i, P i * P i = P i) (hstar : ∀ i, star (P i) = P i)
    (hθ : ∀ a w, θ (a :: w) = U a (θ w))
    (g : List ι) (i : ι) {Z : A} {x : J} (hZ : HasSequentialEffectLift P θ Z x) :
    HasSequentialEffectLift P θ
      (((2 : ℝ) • orbitProjection P g i - 1) * Z * ((2 : ℝ) • orbitProjection P g i - 1))
      (orbitReflectionUpdate U g i x) := by
  have hi := hasSequentialEffectLift_reflection P θ U hstar hθ i
    (hasSequentialEffectLift_reflection_word P θ U hstar hθ g.reverse hZ)
  have hg := hasSequentialEffectLift_reflection_word P θ U hstar hθ g hi
  have he : projectionReflectionWord P g *
      (projectionReflection P i * (projectionReflectionWord P g.reverse * Z *
        star (projectionReflectionWord P g.reverse)) * projectionReflection P i) *
      star (projectionReflectionWord P g) =
      (((2 : ℝ) • orbitProjection P g i - 1) * Z * ((2 : ℝ) • orbitProjection P g i - 1)) := by
    rw [projectionReflectionWord_reverse P hstar, star_star,
      ← conjugate_projectionReflection P hp hstar g i]
    simp only [mul_assoc]
  rw [he] at hg
  exact hg

/-- Prefixing any entire history preserves a finite lift. The native effect
is updated in effect order, the same order as operator conjugation. -/
theorem hasSequentialEffectLift_history (P : ι → A) (θ : Word ι → J)
    (U : Outcome ι → Module.End ℝ J)
    (hstar : ∀ i, star (P i) = P i)
    (hθ : ∀ a w, θ (a :: w) = U a (θ w))
    (t : Word ι) {Z : A} {x : J} (hZ : HasSequentialEffectLift P θ Z x) :
    HasSequentialEffectLift P θ
      (star (wordAmplitude P t) * Z * wordAmplitude P t)
      (t.foldr (fun a y => U a y) x) := by
  induction t with
  | nil => simpa only [wordAmplitude_nil, star_one, one_mul, mul_one, List.foldr_nil] using hZ
  | cons a t ih =>
      have hp := hasSequentialEffectLift_prefix P θ U hstar hθ a ih
      simpa only [List.foldr_cons, wordAmplitude_cons, star_mul,
        algebraicOutcome_star P hstar, mul_assoc] using hp

theorem sequentialEffectLift_square_null (M : AlgebraicProjectiveData ι A)
    (θ : Word ι → J) (U : Outcome ι → Module.End ℝ J)
    (hθ : ∀ a w, θ (a :: w) = U a (θ w)) (ω : J →ₗ[ℝ] ℝ)
    (hmatch : ∀ w, M.probability w = ω (θ w))
    {Z : A} (hZstar : star Z = Z) (hlift : HasSequentialEffectLift M.projection θ (Z * Z) 0)
    (t : Word ι) : NullFor M.state (Z * wordAmplitude M.projection t) := by
  have hzero : t.foldr (fun a y => U a y) 0 = 0 := by
    induction t with
    | nil => rfl
    | cons a t ih => simp only [List.foldr_cons, ih, map_zero]
  have h := hasSequentialEffectLift_history M.projection θ U M.selfAdjoint hθ t hlift
  have he := sequentialEffectLift_expectation M.projection θ M.state ω hmatch h
  rw [hzero, map_zero] at he
  simpa only [NullFor, star_mul, hZstar, mul_assoc] using he

/-- The square lift gives equality to zero in the constructed associative
target, rather than illicit equality in the original nonfaithful model. -/
theorem cyclicRepresentation_eq_zero_of_square_lift (M : AlgebraicProjectiveData ι A)
    (θ : Word ι → J) (U : Outcome ι → Module.End ℝ J)
    (hθ : ∀ a w, θ (a :: w) = U a (θ w)) (ω : J →ₗ[ℝ] ℝ)
    (hmatch : ∀ w, M.probability w = ω (θ w))
    (Z : wordSubalgebra M.projection) (hZstar : star (Z : A) = Z)
    (hlift : HasSequentialEffectLift M.projection θ ((Z : A) * Z) 0) :
    cyclicRepresentation M Z = 0 := by
  apply cyclicRepresentation_eq_zero_of_all_histories
  exact sequentialEffectLift_square_null M θ U hθ ω hmatch hZstar hlift

end FiniteLifts
end AlbertSequential
