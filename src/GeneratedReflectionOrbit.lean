/- SPDX-License-Identifier: Apache-2.0 -/
module
public import FiveTest.JordanReflection
public import JordanPrimitivePairing
public import GeneralEJAGenerated

/-! Orbit span for tests primitive in the generated Euclidean Jordan algebra, core 4.7. -/
@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace AlbertSequential.UnitalJordanProduct
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (P : UnitalJordanProduct E) (q : I → E)

def reflectedMenuPoint : List I → I → E
  | [], i => q i
  | k :: w, i => P.idempotentReflection (q k) (reflectedMenuPoint w i)

def reflectedMenuSpan : Submodule ℝ E :=
  Submodule.span ℝ (insert P.unit (Set.range (fun a : List I × I => P.reflectedMenuPoint q a.1 a.2)))

private theorem point_mem (w : List I) (i : I) : P.reflectedMenuPoint q w i ∈ P.reflectedMenuSpan q :=
  Submodule.subset_span (Set.mem_insert_of_mem _ ⟨(w,i),rfl⟩)

private theorem unit_mem : P.unit ∈ P.reflectedMenuSpan q := Submodule.subset_span (Set.mem_insert _ _)

private theorem simple_reflection_preserves (hq : ∀ i, P.IsPrimitive (q i)) (k : I) :
    P.reflectedMenuSpan q ≤ (P.reflectedMenuSpan q).comap (P.idempotentReflection (q k)) := by
  apply Submodule.span_le.mpr
  rintro x (rfl | ⟨⟨w,i⟩,rfl⟩)
  · change P.idempotentReflection (q k) P.unit ∈ P.reflectedMenuSpan q
    rw [P.idempotentReflection_unit _ (hq k).1]; exact unit_mem P q
  · exact point_mem P q (k::w) i

private theorem orbit_reflection_preserves (hq : ∀ i, P.IsPrimitive (q i)) (w : List I) (i : I)
    (x : E) (hx : x ∈ P.reflectedMenuSpan q) :
    P.idempotentReflection (P.reflectedMenuPoint q w i) x ∈ P.reflectedMenuSpan q := by
  induction w generalizing x with
  | nil => exact simple_reflection_preserves P q hq i hx
  | cons k w ih =>
    let R := P.idempotentReflection (q k)
    have hr : R ((2 : ℝ) • P.reflectedMenuPoint q w i - P.unit) =
        (2 : ℝ) • P.reflectedMenuPoint q (k::w) i - P.unit := by
      rw [map_sub, map_smul, show R P.unit = P.unit from P.idempotentReflection_unit _ (hq k).1]
      rfl
    change P.quadraticRepresentation _ x ∈ _
    rw [← hr, P.idempotentReflection_quadratic]
    exact simple_reflection_preserves P q hq k (ih _ (simple_reflection_preserves P q hq k hx))

theorem reflectedMenuPoint_primitive (hq : ∀ i, P.IsPrimitive (q i)) (w : List I) (i : I) :
    P.IsPrimitive (P.reflectedMenuPoint q w i) := by
  induction w with
  | nil => exact hq i
  | cons k w ih => exact P.idempotentReflection_primitive _ (hq k).1 ih

theorem peirce_product_reflection (a x : E) (ha : P.product a a = a) :
    P.product a x = P.quadraticRepresentation a x +
      (1/4 : ℝ) • (x - P.idempotentReflection a x) := by
  have hu (y : E) : P.product y P.unit = y := (P.commutative _ _).trans (P.unit_left _)
  simp only [idempotentReflection, quadraticRepresentation_apply, map_sub, map_smul,
    LinearMap.sub_apply, LinearMap.smul_apply, P.unit_left, hu, ha]
  module

variable [FiniteDimensional ℝ E]

theorem reflectedMenuSpan_eq_top (hinner : ∀ x y z, inner ℝ (P.product x y) z =
    inner ℝ x (P.product y z)) (hq : ∀ i, P.IsPrimitive (q i)) (hg : P.GeneratesMenu q) :
    P.reflectedMenuSpan q = ⊤ := by
  let S := P.reflectedMenuSpan q
  have hmul (y : E) (hy : y ∈ S) : S ≤ S.comap ((P.product).flip y) := by
    apply Submodule.span_le.mpr
    rintro x (rfl | ⟨⟨w,i⟩,rfl⟩)
    · change P.product P.unit y ∈ S
      rwa [P.unit_left]
    · let a := P.reflectedMenuPoint q w i
      have ha := P.reflectedMenuPoint_primitive q hq w i
      change P.product a y ∈ S
      rw [peirce_product_reflection P a y ha.1, P.primitive_quadraticRepresentation_coefficient hinner a y ha]
      exact S.add_mem (S.smul_mem _ (point_mem P q w i))
        (S.smul_mem _ (S.sub_mem hy (orbit_reflection_preserves P q hq w i y hy)))
  exact top_unique (fun x _ => hg S (unit_mem P q) (fun _ hx y hy => hmul y hy hx)
    (fun i => point_mem P q [] i) x)

/-- Each test may be replaced by its complement before taking its primitive orbit. -/
theorem generatedMenu_reflection_span (p : I → E)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (a : I → P.generatedMenuCarrier p)
    (ha : ∀ i, (P.generatedMenuProduct p).IsPrimitive (a i))
    (hchoice : ∀ i, a i = P.generatedMenuTest p i ∨
      a i = (P.generatedMenuProduct p).unit - P.generatedMenuTest p i) :
    (P.generatedMenuProduct p).reflectedMenuSpan a = ⊤ := by
  let B := P.generatedMenuProduct p
  apply B.reflectedMenuSpan_eq_top a (P.generatedMenuProduct_inner p hinner) ha
  intro S hunit hprod hseed
  apply P.generatedMenuProduct_generates p S hunit hprod
  intro i
  rcases hchoice i with h | h
  · exact h ▸ hseed i
  · have hmem := S.sub_mem hunit (hseed i)
    rw [h, sub_sub_cancel] at hmem
    exact hmem

end AlbertSequential.UnitalJordanProduct
