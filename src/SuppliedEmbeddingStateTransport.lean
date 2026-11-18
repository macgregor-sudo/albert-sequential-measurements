/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HermitianStateTransport
public import Interfaces.SeparationAndConverse
public import NativeSquareCone
public import NativeJordanIdentity
public import ChronologicalWords

/-! Exact state transport for the existing supplied native-subalgebra interface.
The ordinary matrix trace determines a density inside the supplied image.
No embedding existence, subalgebra classification or trace preservation is used. -/
@[expose] public section
noncomputable section
open scoped ComplexOrder
namespace AlbertSequential
open NativeAnalysis

namespace NativeJordanSubalgebra
variable (B : NativeJordanSubalgebra)

def restrictedProduct : UnitalJordanProduct B.carrier where
  product :=
    { toFun x :=
        { toFun y := ⟨jordanMul x y, B.product_mem x x.property y y.property⟩
          map_add' y z := Subtype.ext (jordanMul_add_right x y z)
          map_smul' r y := Subtype.ext (jordanMul_smul_right r x y) }
      map_add' x y := by ext z; exact jordanMul_add_left x y z
      map_smul' r x := by ext z; exact jordanMul_smul_left r x z }
  unit := ⟨albertUnit, B.unit_mem⟩
  commutative x y := Subtype.ext (jordanMul_comm x y)
  unit_left x := Subtype.ext (jordanMul_albertUnit_left x)
  jordan_identity x y := Subtype.ext (jordan_identity x y)

def densityFunctional (ρ : Albert) : B.carrier →ₗ[ℝ] ℝ where
  toFun x := tracePairing ρ x
  map_add' x y := tracePairing_add_right ρ x y
  map_smul' r x := tracePairing_smul_right r ρ x

theorem densityFunctional_positive (ρ : Albert) (hρ : IsDensity ρ) (x : B.carrier) :
    0 ≤ B.densityFunctional ρ (B.restrictedProduct.product x x) :=
  (isPositive_iff_dual_squares ρ).mp hρ.1 x

theorem densityFunctional_normalized (ρ : Albert) (hρ : IsDensity ρ) :
    B.densityFunctional ρ B.restrictedProduct.unit = 1 := by
  change tracePairing ρ albertUnit = 1
  rw [tracePairing_unit_right]
  exact hρ.2

theorem quadratic_mem {a x : Albert} (ha : a ∈ B.carrier) (hx : x ∈ B.carrier) :
    quadraticMap a x ∈ B.carrier := by
  unfold quadraticMap
  rw [two_smul]
  exact B.carrier.sub_mem
    (B.carrier.add_mem (B.product_mem a ha _ (B.product_mem a ha x hx))
      (B.product_mem a ha _ (B.product_mem a ha x hx)))
    (B.product_mem _ (B.product_mem a ha a ha) x hx)

def restrictedQuadratic (a x : B.carrier) : B.carrier :=
  ⟨quadraticMap a x, B.quadratic_mem a.property x.property⟩

def restrictedOutcome {X : Type*} (p : X → B.carrier) (a : Outcome X) : B.carrier :=
  if a.2 then p a.1 else B.restrictedProduct.unit - p a.1

@[simp] theorem restrictedOutcome_value {X : Type*}
    (p : X → B.carrier) (a : Outcome X) :
    (B.restrictedOutcome p a : Albert) = nativeOutcome (fun i => (p i : Albert)) a := by
  rcases a with ⟨i, b⟩
  cases b <;> rfl

def restrictedWordEffect {X : Type*} (p : X → B.carrier) (w : Word X) : B.carrier :=
  w.foldr (fun a x => B.restrictedQuadratic (B.restrictedOutcome p a) x)
    B.restrictedProduct.unit

@[simp] theorem restrictedWordEffect_value {X : Type*} (p : X → B.carrier) (w : Word X) :
    (B.restrictedWordEffect p w : Albert) = nativeWordEffect (fun i => (p i : Albert)) w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      change quadraticMap (B.restrictedOutcome p a) (B.restrictedWordEffect p w) = _
      rw [B.restrictedOutcome_value, ih]
      rfl

end NativeJordanSubalgebra

namespace SuppliedHermitianEmbedding
variable {B : NativeJordanSubalgebra} {d : ℕ} (ι : SuppliedHermitianEmbedding B d)

def faithfulEmbedding : FaithfulHermitianJordanEmbedding B.restrictedProduct d where
  map := ι.map
  injective := ι.injective
  hermitian := ι.hermitian
  unit := ι.unit
  jordan := ι.jordan

theorem unique_pairing (ρ : Albert) :
    ∃! z : B.carrier, ∀ x : B.carrier,
      (Matrix.trace (ι.map z * ι.map x)).re = tracePairing ρ x :=
  ι.faithfulEmbedding.exists_unique_trace_representative (B.densityFunctional ρ)

theorem pairing_density (ρ : Albert) (hρ : IsDensity ρ) (z : B.carrier)
    (hz : ∀ x : B.carrier,
      (Matrix.trace (ι.map z * ι.map x)).re = tracePairing ρ x) :
    IsEmbeddingDensity d (ι.map z) :=
  ⟨ι.faithfulEmbedding.trace_representative_positive (B.densityFunctional ρ)
      (B.densityFunctional_positive ρ hρ) z hz,
    ι.faithfulEmbedding.trace_representative_trace_one (B.densityFunctional ρ)
      (B.densityFunctional_positive ρ hρ) (B.densityFunctional_normalized ρ hρ) z hz⟩

theorem map_quadratic (a x : B.carrier) :
    ι.map (B.restrictedQuadratic a x) = ι.map a * ι.map x * ι.map a := by
  have hid : B.restrictedQuadratic a x =
      B.restrictedProduct.quadraticRepresentation a x := by
    apply Subtype.ext
    change quadraticMap (a : Albert) x =
      (2 : ℝ) • jordanMul a (jordanMul a x) - jordanMul (jordanMul a a) x
    simp only [quadraticMap, two_smul]
  rw [hid]
  exact ι.faithfulEmbedding.map_quadratic a x

@[simp] theorem map_outcome {X : Type*} (p : X → B.carrier) (a : Outcome X) :
    ι.map (B.restrictedOutcome p a) = algebraicOutcome (fun i => ι.map (p i)) a := by
  rcases a with ⟨i, b⟩
  cases b <;> simp [NativeJordanSubalgebra.restrictedOutcome, algebraicOutcome,
    NativeJordanSubalgebra.restrictedProduct, ι.unit]

/-- The product/effect identity holds even without idempotence of the menu. -/
theorem map_wordEffect {X : Type*} (p : X → B.carrier) (w : Word X) :
    ι.map (B.restrictedWordEffect p w) = wordOperator (fun i => ι.map (p i)) w := by
  induction w with
  | nil =>
      rw [wordOperator_nil]
      exact ι.unit
  | cons a w ih =>
      change ι.map (B.restrictedQuadratic (B.restrictedOutcome p a)
        (B.restrictedWordEffect p w)) = _
      rw [ι.map_quadratic, ι.map_outcome, ih,
        wordOperator_cons (fun i => ι.map (p i)) (fun i => ι.hermitian (p i))]

theorem pairing_words (ρ : Albert) (z : B.carrier)
    (hz : ∀ x : B.carrier,
      (Matrix.trace (ι.map z * ι.map x)).re = tracePairing ρ x)
    {X : Type*} (p : X → B.carrier) (w : Word X) :
    (Matrix.trace (ι.map z * wordOperator (fun i => ι.map (p i)) w)).re =
      nativeWordProbability (fun i => (p i : Albert)) ρ w := by
  rw [← ι.map_wordEffect p w, hz, nativeWordProbability_eq_pairing]
  rw [B.restrictedWordEffect_value]

end SuppliedHermitianEmbedding

theorem suppliedEmbeddingStateTransport : SuppliedEmbeddingStateTransport where
  unique_pairing _B _d ι ρ _ := ι.unique_pairing ρ
  density_and_words _B _d ι ρ hρ z hz :=
    ⟨ι.pairing_density ρ hρ z hz, fun _ p _ w => ι.pairing_words ρ z hz p w⟩

end AlbertSequential
