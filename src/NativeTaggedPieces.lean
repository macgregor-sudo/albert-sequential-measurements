/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeScalarKrausSources
public import TaggedLinearEncoding

/-! Scalar preparation/reset tags and atomic zero-corner tags. Decoders name
the represented native piece explicitly; only their sum is the native state. -/
@[expose] public section
noncomputable section
open scoped BigOperators Matrix ComplexOrder
namespace AlbertSequential.NativeAnalysis

def nativeTaggedTrace : Albert →ₗ[ℝ] ℝ where
  toFun := albertTrace
  map_add' := albertTrace_add
  map_smul' r x := albertTrace_smul r x

def nativeTaggedBlock {S : Type*} {n : ℕ} : S ⊕ Fin n → Type
  | .inl _ => Unit
  | .inr _ => SpinorCoordinate

instance nativeTaggedBlock_fintype {S : Type*} {n : ℕ} (t : S ⊕ Fin n) :
    Fintype (nativeTaggedBlock t) := by cases t <;> dsimp [nativeTaggedBlock] <;> infer_instance

instance nativeTaggedBlock_decidableEq {S : Type*} {n : ℕ} (t : S ⊕ Fin n) :
    DecidableEq (nativeTaggedBlock t) := by cases t <;> dsimp [nativeTaggedBlock] <;> infer_instance

def nativeTaggedPieceDecoder {S : Type*} {n : ℕ} (p : Fin n → Albert) (z : S → Albert) :
    S ⊕ Fin n → Module.End ℝ Albert
  | .inl s => nativeTaggedTrace.smulRight (z s)
  | .inr i => quadraticMapLinear (albertUnit - p i)

def nativeTaggedPieceEncoding {S : Type*} {n : ℕ} (p : Fin n → Albert)
    (hp : ∀ i, IsAtom (p i)) :
    ∀ t : S ⊕ Fin n, Albert →ₗ[ℝ] Matrix (nativeTaggedBlock t) (nativeTaggedBlock t) ℝ
  | .inl _ => nativeTaggedTrace.smulRight 1
  | .inr i => (nativeCornerEncoding (p i) (hp i)).comp (nativeCornerProjection (p i) (hp i))

theorem nativeTaggedPiece_trace {S : Type*} {n : ℕ} (p : Fin n → Albert)
    (hp : ∀ i, IsAtom (p i)) (z : S → Albert) (hz : ∀ s, IsDensity (z s))
    (t : S ⊕ Fin n) (x : Albert) :
    Matrix.trace (nativeTaggedPieceEncoding p hp t x) =
      albertTrace (nativeTaggedPieceDecoder p z t x) := by
  cases t with
  | inl s =>
    change Matrix.trace (albertTrace x • (1 : Matrix Unit Unit ℝ)) = albertTrace (albertTrace x • z s)
    rw [Matrix.trace_smul, albertTrace_smul, (hz s).2]
    simp
  | inr i => exact nativeCornerEncoding_trace (p i) (hp i) _

theorem nativeTaggedPiece_positive {S : Type*} {n : ℕ} (p : Fin n → Albert)
    (hp : ∀ i, IsAtom (p i)) (t : S ⊕ Fin n) (x : Albert) (hx : IsPositive x) :
    (nativeTaggedPieceEncoding p hp t x).PosSemidef := by
  cases t with
  | inl s => exact Matrix.PosSemidef.one.smul (isPositive_trace_nonnegative x hx)
  | inr i => exact nativeScalarNoState_positive (p i) (hp i) x hx

def nativeTaggedTarget {S : Type*} {n : ℕ} (reset : Fin n → S) (a : Outcome (Fin n)) :
    S ⊕ Fin n := if a.2 then .inl (reset a.1) else .inr a.1

theorem nativeTaggedTarget_decoder {S : Type*} {n : ℕ} (p : Fin n → Albert)
    (hp : ∀ i, IsAtom (p i)) (z : S → Albert) (reset : Fin n → S)
    (hreset : ∀ i, z (reset i) = p i) (a : Outcome (Fin n)) (x : Albert) :
    nativeTaggedPieceDecoder p z (nativeTaggedTarget reset a)
      (quadraticMap (nativeOutcome p a) x) = quadraticMap (nativeOutcome p a) x := by
  rcases a with ⟨i,b⟩
  cases b
  · change quadraticMap (albertUnit - p i) (quadraticMap (albertUnit - p i) x) = _
    exact quadraticMap_idempotent_comp _ x (complementary_idempotent (p i) (hp i).1)
  · change albertTrace (quadraticMap (p i) x) • z (reset i) = quadraticMap (p i) x
    rw [hreset, albertTrace_quadraticMap, (hp i).1, quadraticMap_atom (p i) x (hp i)]

theorem nativeTaggedTarget_encoding_yes {S : Type*} {n : ℕ} (p : Fin n → Albert)
    (hp : ∀ i, IsAtom (p i)) (s : S) (i : Fin n) (x : Albert) :
    nativeTaggedPieceEncoding p hp (.inl s) (quadraticMap (p i) x) =
      tracePairing (p i) x • (1 : Matrix Unit Unit ℝ) := by
  change albertTrace (quadraticMap (p i) x) • (1 : Matrix Unit Unit ℝ) = _
  rw [albertTrace_quadraticMap, (hp i).1]

theorem nativeTaggedTarget_encoding_no {S : Type*} {n : ℕ} (p : Fin n → Albert)
    (hp : ∀ i, IsAtom (p i)) (i : Fin n) (x : Albert) :
    nativeTaggedPieceEncoding p hp (.inr i : S ⊕ Fin n)
      (quadraticMap (albertUnit - p i) x) =
      nativeCornerEncoding (p i) (hp i) (nativeCornerProjection (p i) (hp i) x) := by
  change nativeCornerEncoding (p i) (hp i)
    (nativeCornerProjection (p i) (hp i) (quadraticMap (albertUnit - p i) x)) = _
  apply congrArg (nativeCornerEncoding (p i) (hp i))
  apply Subtype.ext
  exact quadraticMap_idempotent_comp _ x (complementary_idempotent (p i) (hp i).1)

end AlbertSequential.NativeAnalysis
