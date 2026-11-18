/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeTaggedPieces
public import TaggedAllWordSimulation

/-! Actual native branch maps for every scalar and corner source tag.
All local Kraus families are real and satisfy full per-source normalization. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.NativeAnalysis

def nativeTaggedLocalYes {S : Type*} {n : ℕ} (p : Fin n → Albert)
    (hp : ∀ i, IsAtom (p i)) (z : S → Albert) (hz : ∀ s, IsDensity (z s)) (j : Fin n) :
    ∀ s : S ⊕ Fin n, List (Matrix Unit (nativeTaggedBlock s) ℝ)
  | .inl s => nativeScalarYesKraus (p j) (hp j) (z s) (hz s).1
  | .inr i => nativeCornerYesKraus (p i) (hp i) (p j) (hp j)

def nativeTaggedLocalNo {S : Type*} {n : ℕ} (p : Fin n → Albert)
    (hp : ∀ i, IsAtom (p i)) (z : S → Albert) (hz : ∀ s, IsDensity (z s)) (j : Fin n) :
    ∀ s : S ⊕ Fin n, List (Matrix SpinorCoordinate (nativeTaggedBlock s) ℝ)
  | .inl s => nativeScalarNoKraus (p j) (hp j) (z s) (hz s).1
  | .inr i => nativeCornerNoKraus (p i) (hp i) (p j) (hp j)

theorem nativeTaggedLocal_normalized {S : Type*} {n : ℕ} (p : Fin n → Albert)
    (hp : ∀ i, IsAtom (p i)) (z : S → Albert) (hz : ∀ s, IsDensity (z s))
    (j : Fin n) (s : S ⊕ Fin n) :
    rectangularKrausEffect (nativeTaggedLocalYes p hp z hz j s) +
      rectangularKrausEffect (nativeTaggedLocalNo p hp z hz j s) = 1 := by
  cases s with
  | inl s => exact nativeScalarKraus_normalized (p j) (hp j) (z s) (hz s)
  | inr i => exact nativeCornerKraus_normalized (p i) (hp i) (p j) (hp j)

def nativeTaggedLocalKraus {S : Type*} {n : ℕ} (p : Fin n → Albert)
    (hp : ∀ i, IsAtom (p i)) (z : S → Albert) (hz : ∀ s, IsDensity (z s))
    (reset : Fin n → S) : (a : Outcome (Fin n)) →
    ∀ s : S ⊕ Fin n, List (Matrix (nativeTaggedBlock (nativeTaggedTarget reset a))
      (nativeTaggedBlock s) ℝ)
  | (j,true), s => nativeTaggedLocalYes p hp z hz j s
  | (j,false), s => nativeTaggedLocalNo p hp z hz j s

def nativeTaggedPieceUpdate {S : Type*} {n : ℕ} (p : Fin n → Albert) (z : S → Albert)
    (a : Outcome (Fin n)) (s : S ⊕ Fin n) : Module.End ℝ Albert :=
  (quadraticMapLinear (nativeOutcome p a)).comp (nativeTaggedPieceDecoder p z s)

theorem nativeTaggedLocal_encoding {S : Type*} {n : ℕ} (p : Fin n → Albert)
    (hp : ∀ i, IsAtom (p i)) (z : S → Albert) (hz : ∀ s, IsDensity (z s))
    (reset : Fin n → S) (a : Outcome (Fin n)) (s : S ⊕ Fin n) (x : Albert) :
    rectangularKrausAction (nativeTaggedLocalKraus p hp z hz reset a s)
      (nativeTaggedPieceEncoding p hp s x) =
    nativeTaggedPieceEncoding p hp (nativeTaggedTarget reset a)
      (nativeTaggedPieceUpdate p z a s x) := by
  rcases a with ⟨j,b⟩
  cases b
  · cases s with
    | inl s =>
      change rectangularKrausAction (nativeScalarNoKraus (p j) (hp j) (z s) (hz s).1)
        (albertTrace x • (1 : Matrix Unit Unit ℝ)) =
        nativeTaggedPieceEncoding p hp (.inr j : S ⊕ Fin n)
          (quadraticMap (albertUnit - p j) (albertTrace x • z s))
      rw [nativeScalarNoKraus_action, nativeTaggedTarget_encoding_no]
      simp only [map_smul]
    | inr i =>
      change rectangularKrausAction (nativeCornerNoKraus (p i) (hp i) (p j) (hp j))
        (nativeCornerEncoding (p i) (hp i) (nativeCornerProjection (p i) (hp i) x)) =
        nativeTaggedPieceEncoding p hp (.inr j : S ⊕ Fin n)
          (quadraticMap (albertUnit - p j) (quadraticMap (albertUnit - p i) x))
      rw [nativeCornerNoKraus_encoding, nativeTaggedTarget_encoding_no]
      rfl
  · cases s with
    | inl s =>
      change rectangularKrausAction (nativeScalarYesKraus (p j) (hp j) (z s) (hz s).1)
        (albertTrace x • (1 : Matrix Unit Unit ℝ)) =
        nativeTaggedPieceEncoding p hp (.inl (reset j))
          (quadraticMap (p j) (albertTrace x • z s))
      rw [nativeScalarYesKraus_action, nativeTaggedTarget_encoding_yes, tracePairing_smul_right]
    | inr i =>
      change rectangularKrausAction (nativeCornerYesKraus (p i) (hp i) (p j) (hp j))
        (nativeCornerEncoding (p i) (hp i) (nativeCornerProjection (p i) (hp i) x)) =
        nativeTaggedPieceEncoding p hp (.inl (reset j))
          (quadraticMap (p j) (quadraticMap (albertUnit - p i) x))
      rw [nativeCornerYesKraus_encoding, nativeTaggedTarget_encoding_yes]
      rfl

theorem nativeTaggedLocal_decoding {S : Type*} {n : ℕ} (p : Fin n → Albert)
    (hp : ∀ i, IsAtom (p i)) (z : S → Albert) (reset : Fin n → S)
    (hreset : ∀ i, z (reset i) = p i) (a : Outcome (Fin n)) (s : S ⊕ Fin n) (x : Albert) :
    nativeTaggedPieceDecoder p z (nativeTaggedTarget reset a) (nativeTaggedPieceUpdate p z a s x) =
      quadraticMap (nativeOutcome p a) (nativeTaggedPieceDecoder p z s x) :=
  nativeTaggedTarget_decoder p hp z reset hreset a _

end AlbertSequential.NativeAnalysis
