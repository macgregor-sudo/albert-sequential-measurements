/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeTaggedLocalInstrument
public import RealFiniteKrausModel

/-! Stationary real finite Kraus simulation for supplied scalar/native pieces.
The exact native all-word table is derived from the local maps, not assumed. -/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace AlbertSequential.NativeAnalysis

def nativeTaggedKraus {S : Type*} [Fintype S] [DecidableEq S] {n : ℕ}
    (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i)) (z : S → Albert)
    (hz : ∀ s, IsDensity (z s)) (reset : Fin n → S) (a : Outcome (Fin n)) :
    List (Matrix (Sigma (nativeTaggedBlock (S := S) (n := n)))
      (Sigma (nativeTaggedBlock (S := S) (n := n))) ℝ) :=
  taggedKrausList (nativeTaggedTarget reset a) (nativeTaggedLocalKraus p hp z hz reset a)

theorem nativeTaggedKraus_normalized {S : Type*} [Fintype S] [DecidableEq S] {n : ℕ}
    (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i)) (z : S → Albert)
    (hz : ∀ s, IsDensity (z s)) (reset : Fin n → S) (j : Fin n) :
    rectangularKrausEffect (nativeTaggedKraus p hp z hz reset (j,true)) +
      rectangularKrausEffect (nativeTaggedKraus p hp z hz reset (j,false)) = 1 := by
  exact taggedKrausList_normalized (ι := fun t : S ⊕ Fin n => nativeTaggedBlock t)
    (Sum.inl (reset j)) (Sum.inr j)
    (nativeTaggedLocalYes p hp z hz j) (nativeTaggedLocalNo p hp z hz j)
    (nativeTaggedLocal_normalized p hp z hz j)

theorem nativeTaggedKraus_all_words {S : Type*} [Fintype S] [DecidableEq S] {n : ℕ}
    (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i)) (z : S → Albert)
    (hz : ∀ s, IsDensity (z s)) (reset : Fin n → S) (hreset : ∀ i, z (reset i) = p i)
    (xs : S ⊕ Fin n → Albert) (w : Word (Fin n)) :
    Matrix.trace (w.foldl (fun Y a => rectangularKrausAction (nativeTaggedKraus p hp z hz reset a) Y)
      (taggedLinearEncoding (nativeTaggedPieceEncoding p hp) xs)) =
    nativeWordProbability p (taggedLinearDecoding (nativeTaggedPieceDecoder p z) xs) w := by
  exact taggedAllWordSimulation (nativeTaggedPieceEncoding p hp)
    (nativeTaggedPieceDecoder p z) nativeTaggedTrace (nativeTaggedPiece_trace p hp z hz)
    (nativeTaggedTarget reset) (nativeTaggedPieceUpdate p z)
    (fun a => quadraticMapLinear (nativeOutcome p a))
    (nativeTaggedLocalKraus p hp z hz reset) (nativeTaggedLocal_encoding p hp z hz reset)
    (fun a _ x => nativeTaggedTarget_decoder p hp z reset hreset a _) xs w

theorem nativeTaggedEncoding_positive {S : Type*} [Fintype S] [DecidableEq S] {n : ℕ}
    (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i))
    (xs : S ⊕ Fin n → Albert) (hxs : ∀ s, IsPositive (xs s)) :
    (taggedLinearEncoding (nativeTaggedPieceEncoding p hp) xs).PosSemidef :=
  taggedBlockState_positive _ (fun s => nativeTaggedPiece_positive p hp s (xs s) (hxs s))

def nativeTaggedRealModel {S : Type*} [Fintype S] [DecidableEq S] {n : ℕ}
    (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i)) (z : S → Albert)
    (hz : ∀ s, IsDensity (z s)) (reset : Fin n → S)
    (xs : S ⊕ Fin n → Albert) (hxs : ∀ s, IsPositive (xs s))
    (htrace : albertTrace (taggedLinearDecoding (nativeTaggedPieceDecoder p z) xs) = 1) :
    RealFiniteKrausModel (Sigma (nativeTaggedBlock (S := S) (n := n))) (Fin n) where
  initial := taggedLinearEncoding (nativeTaggedPieceEncoding p hp) xs
  positive := nativeTaggedEncoding_positive p hp xs hxs
  trace_one := (taggedLinearEncoding_trace (nativeTaggedPieceEncoding p hp)
    (nativeTaggedPieceDecoder p z) nativeTaggedTrace (nativeTaggedPiece_trace p hp z hz) xs).trans htrace
  kraus j b := nativeTaggedKraus p hp z hz reset (j,b)
  normalized := nativeTaggedKraus_normalized p hp z hz reset

theorem nativeTaggedRealModel_probability {S : Type*} [Fintype S] [DecidableEq S] {n : ℕ}
    (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i)) (z : S → Albert)
    (hz : ∀ s, IsDensity (z s)) (reset : Fin n → S) (hreset : ∀ i, z (reset i) = p i)
    (xs : S ⊕ Fin n → Albert) (hxs : ∀ s, IsPositive (xs s))
    (htrace : albertTrace (taggedLinearDecoding (nativeTaggedPieceDecoder p z) xs) = 1)
    (w : Word (Fin n)) :
    realFiniteKrausProbability _ _ (nativeTaggedRealModel p hp z hz reset xs hxs htrace) w =
      nativeWordProbability p (taggedLinearDecoding (nativeTaggedPieceDecoder p z) xs) w :=
  nativeTaggedKraus_all_words p hp z hz reset hreset xs w

end AlbertSequential.NativeAnalysis
