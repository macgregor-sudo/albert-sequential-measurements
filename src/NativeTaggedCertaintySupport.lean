/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeTaggedAllWords
public import TaggedCertaintySupport

/-! The actual simulator has certainty-supported yes and no outputs. The
effect acts as identity on its reset ray and as zero on its own corner block. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.NativeAnalysis

theorem nativeScalarYesKraus_effect (q : Albert) (hq : IsAtom q) (z : Albert) (hz : IsPositive z) :
    rectangularKrausEffect (nativeScalarYesKraus q hq z hz) =
      tracePairing q z • (1 : Matrix Unit Unit ℝ) := by
  rw [nativeScalarYesKraus, positiveMeasurePrepare_effect, nativeScalarYesState, Matrix.trace_smul]
  simp

theorem nativeCornerYesEffect_same_zero (p : Albert) (hp : IsAtom p) :
    nativeCornerYesEffect p hp p = 0 := by
  have h : nativeCornerProjection p hp p = 0 := by
    apply Subtype.ext
    change quadraticMap (albertUnit - p) p = 0
    rw [quadraticMap_complement]
    have hpp : quadraticMap p p = p := by
      unfold quadraticMap
      rw [hp.1, hp.1]
      module
    rw [hp.1, hpp]
    module
  rw [nativeCornerYesEffect, h, map_zero]

theorem nativeTaggedLocalYes_reset_identity {S : Type*} {n : ℕ} (p : Fin n → Albert)
    (hp : ∀ i, IsAtom (p i)) (z : S → Albert) (hz : ∀ s, IsDensity (z s))
    (reset : Fin n → S) (hreset : ∀ i, z (reset i) = p i) (j : Fin n) :
    rectangularKrausEffect (nativeTaggedLocalYes p hp z hz j (.inl (reset j))) = 1 := by
  change rectangularKrausEffect (nativeScalarYesKraus (p j) (hp j) (z (reset j)) (hz (reset j)).1) = _
  rw [nativeScalarYesKraus_effect, hreset]
  have hpp : tracePairing (p j) (p j) = 1 := by
    change albertTrace (jordanMul (p j) (p j)) = 1
    rw [(hp j).1, (hp j).2]
  rw [hpp, one_smul]
  rfl

theorem nativeTaggedLocalYes_corner_zero {S : Type*} {n : ℕ} (p : Fin n → Albert)
    (hp : ∀ i, IsAtom (p i)) (z : S → Albert) (hz : ∀ s, IsDensity (z s)) (j : Fin n) :
    rectangularKrausEffect (nativeTaggedLocalYes p hp z hz j (.inr j)) = 0 := by
  change rectangularKrausEffect (nativeCornerYesKraus (p j) (hp j) (p j) (hp j)) = _
  rw [nativeCornerYesKraus_effect, nativeCornerYesEffect_same_zero]
  rfl

theorem nativeTaggedRealModel_certainty {S : Type*} [Fintype S] [DecidableEq S] {n : ℕ}
    (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i)) (z : S → Albert)
    (hz : ∀ s, IsDensity (z s)) (reset : Fin n → S) (hreset : ∀ i, z (reset i) = p i)
    (xs : S ⊕ Fin n → Albert) (hxs : ∀ s, IsPositive (xs s))
    (htrace : albertTrace (taggedLinearDecoding (nativeTaggedPieceDecoder p z) xs) = 1) :
    HasKrausCertaintySupport (nativeTaggedRealModel p hp z hz reset xs hxs htrace).kraus := by
  intro j
  exact taggedKrausList_certainty_support (ι := fun t : S ⊕ Fin n => nativeTaggedBlock t)
    (Sum.inl (reset j)) (Sum.inr j) (nativeTaggedLocalYes p hp z hz j) (nativeTaggedLocalNo p hp z hz j)
    (nativeTaggedLocalYes_reset_identity p hp z hz reset hreset j)
    (nativeTaggedLocalYes_corner_zero p hp z hz j)

end AlbertSequential.NativeAnalysis
