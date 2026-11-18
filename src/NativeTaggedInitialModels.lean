/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeTaggedAllWords

/-! The actual preparation-dependent initial ray and the smaller no-half
initial mixture. No encoding for an additional preparation family is assumed. -/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace AlbertSequential.NativeAnalysis

theorem native_positive_single {T : Type*} [DecidableEq T]
    (t : T) (x : Albert) (hx : IsPositive x) : ∀ s, IsPositive ((Pi.single t x : T → Albert) s) := by
  intro s
  by_cases hs : s = t
  · subst s
    rw [Pi.single_eq_same]
    exact hx
  · rw [Pi.single_eq_of_ne hs]
    exact isPositive_zero

theorem native_atom_density (p : Albert) (hp : IsAtom p) : IsDensity p :=
  ⟨isPositive_idempotent p hp.1, hp.2⟩

def nativeGeneralScalarStates {n : ℕ} (p : Fin n → Albert) (ρ : Albert) : Option (Fin n) → Albert
  | none => ρ
  | some i => p i

theorem nativeGeneralScalarStates_density {n : ℕ} (p : Fin n → Albert)
    (hp : ∀ i, IsAtom (p i)) (ρ : Albert) (hρ : IsDensity ρ) :
    ∀ s, IsDensity (nativeGeneralScalarStates p ρ s)
  | none => hρ
  | some i => native_atom_density (p i) (hp i)

theorem nativeGeneralPieces_decoding {n : ℕ} (p : Fin n → Albert)
    (ρ : Albert) (hρ : IsDensity ρ) :
    taggedLinearDecoding (nativeTaggedPieceDecoder p (nativeGeneralScalarStates p ρ))
      (Pi.single (Sum.inl none) ρ) = ρ := by
  rw [taggedLinearDecoding_single]
  change albertTrace ρ • ρ = ρ
  rw [hρ.2, one_smul]

theorem exists_nativeGeneral_real_simulation {n : ℕ} (p : Fin n → Albert)
    (hp : ∀ i, IsAtom (p i)) (ρ : Albert) (hρ : IsDensity ρ) :
    ∃ r : RealFiniteKrausModel
      (Sigma (fun s : Option (Fin n) ⊕ Fin n => nativeTaggedBlock s)) (Fin n),
      ∀ w, realFiniteKrausProbability _ _ r w = nativeWordProbability p ρ w := by
  let z := nativeGeneralScalarStates p ρ
  let hz := nativeGeneralScalarStates_density p hp ρ hρ
  let xs : Option (Fin n) ⊕ Fin n → Albert := Pi.single (.inl none) ρ
  have hxs : ∀ s, IsPositive (xs s) := native_positive_single _ ρ hρ.1
  have hd : taggedLinearDecoding (nativeTaggedPieceDecoder p z) xs = ρ :=
    nativeGeneralPieces_decoding p ρ hρ
  have ht : albertTrace (taggedLinearDecoding (nativeTaggedPieceDecoder p z) xs) = 1 := by rw [hd, hρ.2]
  refine ⟨nativeTaggedRealModel p hp z hz Option.some xs hxs ht, ?_⟩
  intro w
  rw [nativeTaggedRealModel_probability p hp z hz Option.some (fun _ => rfl) xs hxs ht, hd]

def nativeNoHalfPieces {n : ℕ} (p : Fin n → Albert) (i : Fin n) (t : ℝ) (y : Albert) :
    Fin n ⊕ Fin n → Albert :=
  Pi.single (.inl i) (t • p i) + Pi.single (.inr i) y

theorem nativeNoHalfPieces_positive {n : ℕ} (p : Fin n → Albert)
    (hp : ∀ j, IsAtom (p j)) (i : Fin n) (t : ℝ) (ht : 0 ≤ t) (y : Albert) (hy : IsPositive y) :
    ∀ s, IsPositive (nativeNoHalfPieces p i t y s) := by
  intro s
  exact isPositive_add _ _ (native_positive_single (.inl i : Fin n ⊕ Fin n) _
    (isPositive_smul t (p i) ht (isPositive_idempotent (p i) (hp i).1)) s)
    (native_positive_single (.inr i : Fin n ⊕ Fin n) y hy s)

theorem nativeNoHalfPieces_decoding {n : ℕ} (p : Fin n → Albert)
    (hp : ∀ j, IsAtom (p j)) (i : Fin n) (t : ℝ) (y : Albert) (hy : jordanMul (p i) y = 0) :
    taggedLinearDecoding (nativeTaggedPieceDecoder p p) (nativeNoHalfPieces p i t y) = t • p i + y := by
  rw [nativeNoHalfPieces, map_add, taggedLinearDecoding_single, taggedLinearDecoding_single]
  change albertTrace (t • p i) • p i + quadraticMap (albertUnit - p i) y = _
  rw [albertTrace_smul, (hp i).2, mul_one,
    native_complement_quadratic_fixed_zero (p i) y (hp i).1 hy]

theorem exists_nativeNoHalf_real_simulation {n : ℕ} (p : Fin n → Albert)
    (hp : ∀ i, IsAtom (p i)) (ρ : Albert) (hρ : IsDensity ρ)
    (i : Fin n) (t : ℝ) (ht : 0 ≤ t) (y : Albert) (hy : IsPositive y)
    (hpy : jordanMul (p i) y = 0) (hdecomp : ρ = t • p i + y) :
    ∃ r : RealFiniteKrausModel
      (Sigma (fun s : Fin n ⊕ Fin n => nativeTaggedBlock s)) (Fin n),
      ∀ w, realFiniteKrausProbability _ _ r w = nativeWordProbability p ρ w := by
  let hz : ∀ j, IsDensity (p j) := fun j => native_atom_density (p j) (hp j)
  let xs := nativeNoHalfPieces p i t y
  have hxs : ∀ s, IsPositive (xs s) := nativeNoHalfPieces_positive p hp i t ht y hy
  have hd : taggedLinearDecoding (nativeTaggedPieceDecoder p p) xs = ρ :=
    (nativeNoHalfPieces_decoding p hp i t y hpy).trans hdecomp.symm
  have htr : albertTrace (taggedLinearDecoding (nativeTaggedPieceDecoder p p) xs) = 1 := by rw [hd, hρ.2]
  refine ⟨nativeTaggedRealModel p hp p hz id xs hxs htr, ?_⟩
  intro w
  rw [nativeTaggedRealModel_probability p hp p hz id (fun _ => rfl) xs hxs htr, hd]

theorem nativeTaggedBlock_card {S : Type*} [Fintype S] {n : ℕ} :
    Fintype.card (Sigma (fun s : S ⊕ Fin n => nativeTaggedBlock s)) = Fintype.card S + 16 * n := by
  classical
  rw [Fintype.card_sigma, Fintype.sum_sum_type]
  simp [nativeTaggedBlock, SpinorCoordinate, OctonionCoordinate, mul_comm]

end AlbertSequential.NativeAnalysis
