/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeSupportedInstrumentSimulation
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Trace

@[expose] public section

noncomputable section

open scoped BigOperators Matrix

namespace AlbertSequential.NativeAnalysis

/-- The actual yes-effect on the spinor block is a scaled projection, with
trace eight times the scaling factor. The factor is zero for repeated atoms. -/
theorem nativeCornerYesEffect_square_trace (p q : Albert) (hp : IsAtom p) (hq : IsAtom q) :
    let A := nativeCornerYesEffect p hp q
    let c := 1 - tracePairing p q
    A * A = c • A ∧ Matrix.trace A = 8 * c := by
  let x := nativeCornerProjection p hp q
  let c : ℝ := 1 - tracePairing p q
  let f := albertUnit - p
  have hf := complementary_idempotent p hp.1
  have hqf : tracePairing q f = c := by
    unfold f c tracePairing
    rw [jordanMul_sub_right, jordanMul_albertUnit_right, albertTrace_sub, hq.2, jordanMul_comm q p]
  have hx : jordanMul (x : Albert) x = c • (x : Albert) := by
    change jordanMul (quadraticMap f q) (quadraticMap f q) = c • quadraticMap f q
    rw [← quadraticMap_unit_argument, quadraticMap_fundamental, quadraticMap_unit_argument,
      hf, quadraticMap_atom q f hq, hqf, quadraticMap_smul_right]
  have ht : albertTrace x = c := by
    change albertTrace (quadraticMap f q) = c
    rw [← tracePairing_unit_right, quadraticMap_self_adjoint, quadraticMap_unit_argument, hf, hqf]
  change nativeHalfMatrix p hp x * nativeHalfMatrix p hp x = c • nativeHalfMatrix p hp x ∧
    Matrix.trace (nativeHalfMatrix p hp x) = 8 * c
  refine ⟨?_, by rw [nativeHalfMatrix_trace, ht]⟩
  rw [← nativeHalfMatrix_square, ← map_smul]
  exact congrArg (nativeHalfMatrix p hp) (Subtype.ext hx)

private def cornerDefectSupport (p q : Albert) (hp : IsAtom p) :
    Matrix SpinorCoordinate SpinorCoordinate ℝ :=
  let c := 1 - tracePairing p q
  if c = 0 ∨ c = 1 then 0 else c⁻¹ • nativeCornerYesEffect p hp q

private theorem cornerDefectSupport_properties
    (p q : Albert) (hp : IsAtom p) (hq : IsAtom q) :
    let A := nativeCornerYesEffect p hp q
    let R := cornerDefectSupport p q hp
    R * R = R ∧ (A - A * A) * R = A - A * A ∧ Matrix.trace R ≤ 8 := by
  let A := nativeCornerYesEffect p hp q
  let R := cornerDefectSupport p q hp
  let c : ℝ := 1 - tracePairing p q
  obtain ⟨hA, htr⟩ := nativeCornerYesEffect_square_trace p q hp hq
  change A * A = c • A at hA
  change Matrix.trace A = 8 * c at htr
  change R * R = R ∧ (A - A * A) * R = A - A * A ∧ Matrix.trace R ≤ 8
  by_cases h : c = 0 ∨ c = 1
  · have hR : R = 0 := ite_eq_left h
    have hdef : A - A * A = 0 := by
      rcases h with hzero | hone
      · have hpositive : A.PosSemidef := nativeCornerYesEffect_positive p hp q hq
        have hAz : A = 0 := hpositive.trace_eq_zero_iff.mp (by rw [htr, hzero, mul_zero])
        simp [hAz]
      · rw [hA, hone, one_smul, sub_self]
    simp [hR, hdef]
  · have hR : R = c⁻¹ • A := ite_eq_right h
    have hc : c ≠ 0 := fun hzero => h (Or.inl hzero)
    have hinv : c⁻¹ * c = 1 := inv_mul_cancel₀ hc
    have hfix : A * R = A := by rw [hR, Matrix.mul_smul, hA, smul_smul, hinv, one_smul]
    refine ⟨?_, ?_, ?_⟩
    · rw [show R * R = (c⁻¹ • A) * R by rw [← hR], Matrix.smul_mul, hfix, ← hR]
    · rw [Matrix.sub_mul, hfix, Matrix.mul_assoc A A R, hfix]
    · rw [hR, Matrix.trace_smul, htr, smul_eq_mul,
        show c⁻¹ * (8 * c) = 8 * (c⁻¹ * c) by ring, hinv, mul_one]

private theorem cornerDefectSupport_self (p : Albert) (hp : IsAtom p) :
    cornerDefectSupport p p hp = 0 := by
  have ht : tracePairing p p = 1 := by rw [tracePairing, hp.1, hp.2]
  unfold cornerDefectSupport
  simp [ht]

private theorem taggedBlockState_mul' {𝕜 T : Type*} [RCLike 𝕜] [Fintype T] [DecidableEq T]
    {ι : T → Type*} [∀ s, Fintype (ι s)] [∀ s, DecidableEq (ι s)]
    (A B : ∀ s, Matrix (ι s) (ι s) 𝕜) :
    taggedBlockState A * taggedBlockState B = taggedBlockState (fun s => A s * B s) := by
  classical
  let J := taggedBlockInclusion (𝕜 := 𝕜) (ι := ι)
  change (∑ s, J s * A s * (J s)ᴴ) * (∑ t, J t * B t * (J t)ᴴ) =
    ∑ s, J s * (A s * B s) * (J s)ᴴ
  rw [Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  rw [Matrix.mul_sum, Finset.sum_eq_single s]
  · calc
      _ = J s * (A s * ((J s)ᴴ * J s) * B s) * (J s)ᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [taggedBlockInclusion_same, Matrix.mul_one]
  · intro t _ hts
    calc
      _ = J s * (A s * ((J s)ᴴ * J t) * B t) * (J t)ᴴ := by simp only [Matrix.mul_assoc]
      _ = 0 := by
        rw [taggedBlockInclusion_distinct s t hts.symm, Matrix.mul_zero,
          Matrix.zero_mul, Matrix.mul_zero, Matrix.zero_mul]
  · simp

private theorem taggedBlockState_sub' {𝕜 T : Type*} [RCLike 𝕜] [Fintype T] [DecidableEq T]
    {ι : T → Type*} [∀ s, Fintype (ι s)] [∀ s, DecidableEq (ι s)]
    (A B : ∀ s, Matrix (ι s) (ι s) 𝕜) :
    taggedBlockState A - taggedBlockState B = taggedBlockState (fun s => A s - B s) := by
  simp only [taggedBlockState, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]

private def taggedDefectSupport {S : Type*} [DecidableEq S] {n : ℕ}
    (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i)) (reset : Fin n → S) (j : Fin n) :
    (s : S ⊕ Fin n) → Matrix (nativeTaggedBlock s) (nativeTaggedBlock s) ℝ
  | .inl s => if s = reset j then 0 else 1
  | .inr i => cornerDefectSupport (p i) (p j) (hp i)

private theorem sum_le_of_distinguished_zero {S : Type*} [Fintype S] [DecidableEq S]
    (f : S → ℝ) (s : S) (hf : f s = 0) (k : ℝ) (hk : ∀ t, f t ≤ k) :
    (∑ t, f t) ≤ (Fintype.card S - 1 : ℕ) * k := by
  rw [← Finset.sum_erase_add Finset.univ f (Finset.mem_univ s), hf, add_zero]
  calc
    _ ≤ ∑ _t ∈ Finset.univ.erase s, k := Finset.sum_le_sum (fun t _ => hk t)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ s),
      Finset.card_univ]

/-- A block-diagonal idempotent supports the literal tagged effect defect. Its
trace counts the non-tested reset rails and at most eight per other spinor. -/
theorem nativeTaggedKraus_defect_support {S : Type*} [Fintype S] [DecidableEq S] {n : ℕ}
    (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i)) (z : S → Albert)
    (hz : ∀ s, IsDensity (z s)) (reset : Fin n → S) (hreset : ∀ i, z (reset i) = p i) (j : Fin n) :
    let A := rectangularKrausEffect (nativeTaggedKraus p hp z hz reset (j,true))
    ∃ R : Matrix (Sigma (nativeTaggedBlock (S := S) (n := n)))
        (Sigma (nativeTaggedBlock (S := S) (n := n))) ℝ,
      R * R = R ∧ (A - A * A) * R = A - A * A ∧
        Matrix.trace R ≤ (Fintype.card S - 1 : ℕ) + 8 * (n - 1 : ℕ) := by
  let A (s : S ⊕ Fin n) := rectangularKrausEffect
    (nativeTaggedLocalYes p hp z hz j s)
  let R := taggedDefectSupport p hp reset j
  have hA : rectangularKrausEffect (nativeTaggedKraus p hp z hz reset (j,true)) =
      taggedBlockState A := taggedKrausList_effect _ _
  have hblock (s : S ⊕ Fin n) : R s * R s = R s ∧
      (A s - A s * A s) * R s = A s - A s * A s := by
    cases s with
    | inl t =>
      by_cases h : t = reset j
      · subst t
        have hs : A (.inl (reset j)) = 1 := by
          change rectangularKrausEffect (nativeScalarYesKraus (p j) (hp j) (z (reset j))
            (hz (reset j)).1) = _
          rw [nativeScalarYesKraus_effect, hreset, tracePairing, (hp j).1, (hp j).2, one_smul]
          rfl
        simp [R, taggedDefectSupport, hs]
      · simp [R, taggedDefectSupport, h]
    | inr i =>
      have hs : A (.inr i) = nativeCornerYesEffect (p i) (hp i) (p j) :=
        nativeCornerYesKraus_effect (p i) (hp i) (p j) (hp j)
      rw [hs]
      exact ⟨(cornerDefectSupport_properties (p i) (p j) (hp i) (hp j)).1,
        (cornerDefectSupport_properties (p i) (p j) (hp i) (hp j)).2.1⟩
  have hscalar (s : S) : Matrix.trace (R (.inl s)) ≤ 1 := by
    change Matrix.trace (if s = reset j then 0 else (1 : Matrix Unit Unit ℝ)) ≤ 1
    split <;> simp
  have hspinor (i : Fin n) : Matrix.trace (R (.inr i)) ≤ 8 :=
    (cornerDefectSupport_properties (p i) (p j) (hp i) (hp j)).2.2
  have hs0 : Matrix.trace (R (.inl (reset j))) = 0 := by simp [R, taggedDefectSupport]
  have hi0 : Matrix.trace (R (.inr j)) = 0 := by
    change Matrix.trace (cornerDefectSupport (p j) (p j) (hp j)) = 0
    rw [cornerDefectSupport_self, Matrix.trace_zero]
  change ∃ _, _ ∧ (_ - _ * _) * _ = _ - _ * _ ∧ _
  rw [hA]
  refine ⟨taggedBlockState R, ?_, ?_, ?_⟩
  · rw [taggedBlockState_mul']
    exact congrArg taggedBlockState (funext fun s => (hblock s).1)
  · simp only [taggedBlockState_mul', taggedBlockState_sub']
    exact congrArg taggedBlockState (funext fun s => (hblock s).2)
  · rw [taggedBlockState_trace, Fintype.sum_sum_type]
    have hs := sum_le_of_distinguished_zero (fun s => Matrix.trace (R (.inl s))) (reset j) hs0 1 hscalar
    have hi := sum_le_of_distinguished_zero (fun i => Matrix.trace (R (.inr i))) j hi0 8 hspinor
    rw [Fintype.card_fin] at hi
    simpa only [mul_one, mul_comm (↑(n - 1) : ℝ) 8] using add_le_add hs hi

private theorem idempotent_rank_eq_trace {d : ℕ} (P : ComplexMatrix d) (hP : P * P = P) :
    (P.rank : ℂ) = Matrix.trace P := by
  have h : IsIdempotentElem P.toLin' := by
    change (Matrix.toLinAlgEquiv' P) * (Matrix.toLinAlgEquiv' P) = Matrix.toLinAlgEquiv' P
    rw [← map_mul, hP]
  have ht := LinearMap.IsProj.trace ((LinearMap.isProj_range_iff_isIdempotentElem P.toLin').mpr h)
  rw [Matrix.trace_toLin'_eq] at ht
  change (Module.finrank ℂ (LinearMap.range P.toLin') : ℂ) = Matrix.trace P
  exact ht.symm

private theorem transported_defect_rank_le {I X : Type*} [Fintype I] [DecidableEq I]
    {d k : ℕ} (e : I ≃ Fin d) (r : RealFiniteKrausModel I X) (j : X)
    (R : Matrix I I ℝ) (hR : R * R = R)
    (hDR : let A := rectangularKrausEffect (r.kraus j true); (A - A * A) * R = A - A * A)
    (ht : Matrix.trace R ≤ k) :
    let A := krausEffect ((complexifyRealFiniteKrausModel (renameRealFiniteKrausModel e r)).kraus j true)
    (A - A * A).rank ≤ k := by
  let liftM (M : Matrix I I ℝ) := complexifyMatrix (renameRealMatrix e M)
  let A := rectangularKrausEffect (r.kraus j true)
  let P := liftM R
  have hmul (M N : Matrix I I ℝ) : liftM (M * N) = liftM M * liftM N := by
    simp only [liftM, renameRealMatrix_mul, complexifyMatrix_mul]
  have hsub (M N : Matrix I I ℝ) : liftM (M - N) = liftM M - liftM N :=
    complexifyMatrix_sub (renameRealMatrix e M) (renameRealMatrix e N)
  have hP : P * P = P := by
    change liftM R * liftM R = liftM R
    rw [← hmul, hR]
  change (krausEffect (((r.kraus j true).map (renameRealMatrix e)).map complexifyMatrix) -
    krausEffect (((r.kraus j true).map (renameRealMatrix e)).map complexifyMatrix) *
    krausEffect (((r.kraus j true).map (renameRealMatrix e)).map complexifyMatrix)).rank ≤ k
  rw [← complexifyRectangularKrausEffect, ← renameRectangularKrausEffect]
  change (liftM A - liftM A * liftM A).rank ≤ k
  rw [← hmul, ← hsub]
  have hD : liftM (A - A * A) * P = liftM (A - A * A) := by
    change liftM (A - A * A) * liftM R = liftM (A - A * A)
    rw [← hmul, hDR]
  have htrace : Matrix.trace P = ((Matrix.trace R : ℝ) : ℂ) := by
    change Matrix.trace (complexifyMatrix (renameRealMatrix e R)) = _
    rw [complexifyMatrix_trace, renameRealMatrix_trace]
  have hPr : (P.rank : ℝ) = Matrix.trace R := by
    simpa using congrArg Complex.re ((idempotent_rank_eq_trace P hP).trans htrace)
  calc
    _ = (liftM (A - A * A) * P).rank := congrArg Matrix.rank hD.symm
    _ ≤ P.rank := Matrix.rank_mul_le_right _ _
    _ ≤ k := by exact_mod_cast (hPr.trans_le ht)

private theorem exists_nativeTagged_supported_defect_realization {S : Type*} [Fintype S]
    [DecidableEq S] {n d : ℕ}
    (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i)) (z : S → Albert)
    (hz : ∀ s, IsDensity (z s)) (reset : Fin n → S) (hreset : ∀ i, z (reset i) = p i)
    (xs : S ⊕ Fin n → Albert) (hxs : ∀ s, IsPositive (xs s))
    (ρ : Albert) (hdecode : taggedLinearDecoding (nativeTaggedPieceDecoder p z) xs = ρ)
    (hρ : IsDensity ρ) (hd : Fintype.card (Sigma (nativeTaggedBlock (S := S) (n := n))) = d) :
    ∃ r : BinaryKrausRealization d (Fin n), IsRealKrausRealization r ∧
      HasCertaintySupportedOutputs r ∧
      (∀ j, let A := krausEffect (r.kraus j true)
        (A - A * A).rank ≤ Fintype.card S - 1 + 8 * (n - 1)) ∧
      ∀ w, binaryKrausProbability r w = nativeWordProbability p ρ w := by
  let e := Fintype.equivFinOfCardEq hd
  have ht : albertTrace (taggedLinearDecoding (nativeTaggedPieceDecoder p z) xs) = 1 := by
    rw [hdecode, hρ.2]
  let r := nativeTaggedRealModel p hp z hz reset xs hxs ht
  let renamed := renameRealFiniteKrausModel e r
  refine ⟨complexifyRealFiniteKrausModel renamed, complexifyRealFiniteKrausModel_real _,
    complexifyRealFiniteKrausModel_supported _
      (renameRealFiniteKrausModel_certainty e r (nativeTaggedRealModel_certainty p hp z hz reset
        hreset xs hxs ht)), ?_, ?_⟩
  · intro j
    obtain ⟨R, hR, hDR, hTR⟩ := nativeTaggedKraus_defect_support p hp z hz reset hreset j
    exact transported_defect_rank_le e r j R hR hDR
      (by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hTR)
  · intro w
    rw [complexifyRealFiniteKrausModel_probability, renameRealFiniteKrausModel_probability,
      nativeTaggedRealModel_probability p hp z hz reset hreset xs hxs ht, hdecode]

/-- The (17n+1) spinor model with its literal yes-effect defect ranks bounded by (9n-8). -/
theorem exists_nativeGeneral_supported_defect_17n_add_one {n : ℕ} (hn : 0 < n)
    (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i)) (ρ : Albert) (hρ : IsDensity ρ) :
    ∃ r : BinaryKrausRealization (17 * n + 1) (Fin n), IsRealKrausRealization r ∧
      HasCertaintySupportedOutputs r ∧
      (∀ j, let A := krausEffect (r.kraus j true); (A - A * A).rank ≤ 9*n-8) ∧
      ∀ w, binaryKrausProbability r w = nativeWordProbability p ρ w := by
  let z := nativeGeneralScalarStates p ρ
  let xs : Option (Fin n) ⊕ Fin n → Albert := Pi.single (.inl none) ρ
  have hxs : ∀ s, IsPositive (xs s) := native_positive_single _ ρ hρ.1
  have hd : Fintype.card (Sigma (fun s : Option (Fin n) ⊕ Fin n => nativeTaggedBlock s)) =
      17 * n + 1 := by
    rw [nativeTaggedBlock_card]
    simp only [Fintype.card_option, Fintype.card_fin]
    omega
  obtain ⟨r, hreal, hsupport, hrank, hwords⟩ := exists_nativeTagged_supported_defect_realization
    p hp z (nativeGeneralScalarStates_density p hp ρ hρ) Option.some (fun _ => rfl) xs hxs
    ρ (nativeGeneralPieces_decoding p ρ hρ) hρ hd
  refine ⟨r, hreal, hsupport, ?_, hwords⟩
  intro j
  specialize hrank j
  simp only [Fintype.card_option, Fintype.card_fin] at hrank
  omega

/-- Deleting the initial ray gives (17n) dimensions and defect rank at most (9(n-1)). -/
theorem exists_nativeNoHalf_supported_defect_17n {n : ℕ}
    (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i)) (ρ : Albert) (hρ : IsDensity ρ)
    (hno : ∃ (i : Fin n) (t : ℝ) (y : Albert), 0 ≤ t ∧ IsPositive y ∧
      jordanMul (p i) y = 0 ∧ ρ = t • p i + y) :
    ∃ r : BinaryKrausRealization (17*n) (Fin n), IsRealKrausRealization r ∧
      HasCertaintySupportedOutputs r ∧
      (∀ j, let A := krausEffect (r.kraus j true); (A - A * A).rank ≤ 9*(n-1)) ∧
      ∀ w, binaryKrausProbability r w = nativeWordProbability p ρ w := by
  obtain ⟨i,t,y,ht,hy,hpy,hdecomp⟩ := hno
  let xs := nativeNoHalfPieces p i t y
  have hxs : ∀ s, IsPositive (xs s) := nativeNoHalfPieces_positive p hp i t ht y hy
  have hdecode : taggedLinearDecoding (nativeTaggedPieceDecoder p p) xs = ρ :=
    (nativeNoHalfPieces_decoding p hp i t y hpy).trans hdecomp.symm
  have hd : Fintype.card (Sigma (fun s : Fin n ⊕ Fin n => nativeTaggedBlock s)) = 17 * n := by
    rw [nativeTaggedBlock_card, Fintype.card_fin]
    omega
  obtain ⟨r, hreal, hsupport, hrank, hwords⟩ := exists_nativeTagged_supported_defect_realization
    p hp p (fun j => native_atom_density (p j) (hp j)) id (fun _ => rfl) xs hxs ρ hdecode hρ hd
  refine ⟨r, hreal, hsupport, ?_, hwords⟩
  intro j
  specialize hrank j
  simp only [Fintype.card_fin] at hrank
  omega

end AlbertSequential.NativeAnalysis
