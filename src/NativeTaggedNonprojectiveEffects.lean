/- SPDX-License-Identifier: Apache-2.0 -/
module

public import TaggedDilationDefectSpectrum
public import NativeFiniteInstrumentSimulation
public import SubalgebraCoordsAndLine
public import ThreeAtomAndFourPoint

/-! The nonprojective yes effect of the actual tagged spinor realization. -/

@[expose] public section
noncomputable section
open scoped Matrix

namespace AlbertSequential.NativeAnalysis

private theorem lineSubalgebra_ne_univ (q : Albert) (hq : IsAtom q) :
    ∃ x : Albert, x ∉ (lineSubalgebra q hq).carrier := by
  let v : SpinorCoordinate → ℝ := fun _ => 1
  let x := spinorInclusion q hq v
  have hx : x ≠ 0 := by
    intro he
    have he' := congrArg (spinorReadout q hq) he
    change spinorReadout q hq (spinorInclusion q hq v) = spinorReadout q hq 0 at he'
    rw [spinorReadout_inclusion, map_zero] at he'
    have : Nonempty SpinorCoordinate := Fintype.card_pos_iff.mp (by rw [spinorCoordinate_card]; decide)
    obtain ⟨i⟩ := this
    have hi : (1 : ℝ) = 0 := congrFun he' i
    exact one_ne_zero hi
  have hhalf : jordanMul q x = (1 / 2 : ℝ) • x :=
    (mem_nativePeirceHalf q x).mp (spinorInclusion_mem q hq v)
  refine ⟨x, ?_⟩
  intro h
  have h' := (mem_lineSubalgebra_iff_idem q hq x).mp h
  rw [hhalf, jordanMul_smul_right, hhalf] at h'
  have hz : (1 / 4 : ℝ) • x = 0 := by
    linear_combination (norm := module) -h'
  exact hx ((smul_eq_zero.mp hz).resolve_left (by norm_num))

/-- Any generating family of atoms has a pair with overlap strictly between zero and one. -/
theorem exists_atom_overlap_open_of_generates {ι : Type*} (p : ι → Albert)
    (hp : ∀ i, IsAtom (p i)) (hgen : GeneratesAlbert p) :
    ∃ i j, i ≠ j ∧ 0 < tracePairing (p i) (p j) ∧ tracePairing (p i) (p j) < 1 := by
  classical
  by_contra! h
  by_cases hi : Nonempty ι
  · obtain ⟨i⟩ := hi
    obtain ⟨x, hx⟩ := lineSubalgebra_ne_univ (p i) (hp i)
    apply hx
    apply hgen x (lineSubalgebra (p i) (hp i))
    intro j
    refine (mem_lineSubalgebra_iff_idem _ (hp i) _).mpr ?_
    by_cases hij : i = j
    · subst j
      exact congrArg (jordanMul (p i)) (hp i).1
    · obtain ⟨h0, h1⟩ := atom_tracePairing_bounds (p i) (p j) (hp i) (hp j)
      by_cases hpos : 0 < tracePairing (p i) (p j)
      · have hone := le_antisymm h1 (h i j hij hpos)
        rw [(atom_tracePairing_eq_one_iff _ _ (hp i) (hp j)).mp hone]
        exact congrArg (jordanMul (p j)) (hp j).1
      · have hzero := le_antisymm (le_of_not_gt hpos) h0
        rw [(atom_tracePairing_eq_zero_iff _ _ (hp i) (hp j)).mp hzero, jordanMul_zero_right]
  · obtain ⟨x, hx⟩ := lineSubalgebra_ne_univ (diagAtom 0) (diagAtom_isAtom 0)
    exact hx (hgen x (lineSubalgebra (diagAtom 0) (diagAtom_isAtom 0)) (fun i => (hi ⟨i⟩).elim))

/-- Actual global yes effects leave a spinor block invariant and restrict there to
its native yes effect. The scalar sources and the initial preparation are arbitrary. -/
theorem nativeTaggedKraus_yes_effect_corner {S : Type*} [Fintype S] [DecidableEq S] {n : ℕ}
    (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i)) (z : S → Albert)
    (hz : ∀ s, IsDensity (z s)) (reset : Fin n → S) (i j : Fin n) :
    let A := rectangularKrausEffect (nativeTaggedKraus p hp z hz reset (j, true))
    let J : Matrix (Sigma (nativeTaggedBlock (S := S) (n := n))) SpinorCoordinate ℝ :=
      taggedBlockInclusion (ι := nativeTaggedBlock) (Sum.inr i)
    A * J = J * nativeCornerYesEffect (p i) (hp i) (p j) := by
  let J : Matrix (Sigma (nativeTaggedBlock (S := S) (n := n))) SpinorCoordinate ℝ :=
    taggedBlockInclusion (ι := nativeTaggedBlock) (Sum.inr i)
  calc
    _ = J * rectangularKrausEffect (nativeCornerYesKraus (p i) (hp i) (p j) (hp j)) :=
      taggedKrausList_effect_inclusion (ι := nativeTaggedBlock)
        (nativeTaggedTarget reset (j, true))
        (nativeTaggedLocalKraus p hp z hz reset (j, true)) (Sum.inr i)
    _ = _ := by rw [nativeCornerYesKraus_effect]

/-- The effect and its restricted characteristic polynomial are for the same tagged Kraus maps.
For an open overlap the two eigenvalues are different and both have multiplicity eight. -/
theorem nativeTaggedKraus_yes_effect_open_overlap {S : Type*} [Fintype S] [DecidableEq S] {n : ℕ}
    (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i)) (z : S → Albert)
    (hz : ∀ s, IsDensity (z s)) (reset : Fin n → S) (i j : Fin n)
    (h0 : 0 < tracePairing (p i) (p j)) (h1 : tracePairing (p i) (p j) < 1) :
    let A := rectangularKrausEffect (nativeTaggedKraus p hp z hz reset (j, true))
    let J : Matrix (Sigma (nativeTaggedBlock (S := S) (n := n))) SpinorCoordinate ℝ :=
      taggedBlockInclusion (ι := nativeTaggedBlock) (Sum.inr i)
    A * A ≠ A ∧
      (Jᴴ * A * J).charpoly = Polynomial.X ^ 8 *
        (Polynomial.X - Polynomial.C (1 - tracePairing (p i) (p j))) ^ 8 := by
  let A := rectangularKrausEffect (nativeTaggedKraus p hp z hz reset (j, true))
  let J : Matrix (Sigma (nativeTaggedBlock (S := S) (n := n))) SpinorCoordinate ℝ :=
    taggedBlockInclusion (ι := nativeTaggedBlock) (Sum.inr i)
  let B := nativeCornerYesEffect (p i) (hp i) (p j)
  have hJ : Jᴴ * J = 1 :=
    taggedBlockInclusion_same (ι := nativeTaggedBlock) (Sum.inr i : S ⊕ Fin n)
  have hAJ : A * J = J * B := nativeTaggedKraus_yes_effect_corner p hp z hz reset i j
  have hrestrict : Jᴴ * A * J = B := by
    rw [Matrix.mul_assoc, hAJ, ← Matrix.mul_assoc, hJ, Matrix.one_mul]
  refine ⟨?_, by rw [hrestrict]; exact nativeCornerYesEffect_charpoly _ _ (hp i) (hp j)⟩
  intro hidem
  have hB : B * B = B := by
    have hJJ : Jᴴ * ((A * A) * J) = B * B := by
      rw [Matrix.mul_assoc A A J, hAJ, ← Matrix.mul_assoc A J B, hAJ,
        ← Matrix.mul_assoc Jᴴ (J * B) B, ← Matrix.mul_assoc Jᴴ J B, hJ, Matrix.one_mul]
    rw [hidem, ← Matrix.mul_assoc, hrestrict] at hJJ
    exact hJJ.symm
  obtain ⟨hsq, htr⟩ := nativeCornerYesEffect_square_trace (p i) (p j) (hp i) (hp j)
  change B * B = (1 - tracePairing (p i) (p j)) • B at hsq
  change Matrix.trace B = 8 * (1 - tracePairing (p i) (p j)) at htr
  rw [hB] at hsq
  have ht := congrArg Matrix.trace hsq
  rw [Matrix.trace_smul, smul_eq_mul, htr] at ht
  nlinarith [mul_pos h0 (sub_pos.mpr h1)]

/-- The yes branch sends every output to its scalar reset block. For an open
corner overlap its action on the identity therefore differs from the effect,
which is the value of a Lüders map at the identity. -/
theorem nativeTaggedKraus_yes_action_one_ne_effect {S : Type*} [Fintype S] [DecidableEq S] {n : ℕ}
    (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i)) (z : S → Albert)
    (hz : ∀ s, IsDensity (z s)) (reset : Fin n → S) (i j : Fin n)
    (h1 : tracePairing (p i) (p j) < 1) :
    let K := nativeTaggedKraus p hp z hz reset (j, true)
    rectangularKrausAction K 1 ≠ rectangularKrausEffect K := by
  let K := nativeTaggedKraus p hp z hz reset (j, true)
  let J : Matrix (Sigma (nativeTaggedBlock (S := S) (n := n))) SpinorCoordinate ℝ :=
    taggedBlockInclusion (ι := nativeTaggedBlock) (Sum.inr i)
  let t := nativeTaggedTarget reset (j, true)
  let T := taggedBlockInclusion (𝕜 := ℝ) (ι := nativeTaggedBlock) t
  let B := nativeCornerYesEffect (p i) (hp i) (p j)
  have hn : Jᴴ * T = 0 :=
    taggedBlockInclusion_distinct (ι := nativeTaggedBlock) (Sum.inr i : S ⊕ Fin n) t
      (show (Sum.inr i : S ⊕ Fin n) ≠ Sum.inl (reset j) from Sum.inr_ne_inl)
  have hcompress : Jᴴ * rectangularKrausAction K 1 * J = 0 := by
    have hsum := taggedKrausList_action (ι := nativeTaggedBlock) t
      (nativeTaggedLocalKraus p hp z hz reset (j, true)) 1
    change Jᴴ * rectangularKrausAction
      (taggedKrausList t (nativeTaggedLocalKraus p hp z hz reset (j, true))) 1 * J = 0
    rw [hsum, Matrix.mul_sum, Matrix.sum_mul, Finset.sum_eq_zero]
    intro u _
    simp only [← Matrix.mul_assoc, show Jᴴ * taggedBlockInclusion (𝕜 := ℝ) (ι := nativeTaggedBlock) t = 0 from hn,
      Matrix.zero_mul]
  have hJ : Jᴴ * J = 1 :=
    taggedBlockInclusion_same (ι := nativeTaggedBlock) (Sum.inr i : S ⊕ Fin n)
  have hAJ : rectangularKrausEffect K * J = J * B :=
    nativeTaggedKraus_yes_effect_corner p hp z hz reset i j
  have hrestrict : Jᴴ * rectangularKrausEffect K * J = B := by
    rw [Matrix.mul_assoc, hAJ, ← Matrix.mul_assoc, hJ, Matrix.one_mul]
  change rectangularKrausAction K 1 ≠ rectangularKrausEffect K
  intro he
  rw [he, hrestrict] at hcompress
  have ht := (nativeCornerYesEffect_square_trace (p i) (p j) (hp i) (hp j)).2
  change B.trace = 8 * (1 - tracePairing (p i) (p j)) at ht
  rw [hcompress, Matrix.trace_zero] at ht
  linarith

private theorem complexify_renameRealMatrix_injective {I : Type*} {d : ℕ} (e : I ≃ Fin d) :
    Function.Injective (fun M : Matrix I I ℝ => complexifyMatrix (renameRealMatrix e M)) := by
  intro A B h
  have hre := complexifyMatrix_injective h
  ext i j
  simpa only [renameRealMatrix, Matrix.submatrix_apply, Equiv.symm_apply_apply] using
    congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M (e i) (e j)) hre

/-- Entry renaming and complexification preserve the non-idempotence of measured effects. -/
theorem complexifyRenamedRealFiniteKrausModel_effect_not_idempotent
    {I X : Type*} [Fintype I] [DecidableEq I] {d : ℕ} (e : I ≃ Fin d)
    (r : RealFiniteKrausModel I X) (x : X) (b : Bool)
    (h : let A := rectangularKrausEffect (r.kraus x b); A * A ≠ A) :
    let A := krausEffect ((complexifyRealFiniteKrausModel (renameRealFiniteKrausModel e r)).kraus x b)
    A * A ≠ A := by
  dsimp only [complexifyRealFiniteKrausModel, renameRealFiniteKrausModel]
  rw [← complexifyRectangularKrausEffect, ← renameRectangularKrausEffect]
  intro ha
  apply h
  rw [← complexifyMatrix_mul, ← renameRealMatrix_mul] at ha
  exact complexify_renameRealMatrix_injective e ha

/-- The non-Lüders action at the identity survives the same coordinate transport. -/
theorem complexifyRenamedRealFiniteKrausModel_action_one_ne_effect
    {I X : Type*} [Fintype I] [DecidableEq I] {d : ℕ} (e : I ≃ Fin d)
    (r : RealFiniteKrausModel I X) (x : X) (b : Bool)
    (h : rectangularKrausAction (r.kraus x b) 1 ≠ rectangularKrausEffect (r.kraus x b)) :
    let K := (complexifyRealFiniteKrausModel (renameRealFiniteKrausModel e r)).kraus x b
    krausAction K 1 ≠ krausEffect K := by
  dsimp only [complexifyRealFiniteKrausModel, renameRealFiniteKrausModel]
  intro he
  rw [← complexifyRectangularKrausEffect, ← renameRectangularKrausEffect,
    ← complexifyMatrix_one, ← complexifyRectangularKrausAction,
    ← renameRealMatrix_one e, ← renameRectangularKrausAction] at he
  apply h
  exact complexify_renameRealMatrix_injective e he

/-- The paper's general spinor construction realizes the native table on
complex dimension `17*n+1` and has a nonprojective, non-Lüders yes branch. -/
theorem exists_nativeGeneral_nonprojective_simulation {n : ℕ} (p : Fin n → Albert)
    (hp : ∀ i, IsAtom (p i)) (hgen : GeneratesAlbert p) (ρ : Albert) (hρ : IsDensity ρ) :
    ∃ r : BinaryKrausRealization (17 * n + 1) (Fin n), IsRealKrausRealization r ∧
      (∀ w, binaryKrausProbability r w = nativeWordProbability p ρ w) ∧
      ∃ j, let K := r.kraus j true
           let A := krausEffect K
           A * A ≠ A ∧ krausAction K 1 ≠ A := by
  let z := nativeGeneralScalarStates p ρ
  let hz := nativeGeneralScalarStates_density p hp ρ hρ
  let xs : Option (Fin n) ⊕ Fin n → Albert := Pi.single (.inl none) ρ
  have hxs : ∀ s, IsPositive (xs s) := native_positive_single _ ρ hρ.1
  have hdecoded : taggedLinearDecoding (nativeTaggedPieceDecoder p z) xs = ρ :=
    nativeGeneralPieces_decoding p ρ hρ
  have ht : albertTrace (taggedLinearDecoding (nativeTaggedPieceDecoder p z) xs) = 1 := by
    rw [hdecoded, hρ.2]
  let r := nativeTaggedRealModel p hp z hz Option.some xs hxs ht
  have hd : Fintype.card (Sigma (fun s : Option (Fin n) ⊕ Fin n => nativeTaggedBlock s)) =
      17 * n + 1 := by
    rw [nativeTaggedBlock_card]
    simp only [Fintype.card_option, Fintype.card_fin]
    omega
  let e := Fintype.equivFinOfCardEq hd
  let s := complexifyRealFiniteKrausModel (renameRealFiniteKrausModel e r)
  refine ⟨s, complexifyRealFiniteKrausModel_real _, ?_, ?_⟩
  · intro w
    rw [complexifyRealFiniteKrausModel_probability, renameRealFiniteKrausModel_probability]
    show realFiniteKrausProbability _ _ r w = _
    rw [nativeTaggedRealModel_probability p hp z hz Option.some (fun _ => rfl) xs hxs ht, hdecoded]
  · obtain ⟨i, j, _, h0, h1⟩ := exists_atom_overlap_open_of_generates p hp hgen
    have hnot := (nativeTaggedKraus_yes_effect_open_overlap p hp z hz Option.some i j h0 h1).1
    have haction := nativeTaggedKraus_yes_action_one_ne_effect p hp z hz Option.some i j h1
    exact ⟨j, complexifyRenamedRealFiniteKrausModel_effect_not_idempotent e r j true hnot,
      complexifyRenamedRealFiniteKrausModel_action_one_ne_effect e r j true haction⟩

end AlbertSequential.NativeAnalysis
