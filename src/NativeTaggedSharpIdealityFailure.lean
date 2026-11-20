/- SPDX-License-Identifier: Apache-2.0 -/
module

public import SharpDilationCertaintyDisturbance
public import NativeSupportedInstrumentSimulation
public import RealSupportedSharpDilation
public import ComplexWindowDeterminantAndMax

/-! Certainty-face disturbance in the actual tagged Albert simulator. -/

@[expose] public section
noncomputable section
open scoped Matrix ComplexOrder

namespace AlbertSequential.NativeAnalysis

/-- The rank-one density on one of the original scalar rails. -/
def nativeTaggedScalarRail {S : Type*} [Fintype S] [DecidableEq S] {n : ℕ} (i : S) :
    Matrix (Sigma (nativeTaggedBlock (S := S) (n := n)))
      (Sigma (nativeTaggedBlock (S := S) (n := n))) ℝ :=
  let J := taggedBlockInclusion (𝕜 := ℝ) (ι := nativeTaggedBlock) (.inl i : S ⊕ Fin n)
  J * Jᴴ

theorem nativeTaggedScalarRail_density {S : Type*} [Fintype S] [DecidableEq S] {n : ℕ} (i : S) :
    let X := nativeTaggedScalarRail (n := n) i
    X.PosSemidef ∧ X.trace = 1 := by
  let J := taggedBlockInclusion (𝕜 := ℝ) (ι := nativeTaggedBlock) (.inl i : S ⊕ Fin n)
  change (J * Jᴴ).PosSemidef ∧ (J * Jᴴ).trace = 1
  have hpos := (Matrix.PosSemidef.one : (1 : Matrix (nativeTaggedBlock (.inl i : S ⊕ Fin n)) _ ℝ).PosSemidef).mul_mul_conjTranspose_same J
  rw [Matrix.mul_one] at hpos
  refine ⟨hpos, ?_⟩
  rw [Matrix.trace_mul_comm, taggedBlockInclusion_same]
  change (1 : Matrix Unit Unit ℝ).trace = 1
  simp

theorem nativeTaggedScalarRail_idempotent {S : Type*} [Fintype S] [DecidableEq S] {n : ℕ} (i : S) :
    let X := nativeTaggedScalarRail (n := n) i
    X * X = X := by
  let J := taggedBlockInclusion (𝕜 := ℝ) (ι := nativeTaggedBlock) (.inl i : S ⊕ Fin n)
  change (J * Jᴴ) * (J * Jᴴ) = J * Jᴴ
  calc
    _ = J * (Jᴴ * J) * Jᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [taggedBlockInclusion_same, Matrix.mul_one]

/-- Exact yes effect and reset operation on a given scalar source tag. -/
theorem nativeTagged_yes_scalarRail {S : Type*} [Fintype S] [DecidableEq S] {n : ℕ}
    (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i)) (z : S → Albert)
    (hz : ∀ s, IsDensity (z s)) (reset : Fin n → S) (i : S) (j : Fin n) :
    let K := nativeTaggedKraus p hp z hz reset (j, true)
    let X := nativeTaggedScalarRail (n := n) i
    let a := tracePairing (p j) (z i)
    rectangularKrausEffect K * X = a • X ∧
      rectangularKrausAction K X = a • nativeTaggedScalarRail (n := n) (reset j) := by
  let L := nativeTaggedLocalKraus p hp z hz reset (j, true)
  let s : S ⊕ Fin n := .inl i
  let t := nativeTaggedTarget reset (j, true)
  let J (u : S ⊕ Fin n) := taggedBlockInclusion (𝕜 := ℝ) (ι := nativeTaggedBlock) u
  let a := tracePairing (p j) (z i)
  have heffect : rectangularKrausEffect (L s) = a • (1 : Matrix (nativeTaggedBlock s) _ ℝ) :=
    nativeScalarYesKraus_effect (p j) (hp j) (z i) (hz i).1
  have ha : rectangularKrausAction (L s) 1 =
      a • (1 : Matrix (nativeTaggedBlock t) _ ℝ) := by
    have h := nativeScalarYesKraus_action (p j) (hp j) (z i) (hz i).1 1
    rw [one_smul, one_mul] at h
    exact h
  change rectangularKrausEffect (taggedKrausList t L) * (J s * (J s)ᴴ) = a • (J s * (J s)ᴴ) ∧
    rectangularKrausAction (taggedKrausList t L) (J s * (J s)ᴴ) = a • (J t * (J t)ᴴ)
  constructor
  · calc
      _ = (J s * rectangularKrausEffect (L s)) * (J s)ᴴ := by
        rw [← Matrix.mul_assoc, taggedKrausList_effect_inclusion]
      _ = _ := by rw [heffect, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  · rw [taggedKrausList_action, Finset.sum_eq_single s]
    · have h : (J s)ᴴ * (J s * (J s)ᴴ) * J s = 1 := by
        rw [← Matrix.mul_assoc (J s)ᴴ (J s), taggedBlockInclusion_same, Matrix.one_mul,
          taggedBlockInclusion_same]
      rw [h, ha, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    · intro u _ hu
      have h : (J u)ᴴ * (J s * (J s)ᴴ) * J u = 0 := by
        rw [← Matrix.mul_assoc (J u)ᴴ (J s), taggedBlockInclusion_distinct _ _ hu,
          Matrix.zero_mul, Matrix.zero_mul]
      rw [h]
      simp [rectangularKrausAction, Matrix.mul_zero, Matrix.zero_mul]
    · simp

def complexTaggedScalarRail {S : Type*} [Fintype S] [DecidableEq S] {n d : ℕ}
    (e : Sigma (nativeTaggedBlock (S := S) (n := n)) ≃ Fin d) (i : S) : ComplexMatrix d :=
  complexifyMatrix (renameRealMatrix e (nativeTaggedScalarRail (n := n) i))

private theorem complexTaggedScalarRail_density {S : Type*} [Fintype S] [DecidableEq S] {n d : ℕ}
    (e : Sigma (nativeTaggedBlock (S := S) (n := n)) ≃ Fin d) (i : S) :
    IsMatrixDensity (complexTaggedScalarRail e i) := by
  obtain ⟨hP, htr⟩ := nativeTaggedScalarRail_density (n := n) i
  exact (complexifyMatrix_density_iff _).mpr
    ⟨renameRealMatrix_positive e _ hP, (renameRealMatrix_trace e _).trans htr⟩

private theorem complexTaggedScalarRail_idempotent {S : Type*} [Fintype S] [DecidableEq S] {n d : ℕ}
    (e : Sigma (nativeTaggedBlock (S := S) (n := n)) ≃ Fin d) (i : S) :
    complexTaggedScalarRail e i * complexTaggedScalarRail e i = complexTaggedScalarRail e i := by
  unfold complexTaggedScalarRail
  rw [← complexifyMatrix_mul, ← renameRealMatrix_mul, nativeTaggedScalarRail_idempotent]

private theorem complexTagged_yes_scalarRail {S : Type*} [Fintype S] [DecidableEq S] {n d : ℕ}
    (e : Sigma (nativeTaggedBlock (S := S) (n := n)) ≃ Fin d)
    (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i)) (z : S → Albert)
    (hz : ∀ s, IsDensity (z s)) (reset : Fin n → S) (i : S) (j : Fin n) :
    let K := ((nativeTaggedKraus p hp z hz reset (j, true)).map (renameRealMatrix e)).map complexifyMatrix
    let a := tracePairing (p j) (z i)
    krausEffect K * complexTaggedScalarRail e i = a • complexTaggedScalarRail e i ∧
      krausAction K (complexTaggedScalarRail e i) = a • complexTaggedScalarRail e (reset j) := by
  obtain ⟨heffect, ha⟩ := nativeTagged_yes_scalarRail p hp z hz reset i j
  dsimp only [complexTaggedScalarRail]
  constructor
  · rw [← complexifyRectangularKrausEffect, ← renameRectangularKrausEffect, ← complexifyMatrix_mul,
      ← renameRealMatrix_mul, heffect]
    exact complexifyMatrix_real_smul _ _
  · rw [← complexifyRectangularKrausAction, ← renameRectangularKrausAction, ha]
    exact complexifyMatrix_real_smul _ _

private theorem nativeTagged_effect_ne_zero {S : Type*} [Fintype S] [DecidableEq S] {n : ℕ}
    (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i)) (z : S → Albert)
    (hz : ∀ s, IsDensity (z s)) (reset : Fin n → S) (hreset : ∀ i, z (reset i) = p i)
    (j : Fin n) (a : Bool) :
    rectangularKrausEffect (nativeTaggedKraus p hp z hz reset (j, a)) ≠ 0 := by
  let A := rectangularKrausEffect (nativeTaggedKraus p hp z hz reset (j, true))
  let L := nativeTaggedLocalKraus p hp z hz reset (j, true)
  let t := nativeTaggedTarget reset (j, true)
  cases a with
  | true =>
    intro h
    have he := (nativeTagged_yes_scalarRail p hp z hz reset (reset j) j).1
    change A = 0 at h
    change A * nativeTaggedScalarRail (reset j) = _ at he
    rw [h, Matrix.zero_mul, hreset, tracePairing, (hp j).1, (hp j).2, one_smul] at he
    have htr := (nativeTaggedScalarRail_density (n := n) (reset j)).2
    rw [← he, Matrix.trace_zero] at htr
    exact zero_ne_one htr
  | false =>
    intro h
    have hA := nativeTaggedKraus_normalized p hp z hz reset j
    rw [h, add_zero] at hA
    let J := taggedBlockInclusion (𝕜 := ℝ) (ι := nativeTaggedBlock) (Sum.inr j : S ⊕ Fin n)
    have hJzero : A * J = 0 := by
      have hz0 := nativeTaggedLocalYes_corner_zero p hp z hz j
      calc
        _ = J * rectangularKrausEffect (L (.inr j)) :=
          taggedKrausList_effect_inclusion (ι := nativeTaggedBlock) t L (Sum.inr j)
        _ = _ := by
          have he0 : rectangularKrausEffect (L (.inr j)) = 0 := hz0
          rw [he0, Matrix.mul_zero]
    change A = 1 at hA
    rw [hA, Matrix.one_mul] at hJzero
    have hone := taggedBlockInclusion_same (𝕜 := ℝ) (ι := nativeTaggedBlock) (Sum.inr j : S ⊕ Fin n)
    change Jᴴ * J = (1 : Matrix (nativeTaggedBlock (Sum.inr j : S ⊕ Fin n)) _ ℝ) at hone
    rw [hJzero, Matrix.mul_zero] at hone
    have hcard : Nonempty SpinorCoordinate := Fintype.card_pos_iff.mp (by rw [spinorCoordinate_card]; decide)
    obtain ⟨i⟩ := hcard
    have hone' : (0 : Matrix SpinorCoordinate SpinorCoordinate ℝ) = 1 := hone
    have hi := congrArg (fun M : Matrix SpinorCoordinate SpinorCoordinate ℝ => M i i) hone'
    exact zero_ne_one (by simpa only [Matrix.zero_apply, Matrix.one_apply_eq] using hi)

private theorem complexTagged_effect_ne_zero {S : Type*} [Fintype S] [DecidableEq S] {n d : ℕ}
    (e : Sigma (nativeTaggedBlock (S := S) (n := n)) ≃ Fin d)
    (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i)) (z : S → Albert)
    (hz : ∀ s, IsDensity (z s)) (reset : Fin n → S) (hreset : ∀ i, z (reset i) = p i)
    (j : Fin n) (a : Bool) :
    krausEffect (((nativeTaggedKraus p hp z hz reset (j, a)).map (renameRealMatrix e)).map
      complexifyMatrix) ≠ 0 := by
  rw [← complexifyRectangularKrausEffect, ← renameRectangularKrausEffect]
  intro h
  rw [← complexifyMatrix_zero] at h
  have hr := complexifyMatrix_injective h
  apply nativeTagged_effect_ne_zero p hp z hz reset hreset j a
  ext i j
  have he := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M (e i) (e j)) hr
  simpa only [renameRealMatrix, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.zero_apply] using he

private theorem exists_real_supported_literalDilation {d : ℕ} {I : Type*}
    (r : BinaryKrausRealization d I) (hr : IsRealKrausRealization r)
    (hsup : HasCertaintySupportedOutputs r) (hne : ∀ x a, krausEffect (r.kraus x a) ≠ 0) :
    ∃ (s : ∀ x, BinarySpectralSupport (krausEffect (r.kraus x true)))
      (B : I → Bool → ComplexMatrix d) (C : I → Bool → ComplexMatrix (d + d)),
      IsSharpDilation r (binaryKrausDilation r s B C) ∧
      IsRepeatableSharpDilation (binaryKrausDilation r s B C) ∧
      IsRealSharpDilation (binaryKrausDilation r s B C) := by
  have hA (x : I) := krausEffect_positive (r.kraus x true)
  have hAc (x : I) : (1 - krausEffect (r.kraus x true)).PosSemidef := by
    rw [← r.no_effect]
    exact krausEffect_positive _
  have hreal (x : I) := krausEffect_hasRealEntries (r.kraus x true) (hr.2 x true)
  let s (x : I) := realBinarySpectralSupport (hA x) (hAc x) (hreal x)
  have hd (x : I) (a : Bool) := normalizedKrausOutput_density (r.kraus x a) (hne x a)
  let B (x : I) (a : Bool) := Classical.choose (exists_real_positiveFactor (hd x a).1
    (normalizedKrausOutput_real (r.kraus x a) (hr.2 x a)))
  have hB (x : I) (a : Bool) :
      HasRealEntries (B x a) ∧ B x a * (B x a)ᴴ = normalizedKrausOutput (r.kraus x a) :=
    Classical.choose_spec (exists_real_positiveFactor (hd x a).1
      (normalizedKrausOutput_real (r.kraus x a) (hr.2 x a)))
  obtain ⟨B0, hB0real, hB0⟩ := exists_real_positiveFactor r.density.1 hr.1
  let C (_ : I) (_ : Bool) := embedFirstBlock B0
  have hC (x : I) (a : Bool) : (C x a * (C x a)ᴴ).trace = 1 := by
    change (embedFirstBlock B0 * (embedFirstBlock B0)ᴴ).trace = 1
    rw [embedFirstBlock_conjTranspose, embedFirstBlock_mul, trace_embedFirstBlock, hB0]
    exact r.density.2
  refine ⟨s, B, C, binaryKrausDilation_isSharpDilation r s B C (fun x a => ?_) hC,
    binaryKrausDilation_repeatable_of_supported_resets r s B C hsup (fun x a => ?_),
    binaryKrausDilation_real r hr s B C (fun x => realBinarySpectralSupport_real _ _ _)
      (fun x a => (hB x a).1) (fun _ _ => embedFirstBlock_real B0 hB0real)⟩
  · rw [(hB x a).2]
    exact (hd x a).2
  · rw [(hB x a).2]
    exact normalizedKrausOutput_supported _ _ (r.outcome_supported hsup x a)

/-- A scalar rail of the general complex model. None denotes the initial ray
and some j denotes the reset ray of test j. -/
def nativeGeneralScalarRail {n : ℕ} (i : Option (Fin n)) : ComplexMatrix (17*n+1) :=
  let e := Fintype.equivFinOfCardEq (show Fintype.card
    (Sigma (nativeTaggedBlock (S := Option (Fin n)) (n := n))) = 17*n+1 by
      rw [nativeTaggedBlock_card]
      simp only [Fintype.card_option, Fintype.card_fin]
      omega)
  complexTaggedScalarRail e i

/-- The displayed pure state in the yes face over the initial scalar rail. -/
def nativeGeneralCertainInitState (n : ℕ) (a : ℝ) : ComplexMatrix ((17*n+1)+(17*n+1)) :=
  let X := nativeGeneralScalarRail (none : Option (Fin n))
  let V := (Matrix.fromRows (Real.sqrt a • X) (Real.sqrt (1-a) • X)).submatrix
    (finSumFinEquiv : Fin (17*n+1) ⊕ Fin (17*n+1) ≃ Fin ((17*n+1)+(17*n+1))).symm id
  V * Vᴴ

/-- The literal doubled construction for the general preparation-dependent
simulator fails ideality on the image of its initial rail whenever this rail
has strictly interior yes weight. -/
theorem nativeGeneral_sharp_initialRail_disturbance {n : ℕ}
    (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i)) (ρ : Albert) (hρ : IsDensity ρ) (j : Fin n)
    (ha0 : 0 < tracePairing (p j) ρ) (ha1 : tracePairing (p j) ρ < 1) :
    ∃ (r : BinaryKrausRealization (17*n+1) (Fin n)) (s : SharpDilationData (17*n+1) (Fin n))
      (Z : ComplexMatrix ((17*n+1)+(17*n+1))),
      Z = nativeGeneralCertainInitState n (tracePairing (p j) ρ) ∧
      IsSharpDilation r s ∧ IsRepeatableSharpDilation s ∧ IsRealSharpDilation s ∧
      (∀ w, s.wordProbability r.initial w = nativeWordProbability p ρ w) ∧
      IsMatrixDensity Z ∧ s.projection j * Z = Z ∧
      s.branch j true Z = embedFirstBlock (nativeGeneralScalarRail (some j)) ∧
      s.branch j true Z ≠ Z := by
  let z := nativeGeneralScalarStates p ρ
  let hz := nativeGeneralScalarStates_density p hp ρ hρ
  let xs : Option (Fin n) ⊕ Fin n → Albert := Pi.single (.inl none) ρ
  have hxs := native_positive_single (.inl none : Option (Fin n) ⊕ Fin n) ρ hρ.1
  have hdec : taggedLinearDecoding (nativeTaggedPieceDecoder p z) xs = ρ :=
    nativeGeneralPieces_decoding p ρ hρ
  have ht : albertTrace (taggedLinearDecoding (nativeTaggedPieceDecoder p z) xs) = 1 := by
    rw [hdec]
    exact hρ.2
  let r0 := nativeTaggedRealModel p hp z hz Option.some xs hxs ht
  have hsup0 := nativeTaggedRealModel_certainty p hp z hz Option.some (fun _ => rfl) xs hxs ht
  have hd : Fintype.card (Sigma (nativeTaggedBlock (S := Option (Fin n)) (n := n))) = 17*n+1 := by
    rw [nativeTaggedBlock_card]
    simp only [Fintype.card_option, Fintype.card_fin]
    omega
  let e := Fintype.equivFinOfCardEq hd
  let r := complexifyRealFiniteKrausModel (renameRealFiniteKrausModel e r0)
  have hsup : HasCertaintySupportedOutputs r :=
    complexifyRealFiniteKrausModel_supported _ (renameRealFiniteKrausModel_certainty e r0 hsup0)
  have hne (i : Fin n) (b : Bool) : krausEffect (r.kraus i b) ≠ 0 :=
    complexTagged_effect_ne_zero e p hp z hz Option.some (fun _ => rfl) i b
  have hw (w : Word (Fin n)) : binaryKrausProbability r w = nativeWordProbability p ρ w := by
    rw [complexifyRealFiniteKrausModel_probability, renameRealFiniteKrausModel_probability]
    show realFiniteKrausProbability _ _ r0 w = _
    rw [nativeTaggedRealModel_probability p hp z hz Option.some (fun _ => rfl) xs hxs ht, hdec]
  obtain ⟨s, B, C, hsharp, hrepeat, hreal⟩ :=
    exists_real_supported_literalDilation r (complexifyRealFiniteKrausModel_real _) hsup hne
  let S := binaryKrausDilation r s B C
  let X := complexTaggedScalarRail e none
  let Y := complexTaggedScalarRail e (some j)
  let Z := binaryYesFaceState (s j) X
  have hX : IsMatrixDensity X := complexTaggedScalarRail_density e none
  have hAX : krausEffect (r.kraus j true) * X = tracePairing (p j) ρ • X :=
    (complexTagged_yes_scalarRail e p hp z hz Option.some none j).1
  have hrun : krausAction (r.kraus j true) X = tracePairing (p j) ρ • Y :=
    (complexTagged_yes_scalarRail e p hp z hz Option.some none j).2
  have hbranch : S.branch j true Z = embedFirstBlock Y :=
    binaryKrausDilation_branch_yesFace r s B C j ha0 hX.1.isHermitian hAX hrun
  have hformula : Z = nativeGeneralCertainInitState n (tracePairing (p j) ρ) :=
    binaryYesFaceState_eigenprojection_formula (s j) ha0 ha1 hX.1.isHermitian
      (complexTaggedScalarRail_idempotent e none) hAX
  refine ⟨r, S, Z, hformula, hsharp, hrepeat, hreal,
    fun w => (hsharp.2.2.2.2.2.2.2.2 w).trans (hw w),
    binaryYesFaceState_density (s j) hX, binaryYesFaceState_certain (s j) X, hbranch, ?_⟩
  rw [hbranch]
  exact (binaryYesFaceState_not_first_corner (s j) hX ha0 ha1 hAX Y).symm

/-- The unchanged scalar reset rail of the tagged 68-dimensional model, after
its literal coordinate renaming and complexification. -/
def nativeMScalarRail (i : Fin 4) : ComplexMatrix 68 :=
  let e := Fintype.equivFinOfCardEq (show Fintype.card
    (Sigma (nativeTaggedBlock (S := Fin 4) (n := 4))) = 68 by
      rw [nativeTaggedBlock_card]
      decide)
  complexifyMatrix (renameRealMatrix e (nativeTaggedScalarRail (n := 4) i))

/-- The pure state of the displayed vector on the doubled C reset plane. -/
def nativeMCertainCState : ComplexMatrix 136 :=
  let X := nativeMScalarRail 2
  let V := (Matrix.fromRows (Real.sqrt (1/3 : ℝ) • X) (Real.sqrt (2/3 : ℝ) • X)).submatrix
    (finSumFinEquiv : Fin 68 ⊕ Fin 68 ≃ Fin 136).symm id
  V * Vᴴ

/-- The actual proposed sharp repeatable model of M has a common A-yes and
B-yes certainty state on the C reset plane. The certain A press sends that
state to the A reset rail, and B yes drops to exactly one third. -/
theorem nativeM_sharp_two_presses :
    ∃ (r : BinaryKrausRealization 68 (Fin 4)) (s : SharpDilationData 68 (Fin 4))
      (Z : ComplexMatrix 136),
      Z = nativeMCertainCState ∧ IsSharpDilation r s ∧ IsRepeatableSharpDilation s ∧ IsRealSharpDilation s ∧
      (∀ w, s.wordProbability r.initial w =
        nativeWordProbability maximizerConfig ((1 / 3 : ℝ) • albertUnit) w) ∧
      IsMatrixDensity Z ∧ s.projection 0 * Z = Z ∧ s.projection 1 * Z = Z ∧
      (s.projection 1 * Z).trace = 1 ∧
      s.branch 0 true Z = embedFirstBlock (nativeMScalarRail 0) ∧
      (s.projection 1 * s.branch 0 true Z).trace = (1 / 3 : ℂ) ∧
      (∀ Y : ComplexMatrix 68, Z ≠ embedFirstBlock Y) := by
  let p := maximizerConfig
  let hp := maximizerConfig_isAtom
  let ρ := (1 / 3 : ℝ) • albertUnit
  let y := (1 / 3 : ℝ) • (albertUnit - p 0)
  let hz : ∀ i, IsDensity (p i) := fun i => native_atom_density (p i) (hp i)
  have hy : IsPositive y := isPositive_smul _ _ (by norm_num)
    (isPositive_idempotent _ (complementary_idempotent _ (hp 0).1))
  have hpy : jordanMul (p 0) y = 0 := by
    rw [show y = (1 / 3 : ℝ) • (albertUnit - p 0) from rfl, jordanMul_smul_right,
      jordanMul_sub_right, jordanMul_albertUnit_right, (hp 0).1, sub_self, smul_zero]
  let xs := nativeNoHalfPieces p 0 (1 / 3) y
  have hxs : ∀ s, IsPositive (xs s) := nativeNoHalfPieces_positive p hp _ _ (by norm_num) _ hy
  have hdec : taggedLinearDecoding (nativeTaggedPieceDecoder p p) xs = ρ := by
    rw [show xs = nativeNoHalfPieces p 0 (1 / 3) y from rfl, nativeNoHalfPieces_decoding p hp _ _ _ hpy]
    dsimp only [ρ, y]
    module
  have ht : albertTrace (taggedLinearDecoding (nativeTaggedPieceDecoder p p) xs) = 1 := by
    rw [hdec]
    exact nativeMixedDensity.2
  let r0 := nativeTaggedRealModel p hp p hz id xs hxs ht
  have hsup0 := nativeTaggedRealModel_certainty p hp p hz id (fun _ => rfl) xs hxs ht
  have hd : Fintype.card (Sigma (nativeTaggedBlock (S := Fin 4) (n := 4))) = 68 := by
    rw [nativeTaggedBlock_card]
    decide
  let e := Fintype.equivFinOfCardEq hd
  let r := complexifyRealFiniteKrausModel (renameRealFiniteKrausModel e r0)
  have hsup : HasCertaintySupportedOutputs r :=
    complexifyRealFiniteKrausModel_supported _ (renameRealFiniteKrausModel_certainty e r0 hsup0)
  have hw (w : Word (Fin 4)) : binaryKrausProbability r w = nativeWordProbability p ρ w := by
    rw [complexifyRealFiniteKrausModel_probability, renameRealFiniteKrausModel_probability]
    show realFiniteKrausProbability _ _ r0 w = _
    rw [nativeTaggedRealModel_probability p hp p hz id (fun _ => rfl) xs hxs ht, hdec]
  have hexact (i j : Fin 4) :
      let a := tracePairing (p j) (p i)
      krausEffect (r.kraus j true) * nativeMScalarRail i = a • nativeMScalarRail i ∧
      krausAction (r.kraus j true) (nativeMScalarRail i) = a • nativeMScalarRail j :=
    complexTagged_yes_scalarRail e p hp p hz id i j
  have hden (i : Fin 4) : IsMatrixDensity (nativeMScalarRail i) :=
    complexTaggedScalarRail_density e i
  have hidem (i : Fin 4) : nativeMScalarRail i * nativeMScalarRail i = nativeMScalarRail i :=
    complexTaggedScalarRail_idempotent e i
  have hov (i j : Fin 4) (hij : i ≠ j) : tracePairing (p i) (p j) = 1 / 3 :=
    (maximizerConfig_traces (Equiv.refl _)).1 i j hij
  obtain ⟨s, B, C, hsharp, hrepeat, hreal⟩ :=
    exists_real_supported_literalDilation r (complexifyRealFiniteKrausModel_real _) hsup
      (complexTagged_effect_ne_zero e p hp p hz id (fun _ => rfl))
  let S := binaryKrausDilation r s B C
  let X := nativeMScalarRail 2
  let Z := binaryYesFaceState (s 0) X
  have hX := hden 2
  have hAX : krausEffect (r.kraus 0 true) * X = (1 / 3 : ℝ) • X := by
    have h := (hexact 2 0).1
    rw [hov 0 2 (by decide)] at h
    exact h
  have hBX : krausEffect (r.kraus 1 true) * X = (1 / 3 : ℝ) • X := by
    have h := (hexact 2 1).1
    rw [hov 1 2 (by decide)] at h
    exact h
  have hrun : krausAction (r.kraus 0 true) X = (1 / 3 : ℝ) • nativeMScalarRail 0 := by
    have h := (hexact 2 0).2
    rw [hov 0 2 (by decide)] at h
    exact h
  have hface : Z = binaryYesFaceState (s 1) X :=
    binaryYesFaceState_eq_of_common_eigenvalue _ _ (by norm_num) (by norm_num) hX.1.isHermitian
      (hidem 2) hAX hBX
  have hZ := binaryYesFaceState_density (s 0) hX
  have hcertA : S.projection 0 * Z = Z := binaryYesFaceState_certain (s 0) X
  have hcertB : S.projection 1 * Z = Z := by
    rw [hface]
    exact binaryYesFaceState_certain (s 1) X
  have hbranch : S.branch 0 true Z = embedFirstBlock (nativeMScalarRail 0) :=
    binaryKrausDilation_branch_yesFace r s B C _ (by norm_num) hX.1.isHermitian hAX hrun
  have hformula : Z = nativeMCertainCState := by
    have h := binaryYesFaceState_eigenprojection_formula (s 0) (by norm_num)
      (by norm_num) hX.1.isHermitian (hidem 2) hAX
    dsimp only at h
    rw [show (1 : ℝ) - 1/3 = 2/3 by norm_num] at h
    exact h
  refine ⟨r, S, Z, hformula, hsharp, hrepeat, hreal, fun w => (hsharp.2.2.2.2.2.2.2.2 w).trans (hw w),
    hZ, hcertA, hcertB, by rw [hcertB]; exact hZ.2, hbranch, ?_,
    binaryYesFaceState_not_first_corner (s 0) hX (by norm_num) (by norm_num) hAX⟩
  have hb : krausEffect (r.kraus 1 true) * nativeMScalarRail 0 = (1 / 3 : ℝ) • nativeMScalarRail 0 := by
    have h := (hexact 0 1).1
    rw [hov 1 0 (by decide)] at h
    exact h
  rw [hbranch, embedFirstBlock, ← Matrix.mul_assoc, Matrix.trace_mul_cycle, ← Matrix.mul_assoc]
  change (compressFirstBlock (S.projection 1) * nativeMScalarRail 0).trace = _
  rw [hsharp.2.2.2.2.1 1, hb, Matrix.trace_smul, (hden 0).2]
  norm_num

end AlbertSequential.NativeAnalysis
