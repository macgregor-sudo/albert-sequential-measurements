/- SPDX-License-Identifier: Apache-2.0 -/
module

public import OptimalSpectralFrames
public import OptimalBinaryFrameChoice
public import RealSpectralSupport

/-! Choose reduced sharp frames in the actual real spectral basis whenever
the effect is real. Exactly zero and unit effects use the corresponding
ambient zero and identity, including any unused ancillary coordinates. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential

open Matrix
open scoped ComplexOrder

private theorem zero_entriesReal {n m : Type*} :
    ∀ i j, ((0 : Matrix n m ℂ) i j).im = 0 := fun _ _ => rfl

private theorem one_entriesReal {n : Type*} [DecidableEq n] :
    ∀ i j, ((1 : Matrix n n ℂ) i j).im = 0 := by
  intro i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

private theorem firstRows_entriesReal {n m : Type*} [DecidableEq n] :
    ∀ i j, ((fromRows 1 0 : Matrix (n ⊕ m) n ℂ) i j).im = 0 := by
  intro i j
  cases i with
  | inl i => exact one_entriesReal i j
  | inr i => exact zero_entriesReal i j

private theorem firstRows_gram {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] :
    let J : Matrix (n ⊕ m) n ℂ := fromRows 1 0
    Jᴴ * J = 1 := by
  simp [conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows]

private def zeroEffectSpectral {d : ℕ} {A : ComplexMatrix d} (hA : A = 0) : FiniteSpectralSupport A where
  root := 0
  inverseRoot := 0
  support := 0
  root_positive := Matrix.PosSemidef.zero
  root_hermitian := conjTranspose_zero
  inverse_hermitian := conjTranspose_zero
  support_hermitian := conjTranspose_zero
  root_sq := by simp [hA]
  inverse_root := by simp
  root_inverse := by simp
  inverse_effect := by simp
  support_sq := by simp
  effect_complement := by simp [hA]
  root_complement := by simp

private def unitEffectSpectral {d : ℕ} {A : ComplexMatrix d} (hA : A = 1) : FiniteSpectralSupport A where
  root := 1
  inverseRoot := 1
  support := 1
  root_positive := Matrix.PosSemidef.one
  root_hermitian := conjTranspose_one
  inverse_hermitian := conjTranspose_one
  support_hermitian := conjTranspose_one
  root_sq := by simp [hA]
  inverse_root := by simp
  root_inverse := by simp
  inverse_effect := by simp [hA]
  support_sq := by simp
  effect_complement := by simp
  root_complement := by simp

private def zeroOutcomeFrame {n m : Type*} [Fintype n] [Fintype m]
    (J : Matrix m n ℂ) (P : Matrix m m ℂ) (hP : P = 0) : SharpDilationChannelFrame J P 0 where
  frame := 0
  range_idempotent := by simp
  projection_frame := by simp
  frame_inclusion := by simp
  projection_inclusion := by simp [hP]

private def unitOutcomeFrame {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (J : Matrix m n ℂ) (hJ : Jᴴ * J = 1) (P : Matrix m m ℂ) (hP : P = 1) :
    SharpDilationChannelFrame J P 1 where
  frame := J
  range_idempotent := frameRange_idempotent_of_mul_gram (by rw [hJ, Matrix.mul_one])
  projection_frame := by rw [hP, Matrix.one_mul]
  frame_inclusion := hJ
  projection_inclusion := by rw [hP, Matrix.one_mul, Matrix.mul_one]

private theorem exists_degenerateOptimalBinaryFrameChoice {d m : ℕ} {A : ComplexMatrix d}
    (h : A = 0 ∨ A = 1) (hd : 0 < d) : Nonempty (OptimalBinaryFrameChoice (m := m) A) := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let J : Matrix (Fin d ⊕ Fin m) (Fin d) ℂ := fromRows 1 0
  have hJ : Jᴴ * J = 1 := firstRows_gram
  rcases h with hz | ho
  · let s : BinarySpectralSupport A := ⟨zeroEffectSpectral hz,
      unitEffectSpectral (by rw [hz, sub_zero]), by simp [zeroEffectSpectral, unitEffectSpectral]⟩
    let f : SharpDilationChannelFrame J (1 - 0) s.no.root := unitOutcomeFrame J hJ _ (sub_zero _)
    refine ⟨{ spectral := s
              projection := 0
              hermitian := conjTranspose_zero
              idempotent := Matrix.zero_mul _
              compression := by simp [hz]
              yesFrame := zeroOutcomeFrame J _ rfl
              noFrame := f
              zero_yes := fun _ => rfl
              zero_no := ?_
              real_data := ?_ }⟩
    · intro h
      exact (one_ne_zero ((sub_eq_zero.mp h).trans hz)).elim
    · intro _
      exact ⟨zero_entriesReal, zero_entriesReal, firstRows_entriesReal, zero_entriesReal,
        one_entriesReal, zero_entriesReal, one_entriesReal⟩
  · let s : BinarySpectralSupport A := ⟨unitEffectSpectral ho,
      zeroEffectSpectral (by rw [ho, sub_self]), by simp [zeroEffectSpectral, unitEffectSpectral]⟩
    let f : SharpDilationChannelFrame J (1 - 1) s.no.root := zeroOutcomeFrame J _ (sub_self _)
    refine ⟨{ spectral := s
              projection := 1
              hermitian := conjTranspose_one
              idempotent := Matrix.one_mul _
              compression := by dsimp only; rw [Matrix.mul_one, ho]; exact hJ
              yesFrame := unitOutcomeFrame J hJ _ rfl
              noFrame := f
              zero_yes := fun h => (one_ne_zero (ho.symm.trans h)).elim
              zero_no := fun _ => sub_self _
              real_data := ?_ }⟩
    intro _
    exact ⟨one_entriesReal, firstRows_entriesReal, zero_entriesReal, one_entriesReal,
      zero_entriesReal, one_entriesReal, zero_entriesReal⟩

private theorem complexifyMatrix_conjTranspose_rect {n m : Type*} (V : Matrix m n ℝ) :
    complexifyMatrix Vᴴ = (complexifyMatrix V)ᴴ := complexifyMatrix_transpose V

private def complexifyUnitary {n : Type*} [Fintype n] [DecidableEq n]
    (U : unitary (Matrix n n ℝ)) : unitary (Matrix n n ℂ) :=
  ⟨complexifyMatrix U.val, Unitary.mem_iff.mpr ⟨by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose, complexifyMatrix_conjTranspose_rect,
      complexifyMatrix_mul, complexifyMatrix_one] using congrArg complexifyMatrix (Unitary.coe_star_mul_self U), by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose, complexifyMatrix_conjTranspose_rect,
      complexifyMatrix_mul, complexifyMatrix_one] using congrArg complexifyMatrix (Unitary.coe_mul_star_self U)⟩⟩

private theorem complexify_unitaryRealDiagonal {n : Type*} [Fintype n] [DecidableEq n]
    (U : unitary (Matrix n n ℝ)) (a : n → ℝ) :
    complexifyMatrix (unitaryRealDiagonal U a) = unitaryRealDiagonal (complexifyUnitary U) a := by
  simp only [unitaryRealDiagonal, Unitary.conjStarAlgAut_apply, complexifyMatrix_mul,
    Matrix.star_eq_conjTranspose, complexifyMatrix_conjTranspose_rect]
  congr 2
  ext i j
  by_cases h : i = j
  · subst j; simp [complexifyMatrix]
  · simp [complexifyMatrix, h]

private theorem exists_realNondegenerateOptimalBinaryFrameChoice {d m : ℕ} {A : ComplexMatrix d}
    (hA : A.PosSemidef) (hAc : (1 - A).PosSemidef) (hr : (A - A ^ 2).rank ≤ m)
    (hreal : HasRealEntries A) (h0 : A ≠ 0) (h1 : A ≠ 1) :
    Nonempty (OptimalBinaryFrameChoice (m := m) A) := by
  classical
  let R := realPartMatrix A
  have hR : R.PosSemidef := realPartMatrix_positive_of_real hA hreal
  have hcR : complexifyMatrix R = A := complexify_realPart_of_hasRealEntries A hreal
  have hRc : (1 - R).PosSemidef := by
    apply (complexifyMatrix_posSemidef_iff _).mp
    rw [complexifyMatrix_sub, complexifyMatrix_one, hcR]
    exact hAc
  let sR := binarySpectralSupport hR hRc
  let s := sR.toComplex hcR
  let U := hR.isHermitian.eigenvectorUnitary
  let a := hR.isHermitian.eigenvalues
  have hdiag : unitaryRealDiagonal U a = R := hR.isHermitian.spectral_theorem.symm
  have hcdiag : unitaryRealDiagonal U (fun i => 1 - a i) = 1 - R := by
    rw [← unitaryRealDiagonal_sub, unitaryRealDiagonal_one, hdiag]
  have hc : ∀ i, a i ≤ 1 := fun i => sub_nonneg.mp
    ((unitaryRealDiagonal_positive_iff U _).mp (hcdiag.symm ▸ hRc) i)
  have hcdiagA : unitaryRealDiagonal (complexifyUnitary U) a = A := by
    rw [← complexify_unitaryRealDiagonal, hdiag, hcR]
  rw [← hcdiagA, rank_spectralDefect] at hr
  have hcard : Fintype.card {i : Fin d // a i - a i * a i ≠ 0} ≤ Fintype.card (Fin m) :=
    (Fintype.card_fin m).symm ▸ hr
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  let vr := reducedSpectralFrame U a e (fun i => Real.sqrt (a i)) (fun i => Real.sqrt (1 - a i))
  let wr := reducedSpectralFrame U a e (fun i => Real.sqrt (1 - a i)) (fun i => -Real.sqrt (a i))
  let J : Matrix (Fin d ⊕ Fin m) (Fin d) ℂ := fromRows 1 0
  let Jr : Matrix (Fin d ⊕ Fin m) (Fin d) ℝ := fromRows 1 0
  have hJr : complexifyMatrix Jr = J := by
    simp only [Jr, J, complexifyMatrix, fromRows_map]
    rw [← show complexifyMatrix (1 : Matrix (Fin d) (Fin d) ℝ) = 1 from complexifyMatrix_one,
      ← show complexifyMatrix (0 : Matrix (Fin m) (Fin d) ℝ) = 0 from complexifyMatrix_zero]
    rfl
  let V := complexifyMatrix vr
  let W := complexifyMatrix wr
  obtain ⟨hvr, hwr, hvwr, hvJr, hwJr, hsumr⟩ := reducedSpectralFrame_data U a hR.eigenvalues_nonneg hc e
  have hv : V * (Vᴴ * V) = V := by
    simpa only [V, vr, complexifyMatrix_mul, complexifyMatrix_conjTranspose_rect] using
      congrArg complexifyMatrix hvr
  have hw : W * (Wᴴ * W) = W := by
    simpa only [W, wr, complexifyMatrix_mul, complexifyMatrix_conjTranspose_rect] using
      congrArg complexifyMatrix hwr
  have hvw : Vᴴ * W = 0 := by
    simpa only [V, W, vr, wr, complexifyMatrix_mul, complexifyMatrix_conjTranspose_rect,
      complexifyMatrix_zero] using congrArg complexifyMatrix hvwr
  have hyesRoot : s.yes.root = complexifyMatrix (unitaryRealDiagonal U (fun i => Real.sqrt (a i))) := rfl
  have hnoRoot : s.no.root = complexifyMatrix (unitaryRealDiagonal U (fun i => Real.sqrt (1 - a i))) := rfl
  have hvJ : Vᴴ * J = s.yes.root := by
    rw [← hJr, hyesRoot]
    simpa only [V, vr, Jr, complexifyMatrix_mul, complexifyMatrix_conjTranspose_rect] using
      congrArg complexifyMatrix hvJr
  have hwJ : Wᴴ * J = s.no.root := by
    rw [← hJr, hnoRoot]
    simpa only [W, wr, Jr, complexifyMatrix_mul, complexifyMatrix_conjTranspose_rect] using
      congrArg complexifyMatrix hwJr
  have hsum : J = V * s.yes.root + W * s.no.root := by
    rw [← hJr, hyesRoot, hnoRoot]
    simpa only [V, W, vr, wr, Jr, complexifyMatrix_mul, complexifyMatrix_add] using
      congrArg complexifyMatrix hsumr
  let f := pairedSharpDilationChannelFrame_of_partialFrames J V W _ _ hv hw hvw hvJ hwJ hsum
  have hP := sharpDilationProjectors_of_partialFrame hv
  have hleft := congrArg Matrix.conjTranspose hvJ
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, s.yes.root_hermitian] at hleft
  have hval : Jᴴ * (V * Vᴴ) * J = A := by
    rw [← Matrix.mul_assoc, hleft, Matrix.mul_assoc, hvJ, s.yes.root_sq]
  have hPreal : ∀ i j, ((V * Vᴴ) i j).im = 0 := by
    change ∀ i j, ((complexifyMatrix vr * (complexifyMatrix vr)ᴴ) i j).im = 0
    rw [← complexifyMatrix_conjTranspose_rect, ← complexifyMatrix_mul]
    intro i j; rfl
  have hsreal := sR.toComplex_entries_real hcR
  refine ⟨{ spectral := s
            projection := V * Vᴴ
            hermitian := hP.1
            idempotent := hP.2.1
            compression := hval
            yesFrame := f.1
            noFrame := f.2
            zero_yes := fun h => (h0 h).elim
            zero_no := fun h => (h1 (sub_eq_zero.mp h).symm).elim
            real_data := fun _ => ⟨hPreal, fun _ _ => rfl, fun _ _ => rfl,
              hsreal.2.2.1, hsreal.2.2.2.1, hsreal.2.2.2.2.1, hsreal.2.2.2.2.2⟩ }⟩

/-- Choose both sharp frames at the defect rank, including the zero-effect
guards and literal realness whenever the original effect is real. -/
theorem exists_optimalBinaryFrameChoice {d m : ℕ} {A : ComplexMatrix d}
    (hA : A.PosSemidef) (hAc : (1 - A).PosSemidef) (hr : (A - A ^ 2).rank ≤ m)
    (hd : 0 < d) :
    Nonempty (OptimalBinaryFrameChoice (m := m) A) := by
  classical
  by_cases h0 : A = 0
  · exact exists_degenerateOptimalBinaryFrameChoice (.inl h0) hd
  by_cases h1 : A = 1
  · exact exists_degenerateOptimalBinaryFrameChoice (.inr h1) hd
  by_cases hreal : HasRealEntries A
  · exact exists_realNondegenerateOptimalBinaryFrameChoice hA hAc hr hreal h0 h1
  obtain ⟨P, hP, hPP, hcomp, ⟨f⟩⟩ := exists_optimalSpectralFrames (m := Fin m) hA hAc (by simpa using hr)
  exact ⟨{ spectral := binarySpectralSupport hA hAc
           projection := P
           hermitian := hP
           idempotent := hPP
           compression := hcomp
           yesFrame := f.1
           noFrame := f.2
           zero_yes := fun h => (h0 h).elim
           zero_no := fun h => (h1 (sub_eq_zero.mp h).symm).elim
           real_data := fun h => (hreal h).elim }⟩

end AlbertSequential
