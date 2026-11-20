/- SPDX-License-Identifier: Apache-2.0 -/
module

public import SharpDilationChannelFrame
public import BinaryKrausDilation

/-! Finite Kraus channel transport through the partial-isometry ranges in
companion Proposition 6.4. All action and intertwining formulas take arbitrary matrices. -/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace AlbertSequential

open Matrix
open scoped ComplexOrder

theorem partialFrameCompletedKraus_effect {d D : ℕ} (K : List (ComplexMatrix d))
    (J V : Matrix (Fin D) (Fin d) ℂ) (C : ComplexMatrix D)
    (hK : krausEffect K = 1) (hJ : Jᴴ * J = 1)
    (hV : (V * Vᴴ) * (V * Vᴴ) = V * Vᴴ)
    (hC : Matrix.trace (C * Cᴴ) = 1) :
    krausEffect (isometricCompletedKraus K J V C) = 1 := by
  have hc : (1 - V * Vᴴ) * (1 - V * Vᴴ) = 1 - V * Vᴴ := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul, hV]
    abel
  rw [isometricCompletedKraus, krausEffect_append, isometricLiftKraus_effect K J V hJ, hK,
    Matrix.mul_one, measurePrepareKraus_effect, hC, one_smul,
    isometry_range_complement_hermitian, hc]
  abel

theorem partialFrameCompletedKraus_action {d D : ℕ} (K : List (ComplexMatrix d))
    (J V : Matrix (Fin D) (Fin d) ℂ) (C Z : ComplexMatrix D)
    (hV : (V * Vᴴ) * (V * Vᴴ) = V * Vᴴ) :
    krausAction (isometricCompletedKraus K J V C) Z =
      J * krausAction K (Vᴴ * Z * V) * Jᴴ +
        Matrix.trace ((1 - V * Vᴴ) * Z) • (C * Cᴴ) := by
  have hc : (1 - V * Vᴴ) * (1 - V * Vᴴ) = 1 - V * Vᴴ := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul, hV]
    abel
  rw [isometricCompletedKraus, krausAction_append, isometricLiftKraus_action,
    measurePrepareKraus_action, isometry_range_complement_hermitian]
  congr 2
  rw [Matrix.trace_mul_cycle, hc]

/-- The residual term in the compressed branch has coefficient `Tr ((R - V Vᴴ)Z)`. -/
theorem partialFrameCompletedKraus_compressed_action {d D : ℕ}
    (K : List (ComplexMatrix d)) {J : Matrix (Fin D) (Fin d) ℂ}
    {R : ComplexMatrix D} {S : ComplexMatrix d} (f : SharpDilationChannelFrame J R S)
    (C Z : ComplexMatrix D) (hRh : Rᴴ = R) (hRR : R * R = R) :
    krausAction (isometricCompletedKraus K J f.frame C) (R * Z * R) =
      J * krausAction K (f.frameᴴ * Z * f.frame) * Jᴴ +
        Matrix.trace ((R - f.frame * f.frameᴴ) * Z) • (C * Cᴴ) := by
  let V := f.frame
  let Q := V * Vᴴ
  have hRV : R * V = V := f.projection_frame
  have hVR : Vᴴ * R = Vᴴ := by
    simpa only [Matrix.conjTranspose_mul, hRh] using congrArg Matrix.conjTranspose hRV
  have hRQ : R * Q = Q := by
    change R * (V * Vᴴ) = _
    rw [← Matrix.mul_assoc, hRV]
  have hQR : Q * R = Q := by
    change (V * Vᴴ) * R = _
    rw [Matrix.mul_assoc, hVR]
  have hc : Vᴴ * (R * Z * R) * V = Vᴴ * Z * V := by
    calc
      _ = (Vᴴ * R) * Z * (R * V) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hVR, hRV]
  have ht : Matrix.trace ((1 - Q) * (R * Z * R)) = Matrix.trace ((R - Q) * Z) := by
    have hsub : R * ((1 - Q) * R) = R - Q := by
      rw [Matrix.sub_mul, Matrix.one_mul, hQR, Matrix.mul_sub, hRR, hRQ]
    calc
      _ = Matrix.trace (((1 - Q) * R * Z) * R) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((R * ((1 - Q) * R)) * Z) := by
        rw [Matrix.trace_mul_comm ((1 - Q) * R * Z) R]
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hsub]
  rw [partialFrameCompletedKraus_action K J V C _ f.range_idempotent]
  change J * krausAction K (Vᴴ * (R * Z * R) * V) * Jᴴ +
      Matrix.trace ((1 - Q) * (R * Z * R)) • (C * Cᴴ) = _
  rw [hc, ht]

/-- The common first-corner inclusion, written so the algebra applies in any output dimension. -/
def sharpFrameEmbed {d D : ℕ} (J : Matrix (Fin D) (Fin d) ℂ) (Y : ComplexMatrix d) :
    ComplexMatrix D := J * Y * Jᴴ

theorem sharpFrameEmbed_trace {d D : ℕ} (J : Matrix (Fin D) (Fin d) ℂ)
    (hJ : Jᴴ * J = 1) (Y : ComplexMatrix d) :
    Matrix.trace (sharpFrameEmbed J Y) = Matrix.trace Y := by
  rw [sharpFrameEmbed, Matrix.trace_mul_cycle, hJ, Matrix.one_mul]

theorem sharpFrameEmbed_density {d D : ℕ} (J : Matrix (Fin D) (Fin d) ℂ)
    (hJ : Jᴴ * J = 1) {Y : ComplexMatrix d} (hY : IsMatrixDensity Y) :
    IsMatrixDensity (sharpFrameEmbed J Y) :=
  ⟨hY.1.mul_mul_conjTranspose_same _, (sharpFrameEmbed_trace J hJ Y).trans hY.2⟩

private theorem sharpFrameEmbed_conjTranspose {d D : ℕ} (J : Matrix (Fin D) (Fin d) ℂ)
    (Y : ComplexMatrix d) : (sharpFrameEmbed J Y)ᴴ = sharpFrameEmbed J Yᴴ := by
  simp only [sharpFrameEmbed, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]

private theorem sharpFrameEmbed_mul {d D : ℕ} (J : Matrix (Fin D) (Fin d) ℂ)
    (hJ : Jᴴ * J = 1) (X Y : ComplexMatrix d) :
    sharpFrameEmbed J X * sharpFrameEmbed J Y = sharpFrameEmbed J (X * Y) := by
  unfold sharpFrameEmbed
  calc
    _ = J * (X * (Jᴴ * J) * Y) * Jᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hJ, Matrix.mul_one]

private theorem sharpFrameEmbed_add_smul {d D : ℕ} (J : Matrix (Fin D) (Fin d) ℂ)
    (X Y : ComplexMatrix d) (c : ℂ) :
    sharpFrameEmbed J (X + c • Y) = sharpFrameEmbed J X + c • sharpFrameEmbed J Y := by
  simp [sharpFrameEmbed, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]

/-- Apply the published inner Kraus completion and then its rectangular channel lift. -/
def sharpFrameChannelKraus {d D : ℕ} (K : List (ComplexMatrix d))
    (s : FiniteSpectralSupport (krausEffect K)) {J : Matrix (Fin D) (Fin d) ℂ}
    {R : ComplexMatrix D} (f : SharpDilationChannelFrame J R s.root) (B : ComplexMatrix d) :
    List (ComplexMatrix D) :=
  isometricCompletedKraus (completedKraus K s B) J f.frame (sharpFrameEmbed J B)

theorem sharpFrameChannelKraus_effect {d D : ℕ} (K : List (ComplexMatrix d))
    (s : FiniteSpectralSupport (krausEffect K)) {J : Matrix (Fin D) (Fin d) ℂ}
    {R : ComplexMatrix D} (f : SharpDilationChannelFrame J R s.root) (B : ComplexMatrix d)
    (hJ : Jᴴ * J = 1) (hB : Matrix.trace (B * Bᴴ) = 1) :
    krausEffect (sharpFrameChannelKraus K s f B) = 1 := by
  have hC : Matrix.trace (sharpFrameEmbed J B * (sharpFrameEmbed J B)ᴴ) = 1 := by
    rw [sharpFrameEmbed_conjTranspose, sharpFrameEmbed_mul J hJ, sharpFrameEmbed_trace J hJ, hB]
  exact partialFrameCompletedKraus_effect _ J f.frame _ (completedKraus_effect K s B hB)
    hJ f.range_idempotent hC

/-- Every branch output is in the common first corner, including nonpositive inputs. -/
theorem sharpFrameChannelKraus_branch {d D : ℕ} (K : List (ComplexMatrix d))
    (s : FiniteSpectralSupport (krausEffect K)) {J : Matrix (Fin D) (Fin d) ℂ}
    {R : ComplexMatrix D} (f : SharpDilationChannelFrame J R s.root) (B : ComplexMatrix d)
    (hJ : Jᴴ * J = 1) (hRh : Rᴴ = R) (hRR : R * R = R) (Z : ComplexMatrix D) :
    krausAction (sharpFrameChannelKraus K s f B) (R * Z * R) =
      sharpFrameEmbed J (krausAction (completedKraus K s B) (f.frameᴴ * Z * f.frame) +
        Matrix.trace ((R - f.frame * f.frameᴴ) * Z) • (B * Bᴴ)) := by
  rw [sharpFrameChannelKraus, partialFrameCompletedKraus_compressed_action _ f _ _ hRh hRR,
    sharpFrameEmbed_conjTranspose, sharpFrameEmbed_mul J hJ, sharpFrameEmbed_add_smul]
  rfl

/-- Literal intertwining with the original branch on every input matrix. -/
theorem sharpFrameChannelKraus_intertwining {d D : ℕ} (K : List (ComplexMatrix d))
    (s : FiniteSpectralSupport (krausEffect K)) {J : Matrix (Fin D) (Fin d) ℂ}
    {R : ComplexMatrix D} (f : SharpDilationChannelFrame J R s.root) (B : ComplexMatrix d)
    (hJ : Jᴴ * J = 1) (hRh : Rᴴ = R) (hRR : R * R = R) (Y : ComplexMatrix d) :
    krausAction (sharpFrameChannelKraus K s f B) (R * sharpFrameEmbed J Y * R) =
      sharpFrameEmbed J (krausAction K Y) := by
  have hJv : Jᴴ * f.frame = s.root := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, s.root_hermitian] using
      congrArg Matrix.conjTranspose f.frame_inclusion
  have hinput : f.frameᴴ * sharpFrameEmbed J Y * f.frame = s.root * Y * s.root := by
    unfold sharpFrameEmbed
    calc
      _ = (f.frameᴴ * J) * Y * (Jᴴ * f.frame) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [f.frame_inclusion, hJv]
  have hres : (R - f.frame * f.frameᴴ) * sharpFrameEmbed J Y = 0 := by
    unfold sharpFrameEmbed
    calc
      _ = ((R - f.frame * f.frameᴴ) * J) * Y * Jᴴ := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [f.residual_annihilates_inclusion, Matrix.zero_mul, Matrix.zero_mul]
  rw [sharpFrameChannelKraus_branch K s f B hJ hRh hRR, hinput, hres,
    Matrix.trace_zero, zero_smul, add_zero, completedKraus_factorization]

/-- Compression of the chosen outcome projection recovers the original effect. -/
theorem sharpFrameChannelKraus_projection_compression {d D : ℕ} (K : List (ComplexMatrix d))
    (s : FiniteSpectralSupport (krausEffect K)) {J : Matrix (Fin D) (Fin d) ℂ}
    {R : ComplexMatrix D} (f : SharpDilationChannelFrame J R s.root) :
    Jᴴ * R * J = krausEffect K := by
  have hJv : Jᴴ * f.frame = s.root := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, s.root_hermitian] using
      congrArg Matrix.conjTranspose f.frame_inclusion
  rw [Matrix.mul_assoc, f.projection_inclusion, ← Matrix.mul_assoc, hJv, s.root_sq]

end AlbertSequential
