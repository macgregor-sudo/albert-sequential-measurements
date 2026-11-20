/- SPDX-License-Identifier: Apache-2.0 -/
module
public import RepeatableBinaryDilation
public import ChoiCompletePositivity
import DegenerateSharpDilation
import RectangularKrausFamilies
import BlockB.ElevenSupport

@[expose] public section
noncomputable section
namespace AlbertSequential
open Matrix
open scoped ComplexOrder

/-- The unnormalized matrix reached at every finite history. -/
def binaryKrausState {d : ℕ} {X : Type*} (r : BinaryKrausRealization d X) (w : Word X) :
    ComplexMatrix d :=
  w.foldl (fun Y a => krausAction (r.kraus a.1 a.2) Y) r.initial

private theorem binaryKrausState_append {d : ℕ} {X : Type*} (r : BinaryKrausRealization d X)
    (w : Word X) (i : X) (b : Bool) :
    binaryKrausState r (w ++ [(i,b)]) = krausAction (r.kraus i b) (binaryKrausState r w) := by
  simp [binaryKrausState, List.foldl_append]

private theorem binaryKrausState_positive {d : ℕ} {X : Type*}
    (r : BinaryKrausRealization d X) (w : Word X) : (binaryKrausState r w).PosSemidef := by
  induction w using List.reverseRecOn with
  | nil => exact r.density.1
  | append_singleton w a ih =>
    rcases a with ⟨i,b⟩
    rw [binaryKrausState_append]
    exact krausAction_positive _ ih

private theorem zeroTrace_supported {d : ℕ} {A Y : ComplexMatrix d}
    (s : FiniteSpectralSupport A) (hY : Y.PosSemidef) (hz : trace (A * Y) = 0) :
    (1 - s.support) * Y = Y := by
  obtain ⟨D, hD⟩ := exists_complexPositiveFactor hY
  have ht : trace ((s.root * D)ᴴ * (s.root * D)) = trace (A * Y) := by
    rw [Matrix.conjTranspose_mul, s.root_hermitian, Matrix.mul_assoc Dᴴ, Matrix.trace_mul_comm Dᴴ, hD]
    conv_rhs => rw [← s.root_sq]
    simp only [Matrix.mul_assoc]
  have h0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp (ht.trans hz)
  have hy0 : s.root * Y = 0 := by rw [hD, ← Matrix.mul_assoc, h0, Matrix.zero_mul]
  rw [Matrix.sub_mul, Matrix.one_mul, ← s.inverse_root, Matrix.mul_assoc, hy0,
    Matrix.mul_zero, sub_zero]

private theorem exists_supported_reset {d : ℕ} (P : ComplexMatrix d)
    (hPP : P * P = P) (hP : P ≠ 0) :
    ∃ B : ComplexMatrix d, trace (B * Bᴴ) = 1 ∧ P * (B * Bᴴ) = B * Bᴴ ∧
      ∃ u : Fin d → ℂ, B * Bᴴ = vecMulVec u (star u) := by
  classical
  have hn : ∃ i j, P i j ≠ 0 := by
    by_contra! hn
    exact hP (Matrix.ext fun i j => hn i j)
  obtain ⟨i,j,hij⟩ := hn
  let v := P *ᵥ (Pi.single j 1)
  have hvi : v i ≠ 0 := by
    simpa only [v, Matrix.mulVec_single_one, Matrix.col, Matrix.transpose_apply] using hij
  have hPv : P *ᵥ v = v := by
    rw [show v = P *ᵥ Pi.single j 1 from rfl, Matrix.mulVec_mulVec, hPP]
  let R := vecMulVec v (star v)
  have hR : R.PosSemidef := Matrix.posSemidef_vecMulVec_self_star v
  have hR0 : R ≠ 0 := by
    intro h
    have hd := congrArg (fun M : ComplexMatrix d => M i i) h
    change v i * star (v i) = 0 at hd
    exact (mul_ne_zero hvi (by simpa using hvi)) hd
  have htr := (Complex.nonneg_iff.mp hR.trace_nonneg)
  let a := (trace R).re
  have ha : 0 < a := by
    refine lt_of_le_of_ne htr.1 ?_
    intro he
    apply hR0
    exact (positive_trace_zero_iff hR).mp (Complex.ext he.symm (by simpa using htr.2.symm))
  let c := (Real.sqrt a)⁻¹
  let u : Fin d → ℂ := c • v
  let τ := vecMulVec u (star u)
  have hc : c * c = a⁻¹ := by
    dsimp only [c]
    rw [← mul_inv, Real.mul_self_sqrt ha.le]
  have hτeq : τ = a⁻¹ • R := by
    change vecMulVec (c • v) (star (c • v)) = _
    rw [star_smul, star_trivial, vecMulVec_smul, smul_vecMulVec, smul_smul, hc]
  have hτtr : trace τ = 1 := by
    rw [hτeq, Matrix.trace_smul, show trace R = (a : ℂ) from
      Complex.ext rfl (by simpa using htr.2.symm), Complex.real_smul, ← Complex.ofReal_mul,
      inv_mul_cancel₀ ha.ne', Complex.ofReal_one]
  have hPτ : P * τ = τ := by
    simp only [τ, u, Matrix.mul_vecMulVec, Matrix.mulVec_smul, hPv]
  obtain ⟨B,hB⟩ := exists_complexPositiveFactor (Matrix.posSemidef_vecMulVec_self_star u)
  change τ = B * Bᴴ at hB
  exact ⟨B, hB ▸ hτtr, hB ▸ hPτ, u, hB.symm⟩

private def supportResetKraus {d : ℕ} (P B : ComplexMatrix d) : List (ComplexMatrix d) :=
  [P] ++ measurePrepareKraus B (1 - P)

private theorem complement_projection {d : ℕ} {P : ComplexMatrix d} (hPP : P*P=P) :
    (1-P)*(1-P) = 1-P := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPP]
  abel

private theorem supportReset_effect {d : ℕ} {P B : ComplexMatrix d}
    (hPh : Pᴴ = P) (hPP : P*P=P) (htr : trace (B*Bᴴ)=1) :
    krausEffect (supportResetKraus P B) = 1 := by
  rw [supportResetKraus, krausEffect_append, measurePrepareKraus_effect, htr, one_smul,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPh, complement_projection hPP]
  simp [krausEffect, hPh, hPP]

private theorem supportReset_action {d : ℕ} {P B : ComplexMatrix d}
    (hPh : Pᴴ = P) (hPP : P*P=P) (Y : ComplexMatrix d) :
    krausAction (supportResetKraus P B) Y = P * Y * P + trace ((1-P)*Y) • (B*Bᴴ) := by
  rw [supportResetKraus, krausAction_append, measurePrepareKraus_action,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPh, Matrix.trace_mul_cycle,
    complement_projection hPP]
  simp [krausAction, hPh]

private def postcomposeKraus {d : ℕ} (L K : List (ComplexMatrix d)) : List (ComplexMatrix d) :=
  K.flatMap fun V => L.map (fun W => W * V)

private theorem postcomposeKraus_action {d : ℕ} (L K : List (ComplexMatrix d)) (Y : ComplexMatrix d) :
    krausAction (postcomposeKraus L K) Y = krausAction L (krausAction K Y) := by
  induction K with
  | nil => symm; exact krausAction_zero_input L
  | cons V K ih =>
    change krausAction (L.map (· * V) ++ postcomposeKraus L K) Y =
      krausAction L (V*Y*Vᴴ + krausAction K Y)
    rw [krausAction_append, krausAction_right_multiply, ih]
    exact (rectangularKrausAction_add L _ _).symm

private theorem postcomposeKraus_effect {d : ℕ} (L K : List (ComplexMatrix d))
    (hL : krausEffect L = 1) : krausEffect (postcomposeKraus L K) = krausEffect K := by
  induction K with
  | nil => rfl
  | cons V K ih =>
    change krausEffect (L.map (· * V) ++ postcomposeKraus L K) = Vᴴ * V + krausEffect K
    rw [krausEffect_append, krausEffect_right_multiply, hL, Matrix.mul_one, ih]

/-- A branch is absent at every history, including the empty history. -/
def UnobservedBinaryOutcome {d : ℕ} {X : Type*} (r : BinaryKrausRealization d X)
    (i : X) (b : Bool) : Prop :=
  ∀ w, binaryKrausProbability r (w ++ [(i,b)]) = 0

theorem binaryKraus_not_both_unobserved {d : ℕ} {X : Type*} (r : BinaryKrausRealization d X)
    (i : X) : ¬ (UnobservedBinaryOutcome r i true ∧ UnobservedBinaryOutcome r i false) := by
  rintro ⟨hy, hn⟩
  have h : binaryKrausProbability r [(i,true)] + binaryKrausProbability r [(i,false)] = 1 := by
    change (trace (krausAction (r.kraus i true) r.initial)).re +
      (trace (krausAction (r.kraus i false) r.initial)).re = 1
    rw [← Complex.add_re, trace_krausAction, trace_krausAction, ← Matrix.trace_add,
      ← Matrix.add_mul, r.normalized i, Matrix.one_mul, r.density.2, Complex.one_re]
  have hy0 : binaryKrausProbability r [(i,true)] = 0 := hy []
  have hn0 : binaryKrausProbability r [(i,false)] = 0 := hn []
  rw [hy0, hn0, add_zero] at h
  exact zero_ne_one h

private structure RepairedTest {d : ℕ} {X : Type*} (r : BinaryKrausRealization d X) (i : X) where
  kraus : Bool → List (ComplexMatrix d)
  normalized : krausEffect (kraus true) + krausEffect (kraus false) = 1
  supported : ∀ b Y, krausEffect (kraus b) * krausAction (kraus b) Y = krausAction (kraus b) Y
  agreement : ∀ w b, krausAction (kraus b) (binaryKrausState r w) =
    krausAction (r.kraus i b) (binaryKrausState r w)
  effect : krausEffect (kraus true) = krausEffect (r.kraus i true) ∨
    (krausEffect (kraus true) = 0 ∧ UnobservedBinaryOutcome r i true) ∨
    (krausEffect (kraus true) = 1 ∧ UnobservedBinaryOutcome r i false)

private theorem zero_branch_unobserved {d : ℕ} {X : Type*} (r : BinaryKrausRealization d X)
    (i : X) (b : Bool) (h : ∀ w, krausAction (r.kraus i b) (binaryKrausState r w) = 0) :
    UnobservedBinaryOutcome r i b := by
  intro w
  change (trace (binaryKrausState r (w ++ [(i,b)]))).re = 0
  rw [binaryKrausState_append, h, Matrix.trace_zero]
  rfl

private def deterministicRepair {d : ℕ} {X : Type*} (r : BinaryKrausRealization d X)
    (i : X) (b : Bool)
    (h : ∀ w, krausAction (r.kraus i (!b)) (binaryKrausState r w) = 0) : RepairedTest r i := by
  let K : Bool → List (ComplexMatrix d) := fun c =>
    if c = b then r.kraus i true ++ r.kraus i false else []
  have he (c : Bool) : krausEffect (K c) = if c = b then 1 else 0 := by
    by_cases hc : c = b
    · simp only [K, hc, ite_true, krausEffect_append, r.normalized]
    · simp [K, hc, krausEffect]
  have hnorm : krausEffect (K true) + krausEffect (K false) = 1 := by
    rw [he, he]
    cases b <;> simp
  refine ⟨K, hnorm, ?_, ?_, ?_⟩
  · intro c Y
    by_cases hc : c = b
    · simp [he, hc]
    · simp [K, hc, krausAction]
  · intro w c
    have hnil (Y : ComplexMatrix d) : krausAction [] Y = 0 := rfl
    cases b
    · have hz : krausAction (r.kraus i true) (binaryKrausState r w) = 0 := h w
      cases c <;> simp [K, krausAction_append, hnil, hz]
    · have hz : krausAction (r.kraus i false) (binaryKrausState r w) = 0 := h w
      cases c <;> simp [K, krausAction_append, hnil, hz]
  · cases b
    · exact Or.inr (Or.inl ⟨by simp [he], zero_branch_unobserved r i true h⟩)
    · exact Or.inr (Or.inr ⟨by simp [he], zero_branch_unobserved r i false h⟩)

private theorem repairedTest_exists {d : ℕ} {X : Type*} (r : BinaryKrausRealization d X)
    (i : X) (h : ∀ w b, binaryKrausProbability r (w ++ [(i,b),(i,!b)]) = 0) :
    Nonempty (RepairedTest r i) := by
  let A (b : Bool) := krausEffect (r.kraus i b)
  let s (b : Bool) := finiteSpectralSupport (krausEffect_positive (r.kraus i (!b)))
  let P (b : Bool) := 1 - (s b).support
  have hPh (b : Bool) : (P b)ᴴ = P b := support_complement_hermitian (s b)
  have hPP (b : Bool) : P b * P b = P b := support_complement_idempotent (s b)
  have hAP (b : Bool) : A b * P b = P b := by
    have hsum : A b + A (!b) = 1 := by
      cases b
      · exact (add_comm _ _).trans (r.normalized i)
      · exact r.normalized i
    have he := congrArg (fun E : ComplexMatrix d => E * P b) hsum
    rwa [Matrix.add_mul, (s b).effect_complement, add_zero, Matrix.one_mul] at he
  have hr (w : Word X) (b : Bool) :
      P b * krausAction (r.kraus i b) (binaryKrausState r w) =
        krausAction (r.kraus i b) (binaryKrausState r w) := by
    let Y := krausAction (r.kraus i b) (binaryKrausState r w)
    let Z := krausAction (r.kraus i (!b)) Y
    have hY : Y.PosSemidef := krausAction_positive _ (binaryKrausState_positive r w)
    have hZ : Z.PosSemidef := krausAction_positive _ hY
    have ht := h w b
    change (trace (binaryKrausState r (w ++ [(i,b),(i,!b)]))).re = 0 at ht
    rw [show w ++ [(i,b),(i,!b)] = (w ++ [(i,b)]) ++ [(i,!b)] by simp,
      binaryKrausState_append, binaryKrausState_append] at ht
    have ht0 : trace Z = 0 := Complex.ext ht (by
      simpa using (Complex.nonneg_iff.mp hZ.trace_nonneg).2.symm)
    have hz : trace (A (!b) * Y) = 0 := (trace_krausAction _ Y).symm.trans ht0
    exact zeroTrace_supported (s b) hY hz
  have hdead (b : Bool) (hb : P b = 0) (w : Word X) :
      krausAction (r.kraus i b) (binaryKrausState r w) = 0 := by
    simpa [hb] using (hr w b).symm
  by_cases hyes : P true = 0
  · exact ⟨deterministicRepair r i false (hdead true hyes)⟩
  by_cases hno : P false = 0
  · exact ⟨deterministicRepair r i true (hdead false hno)⟩
  have hPN (b : Bool) : P b ≠ 0 := by cases b <;> assumption
  have hh (b : Bool) := exists_supported_reset (P b) (hPP b) (hPN b)
  choose B hB using hh
  let L (b : Bool) := supportResetKraus (P b) (B b)
  let K (b : Bool) := postcomposeKraus (L b) (r.kraus i b)
  have hL (b : Bool) : krausEffect (L b) = 1 := supportReset_effect (hPh b) (hPP b) (hB b).1
  have hK (b : Bool) : krausEffect (K b) = A b := postcomposeKraus_effect _ _ (hL b)
  have hLP (b : Bool) (Y : ComplexMatrix d) :
      P b * krausAction (L b) Y = krausAction (L b) Y := by
    rw [supportReset_action (hPh b) (hPP b), Matrix.mul_add, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, hPP b, Matrix.mul_smul, (hB b).2.1]
  refine ⟨⟨K, by rw [hK, hK]; exact r.normalized i, ?_, ?_, Or.inl (hK true)⟩⟩
  · intro b Y
    rw [hK, postcomposeKraus_action]
    conv_lhs => rw [← hLP b (krausAction (r.kraus i b) Y), ← Matrix.mul_assoc, hAP]
    exact hLP _ _
  · intro w b
    change krausAction (postcomposeKraus (L b) (r.kraus i b)) (binaryKrausState r w) = _
    rw [postcomposeKraus_action, supportReset_action (hPh b) (hPP b)]
    let Y := krausAction (r.kraus i b) (binaryKrausState r w)
    have hY : Y.PosSemidef := krausAction_positive _ (binaryKrausState_positive r w)
    have hl : P b * Y = Y := hr w b
    have hr' : Y * P b = Y := by
      simpa only [Matrix.conjTranspose_mul, hY.isHermitian.eq, hPh] using
        congrArg Matrix.conjTranspose hl
    change P b * Y * P b + trace ((1 - P b) * Y) • (B b * (B b)ᴴ) = Y
    rw [hl, hr', Matrix.sub_mul, Matrix.one_mul, hl, sub_self, Matrix.trace_zero, zero_smul, add_zero]

/-- The same-dimensional CP repair preserves every reachable matrix and is repeatable
on every positive input. The original effect changes only for a universally absent outcome. -/
theorem binaryKraus_repeatability_repair {d : ℕ} {X : Type*} (r : BinaryKrausRealization d X)
    (h : ∀ w i b, binaryKrausProbability r (w ++ [(i,b),(i,!b)]) = 0) :
    ∃ t : BinaryKrausRealization d X,
      t.initial = r.initial ∧
      (∀ w, binaryKrausState t w = binaryKrausState r w) ∧
      (∀ w, binaryKrausProbability t w = binaryKrausProbability r w) ∧
      (∀ i b, IsCompletelyPositiveMatrixMap (krausAction (t.kraus i b))) ∧
      HasCertaintySupportedOutputs t ∧
      (∀ i b Y, Y.PosSemidef →
        krausAction (t.kraus i (!b)) (krausAction (t.kraus i b) Y) = 0) ∧
      (∀ i, krausEffect (t.kraus i true) = krausEffect (r.kraus i true) ∨
        (krausEffect (t.kraus i true) = 0 ∧ UnobservedBinaryOutcome r i true) ∨
        (krausEffect (t.kraus i true) = 1 ∧ UnobservedBinaryOutcome r i false)) := by
  classical
  let R (i : X) := Classical.choice (repairedTest_exists r i (fun w b => h w i b))
  let t : BinaryKrausRealization d X := ⟨r.initial, r.density, fun i => (R i).kraus,
    fun i => (R i).normalized⟩
  have hs (w : Word X) : binaryKrausState t w = binaryKrausState r w := by
    induction w using List.reverseRecOn with
    | nil => rfl
    | append_singleton w a ih =>
      rcases a with ⟨i,b⟩
      rw [binaryKrausState_append, binaryKrausState_append, ih]
      exact (R i).agreement w b
  have ht (i : X) (b : Bool) (Y : ComplexMatrix d) :
      krausEffect (t.kraus i (!b)) * krausAction (t.kraus i b) Y = 0 := by
    let Z := krausAction (t.kraus i b) Y
    have hn : krausEffect (t.kraus i (!b)) + krausEffect (t.kraus i b) = 1 := by
      cases b
      · exact t.normalized i
      · exact (add_comm _ _).trans (t.normalized i)
    have he := congrArg (fun A : ComplexMatrix d => A * Z) hn
    have hZ : krausEffect (t.kraus i b) * Z = Z := (R i).supported b Y
    rw [Matrix.add_mul, hZ, Matrix.one_mul, add_eq_right] at he
    exact he
  refine ⟨t, rfl, hs, fun w => congrArg (fun Y : ComplexMatrix d => (trace Y).re) (hs w),
    fun i b => krausAction_completelyPositive (t.kraus i b),
    fun i Y _ => ⟨(R i).supported true Y, ht i false Y⟩, ?_, fun i => (R i).effect⟩
  intro i b Y hY
  apply (positive_trace_zero_iff (krausAction_positive _
    (krausAction_positive _ hY))).mp
  rw [trace_krausAction, ht, Matrix.trace_zero]

/-- The opposite-outcome hypothesis holds for every finite model of a native
ideal-test table, by the product-zero identity for complementary idempotents. -/
theorem binaryKraus_noSwitch_of_native {d : ℕ} {X : Type*}
    (r : BinaryKrausRealization d X) (p : X → Albert) (ρ : Albert)
    (hp : ∀ i, jordanMul (p i) (p i) = p i)
    (hmatch : ∀ w, binaryKrausProbability r w = nativeWordProbability p ρ w) :
    ∀ w i b, binaryKrausProbability r (w ++ [(i,b),(i,!b)]) = 0 := by
  intro w i b
  rw [hmatch]
  unfold nativeWordProbability nativeBranchState
  rw [List.foldl_append]
  change albertTrace (quadraticMap (nativeOutcome p (i,!b))
    (quadraticMap (nativeOutcome p (i,b)) (nativeBranchState p ρ w))) = 0
  have hne : (!b) ≠ b := by cases b <;> decide
  rw [BlockB.quadraticMap_nativeOutcome_opposite p hp i _ _ hne]
  change (∑ _ : Fin 3, (0 : ℝ)) = 0
  simp

#print axioms binaryKraus_repeatability_repair
#print axioms binaryKraus_noSwitch_of_native
#print axioms binaryKraus_not_both_unobserved

end AlbertSequential
