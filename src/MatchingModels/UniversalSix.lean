/- SPDX-License-Identifier: Apache-2.0 -/
module

public import MatchingModels.QuatPair
public import MatchingModels.UniversalSixAffinity
public import MatchingModels.MatrixClassIBridge

/-!
# Universal Six-Step Indistinguishability (`prop:cer:universalsix`)

Combines:
- `prop_cer_quatpair_c` (`MatchingModels.QuatPair`), producing two quaternionic-window
  atom quadruples `qPlus`, `qMinus` in `standardQuaternionicWindow` whose `λ`-convex mixture
  reproduces all 13 basic traces of `p` (`0 < λ < 1`);
- `nativeWordProbability_e3_affine_le_six` (`MatchingModels.UniversalSixAffinity`), showing that
  on every word of length `≤ 6` starting from `e/3`, the native octonionic probability of `p`
  equals `λ * Pr_{qPlus}(w | e/3) + (1 - λ) * Pr_{qMinus}(w | e/3)`;
- `c12BlockMixtureModel` and `quatProj6_wordProb_e3` (`MatchingModels.MatrixClassIBridge`),
  realizing that `λ`-convex combination explicitly as a `ℂ¹²` Class-(I) model with rank-`2`
  block projections `χ(qPlus_i) ⊕ χ(qMinus_i)` and state `λ (I_6 / 6) ⊕ (1 - λ) (I_6 / 6)`.

Deduces real-Hilbert, quaternionic, and algebraic Class-(I) matching models on words of length
`≤ 6`, as well as the absence of any Class-(I) linear equality or inequality violation
supported on words of length `≤ 6`.
-/

@[expose] public section

set_option autoImplicit false

namespace AlbertSequential.MatchingModels

open AlbertSequential

/-- Detailed witness form of `prop:cer:universalsix`: constructs an explicit `ℂ¹²` block
mixture model `(Pplus ⊕ Pminus, λ (I_6 / 6) ⊕ (1 - λ) (I_6 / 6))` with `0 < λ < 1`,
whose two `6 × 6` Hermitian idempotent blocks have trace `2` and realize the quaternionic-window
endpoint quadruples `qPlus`, `qMinus` from `prop_cer_quatpair_c`, matching
`nativeWordProbability p ((1 / 3 : ℝ) • albertUnit)` on all words of length `≤ 6`. -/
theorem prop_cer_universalsix_witness (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) :
    ∃ (lam : ℝ) (qPlus qMinus : Fin 4 → Albert)
      (Pplus Pminus : Fin 4 → Matrix (Fin 6) (Fin 6) ℂ)
      (M : HilbertProjectiveData (Fin 4) ℂ (EuclideanSpace ℂ (Fin 12))),
      0 < lam ∧ lam < 1 ∧
      (∀ i, IsAtom (qPlus i)) ∧
      (∀ i, qPlus i ∈ standardQuaternionicWindow.subalgebra.carrier) ∧
      (∀ i, IsAtom (qMinus i)) ∧
      (∀ i, qMinus i ∈ standardQuaternionicWindow.subalgebra.carrier) ∧
      (∀ i, (Pplus i).IsHermitian ∧ Pplus i * Pplus i = Pplus i ∧ Matrix.trace (Pplus i) = 2) ∧
      (∀ i, (Pminus i).IsHermitian ∧ Pminus i * Pminus i = Pminus i ∧ Matrix.trace (Pminus i) = 2) ∧
      (∀ w : Word (Fin 4),
        M.probability w =
          lam * nativeWordProbability qPlus ((1 / 3 : ℝ) • albertUnit) w +
          (1 - lam) * nativeWordProbability qMinus ((1 / 3 : ℝ) • albertUnit) w) ∧
      (∀ w : Word (Fin 4), w.length ≤ 6 →
        M.probability w = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w) := by
  obtain ⟨lam, qPlus, qMinus, hlam0, hlam1, hqp_atom, hqp_std, hqm_atom, hqm_std,
    hqp_o, hqm_o, hqp_R, hqm_R, ht1, ht2, ht3⟩ :=
    prop_cer_quatpair_c p hp hA
  let Pplus : Fin 4 → Matrix (Fin 6) (Fin 6) ℂ :=
    quatProj6 standardQuaternionicWindow qPlus hqp_std
  let Pminus : Fin 4 → Matrix (Fin 6) (Fin 6) ℂ :=
    quatProj6 standardQuaternionicWindow qMinus hqm_std
  have hPplus_herm : ∀ i, (Pplus i).IsHermitian := fun i =>
    quatProj6_hermitian standardQuaternionicWindow qPlus hqp_std i
  have hPplus_idem : ∀ i, Pplus i * Pplus i = Pplus i := fun i =>
    quatProj6_idempotent standardQuaternionicWindow qPlus hqp_std hqp_atom i
  have hPplus_tr : ∀ i, Matrix.trace (Pplus i) = 2 := fun i =>
    quatProj6_trace standardQuaternionicWindow qPlus hqp_std hqp_atom i
  have hPminus_herm : ∀ i, (Pminus i).IsHermitian := fun i =>
    quatProj6_hermitian standardQuaternionicWindow qMinus hqm_std i
  have hPminus_idem : ∀ i, Pminus i * Pminus i = Pminus i := fun i =>
    quatProj6_idempotent standardQuaternionicWindow qMinus hqm_std hqm_atom i
  have hPminus_tr : ∀ i, Matrix.trace (Pminus i) = 2 := fun i =>
    quatProj6_trace standardQuaternionicWindow qMinus hqm_std hqm_atom i
  have hlam_icc : lam ∈ Set.Icc (0 : ℝ) 1 := Set.mem_Icc.mpr ⟨hlam0.le, hlam1.le⟩
  let M : HilbertProjectiveData (Fin 4) ℂ (EuclideanSpace ℂ (Fin 12)) :=
    c12BlockMixtureModel Pplus Pminus hPplus_herm hPplus_idem hPminus_herm hPminus_idem
      lam hlam_icc
  have hprob_mix : ∀ w : Word (Fin 4),
      M.probability w =
        lam * nativeWordProbability qPlus ((1 / 3 : ℝ) • albertUnit) w +
        (1 - lam) * nativeWordProbability qMinus ((1 / 3 : ℝ) • albertUnit) w := by
    intro w
    dsimp only [M]
    rw [c12BlockMixtureModel_probability Pplus Pminus hPplus_herm hPplus_idem hPminus_herm hPminus_idem
        lam hlam_icc w,
      quatProj6_wordProb_e3 standardQuaternionicWindow qPlus hqp_std w,
      quatProj6_wordProb_e3 standardQuaternionicWindow qMinus hqm_std w]
  have ho_pair : ∀ i j, fpOverlap p i j = fpOverlap qPlus i j ∧
      fpOverlap p i j = fpOverlap qMinus i j := fun i j =>
    ⟨(hqp_o i j).symm, (hqm_o i j).symm⟩
  have hR_pair : ∀ i j k, fpTriangle p i j k = fpTriangle qPlus i j k ∧
      fpTriangle p i j k = fpTriangle qMinus i j k := fun i j k =>
    ⟨(hqp_R i j k).symm, (hqm_R i j k).symm⟩
  have hprob_match : ∀ w : Word (Fin 4), w.length ≤ 6 →
      M.probability w = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w := by
    intro w hw
    rw [hprob_mix w]
    exact (nativeWordProbability_e3_affine_le_six hp hqp_atom hqm_atom hA
      ho_pair hR_pair ht1 ht2 ht3 w hw).symm
  exact ⟨lam, qPlus, qMinus, Pplus, Pminus, M, hlam0, hlam1,
    hqp_atom, hqp_std, hqm_atom, hqm_std,
    fun i => ⟨hPplus_herm i, hPplus_idem i, hPplus_tr i⟩,
    fun i => ⟨hPminus_herm i, hPminus_idem i, hPminus_tr i⟩,
    hprob_mix, hprob_match⟩

/-- **`prop:cer:universalsix` (`ℂ¹²` form)**: for any four atoms `p` with
`0 < fourPointInvariant p`, there exists a `ℂ¹²` complex Hilbert projective model matching
`nativeWordProbability p ((1 / 3 : ℝ) • albertUnit)` on all words of length `≤ 6`. -/
theorem prop_cer_universalsix_c12 (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) :
    ∃ M : HilbertProjectiveData (Fin 4) ℂ (EuclideanSpace ℂ (Fin 12)),
      ∀ w : Word (Fin 4), w.length ≤ 6 →
        M.probability w = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w := by
  obtain ⟨_, _, _, _, _, M, _, _, _, _, _, _, _, _, _, hmatch⟩ :=
    prop_cer_universalsix_witness p hp hA
  exact ⟨M, hmatch⟩

/-- Real-Hilbert Class-(I) model matching `nativeWordProbability p ((1 / 3 : ℝ) • albertUnit)`
on all words of length `≤ 6`, obtained from the `ℂ¹²` witness via `hilbertComplexToReal`. -/
theorem prop_cer_universalsix_real (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (_ : CompleteSpace H)
      (M : HilbertProjectiveData (Fin 4) ℝ H),
      ∀ w : Word (Fin 4), w.length ≤ 6 →
        M.probability w = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w := by
  obtain ⟨MC, hMC⟩ := prop_cer_universalsix_c12 p hp hA
  refine ⟨_, _, _, _, hilbertComplexToReal MC, fun w hw => ?_⟩
  rw [hilbertComplexToReal_probability MC w]
  exact hMC w hw

/-- Quaternionic Class-(I) model matching `nativeWordProbability p ((1 / 3 : ℝ) • albertUnit)`
on all words of length `≤ 6`, obtained from the `ℂ¹²` witness via
`hilbertComplexToQuaternionic`. -/
theorem prop_cer_universalsix_quaternionic (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (_ : CompleteSpace H)
      (Q : QuaternionicOperatorStructure H) (M : QuaternionicProjectiveData (Fin 4) Q),
      ∀ w : Word (Fin 4), w.length ≤ 6 →
        M.state (M.wordEffect w) = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w := by
  obtain ⟨MC, hMC⟩ := prop_cer_universalsix_c12 p hp hA
  refine ⟨_, _, _, _, _, hilbertComplexToQuaternionic MC, fun w hw => ?_⟩
  rw [hilbertComplexToQuaternionic_state_wordEffect MC w]
  exact hMC w hw

/-- Algebraic Class-(I) model matching `nativeWordProbability p ((1 / 3 : ℝ) • albertUnit)`
on all words of length `≤ 6`. -/
theorem prop_cer_universalsix_algebraic (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) :
    ∃ (A : Type) (_ : Ring A) (_ : StarRing A) (_ : Module ℝ A)
      (_ : IsScalarTower ℝ A A) (_ : SMulCommClass ℝ A A) (_ : StarModule ℝ A)
      (M : AlgebraicProjectiveData (Fin 4) A),
      ∀ w : Word (Fin 4), w.length ≤ 6 →
        M.probability w = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w := by
  obtain ⟨MC, hMC⟩ := prop_cer_universalsix_c12 p hp hA
  refine ⟨_, _, _, _, _, _, _, MC.toAlgebraic, fun w hw => ?_⟩
  rw [MC.toAlgebraic_probability w]
  exact hMC w hw

/-- Evaluation of a finite real-linear combination of word probabilities. -/
def wordLinearEval (terms : List (ℝ × Word (Fin 4))) (prob : Word (Fin 4) → ℝ) : ℝ :=
  (terms.map (fun t => t.1 * prob t.2)).sum

private theorem wordLinearEval_congr_le_six (terms : List (ℝ × Word (Fin 4)))
    (hterms : ∀ t ∈ terms, t.2.length ≤ 6)
    {prob1 prob2 : Word (Fin 4) → ℝ}
    (hagree : ∀ w : Word (Fin 4), w.length ≤ 6 → prob1 w = prob2 w) :
    wordLinearEval terms prob1 = wordLinearEval terms prob2 := by
  unfold wordLinearEval
  congr 1
  refine List.map_congr_left fun t ht => ?_
  rw [hagree t.2 (hterms t ht)]

/-- No Class-(I) linear equality supported on words of length `≤ 6` is violated by
`nativeWordProbability p ((1 / 3 : ℝ) • albertUnit)`. -/
theorem no_classI_linearEq_le_six (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) (terms : List (ℝ × Word (Fin 4)))
    (hterms : ∀ t ∈ terms, t.2.length ≤ 6) (rhs : ℝ)
    (hvalid : ∀ M : HilbertProjectiveData (Fin 4) ℂ (EuclideanSpace ℂ (Fin 12)),
      wordLinearEval terms M.probability = rhs) :
    wordLinearEval terms (nativeWordProbability p ((1 / 3 : ℝ) • albertUnit)) = rhs := by
  obtain ⟨M, hmatch⟩ := prop_cer_universalsix_c12 p hp hA
  rw [← wordLinearEval_congr_le_six terms hterms hmatch]
  exact hvalid M

/-- No Class-(I) linear inequality supported on words of length `≤ 6` is violated by
`nativeWordProbability p ((1 / 3 : ℝ) • albertUnit)`. -/
theorem no_classI_linearIneq_le_six (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) (terms : List (ℝ × Word (Fin 4)))
    (hterms : ∀ t ∈ terms, t.2.length ≤ 6) (rhs : ℝ)
    (hvalid : ∀ M : HilbertProjectiveData (Fin 4) ℂ (EuclideanSpace ℂ (Fin 12)),
      wordLinearEval terms M.probability ≤ rhs) :
    wordLinearEval terms (nativeWordProbability p ((1 / 3 : ℝ) • albertUnit)) ≤ rhs := by
  obtain ⟨M, hmatch⟩ := prop_cer_universalsix_c12 p hp hA
  rw [← wordLinearEval_congr_le_six terms hterms hmatch]
  exact hvalid M

/-- Universal Class-(I) formulation of `no_classI_linearEq_le_six`: any linear equality
supported on words of length `≤ 6` valid in every complex Hilbert projective model also holds
for `nativeWordProbability p ((1 / 3 : ℝ) • albertUnit)`. -/
theorem no_classI_universalLinearEq_le_six (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) (terms : List (ℝ × Word (Fin 4)))
    (hterms : ∀ t ∈ terms, t.2.length ≤ 6) (rhs : ℝ)
    (hvalid : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (M : HilbertProjectiveData (Fin 4) ℂ H),
      wordLinearEval terms M.probability = rhs) :
    wordLinearEval terms (nativeWordProbability p ((1 / 3 : ℝ) • albertUnit)) = rhs :=
  no_classI_linearEq_le_six p hp hA terms hterms rhs (fun M => hvalid _ M)

end AlbertSequential.MatchingModels
