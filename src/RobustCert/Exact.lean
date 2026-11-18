/- SPDX-License-Identifier: Apache-2.0 -/
module

public import LengthSeven.LemmaA.Main

/-! # Exact certificates at `M` and `S` (thm:cer:seven(a), abstract `WalkForm` level)

The certificate vectors of thm:cer:seven(a) are written in the basis of the 28 path vectors
`[word28 i]` of lem:cer:gram28.  The paper's vectors `Φ = Σ_s sgn(s)(c_C η^C_s + c_R η^R_s + c_H η^H_s)`
use all six `η^C_s` and `η^R_s`, of which `W_28` contains three each; the other three are
eliminated by lem:cer:gram7(a) (`η^C_{xyz} + η^C_{zyx} = 2ω_y ξ`, `η^R_{xyz} + η^R_{xzy} = 2R_{xyz} a_x`),
with the trace values of the configuration substituted.  The coefficient lists below are those
vectors (Lean checks the norms):

* `certM`  = `4κ_C + 10κ_R − 9κ_H` at `M` (the paper's vector), `‖·‖² = −4/27`;
* `certM1` = `2κ_C + 6κ_R − 5κ_H` at `M` (a second certificate vector), `‖·‖² = −4/243`;
* `certS`  = `Φ_S` at `S`, `‖·‖² = −2/729`.

Index map (`word28`): `0 = ξ`; `7, 14, 21 = a_B, a_C, a_D`; `η^H`: `26 = BCD, 18 = BDC, 25 = CBD,
12 = CDB, 19 = DBC, 11 = DCB`; `η^C`: `4 = DCB, 5 = CDB, 6 = DBC`; `η^R`: `13 = BDC, 20 = CBD, 27 = DCB`.

The squared norm is evaluated from Lemma A (`lemmaA`) by exact rational evaluation of the table
polynomials (`polyEvalQ`, cast lemma `polyEval_cast`) and a kernel `decide` on the rational value.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.LengthSeven.Cert

open AlbertSequential AlbertSequential.LengthSeven AlbertSequential.LengthSeven.LemmaA

/-! ## Rational evaluation of table polynomials -/

/-- Rational value of a monomial. -/
def monoEvalQ : List ℚ → List ℕ → ℚ
  | [], _ => 1
  | _ :: _, [] => 1
  | v :: vs, e :: es => v ^ e * monoEvalQ vs es

/-- Rational value of a trace polynomial. -/
def polyEvalQ (v : List ℚ) : TracePoly → ℚ
  | [] => 0
  | m :: p => (m.1 : ℚ) * monoEvalQ v m.2 + polyEvalQ v p

theorem cast_pow_q (a : ℚ) (k : ℕ) : ((a ^ k : ℚ) : ℝ) = (a : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, Rat.cast_mul, ih]

theorem monoEval_cast (v : List ℚ) (e : List ℕ) :
    monoEval (v.map (fun q : ℚ => (q : ℝ))) e = (monoEvalQ v e : ℝ) := by
  induction v generalizing e with
  | nil => simp [monoEval, monoEvalQ]
  | cons a vs ih =>
    cases e with
    | nil => simp [monoEval, monoEvalQ]
    | cons k es => rw [List.map_cons, monoEval, monoEvalQ, ih, Rat.cast_mul, cast_pow_q]

theorem polyEval_cast (τ : TraceData) (v : List ℚ)
    (hv : traceVars τ = v.map (fun q : ℚ => (q : ℝ))) (p : TracePoly) :
    p.eval τ = (polyEvalQ v p : ℝ) := by
  induction p with
  | nil => simp [TracePoly.eval, polyEvalQ]
  | cons m p ih => simp [TracePoly.eval, polyEvalQ, ih, hv, monoEval_cast]

/-! ## Combinations of the 28 path vectors -/

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- `Σ c • [word28 i]` for a list of (index, rational coefficient). -/
def combo (W : WalkForm V) (cs : List (Fin 28 × ℚ)) : V :=
  (cs.map fun p => (p.2 : ℝ) • W.pathVec (word28 p.1)).sum

/-- The rational quadratic form `Σ_{p,q} c_p c_q G_{pq}(v)`. -/
def qform (v : List ℚ) (cs : List (Fin 28 × ℚ)) : ℚ :=
  (cs.map fun p => (cs.map fun q => p.2 * q.2 * polyEvalQ v (gramPoly p.1 q.1)).sum).sum

/-- Hypothesis shape: the 28 × 28 Gram entries are the table polynomials (Lemma A's conclusion). -/
def GramIs (W : WalkForm V) (τ : TraceData) : Prop :=
  ∀ i j : Fin 28, W.form (W.pathVec (word28 i)) (W.pathVec (word28 j)) = gram28 τ i j

theorem form_vec_combo {W : WalkForm V} {τ : TraceData} (hG : GramIs W τ) (v : List ℚ)
    (hv : traceVars τ = v.map (fun q : ℚ => (q : ℝ))) (i : Fin 28) (l : List (Fin 28 × ℚ)) :
    W.form (W.pathVec (word28 i)) (combo W l) =
      ((l.map fun q => q.2 * polyEvalQ v (gramPoly i q.1)).sum : ℚ) := by
  induction l with
  | nil => simp [combo]
  | cons q l ih =>
    simp only [combo, List.map_cons, List.sum_cons, map_add, map_smul, smul_eq_mul] at ih ⊢
    rw [ih, hG, gram28, polyEval_cast τ v hv]
    push_cast
    ring

theorem form_combo_combo {W : WalkForm V} {τ : TraceData} (hG : GramIs W τ) (v : List ℚ)
    (hv : traceVars τ = v.map (fun q : ℚ => (q : ℝ))) (l1 l2 : List (Fin 28 × ℚ)) :
    W.form (combo W l1) (combo W l2) =
      ((l1.map fun p => (l2.map fun q => p.2 * q.2 * polyEvalQ v (gramPoly p.1 q.1)).sum).sum
        : ℚ) := by
  induction l1 with
  | nil => simp [combo]
  | cons p l1 ih =>
    simp only [combo, List.map_cons, List.sum_cons, map_add, map_smul, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul] at ih ⊢
    have hv2 := form_vec_combo hG v hv p.1 l2
    simp only [combo] at hv2
    rw [ih, hv2]
    have hmul : ∀ l : List (Fin 28 × ℚ),
        ((l.map fun q => p.2 * q.2 * polyEvalQ v (gramPoly p.1 q.1)).sum : ℚ) =
          p.2 * (l.map fun q => q.2 * polyEvalQ v (gramPoly p.1 q.1)).sum := by
      intro l
      induction l with
      | nil => simp
      | cons q l ihl => simp only [List.map_cons, List.sum_cons, ihl]; ring
    rw [hmul]
    push_cast
    ring

theorem form_combo {W : WalkForm V} {τ : TraceData} (hG : GramIs W τ) (v : List ℚ)
    (hv : traceVars τ = v.map (fun q : ℚ => (q : ℝ))) (cs : List (Fin 28 × ℚ)) :
    W.form (combo W cs) (combo W cs) = (qform v cs : ℝ) :=
  form_combo_combo hG v hv cs cs

/-! ## The trace values of `M` and `S` (order of `traceVars`:
`o_AB o_AC o_AD o_BC o_BD o_CD R_ABC R_ABD R_ACD R_BCD ω_B ω_C ω_D`) -/

/-- `M`: `o = 1/3`, `R = 1/9`, `ω = 1/27`. -/
def traceValsM : List ℚ :=
  [1/3, 1/3, 1/3, 1/3, 1/3, 1/3, 1/9, 1/9, 1/9, 1/9, 1/27, 1/27, 1/27]

/-- `S`: `o_AB = 1/2`, other `o = 1/3`; `R_ABC = R_ABD = 1/6`, `R_ACD = R_BCD = 1/9`; `ω = 1/18`. -/
def traceValsS : List ℚ :=
  [1/2, 1/3, 1/3, 1/3, 1/3, 1/3, 1/6, 1/6, 1/9, 1/9, 1/18, 1/18, 1/18]

/-- `τ` carries the thirteen traces of `M`. -/
def IsTracesM (τ : TraceData) : Prop := traceVars τ = traceValsM.map (fun q : ℚ => (q : ℝ))

/-- `τ` carries the thirteen traces of `S`. -/
def IsTracesS (τ : TraceData) : Prop := traceVars τ = traceValsS.map (fun q : ℚ => (q : ℝ))

theorem isTracesM_of {τ : TraceData}
    (hAB : τ.o 0 1 = 1/3) (hAC : τ.o 0 2 = 1/3) (hAD : τ.o 0 3 = 1/3) (hBC : τ.o 1 2 = 1/3)
    (hBD : τ.o 1 3 = 1/3) (hCD : τ.o 2 3 = 1/3) (hABC : τ.R 0 1 2 = 1/9) (hABD : τ.R 0 1 3 = 1/9)
    (hACD : τ.R 0 2 3 = 1/9) (hBCD : τ.R 1 2 3 = 1/9) (hB : τ.om 1 = 1/27) (hC : τ.om 2 = 1/27)
    (hD : τ.om 3 = 1/27) : IsTracesM τ := by
  simp only [IsTracesM, traceVars, traceValsM, hAB, hAC, hAD, hBC, hBD, hCD, hABC, hABD, hACD,
    hBCD, hB, hC, hD, List.map_cons, List.map_nil]
  norm_num

theorem isTracesS_of {τ : TraceData}
    (hAB : τ.o 0 1 = 1/2) (hAC : τ.o 0 2 = 1/3) (hAD : τ.o 0 3 = 1/3) (hBC : τ.o 1 2 = 1/3)
    (hBD : τ.o 1 3 = 1/3) (hCD : τ.o 2 3 = 1/3) (hABC : τ.R 0 1 2 = 1/6) (hABD : τ.R 0 1 3 = 1/6)
    (hACD : τ.R 0 2 3 = 1/9) (hBCD : τ.R 1 2 3 = 1/9) (hB : τ.om 1 = 1/18) (hC : τ.om 2 = 1/18)
    (hD : τ.om 3 = 1/18) : IsTracesS τ := by
  simp only [IsTracesS, traceVars, traceValsS, hAB, hAC, hAD, hBC, hBD, hCD, hABC, hABD, hACD,
    hBCD, hB, hC, hD, List.map_cons, List.map_nil]
  norm_num

/-! ## The certificate vectors -/

/-- `Φ = 4κ_C + 10κ_R − 9κ_H` at `M` in the 28-basis (paper, proof of thm:cer:seven(a)). -/
def certM : List (Fin 28 × ℚ) :=
  [(0, -8/27), (4, -8), (5, 8), (6, 8), (7, 20/9), (14, 20/9), (21, 20/9),
    (13, -20), (20, -20), (27, -20), (26, -9), (18, 9), (25, 9), (12, -9), (19, -9), (11, 9)]

/-- A second certificate vector `2κ_C + 6κ_R − 5κ_H` at `M`. -/
def certM1 : List (Fin 28 × ℚ) :=
  [(0, -4/27), (4, -4), (5, 4), (6, 4), (7, 4/3), (14, 4/3), (21, 4/3),
    (13, -12), (20, -12), (27, -12), (26, -5), (18, 5), (25, 5), (12, -5), (19, -5), (11, 5)]

/-- `Φ_S = Σ_s sgn(s)(η^C_s + w(s) η^R_s − 3η^H_s)`, `w = 4` for `B` last, at `S`. -/
def certS : List (Fin 28 × ℚ) :=
  [(0, -1/9), (4, -2), (5, 2), (6, 2), (7, 2/3), (14, 8/9), (21, 2/3),
    (13, -6), (20, -7), (27, -7), (26, -3), (18, 3), (25, 3), (12, -3), (19, -3), (11, 3)]

theorem qform_certM : qform traceValsM certM = -4/27 := by decide +kernel
theorem qform_certM1 : qform traceValsM certM1 = -4/243 := by decide +kernel
theorem qform_certS : qform traceValsS certS = -2/729 := by decide +kernel

/-! ## thm:cer:seven(a), abstract form -/

theorem normSq_certM {W : WalkForm V} {τ : TraceData} (hG : GramIs W τ) (hτ : IsTracesM τ) :
    W.form (combo W certM) (combo W certM) = -4/27 := by
  rw [form_combo hG traceValsM hτ, qform_certM]; norm_num

theorem normSq_certM1 {W : WalkForm V} {τ : TraceData} (hG : GramIs W τ) (hτ : IsTracesM τ) :
    W.form (combo W certM1) (combo W certM1) = -4/243 := by
  rw [form_combo hG traceValsM hτ, qform_certM1]; norm_num

theorem normSq_certS {W : WalkForm V} {τ : TraceData} (hG : GramIs W τ) (hτ : IsTracesS τ) :
    W.form (combo W certS) (combo W certS) = -2/729 := by
  rw [form_combo hG traceValsS hτ, qform_certS]; norm_num

/-- At the traces of `M`, no `WalkForm` has the Gram matrix of Lemma A. -/
theorem not_gramIs_M {W : WalkForm V} {τ : TraceData} (hτ : IsTracesM τ) : ¬ GramIs W τ := by
  intro hG
  have h := W.psd (combo W certM)
  rw [normSq_certM hG hτ] at h
  norm_num at h

/-- At the traces of `S`, no `WalkForm` has the Gram matrix of Lemma A. -/
theorem not_gramIs_S {W : WalkForm V} {τ : TraceData} (hτ : IsTracesS τ) : ¬ GramIs W τ := by
  intro hG
  have h := W.psd (combo W certS)
  rw [normSq_certS hG hτ] at h
  norm_num at h

/-- thm:cer:seven(a) for `M`, rule form: no `WalkForm` satisfies the rule package of
lem:cer:gram28 with the traces of `M`. -/
theorem seven_M_rules {W : WalkForm V} {τ : TraceData} (hτ : IsTracesM τ) :
    ¬ Gram28Rules W τ := fun h => not_gramIs_M hτ (lemmaA_of_gram28Rules h)

theorem seven_S_rules {W : WalkForm V} {τ : TraceData} (hτ : IsTracesS τ) :
    ¬ Gram28Rules W τ := fun h => not_gramIs_S hτ (lemmaA_of_gram28Rules h)

/-- thm:cer:seven(a) for `M`, table form: no `WalkForm` reproduces, from `p_A`, a table with the
traces of `M` on all words of length at most six (= A-initial words of length at most seven from
`e/3`). -/
theorem seven_M {W : WalkForm V} {τ : TraceData} {f : Word Letter → ℝ} (hτ : IsTracesM τ)
    (hT : TableValues τ f) : ¬ W.Reproduces wordsE3 f :=
  fun hrep => not_gramIs_M hτ (lemmaA_e3 hrep hT)

theorem seven_S {W : WalkForm V} {τ : TraceData} {f : Word Letter → ℝ} (hτ : IsTracesS τ)
    (hT : TableValues τ f) : ¬ W.Reproduces wordsE3 f :=
  fun hrep => not_gramIs_S hτ (lemmaA_e3 hrep hT)

/-- Same, from the hypotheses (i)–(iii) of lem:cer:gram28 on an arbitrary word set. -/
theorem seven_M_hyp {W : WalkForm V} {τ : TraceData} {S : Set (Word Letter)} {f : Word Letter → ℝ}
    (hτ : IsTracesM τ) (hS : Gram28Hyp W τ S) (hT : TableValues τ f) : ¬ W.Reproduces S f :=
  fun hrep => not_gramIs_M hτ (lemmaA_of_gram28Hyp hS hrep hT)

theorem seven_S_hyp {W : WalkForm V} {τ : TraceData} {S : Set (Word Letter)} {f : Word Letter → ℝ}
    (hτ : IsTracesS τ) (hS : Gram28Hyp W τ S) (hT : TableValues τ f) : ¬ W.Reproduces S f :=
  fun hrep => not_gramIs_S hτ (lemmaA_of_gram28Hyp hS hrep hT)

end AlbertSequential.LengthSeven.Cert

#print axioms AlbertSequential.LengthSeven.Cert.qform_certM
#print axioms AlbertSequential.LengthSeven.Cert.seven_M
#print axioms AlbertSequential.LengthSeven.Cert.seven_S
#print axioms AlbertSequential.LengthSeven.Cert.seven_M_rules
#print axioms AlbertSequential.LengthSeven.Cert.normSq_certM1
