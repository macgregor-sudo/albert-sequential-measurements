/- Apache-2.0. Part of the proofs in `Solution`: transfer of the development's theorems to the
definitions of `Challenge`. -/
module

public import ChallengeDefs
public import Defs
public import Interfaces.Geometry
public import Interfaces.WordsAndCertificates
public import ThirteenTracesAndAform
public import ThreeAtomAndFourPoint
public import ComplexWindowDeterminantAndMax
public import FixedSBinding

/-!
# Albert-side bridge: the Challenge's definitions are the development's

The Challenge's octonions, Albert algebra, Jordan product, trace, quadratic map, atoms, densities and
word probabilities are textual copies of the development's (`Defs.lean`,
`Interfaces/WordsAndCertificates.lean`), so they agree definitionally (`rfl`). Generation is phrased
with a different (but equivalent) subalgebra structure; the four-point invariant is the same
polynomial in `let` form; the explicit quadruples `M` and `S` are the development's `maximizerConfig`
and `fixedS` up to rewriting of scalars.
-/

@[expose] public section
noncomputable section

namespace AlbertChallenge.Bridge

open AlbertChallenge

theorem albert_eq : AlbertChallenge.Albert = AlbertSequential.Albert := rfl

/-- The identity map, read from the Challenge's copy of `J` to the development's. All transport
lemmas below are stated through `toT`, so that every rewrite stays type-homogeneous. -/
def toT (x : Albert) : AlbertSequential.Albert := x

theorem toT_inj (x y : Albert) : toT x = toT y ↔ x = y := Iff.rfl

/-! ### Octonion level (bodies identical; checked on abstract arguments only) -/

theorem octMul_eq (x y : Octonion) : octMul x y = AlbertSequential.octonionMul x y := rfl
theorem octConj_eq (x : Octonion) : octConj x = AlbertSequential.octonionConj x := rfl
theorem octScalar_eq (r : ℝ) : octScalar r = AlbertSequential.octonionScalar r := rfl
theorem octRe_eq (x : Octonion) : octRe x = AlbertSequential.octonionReal x := rfl
theorem octI_eq : octI = AlbertSequential.octI := rfl
theorem octJ_eq : octJ = AlbertSequential.octJ := rfl
theorem octL_eq : octL = AlbertSequential.octL := rfl
theorem octNormSq_eq (x : Octonion) : octNormSq x = AlbertSequential.octNormSq x := rfl

/-- `v v†` is the development's `octDyad v`. -/
theorem rankOne_eq (v : Fin 3 → Octonion) : rankOne v = AlbertSequential.octDyad v := rfl

/-! ### Albert level. Nested products are compared by rewriting, never by unfolding: the
definitional checker would otherwise evaluate octonion arithmetic coordinatewise. -/

theorem jordanMul_eq (x y : Albert) :
    jordanMul x y = AlbertSequential.jordanMul x y := rfl

theorem jordanMul_toT (x y : Albert) :
    AlbertSequential.jordanMul (toT x) (toT y) = toT (jordanMul x y) := rfl

theorem albertUnit_toT : AlbertSequential.albertUnit = toT albertUnit := rfl

theorem albertTrace_toT (x : Albert) : AlbertSequential.albertTrace (toT x) = albertTrace x := rfl

theorem sub_toT (x y : Albert) : toT x - toT y = toT (x - y) := rfl

theorem nsmul_toT (k : ℕ) (x : Albert) : k • toT x = toT (k • x) := rfl

theorem smul_toT (r : ℝ) (x : Albert) : r • toT x = toT (r • x) := rfl

theorem tracePairing_toT (x y : Albert) :
    AlbertSequential.tracePairing (toT x) (toT y) = tracePairing x y := by
  unfold AlbertSequential.tracePairing tracePairing
  rw [jordanMul_toT, albertTrace_toT]

theorem quadraticMap_toT (x y : Albert) :
    AlbertSequential.quadraticMap (toT x) (toT y) = toT (quadraticMap x y) := by
  unfold AlbertSequential.quadraticMap quadraticMap
  rw [jordanMul_toT, jordanMul_toT, jordanMul_toT, jordanMul_toT, nsmul_toT, sub_toT]

theorem isAtom_toT (p : Albert) : AlbertSequential.IsAtom (toT p) ↔ IsAtom p := by
  unfold AlbertSequential.IsAtom IsAtom
  rw [jordanMul_toT, albertTrace_toT, toT_inj]

theorem isDensity_toT (ρ : Albert) : AlbertSequential.IsDensity (toT ρ) ↔ IsDensity ρ := Iff.rfl

theorem maximallyMixed_toT :
    (1 / 3 : ℝ) • AlbertSequential.albertUnit = toT maximallyMixed := rfl

theorem outcome_toT {n : ℕ} (p : Fin n → Albert) (a : Fin n × Bool) :
    AlbertSequential.nativeOutcome (fun i => toT (p i)) a = toT (outcomeEffect p a) := by
  unfold AlbertSequential.nativeOutcome outcomeEffect
  split
  · rfl
  · rw [albertUnit_toT, sub_toT]

theorem branch_toT {n : ℕ} (p : Fin n → Albert) (w : Word n) (ρ : Albert) :
    AlbertSequential.nativeBranchState (fun i => toT (p i)) (toT ρ) w =
      toT (w.foldl (fun σ a => quadraticMap (outcomeEffect p a) σ) ρ) := by
  unfold AlbertSequential.nativeBranchState
  refine List.foldl_hom toT (fun x a => ?_)
  show AlbertSequential.quadraticMap (AlbertSequential.nativeOutcome (fun i => toT (p i)) a) (toT x) =
    toT (quadraticMap (outcomeEffect p a) x)
  rw [outcome_toT, quadraticMap_toT]

theorem wordProbability_toT {n : ℕ} (p : Fin n → Albert) (ρ : Albert) (w : Word n) :
    AlbertSequential.nativeWordProbability (fun i => toT (p i)) (toT ρ) w = wordProbability p ρ w := by
  unfold AlbertSequential.nativeWordProbability wordProbability
  rw [branch_toT, albertTrace_toT]

/-- The development's unital Jordan subalgebras are the Challenge's. -/
def toNative (B : JordanSubalgebra) : AlbertSequential.NativeJordanSubalgebra where
  carrier := B.carrier
  unit_mem := B.unit_mem
  product_mem := B.mul_mem

def ofNative (B : AlbertSequential.NativeJordanSubalgebra) : JordanSubalgebra where
  carrier := B.carrier
  unit_mem := B.unit_mem
  mul_mem := B.product_mem

theorem generates_toT {n : ℕ} (p : Fin n → Albert) :
    AlbertSequential.GeneratesAlbert (fun i => toT (p i)) ↔ Generates p := by
  constructor
  · intro h B hB
    rw [eq_top_iff]
    intro x _
    exact h (toT x) (toNative B) hB
  · intro h x B hB
    have htop : (ofNative B).carrier = ⊤ := h (ofNative B) hB
    have hx : (show Albert from x) ∈ (ofNative B).carrier := htop ▸ Submodule.mem_top
    exact hx

/-! ### The four-point invariant -/

theorem overlap_toT (p : Fin 4 → Albert) (i j : Fin 4) :
    AlbertSequential.fpOverlap (fun i => toT (p i)) i j = overlap p i j :=
  tracePairing_toT _ _

theorem triangle_toT (p : Fin 4 → Albert) (i j k : Fin 4) :
    AlbertSequential.fpTriangle (fun i => toT (p i)) i j k = triangle p i j k := by
  unfold AlbertSequential.fpTriangle triangle
  rw [jordanMul_toT, tracePairing_toT]

theorem doublePair_toT (p : Fin 4 → Albert) :
    AlbertSequential.fpDoublePair1 (fun i => toT (p i)) = doublePair p 0 ∧
      AlbertSequential.fpDoublePair2 (fun i => toT (p i)) = doublePair p 1 ∧
      AlbertSequential.fpDoublePair3 (fun i => toT (p i)) = doublePair p 2 := by
  unfold AlbertSequential.fpDoublePair1 AlbertSequential.fpDoublePair2
    AlbertSequential.fpDoublePair3
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [jordanMul_toT, jordanMul_toT, tracePairing_toT]
    rfl

/-- The Challenge's `let` form is the development's `fourPointOmegaPoly` of the same traces. -/
theorem fourPointInvariant_shape (p : Fin 4 → Albert) :
    fourPointInvariant p = AlbertSequential.fourPointOmegaPoly
      (overlap p 0 1) (overlap p 0 2) (overlap p 0 3) (overlap p 1 2) (overlap p 1 3)
      (overlap p 2 3) (triangle p 0 1 2) (triangle p 0 1 3) (triangle p 0 2 3) (triangle p 1 2 3)
      (doublePair p 1 + doublePair p 2 - doublePair p 0)
      (doublePair p 0 + doublePair p 2 - doublePair p 1)
      (doublePair p 0 + doublePair p 1 - doublePair p 2) := rfl

theorem fourPointInvariant_toT (p : Fin 4 → Albert) :
    AlbertSequential.fourPointInvariant (fun i => toT (p i)) = fourPointInvariant p := by
  obtain ⟨h0, h1, h2⟩ := doublePair_toT p
  rw [fourPointInvariant_shape]
  unfold AlbertSequential.fourPointInvariant AlbertSequential.fpOmega1 AlbertSequential.fpOmega2
    AlbertSequential.fpOmega3
  simp only [overlap_toT, triangle_toT, h0, h1, h2]

/-! ### The explicit quadruples -/

theorem quadrupleS_eq : quadrupleS = AlbertSequential.fixedS := by
  funext i
  fin_cases i
  · change ((![1, 0, 0] : Fin 3 → ℝ), (0 : Fin 3 → Octonion)) = AlbertSequential.diagAtom 0
    refine Prod.ext ?_ rfl
    funext j
    fin_cases j <;> simp [AlbertSequential.diagAtom]
  · change (1 / 2 : ℝ) • ((![1, 1, 0] : Fin 3 → ℝ), ![octScalar 1, 0, 0]) = AlbertSequential.atomB
    rw [octScalar_eq]
    rfl
  · change (1 / 3 : ℝ) • ((![1, 1, 1] : Fin 3 → ℝ), ![-octI, octScalar 1, octI]) =
      AlbertSequential.atomC
    rw [octScalar_eq, octI_eq]
    rfl
  · change (1 / 3 : ℝ) • ((![1, 1, 1] : Fin 3 → ℝ), ![-octJ, -octL, -octMul octJ octL]) =
      AlbertSequential.atomD
    rw [octMul_eq, octJ_eq, octL_eq]
    rfl

theorem quadrupleM_eq : quadrupleM = AlbertSequential.maximizerConfig := by
  have h0 : AlbertSequential.octonionScalar 0 = 0 := by
    apply Prod.ext
    · rfl
    · rfl
  funext i
  fin_cases i
  · change rankOne ![octScalar 1, 0, 0] = AlbertSequential.octDyad ![AlbertSequential.octonionScalar 1, 0, 0]
    rw [rankOne_eq, octScalar_eq]
    rfl
  · change rankOne ![octScalar (1 / Real.sqrt 3), octScalar (Real.sqrt 2 * (1 / Real.sqrt 3)), 0] =
      AlbertSequential.octDyad ![AlbertSequential.octonionScalar (1 / Real.sqrt 3),
        AlbertSequential.octonionScalar (Real.sqrt 2 / Real.sqrt 3), 0]
    rw [rankOne_eq, octScalar_eq, octScalar_eq, mul_one_div]
    rfl
  · change rankOne ![octScalar (1 / Real.sqrt 3), (1 / Real.sqrt 3) • octI,
        octScalar (1 / Real.sqrt 3)] =
      AlbertSequential.octDyad ![AlbertSequential.octonionScalar (1 / Real.sqrt 3),
        AlbertSequential.octonionScalar 0 + (1 / Real.sqrt 3) • AlbertSequential.octI,
        AlbertSequential.octonionScalar (1 / Real.sqrt 3)]
    rw [rankOne_eq, octScalar_eq, octI_eq, h0, zero_add]
    rfl
  · change rankOne ![octScalar (1 / Real.sqrt 3), (1 / Real.sqrt 3) • octJ,
        (1 / Real.sqrt 3) • octL] =
      AlbertSequential.octDyad ![AlbertSequential.octonionScalar (1 / Real.sqrt 3),
        AlbertSequential.octonionScalar 0 + (0 : ℝ) • AlbertSequential.octI +
          (1 / Real.sqrt 3) • AlbertSequential.octJ,
        (1 / Real.sqrt 3) • AlbertSequential.octL]
    rw [rankOne_eq, octScalar_eq, octJ_eq, octL_eq, h0, zero_add, zero_smul, zero_add]
    rfl

end AlbertChallenge.Bridge
