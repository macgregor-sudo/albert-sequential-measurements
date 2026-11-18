/- SPDX-License-Identifier: Apache-2.0 -/
module
public import NativeJordanQuadratic
public import NativeAtomCompression
public import NativeWordPositivity
public import SupportedPurityLeaves

/-! Symbolic native purity on the literal efficient measured histories. No
conditioning, fixed certificate, numerical constants or short-witness input. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.NativeAnalysis

theorem quadraticMap_unit_left (x : Albert) : quadraticMap albertUnit x = x := by
  simp only [quadraticMap, jordanMul_albertUnit_left, two_smul]
  abel

theorem nativeWordEffect_singleton {ι : Type*} (p : ι → Albert)
    (hp : ∀ i, jordanMul (p i) (p i) = p i) (a : Outcome ι) :
    nativeWordEffect p [a] = nativeOutcome p a := by
  change quadraticMap (nativeOutcome p a) albertUnit = _
  rw [quadraticMap_unit_argument, nativeOutcome_idempotent p hp]

/-- Reversing the word except its last letter gives the quadratic effect map,
with chronological order fixed by the actual native branch definition. -/
theorem nativeWordEffect_quadratic_mirror {ι : Type*} (p : ι → Albert)
    (hp : ∀ i, jordanMul (p i) (p i) = p i) (v : Word ι) (x : Albert) :
    quadraticMap (nativeWordEffect p v) x =
      nativeBranchState p x (v ++ purityMirror v) := by
  induction v generalizing x with
  | nil => exact quadraticMap_unit_left x
  | cons a w ih =>
    cases w with
    | nil =>
      rw [nativeWordEffect_singleton p hp]
      rfl
    | cons b v =>
      have hm : purityMirror (a :: b :: v) = purityMirror (b :: v) ++ [a] := by
        simp only [purityMirror, List.dropLast_cons_cons, List.reverse_cons]
      rw [hm]
      change quadraticMap (quadraticMap (nativeOutcome p a)
        (nativeWordEffect p (b :: v))) x = _
      rw [quadraticMap_fundamental, ih]
      simp only [List.cons_append, nativeBranchState_cons, ← List.append_assoc,
        nativeBranchState_append]
      rfl

theorem native_probability_append {ι : Type*} (p : ι → Albert)
    (rho : Albert) (u v : Word ι) :
    nativeWordProbability p rho (u ++ v) =
      nativeWordProbability p (nativeBranchState p rho u) v := by
  exact congrArg albertTrace (nativeBranchState_append p rho u v)

theorem native_corner_middle_probability {ι : Type*} (p : ι → Albert)
    (rho : Albert) (t v : Word ι) (a : Outcome ι)
    (ha : IsAtom (nativeOutcome p a)) :
    nativeWordProbability p rho ((t ++ [a]) ++ v) =
      tracePairing (nativeOutcome p a) (nativeWordEffect p v) *
        nativeWordProbability p rho (t ++ [a]) := by
  rw [native_probability_append, nativeWordProbability_eq_pairing,
    nativeBranchState_append]
  change tracePairing (quadraticMap (nativeOutcome p a) (nativeBranchState p rho t))
      (nativeWordEffect p v) = _
  rw [quadraticMap_atom _ _ ha, tracePairing_smul_left]
  have ht : nativeWordProbability p rho (t ++ [a]) =
      tracePairing (nativeOutcome p a) (nativeBranchState p rho t) := by
    change albertTrace (nativeBranchState p rho (t ++ [a])) = _
    rw [nativeBranchState_append]
    change albertTrace (quadraticMap (nativeOutcome p a) (nativeBranchState p rho t)) = _
    rw [albertTrace_quadraticMap, ha.1]
  rw [ht, mul_comm]

theorem native_corner_long_probability {ι : Type*} (p : ι → Albert)
    (hp : ∀ i, jordanMul (p i) (p i) = p i) (rho : Albert)
    (t v : Word ι) (a : Outcome ι) (ha : IsAtom (nativeOutcome p a)) :
    nativeWordProbability p rho ((t ++ [a]) ++ v ++ purityMirror v ++ [a]) =
      tracePairing (nativeOutcome p a) (nativeWordEffect p v) ^ 2 *
        nativeWordProbability p rho (t ++ [a]) := by
  have hbranch : nativeBranchState p rho ((t ++ [a]) ++ v ++ purityMirror v ++ [a]) =
      quadraticMap (nativeOutcome p a)
        (quadraticMap (nativeWordEffect p v)
          (quadraticMap (nativeOutcome p a) (nativeBranchState p rho t))) := by
    rw [List.append_assoc (t ++ [a]) v (purityMirror v),
      nativeBranchState_append, nativeBranchState_append,
      ← nativeWordEffect_quadratic_mirror p hp, nativeBranchState_append]
    rfl
  change albertTrace (nativeBranchState p rho _) = _
  rw [hbranch, ← quadraticMap_fundamental, quadraticMap_atom _ _ ha,
    quadraticMap_smul_left, albertTrace_smul]
  congr 1
  exact congrArg albertTrace (nativeBranchState_append p rho t [a]).symm

end AlbertSequential.NativeAnalysis

namespace AlbertSequential.SupportedPurityLeaf
open NativeAnalysis

theorem native_middle_probability {n : ℕ} (l : SupportedPurityLeaf (Fin n))
    (p : Fin n → Albert) (rho : Albert) (ha : IsAtom (nativeOutcome p l.outcome))
    (hc : l.constant = tracePairing (nativeOutcome p l.outcome) (nativeWordEffect p l.suffix)) :
    nativeWordProbability p rho l.middleWord =
      l.constant * nativeWordProbability p rho l.shortWord := by
  rw [hc]
  exact native_corner_middle_probability p rho l.historyPrefix l.suffix l.outcome ha

theorem native_long_probability {n : ℕ} (l : SupportedPurityLeaf (Fin n))
    (p : Fin n → Albert) (hp : ∀ i, jordanMul (p i) (p i) = p i)
    (rho : Albert) (ha : IsAtom (nativeOutcome p l.outcome))
    (hc : l.constant = tracePairing (nativeOutcome p l.outcome) (nativeWordEffect p l.suffix)) :
    nativeWordProbability p rho l.longWord =
      l.constant ^ 2 * nativeWordProbability p rho l.shortWord := by
  cases hv : l.suffix with
  | nil =>
    have hc1 : l.constant = 1 := by
      rw [hc, hv]
      exact (tracePairing_unit_right _).trans ha.2
    simp only [longWord, hv, hc1, one_pow, one_mul, shortWord]
  | cons b v =>
    rw [longWord, hv, hc]
    simpa only [hv, shortWord, history] using
      native_corner_long_probability p hp rho l.historyPrefix (b :: v) l.outcome ha

/-- Exact vanishing of the existing three-history functional for every raw
native initial element, including zero histories, without conditioning. -/
theorem wordFunctional_native_zero {n : ℕ} (l : SupportedPurityLeaf (Fin n))
    (p : Fin n → Albert) (hp : ∀ i, jordanMul (p i) (p i) = p i)
    (rho : Albert) (ha : IsAtom (nativeOutcome p l.outcome))
    (hc : l.constant = tracePairing (nativeOutcome p l.outcome) (nativeWordEffect p l.suffix)) :
    l.wordFunctional.evaluate (nativeWordProbability p rho) = 0 := by
  rw [wordFunctional_evaluate, l.native_middle_probability p rho ha hc,
    l.native_long_probability p hp rho ha hc]
  ring

#print axioms wordFunctional_native_zero
end AlbertSequential.SupportedPurityLeaf
