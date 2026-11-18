/- SPDX-License-Identifier: Apache-2.0 -/
module
public import NativeWordPurity
public import NativePeirceIdentities
public import PrimitivePurityDecomposition

/-! The existing signed skip/yes/no lists have their actual native Jordan
semantics. All constants remain symbolic; no chosen configuration is evaluated. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.NativeAnalysis

def weightedNativeEffect {ι : Type*} (p : ι → Albert)
    (ts : List (ℝ × Word ι)) : Albert :=
  (ts.map (fun t => t.1 • nativeWordEffect p t.2)).sum

theorem weightedNativeEffect_nil {ι : Type*} (p : ι → Albert) :
    weightedNativeEffect p [] = 0 := rfl

theorem weightedNativeEffect_cons {ι : Type*} (p : ι → Albert)
    (r : ℝ) (w : Word ι) (ts : List (ℝ × Word ι)) :
    weightedNativeEffect p ((r,w)::ts) =
      r • nativeWordEffect p w + weightedNativeEffect p ts := rfl

theorem weightedNativeEffect_append {ι : Type*} (p : ι → Albert)
    (ts us : List (ℝ × Word ι)) :
    weightedNativeEffect p (ts ++ us) = weightedNativeEffect p ts + weightedNativeEffect p us := by
  simp only [weightedNativeEffect, List.map_append, List.sum_append]

theorem weightedNativeEffect_scale {ι : Type*} (p : ι → Albert)
    (r : ℝ) (ts : List (ℝ × Word ι)) :
    weightedNativeEffect p (scaleWordTerms r ts) = r • weightedNativeEffect p ts := by
  induction ts with
  | nil => simp only [scaleWordTerms, List.map_nil, weightedNativeEffect_nil, smul_zero]
  | cons t ts ih =>
    rcases t with ⟨b,w⟩
    simp only [scaleWordTerms, List.map_cons, weightedNativeEffect_cons] at ih ⊢
    rw [ih, mul_smul, smul_add]

theorem weightedNativeEffect_access {ι : Type*} (p : ι → Albert)
    (i : ι) (w : Word ι) :
    weightedNativeEffect p (accessWordTerms i w) =
      (2 : ℝ) • jordanMul (p i) (nativeWordEffect p w) := by
  simp only [accessWordTerms, signedAccessChoices, List.map_cons, List.map_nil,
    accessPrefix, weightedNativeEffect_cons, weightedNativeEffect_nil,
    one_smul, neg_one_smul, add_zero, nativeWordEffect, nativeOutcome,
    Bool.false_eq_true, ite_true, ite_false]
  rw [quadraticMap_complement]
  module

theorem weightedNativeEffect_accessLift {ι : Type*} (p : ι → Albert)
    (i : ι) (ts : List (ℝ × Word ι)) :
    weightedNativeEffect p (accessLiftWordTerms i ts) =
      (2 : ℝ) • jordanMul (p i) (weightedNativeEffect p ts) := by
  induction ts with
  | nil => simp only [accessLiftWordTerms, List.flatMap_nil,
      weightedNativeEffect_nil, jordanMul_zero_right, smul_zero]
  | cons t ts ih =>
    simp only [accessLiftWordTerms, List.flatMap_cons] at ih ⊢
    rw [weightedNativeEffect_append, weightedNativeEffect_scale,
      weightedNativeEffect_access, ih]
    rcases t with ⟨r,w⟩
    rw [weightedNativeEffect_cons, jordanMul_add_right, jordanMul_smul_right]
    module

theorem weightedNativeEffect_doubleAccess {ι : Type*} (p : ι → Albert)
    (hp : ∀ i, jordanMul (p i) (p i) = p i) (k l m : ι) :
    weightedNativeEffect p (doubleAccessWordTerms k l m) =
      (4 : ℝ) • jordanMul (p k) (jordanMul (p l) (p m)) := by
  rw [doubleAccessWordTerms, weightedNativeEffect_accessLift,
    weightedNativeEffect_access, nativeWordEffect_singleton p hp,
    jordanMul_smul_right]
  change (2 : ℝ) • (2 : ℝ) • jordanMul (p k) (jordanMul (p l) (p m)) = _
  module

theorem weightedNativeEffect_polarizedTriple {ι : Type*} (p : ι → Albert)
    (hp : ∀ i, jordanMul (p i) (p i) = p i) (k l m : ι) :
    weightedNativeEffect p (polarizedTripleWordTerms k l m) =
      (4 : ℝ) • (jordanMul (p k) (jordanMul (p l) (p m)) +
        jordanMul (p m) (jordanMul (p k) (p l)) -
        jordanMul (p l) (jordanMul (p k) (p m))) := by
  rw [polarizedTripleWordTerms, weightedNativeEffect_append, weightedNativeEffect_append,
    weightedNativeEffect_scale, neg_one_smul]
  rw [weightedNativeEffect_doubleAccess p hp, weightedNativeEffect_doubleAccess p hp,
    weightedNativeEffect_doubleAccess p hp]
  module

theorem weightedWordScalar_native {ι : Type*} (p : ι → Albert) (rho : Albert)
    (ts : List (ℝ × Word ι)) :
    weightedWordScalar (nativeWordProbability p rho) ts =
      tracePairing rho (weightedNativeEffect p ts) := by
  induction ts with
  | nil =>
    change 0 = tracePairing rho 0
    simp only [tracePairing, jordanMul_zero_right, albertTrace_zero]
  | cons t ts ih =>
    rcases t with ⟨r,w⟩
    change r * nativeWordProbability p rho w +
      weightedWordScalar (nativeWordProbability p rho) ts = _
    rw [weightedNativeEffect_cons, tracePairing_add_right, tracePairing_smul_right,
      nativeWordProbability_eq_pairing, ih]

theorem native_scalar_triangle_access {ι : Type*} (p : ι → Albert)
    (hp : ∀ i, jordanMul (p i) (p i) = p i) (rho : Albert) (b d : ι) :
    weightedWordScalar (nativeWordProbability p rho) (accessWordTerms b [(d,true)]) =
      2 * tracePairing rho (jordanMul (p b) (p d)) := by
  rw [weightedWordScalar_native, weightedNativeEffect_access,
    nativeWordEffect_singleton p hp, tracePairing_smul_right]
  rfl

theorem native_scalar_polarizedTriple_access {ι : Type*} (p : ι → Albert)
    (hp : ∀ i, jordanMul (p i) (p i) = p i) (rho : Albert) (k l m : ι) :
    weightedWordScalar (nativeWordProbability p rho) (polarizedTripleWordTerms k l m) =
      4 * tracePairing rho (jordanMul (p k) (jordanMul (p l) (p m)) +
        jordanMul (p m) (jordanMul (p k) (p l)) -
        jordanMul (p l) (jordanMul (p k) (p m))) := by
  rw [weightedWordScalar_native, weightedNativeEffect_polarizedTriple p hp,
    tracePairing_smul_right]

#print axioms native_scalar_polarizedTriple_access
end AlbertSequential.NativeAnalysis
