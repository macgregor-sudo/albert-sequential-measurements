module

import NativeTaggedSharpIdealityFailure
open AlbertSequential AlbertSequential.NativeAnalysis
open scoped Matrix ComplexOrder
noncomputable section

example {d : ℕ} {P F : ComplexMatrix d} (hP : P * P = P) (hF : F.PosSemidef)
    (hy : P * F * P = 0) (hn : (1 - P) * F * (1 - P) = 0) : F = 0 :=
  positiveEffect_eq_zero_of_complementaryCorners hP hF hy hn

example {n : ℕ} (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i))
    (ρ : Albert) (hρ : IsDensity ρ) (j : Fin n)
    (ha0 : 0 < tracePairing (p j) ρ) (ha1 : tracePairing (p j) ρ < 1) :
    ∃ (r : BinaryKrausRealization (17*n+1) (Fin n)) (s : SharpDilationData (17*n+1) (Fin n))
      (Z : ComplexMatrix ((17*n+1)+(17*n+1))),
      Z = nativeGeneralCertainInitState n (tracePairing (p j) ρ) ∧
      IsSharpDilation r s ∧ IsRepeatableSharpDilation s ∧ IsRealSharpDilation s ∧
      (∀ w, s.wordProbability r.initial w = nativeWordProbability p ρ w) ∧
      IsMatrixDensity Z ∧ s.projection j * Z = Z ∧
      s.branch j true Z = embedFirstBlock (nativeGeneralScalarRail (some j)) ∧
      s.branch j true Z ≠ Z :=
  nativeGeneral_sharp_initialRail_disturbance p hp ρ hρ j ha0 ha1

example :
    ∃ (r : BinaryKrausRealization 68 (Fin 4)) (s : SharpDilationData 68 (Fin 4))
      (Z : ComplexMatrix 136),
      Z = nativeMCertainCState ∧ IsSharpDilation r s ∧ IsRepeatableSharpDilation s ∧ IsRealSharpDilation s ∧
      (∀ w, s.wordProbability r.initial w =
        nativeWordProbability maximizerConfig ((1 / 3 : ℝ) • albertUnit) w) ∧
      IsMatrixDensity Z ∧ s.projection 0 * Z = Z ∧ s.projection 1 * Z = Z ∧
      (s.projection 1 * Z).trace = 1 ∧
      s.branch 0 true Z = embedFirstBlock (nativeMScalarRail 0) ∧
      (s.projection 1 * s.branch 0 true Z).trace = (1 / 3 : ℂ) ∧
      (∀ Y : ComplexMatrix 68, Z ≠ embedFirstBlock Y) :=
  nativeM_sharp_two_presses

#print axioms positiveEffect_eq_zero_of_complementaryCorners
#print axioms binaryYesFaceState_eigenprojection_formula
#print axioms binaryYesFaceState_eq_of_common_eigenvalue
#print axioms binaryKrausDilation_branch_yesFace
#print axioms nativeGeneral_sharp_initialRail_disturbance
#print axioms nativeM_sharp_two_presses

example {d : ℕ} {X : Type*} (r : BinaryKrausRealization d X) (s : SharpDilationData d X)
    (hs : IsSharpDilation r s) (w : Word X) :
    ∃ Y : ComplexMatrix d,
      w.foldl (fun Z a => s.branch a.1 a.2 Z) (embedFirstBlock r.initial) = embedFirstBlock Y := by
  have hcorner (u : Word X) (Z : ComplexMatrix (d+d)) (hZ : ∃ Y, Z = embedFirstBlock Y) :
      ∃ Y : ComplexMatrix d, u.foldl (fun U a => s.branch a.1 a.2 U) Z = embedFirstBlock Y := by
    induction u generalizing Z with
    | nil => exact hZ
    | cons a u ih => exact ih _ (hs.2.2.2.2.2.2.2.1 a.1 a.2 Z)
  exact hcorner w _ ⟨r.initial, rfl⟩
