module

public import NativeAtomCompression
public import NativePeirceIdentities

/-! Actual atom reflections from a concrete real sign conjugation transported
through a genuine one-atom normalizer. The same formula for arbitrary p is not
asserted to define an automorphism. -/

@[expose] public section
noncomputable section
namespace AlbertSequential.NativeAnalysis

def firstRecoveredReflection : Glennie.CompactAutomorphism :=
  Glennie.realRotation12Automorphism (-1) 0 (by norm_num)

private def firstRecoveredSymmetry : Glennie.Albert := ⟨1, -1, -1, 0, 0, 0⟩

private theorem firstRecoveredReflection_formula (x : Glennie.Albert) :
    firstRecoveredReflection.equiv x = Glennie.U firstRecoveredSymmetry x := by
  change Glennie.realConjugateAlbert (Glennie.realRotation12 (-1) 0) x = _
  apply Glennie.Albert.ext
  all_goals simp [Glennie.realConjugateAlbert, Glennie.fromMatrix,
    Glennie.matrixConjugateReal, Glennie.matrixRowMix, Glennie.matrixColMix,
    Glennie.realRotation12, Fin.sum_univ_three, Glennie.toMatrix,
    firstRecoveredSymmetry, Glennie.U,
    Glennie.jordan_d0, Glennie.jordan_d1, Glennie.jordan_d2,
    Glennie.jordan_o01, Glennie.jordan_o02, Glennie.jordan_o12,
    Glennie.octDot_coordinates, Glennie.octNormSq, Glennie.octMul,
    Glennie.octConj, Glennie.octScalar, Glennie.octRe]
  all_goals norm_num [show ((0 : Quaternion ℝ), (0 : Quaternion ℝ)) =
    (0 : Glennie.Octonion) from rfl, smul_smul]
  all_goals first | (ring; done) | (simp only [two_smul]; abel)

def firstDiagonalReflection : NativeAlbertAutomorphism :=
  recoveredNativeAutomorphism firstRecoveredReflection

theorem firstDiagonalReflection_apply (x : Albert) :
    firstDiagonalReflection.linearEquiv x =
      quadraticMap ((2 : ℝ) • diagAtom 0 - albertUnit) x := by
  have hs : recoveredCoordinateEquiv ((2 : ℝ) • diagAtom 0 - albertUnit) =
      firstRecoveredSymmetry := by
    rw [map_sub, map_smul, recoveredCoordinateEquiv_diagAtom, recoveredCoordinateEquiv_unit]
    apply Glennie.Albert.ext <;> norm_num [Glennie.standardFrame, firstRecoveredSymmetry]
  apply recoveredCoordinateEquiv.injective
  change firstRecoveredReflection.equiv (recoveredCoordinateEquiv x) = _
  rw [recoveredCoordinateEquiv_quadraticMap, hs]
  exact firstRecoveredReflection_formula _

private theorem firstRecoveredReflection_involutive (x : Glennie.Albert) :
    firstRecoveredReflection.equiv (firstRecoveredReflection.equiv x) = x := by
  have h := firstRecoveredReflection.equiv.symm_apply_apply x
  change Glennie.realConjugateAlbert (Glennie.realRotation12 (-1) 0).transpose
    (Glennie.realConjugateAlbert (Glennie.realRotation12 (-1) 0) x) = x at h
  rw [Glennie.realRotation12_transpose, neg_zero] at h
  exact h

theorem firstDiagonalReflection_involutive (x : Albert) :
    firstDiagonalReflection.linearEquiv (firstDiagonalReflection.linearEquiv x) = x := by
  apply recoveredCoordinateEquiv.injective
  change firstRecoveredReflection.equiv
    (firstRecoveredReflection.equiv (recoveredCoordinateEquiv x)) = recoveredCoordinateEquiv x
  exact firstRecoveredReflection_involutive _

private def recoveredSwapToFirst (i : Fin 3) : Glennie.CompactAutomorphism :=
  ![Glennie.CompactAutomorphism.refl, Glennie.realSwap01Automorphism,
    Glennie.realSwap02Automorphism] i

private theorem recoveredSwapToFirst_apply (i : Fin 3) :
    (recoveredSwapToFirst i).equiv (Glennie.standardFrame i) = Glennie.standardFrame 0 := by
  fin_cases i
  · rfl
  · change Glennie.realConjugateAlbert Glennie.realSwap01 (Glennie.standardFrame 1) = _
    rw [Glennie.realSwap01_coordinates]
    simp [Glennie.standardFrame, Glennie.octConj]
  · change Glennie.realConjugateAlbert Glennie.realSwap02 (Glennie.standardFrame 2) = _
    rw [Glennie.realSwap02_coordinates]
    simp [Glennie.standardFrame, Glennie.octConj]

private theorem nativeSwapToFirst_apply (i : Fin 3) :
    (recoveredNativeAutomorphism (recoveredSwapToFirst i)).linearEquiv (diagAtom i) = diagAtom 0 := by
  apply recoveredCoordinateEquiv.injective
  change (recoveredSwapToFirst i).equiv (recoveredCoordinateEquiv (diagAtom i)) =
    recoveredCoordinateEquiv (diagAtom 0)
  rw [recoveredCoordinateEquiv_diagAtom, recoveredCoordinateEquiv_diagAtom,
    recoveredSwapToFirst_apply]

theorem nativeAtomNormalizer_first (p : Albert) (hp : IsAtom p) :
    ∃ g : NativeAlbertAutomorphism, g.linearEquiv p = diagAtom 0 := by
  obtain ⟨g, i, hgp⟩ := nativeAtomNormalizer p hp
  refine ⟨nativeAutomorphismComposition
    (recoveredNativeAutomorphism (recoveredSwapToFirst i)) g, ?_⟩
  change (recoveredNativeAutomorphism (recoveredSwapToFirst i)).linearEquiv (g.linearEquiv p) = _
  rw [hgp, nativeSwapToFirst_apply]

def chosenAtomNormalizer (p : Albert) (hp : IsAtom p) : NativeAlbertAutomorphism :=
  Classical.choose (nativeAtomNormalizer_first p hp)

private theorem chosenAtomNormalizer_apply (p : Albert) (hp : IsAtom p) :
    (chosenAtomNormalizer p hp).linearEquiv p = diagAtom 0 :=
  Classical.choose_spec (nativeAtomNormalizer_first p hp)

def atomReflectionAutomorphism (p : Albert) (hp : IsAtom p) : NativeAlbertAutomorphism :=
  let g := chosenAtomNormalizer p hp
  nativeAutomorphismComposition (nativeAutomorphismInverse g)
    (nativeAutomorphismComposition firstDiagonalReflection g)

theorem atomReflectionAutomorphism_apply (p : Albert) (hp : IsAtom p) (x : Albert) :
    (atomReflectionAutomorphism p hp).linearEquiv x =
      quadraticMap ((2 : ℝ) • p - albertUnit) x := by
  let g := chosenAtomNormalizer p hp
  have hgp : g.linearEquiv p = diagAtom 0 := chosenAtomNormalizer_apply p hp
  change g.linearEquiv.symm (firstDiagonalReflection.linearEquiv (g.linearEquiv x)) = _
  apply g.linearEquiv.injective
  rw [LinearEquiv.apply_symm_apply, firstDiagonalReflection_apply,
    nativeAutomorphism_quadraticMap, map_sub, map_smul, hgp, g.preserves_unit]

theorem atomReflection_preserves_atom (p : Albert) (hp : IsAtom p)
    (q : Albert) (hq : IsAtom q) :
    IsAtom (quadraticMap ((2 : ℝ) • p - albertUnit) q) := by
  rw [← atomReflectionAutomorphism_apply p hp q]
  exact nativeAutomorphism_atom _ _ hq

theorem atomReflection_involutive (p : Albert) (hp : IsAtom p) (x : Albert) :
    quadraticMap ((2 : ℝ) • p - albertUnit)
      (quadraticMap ((2 : ℝ) • p - albertUnit) x) = x := by
  rw [← atomReflectionAutomorphism_apply p hp
    (quadraticMap ((2 : ℝ) • p - albertUnit) x), ← atomReflectionAutomorphism_apply p hp x]
  let g := chosenAtomNormalizer p hp
  change g.linearEquiv.symm (firstDiagonalReflection.linearEquiv
    (g.linearEquiv (g.linearEquiv.symm (firstDiagonalReflection.linearEquiv (g.linearEquiv x))))) = x
  rw [LinearEquiv.apply_symm_apply, firstDiagonalReflection_involutive,
    LinearEquiv.symm_apply_apply]

theorem atomReflection_preserves_product (p : Albert) (hp : IsAtom p) (x y : Albert) :
    quadraticMap ((2 : ℝ) • p - albertUnit) (jordanMul x y) =
      jordanMul (quadraticMap ((2 : ℝ) • p - albertUnit) x)
        (quadraticMap ((2 : ℝ) • p - albertUnit) y) := by
  rw [← atomReflectionAutomorphism_apply p hp (jordanMul x y),
    ← atomReflectionAutomorphism_apply p hp x, ← atomReflectionAutomorphism_apply p hp y]
  exact (atomReflectionAutomorphism p hp).preserves_product x y

theorem atomReflection_preserves_trace (p : Albert) (hp : IsAtom p) (x : Albert) :
    albertTrace (quadraticMap ((2 : ℝ) • p - albertUnit) x) = albertTrace x := by
  rw [← atomReflectionAutomorphism_apply p hp x]
  exact (atomReflectionAutomorphism p hp).preserves_trace x

theorem nativeAutomorphism_reflection (g : NativeAlbertAutomorphism) (p x : Albert) :
    g.linearEquiv (quadraticMap ((2 : ℝ) • p - albertUnit) x) =
      quadraticMap ((2 : ℝ) • g.linearEquiv p - albertUnit) (g.linearEquiv x) := by
  rw [nativeAutomorphism_quadraticMap, map_sub, map_smul, g.preserves_unit]

end AlbertSequential.NativeAnalysis
