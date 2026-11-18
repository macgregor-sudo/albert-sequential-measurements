module

public import NativeAutomorphisms

/-! Rank-one quadratic compression for every literal native trace-one
idempotent. Actual compact diagonalization reduces to the existing three
diagonal controls; no computational cubic residual is used. -/

@[expose] public section
noncomputable section
namespace AlbertSequential.NativeAnalysis

private theorem zero_or_one_of_square_eq_self (a : ℝ) (ha : a * a = a) :
    a = 0 ∨ a = 1 := by
  have h : a * (a - 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp h with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

private theorem recovered_diagonal_atom (x : Glennie.Albert) (hx : Glennie.IsDiagonal x)
    (hp : Glennie.jordan x x = x) (ht : Glennie.trace x = 1) :
    ∃ i : Fin 3, x = Glennie.standardFrame i := by
  rcases hx with ⟨h01, h02, h12⟩
  have h0 : x.d0 * x.d0 = x.d0 := by
    have h := congrArg Glennie.Albert.d0 hp
    simpa [Glennie.jordan_d0, h01, h02, Glennie.octDot_coordinates, Glennie.octNormSq] using h
  have h1 : x.d1 * x.d1 = x.d1 := by
    have h := congrArg Glennie.Albert.d1 hp
    simpa [Glennie.jordan_d1, h01, h12, Glennie.octDot_coordinates, Glennie.octNormSq] using h
  have h2 : x.d2 * x.d2 = x.d2 := by
    have h := congrArg Glennie.Albert.d2 hp
    simpa [Glennie.jordan_d2, h02, h12, Glennie.octDot_coordinates, Glennie.octNormSq] using h
  change x.d0 + x.d1 + x.d2 = 1 at ht
  have hn1 : 0 ≤ x.d1 := by nlinarith [sq_nonneg x.d1]
  have hn2 : 0 ≤ x.d2 := by nlinarith [sq_nonneg x.d2]
  rcases zero_or_one_of_square_eq_self _ h0 with h0 | h0
  · rcases zero_or_one_of_square_eq_self _ h1 with h1 | h1
    · have h2 : x.d2 = 1 := by linarith
      exact ⟨2, by apply Glennie.Albert.ext <;> simp_all [Glennie.standardFrame]⟩
    · have h2 : x.d2 = 0 := by linarith
      exact ⟨1, by apply Glennie.Albert.ext <;> simp_all [Glennie.standardFrame]⟩
  · have h1 : x.d1 = 0 := by linarith
    have h2 : x.d2 = 0 := by linarith
    exact ⟨0, by apply Glennie.Albert.ext <;> simp_all [Glennie.standardFrame]⟩

theorem recoveredCoordinateEquiv_diagAtom (i : Fin 3) :
    recoveredCoordinateEquiv (diagAtom i) = Glennie.standardFrame i := by
  fin_cases i <;> apply Glennie.Albert.ext <;> rfl

/-- A genuine automorphism normalizing one native atom. No frame, pair or
two-slot normalizer is supplied by this helper. -/
theorem nativeAtomNormalizer (p : Albert) (hp : IsAtom p) :
    ∃ g : NativeAlbertAutomorphism, ∃ i : Fin 3, g.linearEquiv p = diagAtom i := by
  obtain ⟨g, hg⟩ := Glennie.native_diagonalization (recoveredCoordinateEquiv p)
  have hpid : Glennie.jordan (recoveredCoordinateEquiv p) (recoveredCoordinateEquiv p) =
      recoveredCoordinateEquiv p := by
    rw [← recoveredCoordinateEquiv_jordanMul, hp.1]
  have hgid : Glennie.jordan (g.equiv (recoveredCoordinateEquiv p))
      (g.equiv (recoveredCoordinateEquiv p)) = g.equiv (recoveredCoordinateEquiv p) := by
    rw [← g.map_jordan, hpid]
  have hgt : Glennie.trace (g.equiv (recoveredCoordinateEquiv p)) = 1 := by
    rw [g.map_trace, recoveredCoordinateEquiv_trace, hp.2]
  obtain ⟨i, hi⟩ := recovered_diagonal_atom _ hg hgid hgt
  refine ⟨recoveredNativeAutomorphism g, i, ?_⟩
  apply recoveredCoordinateEquiv.injective
  change g.equiv (recoveredCoordinateEquiv p) = recoveredCoordinateEquiv (diagAtom i)
  rw [recoveredCoordinateEquiv_diagAtom]
  exact hi

/-- Core setting eq:set:pure, specialized to the exact compact Albert model. -/
theorem quadraticMap_atom (p x : Albert) (hp : IsAtom p) :
    quadraticMap p x = tracePairing p x • p := by
  obtain ⟨g, i, hgp⟩ := nativeAtomNormalizer p hp
  have hpair : tracePairing p x = (g.linearEquiv x).1 i := by
    rw [← nativeAutomorphism_pairing g p x, hgp, tracePairing_diagAtom]
  apply g.linearEquiv.injective
  rw [nativeAutomorphism_quadraticMap, map_smul, hgp, quadraticMap_diagAtom, hpair]

theorem nativeAutomorphism_atom (g : NativeAlbertAutomorphism) (p : Albert) (hp : IsAtom p) :
    IsAtom (g.linearEquiv p) := by
  constructor
  · rw [← g.preserves_product, hp.1]
  · rw [g.preserves_trace, hp.2]

end AlbertSequential.NativeAnalysis
