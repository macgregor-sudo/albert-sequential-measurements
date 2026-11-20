/- SPDX-License-Identifier: Apache-2.0 -/
module
public import CompanionIltyakovTraces
public import NativeAtomSpanning
public import NativeOrbitLifts
public import Mathlib.LinearAlgebra.Trace

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace AlbertSequential.CompanionIltyakov

open NativeAnalysis MvPolynomial

local instance : FiniteDimensional ℝ Albert := nativeBasis.finiteDimensional_of_finite

private def regularTrace : Albert →ₗ[ℝ] ℝ := (LinearMap.trace ℝ Albert).comp nativeJordanProductLinear

private theorem regularTrace_preserved (g : NativeAlbertAutomorphism) (x : Albert) :
    regularTrace (g.linearEquiv x) = regularTrace x := by
  have he : g.linearEquiv.conj (nativeJordanProductLinear x) =
      nativeJordanProductLinear (g.linearEquiv x) := by
    ext y
    change g.linearEquiv (jordanMul x (g.linearEquiv.symm y)) = jordanMul (g.linearEquiv x) y
    rw [g.preserves_product, LinearEquiv.apply_symm_apply]
  change LinearMap.trace ℝ Albert (nativeJordanProductLinear (g.linearEquiv x)) =
    LinearMap.trace ℝ Albert (nativeJordanProductLinear x)
  rw [← he, LinearMap.trace_conj']

private theorem regularTrace_diagConstant (i : Fin 3) : regularTrace (diagAtom i) = regularTrace (diagAtom 0) := by
  fin_cases i
  · rfl
  · have h := swap01AlbertAuto_diagAtom 0
    rw [Equiv.swap_apply_left] at h
    change regularTrace (diagAtom 1) = regularTrace (diagAtom 0)
    rw [← h, regularTrace_preserved]
  · have h := swap02AlbertAuto_diagAtom 0
    rw [Equiv.swap_apply_left] at h
    change regularTrace (diagAtom 2) = regularTrace (diagAtom 0)
    rw [← h, regularTrace_preserved]

private theorem regularTrace_diagonal (d : Fin 3 → ℝ) :
    regularTrace (diagonalElement d) = (∑ i, d i) * regularTrace (diagAtom 0) := by
  rw [diagonalElement_eq_sum_atoms, map_sum, Finset.sum_mul]
  simp only [map_smul, smul_eq_mul, regularTrace_diagConstant]

private theorem regularTrace_d0 : regularTrace (diagAtom 0) = 9 := by
  have hId : nativeJordanProductLinear albertUnit = LinearMap.id := by
    ext a
    change jordanMul albertUnit a = a
    exact jordanMul_albertUnit_left a
  have hdim : Module.finrank ℝ Albert = 27 := by
    rw [Module.finrank_eq_card_basis nativeBasis]
    simp
  have hUnit : regularTrace albertUnit = 27 := by
    change LinearMap.trace ℝ Albert (nativeJordanProductLinear albertUnit) = 27
    rw [hId, LinearMap.trace_id, hdim]
    norm_num
  have hDiag := regularTrace_diagonal (fun _ => 1)
  change regularTrace albertUnit = _ at hDiag
  rw [hUnit, Fin.sum_univ_three] at hDiag
  norm_num at hDiag
  linarith

/-- The ordinary native Jordan trace is one ninth of the trace of left multiplication. -/
theorem native_leftTrace_eq_nine (x : Albert) :
    LinearMap.trace ℝ Albert (nativeJordanProductLinear x) = 9 * albertTrace x := by
  obtain ⟨g, d, h⟩ := nativeDiagonalization x
  change regularTrace x = _
  rw [← regularTrace_preserved g x, ← g.preserves_trace x, h,
    regularTrace_diagonal, diagonal_trace, regularTrace_d0, mul_comm]

/-- Left Jordan multiplication on the complexification by native structure constants. -/
def complexJordanLeft (x : ComplexCoordinates) : ComplexCoordinates →ₗ[ℂ] ComplexCoordinates where
  toFun := complexJordanProduct x
  map_add' y z := by
    funext k
    simp only [complexJordanProduct, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' r y := by
    funext k
    simp only [complexJordanProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [RingHom.id_apply]
    ring

private theorem diagonalStructureConstants (i : Fin 27) :
    ∑ j, structureConstant i j j = 9 * albertTrace (nativeBasis i) := by
  have h := native_leftTrace_eq_nine (nativeBasis i)
  rw [LinearMap.trace_eq_matrix_trace ℝ nativeBasis, Matrix.trace] at h
  have he (j : Fin 27) : nativeJordanProductLinear (nativeBasis i) (nativeBasis j) =
      jordanMul (nativeBasis i) (nativeBasis j) := rfl
  simpa only [Matrix.diag_apply, LinearMap.toMatrix_apply, structureConstant,
    Module.Basis.equivFun_apply, he] using h

/-- The trace identity extends to the genuine complex coefficient product. -/
theorem complex_leftTrace_eq_nine (x : ComplexCoordinates) :
    LinearMap.trace ℂ ComplexCoordinates (complexJordanLeft x) = 9 * complexJordanTrace x := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin 27)), Matrix.trace]
  have h (j : Fin 27) : LinearMap.toMatrix (Pi.basisFun ℂ (Fin 27)) (Pi.basisFun ℂ (Fin 27))
      (complexJordanLeft x) j j = ∑ i, (structureConstant i j j : ℂ) * x i := by
    rw [LinearMap.toMatrix_apply]
    change (complexJordanProduct x ((Pi.basisFun ℂ (Fin 27)) j)) j = _
    simp [complexJordanProduct, Pi.basisFun_apply, Pi.single_apply]
  simp_rw [Matrix.diag_apply, h]
  rw [Finset.sum_comm]
  unfold complexJordanTrace
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, diagonalStructureConstants, Complex.ofReal_mul]
  simp only [Complex.ofReal_ofNat, mul_assoc]

/-- No separate trace hypothesis is needed on a complex-linear Jordan automorphism. -/
theorem complexTrace_preserved_of_product (g : ComplexCoordinates ≃ₗ[ℂ] ComplexCoordinates)
    (hg : ∀ x y, g (complexJordanProduct x y) = complexJordanProduct (g x) (g y)) (x : ComplexCoordinates) :
    complexJordanTrace (g x) = complexJordanTrace x := by
  have he : g.conj (complexJordanLeft x) = complexJordanLeft (g x) := by
    apply LinearMap.ext
    intro y
    change g (complexJordanProduct x (g.symm y)) = complexJordanProduct (g x) y
    rw [hg, LinearEquiv.apply_symm_apply]
  have ht := LinearMap.trace_conj' (complexJordanLeft x) g
  rw [he, complex_leftTrace_eq_nine, complex_leftTrace_eq_nine] at ht
  exact mul_left_cancel₀ (by norm_num : (9 : ℂ) ≠ 0) ht

theorem complexTracePolynomial_fixed (t : TraceMonomial) (g : ComplexCoordinates ≃ₗ[ℂ] ComplexCoordinates)
    (hg : ∀ x y, g (complexJordanProduct x y) = complexJordanProduct (g x) (g y))
    (x : Fin 3 → ComplexCoordinates) :
    MvPolynomial.eval (fun i => g (x i.1) i.2) (complexTracePolynomial t) =
      MvPolynomial.eval (fun i => x i.1 i.2) (complexTracePolynomial t) :=
  complexTracePolynomial_invariant t g hg (complexTrace_preserved_of_product g hg) x

/-- Polynomial invariants for the diagonal action of all complex-linear product automorphisms. -/
def complexInvariantSubalgebra : Subalgebra ℂ (MvPolynomial (Fin 3 × Fin 27) ℂ) where
  carrier := {p | ∀ (g : ComplexCoordinates ≃ₗ[ℂ] ComplexCoordinates),
    (∀ x y, g (complexJordanProduct x y) = complexJordanProduct (g x) (g y)) →
    ∀ x : Fin 3 → ComplexCoordinates,
      MvPolynomial.eval (fun i => g (x i.1) i.2) p = MvPolynomial.eval (fun i => x i.1 i.2) p}
  algebraMap_mem' r g hg x := by simp [MvPolynomial.algebraMap_eq]
  add_mem' hp hq g hg x := by simp only [map_add, hp g hg x, hq g hg x]
  mul_mem' hp hq g hg x := by simp only [map_mul, hp g hg x, hq g hg x]
  zero_mem' g hg x := by simp
  one_mem' g hg x := by simp

theorem complexTracePolynomial_mem (t : TraceMonomial) : complexTracePolynomial t ∈ complexInvariantSubalgebra :=
  complexTracePolynomial_fixed t

theorem adjoin_complexIltyakovTraces_le :
    Algebra.adjoin ℂ (Set.range (fun i : GeneratorIndex => complexTracePolynomial (traceGenerator i)) ∪
      {complexTracePolynomial omegaMonomial}) ≤ complexInvariantSubalgebra := by
  apply Algebra.adjoin_le
  rintro p (⟨i, rfl⟩ | hp)
  · exact complexTracePolynomial_mem _
  · obtain rfl : p = complexTracePolynomial omegaMonomial := hp
    exact complexTracePolynomial_mem _

theorem omegaComplexPolynomial_totalDegree : (complexTracePolynomial omegaMonomial).totalDegree = 9 := by
  apply (complexTracePolynomial_homogeneous omegaMonomial).totalDegree
  intro hz
  have hInj := MvPolynomial.map_injective (σ := Fin 3 × Fin 27) Complex.ofRealHom Complex.ofReal_injective
  have hZero : tracePolynomial omegaMonomial = 0 := hInj (by simpa only [complexTracePolynomial, map_zero] using hz)
  have hDegree := omegaPolynomial_totalDegree
  simp [hZero] at hDegree

end AlbertSequential.CompanionIltyakov
