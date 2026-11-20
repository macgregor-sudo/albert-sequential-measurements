/- SPDX-License-Identifier: Apache-2.0 -/
module
public import SpinFactorTables
public import Mathlib.LinearAlgebra.Matrix.Kronecker

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential

open scoped Matrix Kronecker

private def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
private def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

private theorem pauliX_hermitian : pauliXᴴ = pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [pauliX, Matrix.conjTranspose_apply]

private theorem pauliZ_hermitian : pauliZᴴ = pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [pauliZ, Matrix.conjTranspose_apply]

private theorem pauliX_square : pauliX * pauliX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [pauliX, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

private theorem pauliZ_square : pauliZ * pauliZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [pauliZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

private theorem pauli_anticommutator : pauliX * pauliZ + pauliZ * pauliX = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

private theorem pauliX_trace : Matrix.trace pauliX = 0 := by
  norm_num [pauliX, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

private theorem pauliZ_trace : Matrix.trace pauliZ = 0 := by
  norm_num [pauliZ, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

/-- Finite matrix generators with the Clifford relations in every dimension. -/
private theorem exists_clifford_matrices (n : ℕ) :
    ∃ (κ : Type) (hκ : Fintype κ) (hdec : DecidableEq κ),
      letI := hκ
      letI := hdec
      Nonempty κ ∧ ∃ Γ : Fin n → Matrix κ κ ℂ,
        (∀ i, (Γ i)ᴴ = Γ i) ∧ (∀ i, Γ i * Γ i = 1) ∧
        (∀ i j, i ≠ j → Γ i * Γ j + Γ j * Γ i = 0) ∧ (∀ i, Matrix.trace (Γ i) = 0) := by
  induction n with
  | zero =>
    refine ⟨Unit, inferInstance, inferInstance, inferInstance, fun i => i.elim0, ?_, ?_, ?_, ?_⟩
    all_goals intro i; exact i.elim0
  | succ n ih =>
    obtain ⟨κ, hκ, hdec, hnonempty, Γ, hHerm, hSq, hAnti, _⟩ := ih
    let := hκ
    let := hdec
    let := hnonempty
    let new : Fin (n + 1) → Matrix (κ × Fin 2) (κ × Fin 2) ℂ :=
      Fin.cases ((1 : Matrix κ κ ℂ) ⊗ₖ pauliX) (fun i => Γ i ⊗ₖ pauliZ)
    refine ⟨κ × Fin 2, inferInstance, inferInstance, inferInstance, new, ?_, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [new, Matrix.conjTranspose_kronecker, pauliX_hermitian]
      · simp [new, Matrix.conjTranspose_kronecker, pauliZ_hermitian, hHerm]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [new, ← Matrix.mul_kronecker_mul, pauliX_square]
      · simp [new, ← Matrix.mul_kronecker_mul, pauliZ_square, hSq]
    · intro i j
      refine Fin.cases ?_ (fun a => ?_) i
      · refine Fin.cases ?_ (fun b => ?_) j
        · intro h
          exact (h rfl).elim
        · intro _
          simp [new, ← Matrix.mul_kronecker_mul, ← Matrix.kronecker_add, pauli_anticommutator]
      · refine Fin.cases ?_ (fun b => ?_) j
        · intro _
          have h := pauli_anticommutator
          rw [add_comm] at h
          simp [new, ← Matrix.mul_kronecker_mul, ← Matrix.kronecker_add, h]
        · intro h
          have hab : a ≠ b := fun he => h (congrArg Fin.succ he)
          simp [new, ← Matrix.mul_kronecker_mul, ← Matrix.add_kronecker, hAnti a b hab]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [new, Matrix.trace_kronecker, pauliX_trace]
      · simp [new, Matrix.trace_kronecker, pauliZ_trace]

section VectorMatrices

variable {κ W : Type*} [Fintype κ] [DecidableEq κ] [NormedAddCommGroup W]
  [InnerProductSpace ℝ W] {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ W)
  (Γ : Fin n → Matrix κ κ ℂ)

private def cliffordVector : W →ₗ[ℝ] Matrix κ κ ℂ where
  toFun u := ∑ i, inner ℝ (b i) u • Γ i
  map_add' u v := by simp only [inner_add_right, add_smul, Finset.sum_add_distrib]
  map_smul' r u := by
    simp only [real_inner_smul_right, RingHom.id_apply, Finset.smul_sum, smul_smul]

omit [Fintype κ] [DecidableEq κ] in
private theorem cliffordVector_hermitian (hHerm : ∀ i, (Γ i)ᴴ = Γ i) (u : W) :
    (cliffordVector b Γ u)ᴴ = cliffordVector b Γ u := by
  change (∑ i, inner ℝ (b i) u • Γ i)ᴴ = ∑ i, inner ℝ (b i) u • Γ i
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_trivial, hHerm]

omit [DecidableEq κ] in
private theorem cliffordVector_trace (hTrace : ∀ i, Matrix.trace (Γ i) = 0) (u : W) :
    Matrix.trace (cliffordVector b Γ u) = 0 := by
  change Matrix.trace (∑ i, inner ℝ (b i) u • Γ i) = 0
  simp [Matrix.trace_sum, hTrace]

private theorem cliffordVector_anticommutator
    (hSq : ∀ i, Γ i * Γ i = 1)
    (hAnti : ∀ i j, i ≠ j → Γ i * Γ j + Γ j * Γ i = 0) (u v : W) :
    cliffordVector b Γ u * cliffordVector b Γ v + cliffordVector b Γ v * cliffordVector b Γ u =
      (2 * inner ℝ u v) • (1 : Matrix κ κ ℂ) := by
  have hmul (x y : W) : cliffordVector b Γ x * cliffordVector b Γ y =
      ∑ i, ∑ j, (inner ℝ (b i) x * inner ℝ (b j) y) • (Γ i * Γ j) := by
    change (∑ i, inner ℝ (b i) x • Γ i) * (∑ j, inner ℝ (b j) y • Γ j) = _
    simp only [Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm (inner ℝ (b j) y) (inner ℝ (b i) x)]
  have hswap : (∑ i, ∑ j, (inner ℝ (b i) v * inner ℝ (b j) u) • (Γ i * Γ j)) =
      ∑ i, ∑ j, (inner ℝ (b i) u * inner ℝ (b j) v) • (Γ j * Γ i) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm (inner ℝ (b j) v) (inner ℝ (b i) u)]
  have hinner : (∑ i, inner ℝ (b i) u * inner ℝ (b i) v) = inner ℝ u v := by
    calc
      _ = ∑ i, inner ℝ u (b i) * inner ℝ (b i) v := by
        apply Finset.sum_congr rfl
        intro i _
        rw [real_inner_comm u (b i)]
      _ = _ := b.sum_inner_mul_inner u v
  calc
    _ = ∑ i, ∑ j, (inner ℝ (b i) u * inner ℝ (b j) v) • (Γ i * Γ j + Γ j * Γ i) := by
      rw [hmul u v, hmul v u, hswap]
      simp only [smul_add, Finset.sum_add_distrib]
    _ = ∑ i, ((inner ℝ (b i) u * inner ℝ (b i) v) * 2) • (1 : Matrix κ κ ℂ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · rw [hSq i, ← two_smul ℝ (1 : Matrix κ κ ℂ), smul_smul]
      · intro j _ hji
        rw [hAnti i j hji.symm, smul_zero]
      · intro hi
        exact (hi (Finset.mem_univ i)).elim
    _ = _ := by rw [← Finset.sum_smul, ← Finset.sum_mul, hinner, mul_comm]

end VectorMatrices

namespace SpinFactorCoordinates

variable {E W : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] {P : UnitalJordanProduct E}
  (S : SpinFactorCoordinates P W)

include S in
/-- The actual Clifford matrices give a faithful finite-dimensional Hermitian realization. -/
theorem exists_faithfulHermitianJordanEmbedding :
    ∃ d : ℕ, Nonempty (FaithfulHermitianJordanEmbedding P d) := by
  let inclusion := S.coordinates.symm.toLinearMap.comp (LinearMap.inr ℝ ℝ W)
  let _ : FiniteDimensional ℝ W :=
    FiniteDimensional.of_injective inclusion (S.coordinates.symm.injective.comp
      (show Function.Injective (LinearMap.inr ℝ ℝ W) from LinearMap.inr_injective))
  let b := stdOrthonormalBasis ℝ W
  obtain ⟨κ, hκ, hdec, hnonempty, Γ, hHerm, hSq, hAnti, hTrace⟩ :=
    exists_clifford_matrices (Module.finrank ℝ W)
  let := hκ
  let := hdec
  let := hnonempty
  let V := cliffordVector b Γ
  let g : E →ₗ[ℝ] Matrix κ κ ℂ :=
    { toFun x := (S.coordinates x).1 • (1 : Matrix κ κ ℂ) + V (S.coordinates x).2
      map_add' x y := by
        simp only [map_add, Prod.fst_add, Prod.snd_add, add_smul]
        abel
      map_smul' r x := by
        simp only [map_smul, Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, smul_add, smul_smul,
          smul_eq_mul] }
  have hHermitian (x : E) : (g x)ᴴ = g x := by
    have hv := cliffordVector_hermitian b Γ hHerm (S.coordinates x).2
    change (V (S.coordinates x).2)ᴴ = V (S.coordinates x).2 at hv
    change ((S.coordinates x).1 • (1 : Matrix κ κ ℂ) + V (S.coordinates x).2)ᴴ =
      (S.coordinates x).1 • (1 : Matrix κ κ ℂ) + V (S.coordinates x).2
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, star_trivial,
      Matrix.conjTranspose_one, hv]
  have hunit : g P.unit = 1 := by
    change (S.coordinates P.unit).1 • (1 : Matrix κ κ ℂ) + V (S.coordinates P.unit).2 = 1
    simp [S.unit]
  have hproduct (x y : E) : g (P.product x y) = (1 / 2 : ℝ) • (g x * g y + g y * g x) := by
    let a := (S.coordinates x).1
    let c := (S.coordinates y).1
    let u := (S.coordinates x).2
    let v := (S.coordinates y).2
    change (S.coordinates (P.product x y)).1 • (1 : Matrix κ κ ℂ) + V (S.coordinates (P.product x y)).2 =
      (1 / 2 : ℝ) • ((a • 1 + V u) * (c • 1 + V v) + (c • 1 + V v) * (a • 1 + V u))
    rw [S.product x y]
    change (a * c + inner ℝ u v) • (1 : Matrix κ κ ℂ) + V (a • v + c • u) = _
    have huv := cliffordVector_anticommutator b Γ hSq hAnti u v
    calc
      _ = (1 / 2 : ℝ) • (((2 * (a * c)) • (1 : Matrix κ κ ℂ) +
          (2 : ℝ) • (a • V v + c • V u)) + (V u * V v + V v * V u)) := by
        rw [huv, map_add, map_smul, map_smul]
        module
      _ = _ := by
        simp only [mul_add, add_mul, Matrix.smul_mul, Matrix.mul_smul, mul_one, one_mul, smul_smul]
        module
  have hinjective : Function.Injective g := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    let a := (S.coordinates x).1
    let u := (S.coordinates x).2
    change a • (1 : Matrix κ κ ℂ) + V u = 0 at hx
    have htrace := congrArg Matrix.trace hx
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, cliffordVector_trace b Γ hTrace,
      add_zero, Matrix.trace_zero] at htrace
    have hreal : a * (Fintype.card κ : ℝ) = 0 := by
      simpa [Complex.real_smul] using congrArg Complex.re htrace
    have hcard : (Fintype.card κ : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card κ ≠ 0)
    have ha := (mul_eq_zero.mp hreal).resolve_right hcard
    have hV : V u = 0 := by simpa [ha] using hx
    have hscalar : (2 * inner ℝ u u) • (1 : Matrix κ κ ℂ) = 0 := by
      have h := cliffordVector_anticommutator b Γ hSq hAnti u u
      change V u * V u + V u * V u = _ at h
      simpa only [hV, zero_mul, add_zero] using h.symm
    let i : κ := Classical.choice hnonempty
    have hdiag : (2 * inner ℝ u u) • (1 : ℂ) = 0 := by
      simpa only [Matrix.smul_apply, Matrix.one_apply_eq, Matrix.zero_apply] using
        congrArg (fun A : Matrix κ κ ℂ => A i i) hscalar
    have huu : 2 * inner ℝ u u = 0 := by
      simpa only [Complex.real_smul, mul_one, Complex.ofReal_re, Complex.zero_re] using congrArg Complex.re hdiag
    have huu0 : inner ℝ u u = 0 := by linarith
    have hu : u = 0 := inner_self_eq_zero.mp huu0
    apply S.coordinates.injective
    rw [map_zero]
    exact Prod.ext ha hu
  let reindex := Matrix.reindexStarAlgEquiv ℝ ℂ (Fintype.equivFin κ)
  refine ⟨Fintype.card κ, ⟨{
    map := reindex.toAlgEquiv.toLinearEquiv.toLinearMap.comp g
    injective := reindex.injective.comp hinjective
    hermitian := fun x => ?_
    unit := ?_
    jordan := fun x y => ?_ }⟩⟩
  · change star (reindex (g x)) = reindex (g x)
    rw [← map_star, show star (g x) = g x from hHermitian x]
  · change reindex (g P.unit) = 1
    rw [hunit, map_one]
  · change reindex (g (P.product x y)) =
      (1 / 2 : ℝ) • (reindex (g x) * reindex (g y) + reindex (g y) * reindex (g x))
    rw [hproduct, map_smul, map_add, map_mul, map_mul]

include S in
/-- Every table of a finite-dimensional spin factor belongs to the finite complex class. -/
theorem canonicalProjectiveTables_subset_finiteComplex (hfr : P.FormallyReal) (n : ℕ) :
    P.canonicalProjectiveTables hfr n ⊆ finiteHilbertProjectiveTables.{0} ℂ n := by
  rintro f ⟨p, ρ, hp, hρ, hwords⟩
  obtain ⟨d, ⟨embedding⟩⟩ := S.exists_faithfulHermitianJordanEmbedding
  let φ := P.canonicalPairingFunctional hfr ρ
  have hpositive : ∀ x, 0 ≤ φ (P.product x x) :=
    (P.canonicalTraceRepresentative_positive_iff hfr φ).mp (by
      rw [P.canonicalTraceRepresentative_pairingFunctional]
      exact hρ.1)
  have hnormalized : φ P.unit = 1 :=
    (P.canonicalTraceFormOfFormallyReal_unit hfr ρ).trans hρ.2
  obtain ⟨M, _, hM⟩ := embedding.exists_projectiveRepresentation_of_embedding p hp φ hpositive hnormalized
  let A := AlbertChallenge.Bridge.ofProjectiveRepresentation M
  let R := cyclicHilbertModel A
  let hfinite := hilbertOperatorAlgebra_finiteReal (𝕜 := ℂ) (H := EuclideanSpace ℂ (Fin d))
  let _ : FiniteDimensional ℝ (CyclicHilbert A) :=
    @cyclicHilbert_finite_of_ambient (Fin n) (HilbertOperatorAlgebra ℂ (EuclideanSpace ℂ (Fin d)))
      _ _ _ _ _ _ A hfinite
  let _ : FiniteDimensional ℂ (RealHilbertComplexification (CyclicHilbert A)) := complexification_finiteDimensional
  apply mem_finiteHilbertProjectiveTables_of_model R.complexExtensionModel
  intro w
  exact (R.complexExtensionModel_probability w).trans ((cyclicHilbertModel_probability A w).trans
    ((AlbertChallenge.Bridge.ofProjectiveRepresentation_probability M w).trans ((hM w).trans (hwords w))))

end SpinFactorCoordinates

universe u v

/-- The union of the `n`-test table classes of all finite spin factors. -/
def spinFactorTableUnion (n : ℕ) : Set (Word (Fin n) → ℝ) :=
  {f | ∃ (E : Type u) (W : Type v) (hE : AddCommGroup E),
    letI := hE
    ∃ hM : Module ℝ E,
      letI := hM
      ∃ (hF : FiniteDimensional ℝ E) (hW : NormedAddCommGroup W),
        letI := hF
        letI := hW
        ∃ hI : InnerProductSpace ℝ W,
          letI := hI
          ∃ (P : UnitalJordanProduct E) (_ : SpinFactorCoordinates P W) (hfr : P.FormallyReal),
            f ∈ P.canonicalProjectiveTables hfr n}

theorem spinFactorTableUnion_subset_finiteComplex (n : ℕ) :
    spinFactorTableUnion.{u,v} n ⊆ finiteHilbertProjectiveTables.{0} ℂ n := by
  rintro f ⟨E, W, hE, hM, hF, hW, hI, P, S, hfr, hf⟩
  let := hE
  let := hM
  let := hF
  let := hW
  let := hI
  exact S.canonicalProjectiveTables_subset_finiteComplex hfr n hf

/-- Already at three tests, the union of spin-factor tables is strictly smaller. -/
theorem spinFactorTableUnion_ssubset_finiteComplex_three :
    spinFactorTableUnion.{u,v} 3 ⊂ finiteHilbertProjectiveTables.{0} ℂ 3 := by
  refine lt_of_le_of_ne (spinFactorTableUnion_subset_finiteComplex 3) ?_
  intro heq
  have hwitness : spinSeparationQutritTable ∈ spinFactorTableUnion.{u,v} 3 :=
    heq.symm ▸ spinSeparationQutritTable_mem_finiteComplex
  obtain ⟨E, W, hE, hM, hF, hW, hI, P, S, hfr, hf⟩ := hwitness
  let := hE
  let := hM
  let := hF
  let := hW
  let := hI
  exact spinSeparationQutritTable_not_mem_spinFactor S hfr hf

end AlbertSequential
