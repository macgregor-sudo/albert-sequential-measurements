/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilityGaussian
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.MvPolynomial.DeterminantalIdeal

/-! The rank of the Gaussian Gram sample from companion Proposition 5.1. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open MeasureTheory MvPolynomial Set
open scoped BigOperators

private theorem ae_mvPolynomial_eval_ne_zero_fin (μ : Measure ℂ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (n : ℕ) (p : MvPolynomial (Fin n) ℂ) (hp : p ≠ 0) :
    ∀ᵐ z ∂(Measure.pi fun _ : Fin n => μ), eval z p ≠ 0 := by
  induction n with
  | zero =>
    let e := isEmptyAlgEquiv ℂ (Fin 0)
    have he : e p ≠ 0 := by intro h; exact hp (e.injective (h.trans e.map_zero.symm))
    have hc : p = C (e p) := by
      simpa only [e, isEmptyAlgEquiv_symm_apply] using (e.symm_apply_apply p).symm
    rw [hc]
    exact Filter.Eventually.of_forall fun z => by simpa only [eval_C] using he
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0
    let ν := Measure.pi fun _ : Fin n => μ
    have hpₑ : MeasurePreserving e (Measure.pi fun _ : Fin (n + 1) => μ) (μ.prod ν) :=
      measurePreserving_piFinSuccAbove _ 0
    have hpre : MeasurableSet {z : Fin (n + 1) → ℂ | eval z p ≠ 0} :=
      (isClosed_eq (continuous_eval p) continuous_const).isOpen_compl.measurableSet
    have hsection : MeasurableSet {z : ℂ × (Fin n → ℂ) | eval (e.symm z) p ≠ 0} :=
      e.symm.measurable hpre
    rw [← (hpₑ.symm e).map_eq, ae_map_iff e.symm.measurable.aemeasurable hpre,
      Measure.ae_prod_iff_ae_ae hsection, Measure.ae_ae_comm hsection]
    let q := finSuccEquiv ℂ n p
    have hq : q ≠ 0 := by
      intro h
      exact hp ((finSuccEquiv ℂ n).injective (h.trans (finSuccEquiv ℂ n).map_zero.symm))
    have hc : q.coeff q.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree, ne_eq, Polynomial.leadingCoeff_eq_zero]
      exact hq
    filter_upwards [ih (q.coeff q.natDegree) hc] with w hw
    have hqw : Polynomial.map (eval w) q ≠ 0 := by
      intro hz
      exact hw (by rw [← Polynomial.coeff_map, hz, Polynomial.coeff_zero])
    have hf := (Polynomial.finite_setOfPred_isRoot hqw).measure_zero μ
    rw [ae_iff]
    have hh : {x : ℂ | ¬ eval (e.symm (x, w)) p ≠ 0} =
        {x : ℂ | Polynomial.IsRoot (Polynomial.map (eval w) q) x} := by
      ext x
      change (¬eval (e.symm (x, w)) p ≠ 0) ↔ Polynomial.IsRoot (Polynomial.map (eval w) q) x
      rw [not_ne_iff, Polynomial.IsRoot]
      have he (x : ℂ) : e.symm (x, w) = Fin.cons x w := by
        simp [e]
      rw [he, eval_eq_eval_mv_eval']
    rw [hh]
    exact hf

/-- A nonzero complex polynomial vanishes with probability zero under
independent non-atomic coordinates. -/
theorem ae_mvPolynomial_eval_ne_zero {ι : Type*} [Fintype ι] (μ : Measure ℂ)
    [IsProbabilityMeasure μ] [NullSingletonClass μ] (p : MvPolynomial ι ℂ) (hp : p ≠ 0) :
    ∀ᵐ z ∂(Measure.pi fun _ : ι => μ), eval z p ≠ 0 := by
  let e := Fintype.equivFin ι
  have he : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : Fin (Fintype.card ι) => ℂ) e)
      (Measure.pi fun _ : ι => μ) (Measure.pi fun _ : Fin (Fintype.card ι) => μ) :=
    measurePreserving_piCongrLeft (fun _ => μ) e
  let q := renameEquiv ℂ e p
  have hq : q ≠ 0 := by
    intro hz
    exact hp ((renameEquiv ℂ e).injective (hz.trans (renameEquiv ℂ e).map_zero.symm))
  have h := ae_mvPolynomial_eval_ne_zero_fin μ (Fintype.card ι) q hq
  have h' := ae_of_ae_map he.measurable.aemeasurable (he.map_eq.symm ▸ h)
  filter_upwards [h'] with z hz
  change eval ((MeasurableEquiv.piCongrLeft (fun _ => ℂ) e) z) (rename e p) ≠ 0 at hz
  rw [eval_rename] at hz
  simpa only [Function.comp_def, MeasurableEquiv.piCongrLeft_apply_apply, Equiv.symm_apply_apply] using hz

/-- Flatten two finite independent coordinate products into the product-index measure. -/
theorem measurePreserving_uncurry_product {I J : Type*} [Fintype I] [Fintype J]
    (μ : Measure ℂ) [IsProbabilityMeasure μ] :
    MeasurePreserving (fun x : I → J → ℂ => fun p : I × J => x p.1 p.2)
      (Measure.pi fun _ : I => Measure.pi fun _ : J => μ)
      (Measure.pi fun _ : I × J => μ) := by
  have hM : Measurable (fun x : I → J → ℂ => fun p : I × J => x p.1 p.2) :=
    measurable_pi_iff.mpr fun p => (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
  refine ⟨hM, (Measure.pi_eq (μ := fun _ : I × J => μ) fun s hs => ?_).symm⟩
  rw [Measure.map_apply hM (MeasurableSet.pi (Set.to_countable _) fun p _ => hs p)]
  have hset : (fun x : I → J → ℂ => fun p : I × J => x p.1 p.2) ⁻¹' pi univ s =
      pi univ (fun i : I => pi univ fun j : J => s (i, j)) := by ext x; simp [Set.mem_pi]
  rw [hset, Measure.pi_pi, ← Finset.univ_product_univ, Finset.prod_product]
  simp_rw [Measure.pi_pi]

/-- The exact complex Gram sample has full rectangular rank almost surely
before and after normalization. -/
theorem ae_rank_normalizedComplexGram (k : ℕ) :
    ∀ᵐ Z ∂standardComplexGaussianMatrix k, (normalizedComplexGram k Z).rank = min 3 k := by
  classical
  let n := min 3 k
  let i : Fin n → Fin 3 := Fin.castLE (Nat.min_le_left 3 k)
  let j : Fin n → Fin k := Fin.castLE (Nat.min_le_right 3 k)
  let p := Matrix.mvPolynomialMinor ℂ i j
  have h_eval (Z : Matrix (Fin 3) (Fin k) ℂ) :
      eval (fun q : Fin 3 × Fin k => Z q.1 q.2) p = (Z.submatrix i j).det := by
    let ev := eval (fun q : Fin 3 × Fin k => Z q.1 q.2)
    change ev (Matrix.mvPolynomialMinor ℂ i j) = _
    rw [Matrix.mvPolynomialMinor_eq_det_submatrix, RingHom.map_det]
    congr 1
    ext a b
    change ev (X (i a, j b)) = Z (i a) (j b)
    exact eval_X _
  have hp : p ≠ 0 := by
    intro hz
    let Z : Matrix (Fin 3) (Fin k) ℂ := fun a b => if a.val = b.val then 1 else 0
    have he : Z.submatrix i j = 1 := by
      ext a b
      change (if a.val = b.val then (1 : ℂ) else 0) = _
      simp [Matrix.one_apply, Fin.ext_iff]
    simpa [hz, he] using h_eval Z
  have h := ae_mvPolynomial_eval_ne_zero standardComplexGaussian p hp
  have hflat := measurePreserving_uncurry_product (I := Fin 3) (J := Fin k) standardComplexGaussian
  have hZ := ae_of_ae_map hflat.measurable.aemeasurable (hflat.map_eq.symm ▸ h)
  filter_upwards [hZ] with Z hz
  change eval (fun q : Fin 3 × Fin k => Z q.1 q.2) p ≠ 0 at hz
  rw [h_eval Z] at hz
  have hle : n ≤ Z.rank := by
    simpa [Matrix.rank_of_det_ne_zero hz] using Matrix.rank_submatrix_le Z i j
  have hge : Z.rank ≤ n := by
    apply le_min
    · simpa using Matrix.rank_le_card_height Z
    · simpa using Matrix.rank_le_card_width Z
  rw [rank_normalizedComplexGram, le_antisymm hge hle]

/-- Full rank of a finite square complex matrix is equivalent to a nonzero determinant. -/
theorem complexMatrix_rank_eq_card_iff_det_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) : M.rank = Fintype.card ι ↔ M.det ≠ 0 := by
  constructor
  · intro hr
    have hs : Function.Surjective M.mulVec := Matrix.mulVec_surjective_iff_rank_eq_card.mpr hr
    have hi : Function.Injective M.mulVec :=
      LinearMap.injective_iff_surjective.mpr (show Function.Surjective M.mulVecLin from hs)
    exact ((Matrix.isUnit_iff_isUnit_det M).mp (Matrix.mulVec_injective_iff_isUnit.mp hi)).ne_zero
  · exact Matrix.rank_of_det_ne_zero

/-- The exact two-column output probability is almost surely carried by rank-two matrices. -/
theorem ae_inducedComplexStateLaw_two_rank :
    ∀ᵐ M ∂inducedComplexStateLaw 2, M.rank = 2 := by
  let rows : Fin 2 → Fin 3 := Fin.castLE (by decide : 2 ≤ 3)
  let p := Matrix.mvPolynomialMinor ℂ rows (id : Fin 2 → Fin 2)
  have h_eval (Z : Matrix (Fin 3) (Fin 2) ℂ) :
      eval (fun q : Fin 3 × Fin 2 => Z q.1 q.2) p = (Z.submatrix rows id).det := by
    let ev := eval (fun q : Fin 3 × Fin 2 => Z q.1 q.2)
    change ev (Matrix.mvPolynomialMinor ℂ rows id) = _
    rw [Matrix.mvPolynomialMinor_eq_det_submatrix, RingHom.map_det]
    congr 1
    ext a b
    change ev (X (rows a, b)) = Z (rows a) b
    exact eval_X _
  have hp : p ≠ 0 := by
    intro hz
    let Z : Matrix (Fin 3) (Fin 2) ℂ := fun a b => if a.val = b.val then 1 else 0
    have he : Z.submatrix rows id = 1 := by
      ext a b
      change (if a.val = b.val then (1 : ℂ) else 0) = _
      simp [Matrix.one_apply, Fin.ext_iff]
    simpa [hz, he] using h_eval Z
  have hflat := measurePreserving_uncurry_product (I := Fin 3) (J := Fin 2) standardComplexGaussian
  have hpAE := ae_mvPolynomial_eval_ne_zero standardComplexGaussian p hp
  have hA : ∀ᵐ Z ∂standardComplexGaussianMatrix 2, (Z.submatrix rows id).det ≠ 0 := by
    have h := ae_of_ae_map hflat.measurable.aemeasurable (hflat.map_eq.symm ▸ hpAE)
    filter_upwards [h] with Z hz
    change eval (fun q : Fin 3 × Fin 2 => Z q.1 q.2) p ≠ 0 at hz
    rwa [← h_eval Z]
  have hM (Z : Matrix (Fin 3) (Fin 2) ℂ) :
      (normalizedComplexGram 2 Z).submatrix rows rows =
        (Z * Z.conjTranspose).trace⁻¹ • (Z.submatrix rows id * (Z.submatrix rows id).conjTranspose) := by
    ext i j
    rfl
  let S := {M : ComplexMatrix 3 | M.det = 0 ∧ (M.submatrix rows rows).det ≠ 0}
  have hs : MeasurableSet S := by
    have hd : Continuous (fun M : ComplexMatrix 3 => M.det) := continuous_id.matrix_det
    have hmin : Continuous (fun M : ComplexMatrix 3 => (M.submatrix rows rows).det) :=
      (continuous_id.matrix_submatrix rows rows).matrix_det
    exact (isClosed_eq hd continuous_const).measurableSet.inter
      (isClosed_eq hmin continuous_const).isOpen_compl.measurableSet
  have hsAE : ∀ᵐ M ∂inducedComplexStateLaw 2, M ∈ S := by
    unfold inducedComplexStateLaw normalizedGramPushforward
    change ∀ᵐ M ∂(standardComplexGaussianMatrix 2).map (normalizedComplexGram 2),
      M.det = 0 ∧ (M.submatrix rows rows).det ≠ 0
    rw [ae_map_iff (measurable_normalizedComplexGram 2).aemeasurable hs]
    filter_upwards [hA, ae_rank_normalizedComplexGram 2, ae_gaussianGram_trace_ne_zero 2 (by decide)] with Z hZ hR ht
    refine ⟨?_, ?_⟩
    · by_contra hd
      have he := (complexMatrix_rank_eq_card_iff_det_ne_zero (normalizedComplexGram 2 Z)).mpr hd
      rw [hR, Fintype.card_fin] at he
      norm_num at he
    · rw [hM, Matrix.det_smul, Matrix.det_mul, Matrix.det_conjTranspose]
      exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero ht)) (mul_ne_zero hZ (star_ne_zero.mpr hZ))
  filter_upwards [hsAE] with M hm
  obtain ⟨hdet, hminor⟩ := hm
  have hlo : 2 ≤ M.rank := by
    simpa [Matrix.rank_of_det_ne_zero hminor] using Matrix.rank_submatrix_le M rows rows
  have hhi : M.rank ≤ 3 := M.rank_le_height
  have hne : M.rank ≠ 3 := fun h =>
    (complexMatrix_rank_eq_card_iff_det_ne_zero M).mp (by simpa using h) hdet
  omega

end AlbertSequential.WindowProbability
