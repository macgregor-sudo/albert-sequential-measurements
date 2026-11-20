/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GeneralEJAAssociativeEnvelope
public import GeneralEJAWordTransport
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.RingTheory.Artinian.Module

/-! A faithful Jordan representation on any complex Hilbert space compresses
faithfully to a finite-dimensional reducing subspace. -/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

open scoped InnerProductSpace

variable {E H : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private def operatorEvaluation (A : Subalgebra ℝ (H →L[ℂ] H)) (v : H) : A →ₗ[ℝ] H where
  toFun a := a.val v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem exists_finite_separating_vectors (A : Subalgebra ℝ (H →L[ℂ] H))
    [FiniteDimensional ℝ A] :
    ∃ T : Finset H, ∀ a : A, (∀ v ∈ T, a.val v = 0) → a = 0 := by
  obtain ⟨T, hT⟩ := Finset.exists_inf_le fun v : H => LinearMap.ker (operatorEvaluation A v)
  refine ⟨T, fun a ha => ?_⟩
  have hinf : a ∈ T.inf fun v => LinearMap.ker (operatorEvaluation A v) :=
    Submodule.mem_finsetInf.mpr fun v hv => LinearMap.mem_ker.mpr (ha v hv)
  apply Subtype.ext
  ext v
  exact LinearMap.mem_ker.mp (hT v hinf)

private theorem orbit_span_mem (A : Subalgebra ℝ (H →L[ℂ] H))
    [FiniteDimensional ℝ A] (T : Finset H) :
    let g := fun i : Fin (Module.finrank ℝ A) × T => (Module.finBasis ℝ A i.1).val i.2.val
    ∀ (a : A) (v : T), a.val v.val ∈ Submodule.span ℂ (Set.range g) := by
  intro g a v
  let b := Module.finBasis ℝ A
  have heq : a.val v.val = ∑ i, b.repr a i • (b i).val v.val := by
    calc
      a.val v.val = operatorEvaluation A v.val a := rfl
      _ = operatorEvaluation A v.val (∑ i, b.repr a i • b i) := by rw [b.sum_repr]
      _ = _ := by simp only [map_sum, map_smul, operatorEvaluation, LinearMap.coe_mk, AddHom.coe_mk]
  rw [heq]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨(i, v), rfl⟩)

variable [CompleteSpace H]

/-- Compress a faithful complex Hilbert operator representation of a finite
real Jordan algebra to a faithful Hermitian matrix representation. -/
theorem exists_faithfulHermitianJordanEmbedding_of_operators (P : UnitalJordanProduct E)
    (f : E →ₗ[ℝ] (H →L[ℂ] H)) (hf : Function.Injective f)
    (hunit : f P.unit = 1) (hself : ∀ x, IsSelfAdjoint (f x))
    (hmul : ∀ x y, f (P.product x y) = (1 / 2 : ℝ) • (f x * f y + f y * f x)) :
    ∃ d : ℕ, Nonempty (FaithfulHermitianJordanEmbedding P d) := by
  classical
  let A := associativeEnvelope f
  let _ : FiniteDimensional ℝ A := finiteDimensional_associativeEnvelope f P hmul
  obtain ⟨T, hT⟩ := exists_finite_separating_vectors A
  let g := fun i : Fin (Module.finrank ℝ A) × T => (Module.finBasis ℝ A i.1).val i.2.val
  let W := Submodule.span ℂ (Set.range g)
  let _ : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (Set.finite_range g)
  have hOrbit : ∀ (a : A) (v : T), a.val v.val ∈ W := orbit_span_mem A T
  have hInvariant (a : A) (v : H) (hv : v ∈ W) : a.val v ∈ W := by
    refine Submodule.span_induction (p := fun x _ => a.val x ∈ W) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨⟨i, v⟩, rfl⟩
      exact hOrbit (a * Module.finBasis ℝ A i) v
    · simp
    · intro x y _ _ hx hy
      rw [map_add]
      exact W.add_mem hx hy
    · intro c x _ hx
      rw [map_smul]
      exact W.smul_mem c hx
  have hTmem (v : H) (hv : v ∈ T) : v ∈ W := hOrbit 1 ⟨v, hv⟩
  let compression : A →ₗ[ℝ] (W →ₗ[ℂ] W) :=
    { toFun := fun a => a.val.toLinearMap.restrict (hInvariant a)
      map_add' := by intro a b; ext v; rfl
      map_smul' := by intro r a; ext v; rfl }
  have hcompression_apply (a : A) (v : W) : (compression a v).val = a.val v.val := rfl
  have hcompression_one : compression 1 = 1 := by ext v; rfl
  have hcompression_mul (a b : A) : compression (a * b) = compression a * compression b := by
    ext v
    rfl
  have hcompression_inj : Function.Injective compression := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.eq_bot_iff]
    intro a ha
    refine hT a fun v hv => ?_
    have h := LinearMap.congr_fun (LinearMap.mem_ker.mp ha) (⟨v, hTmem v hv⟩ : W)
    exact congrArg Subtype.val h
  let fA : E →ₗ[ℝ] A := f.codRestrict A.toSubmodule (image_mem_associativeEnvelope f)
  have hfA : Function.Injective fA := fun _ _ h => hf (congrArg Subtype.val h)
  have hfA_unit : fA P.unit = 1 := Subtype.ext hunit
  have hfA_mul (x y : E) : fA (P.product x y) = (1 / 2 : ℝ) • (fA x * fA y + fA y * fA x) :=
    Subtype.ext (hmul x y)
  let d := Module.finrank ℂ W
  let m : (W →ₗ[ℂ] W) ≃⋆ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ :=
    LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℂ W)
  let mR : (W →ₗ[ℂ] W) →ₗ[ℝ] Matrix (Fin d) (Fin d) ℂ :=
    m.toAlgEquiv.toLinearMap.restrictScalars ℝ
  let φ := mR.comp (compression.comp fA)
  refine ⟨d, ⟨{
    map := φ
    injective := m.injective.comp (hcompression_inj.comp hfA)
    hermitian := ?_
    unit := ?_
    jordan := ?_ }⟩⟩
  · intro x
    have hsymm : (compression (fA x)).IsSymmetric := by
      intro v w
      change inner ℂ ((compression (fA x) v).val) w.val =
        inner ℂ v.val ((compression (fA x) w).val)
      simp only [hcompression_apply]
      exact (hself x).isSymmetric v.val w.val
    change star (m (compression (fA x))) = m (compression (fA x))
    rw [← map_star, LinearMap.star_eq_adjoint, hsymm.adjoint_eq]
  · change m (compression (fA P.unit)) = 1
    rw [hfA_unit, hcompression_one, map_one]
  · intro x y
    change mR (compression (fA (P.product x y))) =
      (1 / 2 : ℝ) • (m (compression (fA x)) * m (compression (fA y)) +
        m (compression (fA y)) * m (compression (fA x)))
    simp only [hfA_mul, map_smul, map_add, hcompression_mul]
    change (1 / 2 : ℝ) • (m (compression (fA x) * compression (fA y)) +
      m (compression (fA y) * compression (fA x))) = _
    rw [map_mul, map_mul]

/-- A represented finite Euclidean Jordan algebra has its exact sequential
word table in one finite complex projective model. -/
theorem exists_projectiveRepresentation_of_operators (P : UnitalJordanProduct E)
    (f : E →ₗ[ℝ] (H →L[ℂ] H)) (hf : Function.Injective f)
    (hunit : f P.unit = 1) (hself : ∀ x, IsSelfAdjoint (f x))
    (hmul : ∀ x y, f (P.product x y) = (1 / 2 : ℝ) • (f x * f y + f y * f x))
    {n : ℕ} (p : Fin n → E) (hp : ∀ i, P.product (p i) (p i) = p i)
    (ω : E →ₗ[ℝ] ℝ) (hpos : ∀ x, 0 ≤ ω (P.product x x)) (hnorm : ω P.unit = 1) :
    ∃ (d : ℕ) (M : AlbertChallenge.ProjectiveRepresentation n ℂ (EuclideanSpace ℂ (Fin d))),
      M.HasDensityState ∧
      ∀ w, M.probability w = ω (P.sequentialWordEffect p w) := by
  obtain ⟨d, ⟨embedding⟩⟩ := P.exists_faithfulHermitianJordanEmbedding_of_operators f hf hunit hself hmul
  exact ⟨d, embedding.exists_projectiveRepresentation_of_embedding p hp ω hpos hnorm⟩

end AlbertSequential.UnitalJordanProduct
