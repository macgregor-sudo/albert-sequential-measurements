/- Apache-2.0. Part of the proofs in `Solution`: transfer of the development's theorems to the
definitions of `Challenge`. -/
module

public import Bridge.Matrix
public import SubalgebraCoordsAndLine

/-!
# The Albert criterion in the Challenge's terms (thm:bridgeJ, every finite family of atoms)

For atoms `p₁, …, p_n` that do not generate `J`, some proper unital subalgebra `B` contains them.
By the subalgebra dichotomy `lem_five_sub` (case `𝕆`), `B` lies in a line subalgebra or in a
quaternionic window, which carry the supplied unital Jordan embeddings `lineCliffordEmbed` (into
`24 × 24` complex Hermitian matrices, trace form scaled by `8`) and `symplecticQuatEmbed` (into
`6 × 6`, scaled by `2`). The images `P_i` of the atoms are Hermitian idempotents that do not depend
on the state; for each state `ρ`, `suppliedEmbedding_scaled_state_transport` gives a density matrix
`σ` with `Re tr(σ · Q₁⋯Q_m⋯Q₁) = Pr_ρ(w)` for every word. `matrixRepresentation` turns `(P, σ)`
into a Challenge `ProjectiveRepresentation` on `ℂ^d`, whose state is `T ↦ tr(σ T)`.
The converse directions use the exclusion `no_representation_bridge` and the speciality
equivalence `proper_iff_special`. This is the same route as the development's
`cor_helly_operational_if`, without the Helly step, which is not needed when the whole family lies
in one proper subalgebra.
-/

@[expose] public section
noncomputable section

namespace AlbertChallenge.Bridge

open AlbertChallenge AlbertSequential.MatchingModels
open scoped MatrixOrder ComplexOrder

local notation "E" d => EuclideanSpace ℂ (Fin d)

/-- `LinearMap.trace` of the operator of a matrix is the matrix trace. -/
theorem trace_matToCLM {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    LinearMap.trace ℂ (E d) ((matToCLM A : (E d) →L[ℂ] (E d)) : (E d) →ₗ[ℂ] (E d)) =
      Matrix.trace A := by
  have h : ((matToCLM A : (E d) →L[ℂ] (E d)) : (E d) →ₗ[ℂ] (E d)) =
      Matrix.toLin (EuclideanSpace.basisFun (Fin d) ℂ).toBasis
        (EuclideanSpace.basisFun (Fin d) ℂ).toBasis A := by
    rw [← Matrix.toEuclideanLin_eq_toLin_orthonormal]
    rfl
  rw [h, Matrix.trace_toLin_eq]

/-- The state of `matrixRepresentation` is `T ↦ tr(σ T)` with `σ` the operator of the density
matrix. -/
theorem matrixRepresentation_state {n d : ℕ} (P : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (hherm : ∀ i, (P i).IsHermitian) (hidem : ∀ i, P i * P i = P i)
    (σ : Matrix (Fin d) (Fin d) ℂ) (hσ : σ.PosSemidef) (htr : Matrix.trace σ = 1)
    (T : (E d) →L[ℂ] (E d)) :
    (matrixRepresentation P hherm hidem σ hσ htr).state T =
      LinearMap.trace ℂ (E d) ((matToCLM σ * T : (E d) →L[ℂ] (E d)) : (E d) →ₗ[ℂ] (E d)) := by
  have hT : matToCLM σ * T = matToCLM (σ * clmMatrix T) := by
    rw [matToCLM_mul, matToCLM_clmMatrix]
    rfl
  rw [hT, trace_matToCLM]
  rfl

/-- The operator of a positive semidefinite matrix is a positive operator. -/
theorem matToCLM_isPositive {d : ℕ} {σ : Matrix (Fin d) (Fin d) ℂ} (hσ : σ.PosSemidef) :
    (matToCLM σ).IsPositive := by
  have h := (Matrix.isPositive_toEuclideanLin_iff (A := σ)).mpr hσ
  exact (ContinuousLinearMap.isPositive_toLinearMap_iff _).mp h

/-- Atoms that do not generate `J` lie in a proper subalgebra of the development. -/
theorem exists_proper_native_of_not_generates {n : ℕ} (p : Fin n → Albert)
    (hg : ¬ Generates p) :
    ∃ B : AlbertSequential.NativeJordanSubalgebra,
      B.carrier < (AlbertSequential.H3Subalgebra .O).carrier ∧ ∀ i, toT (p i) ∈ B.carrier := by
  rw [← generates_toT] at hg
  unfold AlbertSequential.GeneratesAlbert AlbertSequential.InGeneratedAlgebra at hg
  push Not at hg
  obtain ⟨x, B, hpB, hx⟩ := hg
  refine ⟨B, ?_, hpB⟩
  rw [AlbertSequential.H3Subalgebra_O_eq_top]
  exact lt_of_le_of_ne le_top fun h => hx (h ▸ trivial)

/-- One family of Hermitian idempotent matrices on `ℂ^d`, `d ∈ {6, 24}`, and for each state a
density matrix reproducing every word, from a proper subalgebra containing the atoms. -/
theorem matrix_data_of_proper {n : ℕ} (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i))
    (B : AlbertSequential.NativeJordanSubalgebra)
    (hlt : B.carrier < (AlbertSequential.H3Subalgebra .O).carrier)
    (hpB : ∀ i, toT (p i) ∈ B.carrier) :
    ∃ (d : ℕ) (P : Fin n → Matrix (Fin d) (Fin d) ℂ), (d = 6 ∨ d = 24) ∧
      (∀ i, (P i).IsHermitian) ∧ (∀ i, P i * P i = P i) ∧
      ∀ ρ, IsDensity ρ → ∃ σ : Matrix (Fin d) (Fin d) ℂ, σ.PosSemidef ∧ Matrix.trace σ = 1 ∧
        ∀ w : Word n, (Matrix.trace (σ * AlbertSequential.wordOperator P w)).re =
          wordProbability p ρ w := by
  -- the construction from a supplied embedding of a subalgebra containing `B`
  have key : ∀ (C : AlbertSequential.NativeJordanSubalgebra) (d : ℕ)
      (ι : AlbertSequential.SuppliedHermitianEmbedding C d) (c : ℝ), 0 < c →
      (∀ x y : C.carrier,
        (Matrix.trace (ι.map x * ι.map y)).re = c * AlbertSequential.tracePairing x.1 y.1) →
      (hpC : ∀ i, toT (p i) ∈ C.carrier) → (d = 6 ∨ d = 24) →
      ∃ (d' : ℕ) (P : Fin n → Matrix (Fin d') (Fin d') ℂ), (d' = 6 ∨ d' = 24) ∧
        (∀ i, (P i).IsHermitian) ∧ (∀ i, P i * P i = P i) ∧
        ∀ ρ, IsDensity ρ → ∃ σ : Matrix (Fin d') (Fin d') ℂ, σ.PosSemidef ∧ Matrix.trace σ = 1 ∧
          ∀ w : Word n, (Matrix.trace (σ * AlbertSequential.wordOperator P w)).re =
            wordProbability p ρ w := by
    intro C d ι c hc htr hpC hd
    refine ⟨d, fun i => ι.map ⟨toT (p i), hpC i⟩, hd, fun i => ι.hermitian _, fun i => ?_,
      fun ρ hρ => ?_⟩
    · have hj := ι.jordan ⟨toT (p i), hpC i⟩ ⟨toT (p i), hpC i⟩
      have hp1 : (⟨AlbertSequential.jordanMul (toT (p i)) (toT (p i)),
          C.product_mem _ (hpC i) _ (hpC i)⟩ : C.carrier) = ⟨toT (p i), hpC i⟩ :=
        Subtype.ext ((isAtom_toT (p i)).mpr (hp i)).1
      rw [hp1] at hj
      set Q := ι.map ⟨toT (p i), hpC i⟩
      have h2 : (1 / 2 : ℝ) • (Q * Q + Q * Q) = Q * Q := by module
      rw [h2] at hj
      exact hj.symm
    · obtain ⟨σ, ⟨hσ, hσtr⟩, hstats⟩ :=
        AlbertSequential.suppliedEmbedding_scaled_state_transport C d ι c hc htr (toT ρ)
          ((isDensity_toT ρ).mpr hρ)
      refine ⟨σ, hσ, hσtr, fun w => ?_⟩
      rw [← wordProbability_toT]
      exact hstats n (fun i => toT (p i)) hpC w
  rcases AlbertSequential.lem_five_sub .O B hlt with ⟨q, hq, _, hline⟩ | ⟨Q, hQ⟩
  · exact key _ 24 (AlbertSequential.lineCliffordEmbed q hq) 8 (by norm_num)
      (AlbertSequential.lineCliffordEmbed_tracePairing q hq) (fun i => hline (hpB i)) (Or.inr rfl)
  · exact key _ 6 (AlbertSequential.symplecticQuatEmbed Q) 2 (by norm_num)
      (AlbertSequential.symplecticQuatEmbed_tracePairing Q) (fun i => hQ (hpB i)) (Or.inl rfl)

/-- The diagonal atom `diag(1, 0, 0)` is a state, so the set of states is nonempty. -/
theorem exists_isDensity : ∃ ρ : Albert, IsDensity ρ :=
  ⟨AlbertSequential.diagAtom 0,
    isDensity_of_isAtom ((isAtom_toT _).mp (AlbertSequential.diagAtom_isAtom 0))⟩

/-- **The Albert criterion, all finite families** (thm:bridgeJ, (1) ⇔ (2) ⇔ (3)). -/
theorem albert_criterion_bridge {n : ℕ} (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i)) :
    (¬ Generates p ↔ ∃ B : JordanSubalgebra, (∀ i, p i ∈ B.carrier) ∧ B.IsSpecial) ∧
    (¬ Generates p ↔ ∃ d : ℕ, (d = 6 ∨ d = 24) ∧
      ∃ M₀ : ProjectiveRepresentation n ℂ (EuclideanSpace ℂ (Fin d)), ∀ ρ, IsDensity ρ →
        ∃ M : ProjectiveRepresentation n ℂ (EuclideanSpace ℂ (Fin d)),
          M.projection = M₀.projection ∧ M.HasDensityState ∧
          ∀ w : Word n, M.probability w = wordProbability p ρ w) ∧
    (¬ Generates p ↔ ∃ ρ, IsDensity ρ ∧ ¬ NoRepresentationOn.{0} p ρ Set.univ) := by
  -- (2) from non-generation
  have h2 : ¬ Generates p → ∃ d : ℕ, (d = 6 ∨ d = 24) ∧
      ∃ M₀ : ProjectiveRepresentation n ℂ (E d), ∀ ρ, IsDensity ρ →
        ∃ M : ProjectiveRepresentation n ℂ (E d),
          M.projection = M₀.projection ∧ M.HasDensityState ∧
          ∀ w : Word n, M.probability w = wordProbability p ρ w := by
    intro hg
    obtain ⟨B, hlt, hpB⟩ := exists_proper_native_of_not_generates p hg
    obtain ⟨d, P, hd, hherm, hidem, hρ⟩ := matrix_data_of_proper p hp B hlt hpB
    obtain ⟨ρ₀, hρ₀⟩ := exists_isDensity
    obtain ⟨σ₀, hσ₀, htr₀, -⟩ := hρ ρ₀ hρ₀
    refine ⟨d, hd, matrixRepresentation P hherm hidem σ₀ hσ₀ htr₀, fun ρ hρd => ?_⟩
    obtain ⟨σ, hσ, htr, hw⟩ := hρ ρ hρd
    refine ⟨matrixRepresentation P hherm hidem σ hσ htr, rfl,
      ⟨matToCLM σ, matToCLM_isPositive hσ, by rw [trace_matToCLM, htr],
        matrixRepresentation_state P hherm hidem σ hσ htr⟩, fun w => ?_⟩
    rw [matrixRepresentation_probability]
    exact hw w
  -- a representation from one state excludes generation
  have h3 : (∃ ρ, IsDensity ρ ∧ ¬ NoRepresentationOn.{0} p ρ Set.univ) → ¬ Generates p := by
    rintro ⟨ρ, _, hno⟩ hg
    exact hno (no_representation_bridge.{0} p hp hg ρ)
  have h23 : (∃ d : ℕ, (d = 6 ∨ d = 24) ∧
      ∃ M₀ : ProjectiveRepresentation n ℂ (E d), ∀ ρ, IsDensity ρ →
        ∃ M : ProjectiveRepresentation n ℂ (E d),
          M.projection = M₀.projection ∧ M.HasDensityState ∧
          ∀ w : Word n, M.probability w = wordProbability p ρ w) →
      ∃ ρ, IsDensity ρ ∧ ¬ NoRepresentationOn.{0} p ρ Set.univ := by
    rintro ⟨d, _, _, hrep⟩
    obtain ⟨ρ, hρ⟩ := exists_isDensity
    obtain ⟨M, _, _, hw⟩ := hrep ρ hρ
    exact ⟨ρ, hρ, fun hno => hno.1 ℂ (E d) M (fun w _ => hw w)⟩
  refine ⟨⟨fun hg => ?_, fun ⟨B, hpB, d, f, hd, hinj, hherm, hunit, hjor⟩ => ?_⟩,
    ⟨h2, fun h => h3 (h23 h)⟩, ⟨fun hg => h23 (h2 hg), h3⟩⟩
  · -- (1): a proper subalgebra containing the atoms, embedded by `proper_iff_special`
    obtain ⟨B, hlt, hpB⟩ := exists_proper_native_of_not_generates p hg
    have hne : B ≠ ⊤ := by
      rintro rfl
      rw [AlbertSequential.H3Subalgebra_O_eq_top] at hlt
      exact lt_irrefl _ hlt
    obtain ⟨d, hd, ⟨ι⟩⟩ := (AlbertSequential.proper_iff_special B).mp hne
    refine ⟨ofNative B, hpB, d, ι.map, hd, ι.injective, ι.hermitian, ι.unit, fun x y => ?_⟩
    have hxy : (⟨jordanMul x.1 y.1, (ofNative B).mul_mem x.1 x.2 y.1 y.2⟩ : (ofNative B).carrier) =
        ⟨AlbertSequential.jordanMul x.1 y.1, B.product_mem x.1 x.2 y.1 y.2⟩ :=
      Subtype.ext (jordanMul_eq x.1 y.1)
    rw [hxy]
    exact ι.jordan x y
  · -- a special subalgebra containing the atoms is proper
    intro hg
    let ι : AlbertSequential.SuppliedHermitianEmbedding (toNative B) d :=
      { map := f, injective := hinj, hermitian := hherm, unit := hunit,
        jordan := fun x y => by
          have hxy : (⟨AlbertSequential.jordanMul x.1 y.1, (toNative B).product_mem x.1 x.2 y.1 y.2⟩ :
              (toNative B).carrier) = ⟨jordanMul x.1 y.1, B.mul_mem x.1 x.2 y.1 y.2⟩ :=
            Subtype.ext (jordanMul_eq x.1 y.1).symm
          rw [hxy]
          exact hjor x y }
    have hne := (AlbertSequential.proper_iff_special (toNative B)).mpr ⟨d, hd, ⟨ι⟩⟩
    apply hne
    apply AlbertSequential.nativeJordanSubalgebra_ext
    exact hg B hpB

end AlbertChallenge.Bridge
