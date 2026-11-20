/- SPDX-License-Identifier: Apache-2.0
Original owner-directed Lean from the frozen 2026-11-17 ProjectiveTableFieldEquivalence return. -/
module
public import FieldDimensionTableClasses
public import CyclicFiniteDimension

/-! Exact prop:field(a): existential table classes agree over R,C,H, both
finite and arbitrary dimensional. Carrier universe is arbitrary; transformed
carriers are explicitly constructed and need not equal the input Hilbert space.
No resizing across unequal universes or fixed-dimension equality is claimed. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
universe u
namespace AlbertSequential

section Packaging
variable {n : ℕ} {f : Word (Fin n) → ℝ}
variable {𝕜 : Type} [RCLike 𝕜] {H : Type u} [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]

theorem mem_hilbertProjectiveTables_of_model (M : HilbertProjectiveData (Fin n) 𝕜 H)
    (hf : ∀ w, M.toAlgebraic.probability w = f w) :
    f ∈ hilbertProjectiveTables.{u} 𝕜 n :=
  ⟨H, inferInstance, inferInstance, inferInstance, M, hf⟩

theorem mem_finiteHilbertProjectiveTables_of_model [FiniteDimensional 𝕜 H]
    (M : HilbertProjectiveData (Fin n) 𝕜 H)
    (hf : ∀ w, M.toAlgebraic.probability w = f w) :
    f ∈ finiteHilbertProjectiveTables.{u} 𝕜 n :=
  ⟨H, inferInstance, inferInstance, inferInstance, inferInstance, M, hf⟩
end Packaging

section QuaternionicPackaging
variable {ι : Type*} {n : ℕ} {f : Word (Fin n) → ℝ}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {Q Q' : QuaternionicOperatorStructure H}

def QuaternionicProjectiveData.castStructure (h : Q = Q')
    (M : QuaternionicProjectiveData ι Q) : QuaternionicProjectiveData ι Q' := h ▸ M

theorem QuaternionicProjectiveData.castStructure_probability (h : Q = Q')
    (M : QuaternionicProjectiveData ι Q) (w : Word ι) :
    (M.castStructure h).toAlgebraic.probability w = M.toAlgebraic.probability w := by
  cases h
  rfl

theorem mem_quaternionicProjectiveTables_of_model (S : RightQuaternionicHilbertStructure H)
    (M : QuaternionicProjectiveData (Fin n) S.toOperatorStructure)
    (hf : ∀ w, M.toAlgebraic.probability w = f w) :
    f ∈ quaternionicProjectiveTables.{u} n :=
  ⟨H, inferInstance, inferInstance, inferInstance, S, M, hf⟩

theorem mem_finiteQuaternionicProjectiveTables_of_model (S : RightQuaternionicHilbertStructure H)
    (hfinite : letI := S.oppositeModule
      FiniteDimensional (Quaternion ℝ)ᵐᵒᵖ H)
    (M : QuaternionicProjectiveData (Fin n) S.toOperatorStructure)
    (hf : ∀ w, M.toAlgebraic.probability w = f w) :
    f ∈ finiteQuaternionicProjectiveTables.{u} n :=
  ⟨H, inferInstance, inferInstance, inferInstance, S, hfinite, M, hf⟩

/-- The finite RIGHT-quaternionic premise is the literal accepted source module.
It supplies the real-finite premise of the frozen GNS corollary without replacing it. -/
theorem RightQuaternionicHilbertStructure.cyclicHilbert_finite
    (S : RightQuaternionicHilbertStructure H)
    (hfinite : letI := S.oppositeModule
      FiniteDimensional (Quaternion ℝ)ᵐᵒᵖ H)
    (M : QuaternionicProjectiveData ι S.toOperatorStructure) :
    FiniteDimensional ℝ (CyclicHilbert M.toAlgebraic) := by
  let : FiniteDimensional ℝ H := S.real_finiteDimensional_of_opposite hfinite
  exact M.cyclicHilbert_finite_of_real
end QuaternionicPackaging

section ArbitraryTables
variable {n : ℕ} {f : Word (Fin n) → ℝ}

theorem complex_projectiveTable_is_real (h : f ∈ hilbertProjectiveTables.{u} ℂ n) :
    f ∈ hilbertProjectiveTables.{u} ℝ n := by
  rcases h with ⟨H,hN,h⟩
  let := hN
  rcases h with ⟨hI,h⟩
  let := hI
  rcases h with ⟨hC,M,hf⟩
  let := hC
  apply mem_hilbertProjectiveTables_of_model (cyclicHilbertModel M.toAlgebraic)
  intro w
  exact (cyclicHilbertModel_probability M.toAlgebraic w).trans (hf w)

theorem quaternionic_projectiveTable_is_real (h : f ∈ quaternionicProjectiveTables.{u} n) :
    f ∈ hilbertProjectiveTables.{u} ℝ n := by
  rcases h with ⟨H,hN,h⟩
  let := hN
  rcases h with ⟨hI,h⟩
  let := hI
  rcases h with ⟨hC,S,M,hf⟩
  let := hC
  apply mem_hilbertProjectiveTables_of_model (cyclicHilbertModel M.toAlgebraic)
  intro w
  exact (cyclicHilbertModel_probability M.toAlgebraic w).trans (hf w)

theorem real_projectiveTable_is_complex (h : f ∈ hilbertProjectiveTables.{u} ℝ n) :
    f ∈ hilbertProjectiveTables.{u} ℂ n := by
  rcases h with ⟨H,hN,h⟩
  let := hN
  rcases h with ⟨hI,h⟩
  let := hI
  rcases h with ⟨hC,M,hf⟩
  let := hC
  apply mem_hilbertProjectiveTables_of_model M.complexExtensionModel
  intro w
  exact (M.complexExtensionModel_probability w).trans (hf w)

theorem real_projectiveTable_is_quaternionic (h : f ∈ hilbertProjectiveTables.{u} ℝ n) :
    f ∈ quaternionicProjectiveTables.{u} n := by
  rcases h with ⟨H,hN,h⟩
  let := hN
  rcases h with ⟨hI,h⟩
  let := hI
  rcases h with ⟨hC,M,hf⟩
  let := hC
  let Q := fourCopyQuaternionicStructure (H := H)
  let S := Q.toRightHilbertStructure
  let MQ : QuaternionicProjectiveData (Fin n) S.toOperatorStructure :=
    M.quaternionExtensionModel.castStructure Q.toOperatorStructure_toRightHilbertStructure.symm
  apply mem_quaternionicProjectiveTables_of_model S MQ
  intro w
  exact (M.quaternionExtensionModel.castStructure_probability
    Q.toOperatorStructure_toRightHilbertStructure.symm w).trans
      ((M.quaternionExtensionModel_probability w).trans (hf w))
end ArbitraryTables

section FiniteTables
variable {n : ℕ} {f : Word (Fin n) → ℝ}

theorem finite_complex_projectiveTable_is_real
    (h : f ∈ finiteHilbertProjectiveTables.{u} ℂ n) :
    f ∈ finiteHilbertProjectiveTables.{u} ℝ n := by
  rcases h with ⟨H,hN,h⟩
  let := hN
  rcases h with ⟨hI,h⟩
  let := hI
  rcases h with ⟨hC,hfinite,M,hf⟩
  let := hC
  let := hfinite
  let : FiniteDimensional ℝ (CyclicHilbert M.toAlgebraic) := M.cyclicHilbert_finite
  apply mem_finiteHilbertProjectiveTables_of_model (cyclicHilbertModel M.toAlgebraic)
  intro w
  exact (cyclicHilbertModel_probability M.toAlgebraic w).trans (hf w)

theorem finite_quaternionic_projectiveTable_is_real
    (h : f ∈ finiteQuaternionicProjectiveTables.{u} n) :
    f ∈ finiteHilbertProjectiveTables.{u} ℝ n := by
  rcases h with ⟨H,hN,h⟩
  let := hN
  rcases h with ⟨hI,h⟩
  let := hI
  rcases h with ⟨hC,S,hfinite,M,hf⟩
  let := hC
  let : FiniteDimensional ℝ (CyclicHilbert M.toAlgebraic) := S.cyclicHilbert_finite hfinite M
  apply mem_finiteHilbertProjectiveTables_of_model (cyclicHilbertModel M.toAlgebraic)
  intro w
  exact (cyclicHilbertModel_probability M.toAlgebraic w).trans (hf w)

theorem finite_real_projectiveTable_is_complex
    (h : f ∈ finiteHilbertProjectiveTables.{u} ℝ n) :
    f ∈ finiteHilbertProjectiveTables.{u} ℂ n := by
  rcases h with ⟨H,hN,h⟩
  let := hN
  rcases h with ⟨hI,h⟩
  let := hI
  rcases h with ⟨hC,hfinite,M,hf⟩
  let := hC
  let := hfinite
  let : FiniteDimensional ℂ (RealHilbertComplexification H) :=
    complexification_finiteDimensional
  apply mem_finiteHilbertProjectiveTables_of_model M.complexExtensionModel
  intro w
  exact (M.complexExtensionModel_probability w).trans (hf w)

theorem finite_real_projectiveTable_is_quaternionic
    (h : f ∈ finiteHilbertProjectiveTables.{u} ℝ n) :
    f ∈ finiteQuaternionicProjectiveTables.{u} n := by
  rcases h with ⟨H,hN,h⟩
  let := hN
  rcases h with ⟨hI,h⟩
  let := hI
  rcases h with ⟨hC,hfinite,M,hf⟩
  let := hC
  let := hfinite
  let Q := fourCopyQuaternionicStructure (H := H)
  let S := Q.toRightHilbertStructure
  let MQ : QuaternionicProjectiveData (Fin n) S.toOperatorStructure :=
    M.quaternionExtensionModel.castStructure Q.toOperatorStructure_toRightHilbertStructure.symm
  have hS : letI := S.oppositeModule
      FiniteDimensional (Quaternion ℝ)ᵐᵒᵖ (RealHilbertQuaternionification H) :=
    quaternionification_finiteDimensional
  apply mem_finiteQuaternionicProjectiveTables_of_model S hS MQ
  intro w
  exact (M.quaternionExtensionModel.castStructure_probability
    Q.toOperatorStructure_toRightHilbertStructure.symm w).trans
      ((M.quaternionExtensionModel_probability w).trans (hf w))
end FiniteTables

/-- Arbitrary-dimensional models, at EACH arbitrary carrier universe. -/
theorem real_complex_projectiveTables_eq (n : ℕ) :
    hilbertProjectiveTables.{u} ℝ n = hilbertProjectiveTables.{u} ℂ n :=
  Set.Subset.antisymm (fun _ h => real_projectiveTable_is_complex h)
    (fun _ h => complex_projectiveTable_is_real h)

theorem real_quaternionic_projectiveTables_eq (n : ℕ) :
    hilbertProjectiveTables.{u} ℝ n = quaternionicProjectiveTables.{u} n :=
  Set.Subset.antisymm (fun _ h => real_projectiveTable_is_quaternionic h)
    (fun _ h => quaternionic_projectiveTable_is_real h)

theorem finite_real_complex_projectiveTables_eq (n : ℕ) :
    finiteHilbertProjectiveTables.{u} ℝ n = finiteHilbertProjectiveTables.{u} ℂ n :=
  Set.Subset.antisymm (fun _ h => finite_real_projectiveTable_is_complex h)
    (fun _ h => finite_complex_projectiveTable_is_real h)

theorem finite_real_quaternionic_projectiveTables_eq (n : ℕ) :
    finiteHilbertProjectiveTables.{u} ℝ n = finiteQuaternionicProjectiveTables.{u} n :=
  Set.Subset.antisymm (fun _ h => finite_real_projectiveTable_is_quaternionic h)
    (fun _ h => finite_quaternionic_projectiveTable_is_real h)

/-- Exact two-branch prop:field(a) endpoint. Equality is between actual
existential ALL-word table classes, with source-field finite dimension separate. -/
theorem projectiveTables_field_equivalence (n : ℕ) :
    (hilbertProjectiveTables.{u} ℝ n = hilbertProjectiveTables.{u} ℂ n ∧
      hilbertProjectiveTables.{u} ℝ n = quaternionicProjectiveTables.{u} n) ∧
    (finiteHilbertProjectiveTables.{u} ℝ n = finiteHilbertProjectiveTables.{u} ℂ n ∧
      finiteHilbertProjectiveTables.{u} ℝ n = finiteQuaternionicProjectiveTables.{u} n) :=
  ⟨⟨real_complex_projectiveTables_eq n,real_quaternionic_projectiveTables_eq n⟩,
    ⟨finite_real_complex_projectiveTables_eq n,finite_real_quaternionic_projectiveTables_eq n⟩⟩

end AlbertSequential
