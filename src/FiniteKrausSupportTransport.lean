/- SPDX-License-Identifier: Apache-2.0 -/
module

public import RealFiniteKrausComplexification
public import KrausCertaintySupport
public import Interfaces.OperationalBoundaries

/-! Kraus-range certainty support survives coordinate renaming and literal
real-to-complex transport, including nonreal input matrices. -/
@[expose] public section
noncomputable section
namespace AlbertSequential

theorem renameRealFiniteKrausModel_certainty {I J X : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) (r : RealFiniteKrausModel I X) (h : HasKrausCertaintySupport r.kraus) :
    HasKrausCertaintySupport (renameRealFiniteKrausModel e r).kraus := by
  intro x
  constructor
  · intro V hV
    obtain ⟨A,hA,rfl⟩ := List.mem_map.mp hV
    change rectangularKrausEffect ((r.kraus x true).map (renameRealMatrix e)) * renameRealMatrix e A = _
    rw [← renameRectangularKrausEffect, ← renameRealMatrix_mul, (h x).1 A hA]
  · intro V hV
    obtain ⟨A,hA,rfl⟩ := List.mem_map.mp hV
    change rectangularKrausEffect ((r.kraus x true).map (renameRealMatrix e)) * renameRealMatrix e A = 0
    rw [← renameRectangularKrausEffect, ← renameRealMatrix_mul, (h x).2 A hA, renameRealMatrix_zero]

theorem complexifyRealFiniteKrausModel_kraus_certainty {d : ℕ} {X : Type*}
    (r : RealFiniteKrausModel (Fin d) X) (h : HasKrausCertaintySupport r.kraus) :
    HasKrausCertaintySupport (complexifyRealFiniteKrausModel r).kraus := by
  intro x
  constructor
  · intro V hV
    obtain ⟨A,hA,rfl⟩ := List.mem_map.mp hV
    change krausEffect ((r.kraus x true).map complexifyMatrix) * complexifyMatrix A = _
    rw [← complexifyRectangularKrausEffect, ← complexifyMatrix_mul, (h x).1 A hA]
  · intro V hV
    obtain ⟨A,hA,rfl⟩ := List.mem_map.mp hV
    change krausEffect ((r.kraus x true).map complexifyMatrix) * complexifyMatrix A = 0
    rw [← complexifyRectangularKrausEffect, ← complexifyMatrix_mul, (h x).2 A hA, complexifyMatrix_zero]

theorem complexifyRealFiniteKrausModel_supported {d : ℕ} {X : Type*}
    (r : RealFiniteKrausModel (Fin d) X) (h : HasKrausCertaintySupport r.kraus) :
    HasCertaintySupportedOutputs (complexifyRealFiniteKrausModel r) := by
  intro x Y _
  exact (complexifyRealFiniteKrausModel_kraus_certainty r h).outputs x Y

theorem exists_supported_complexFiniteKrausModel_of_card {I X : Type*}
    [Fintype I] [DecidableEq I] {d : ℕ} (hd : Fintype.card I = d)
    (r : RealFiniteKrausModel I X) (h : HasKrausCertaintySupport r.kraus) :
    ∃ s : BinaryKrausRealization d X, IsRealKrausRealization s ∧ HasCertaintySupportedOutputs s ∧
      ∀ w, binaryKrausProbability s w = realFiniteKrausProbability I X r w := by
  let e : I ≃ Fin d := Fintype.equivFinOfCardEq hd
  let renamed := renameRealFiniteKrausModel e r
  refine ⟨complexifyRealFiniteKrausModel renamed, complexifyRealFiniteKrausModel_real renamed,
    complexifyRealFiniteKrausModel_supported renamed (renameRealFiniteKrausModel_certainty e r h), ?_⟩
  intro w
  rw [complexifyRealFiniteKrausModel_probability, renameRealFiniteKrausModel_probability]

end AlbertSequential
