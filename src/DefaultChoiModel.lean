module

public import ChoiParameterCompactness

/-! Explicit nonempty normalized model and elementary Choi action controls.
There is no inverse dimension and no exclusion of zero outcome maps.
-/
@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder
namespace AlbertSequential

def identityChoi (d : ℕ) : ChoiMatrix d :=
  Matrix.vecMulVec (fun i : Fin d × Fin d => if i.1 = i.2 then 1 else 0)
    (star (fun i : Fin d × Fin d => if i.1 = i.2 then (1 : ℂ) else 0))

theorem identityChoi_positive (d : ℕ) : (identityChoi d).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star _

theorem identityChoi_outputTrace (d : ℕ) : choiOutputTrace (identityChoi d) = 1 := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    simp [choiOutputTrace, identityChoi, Matrix.vecMulVec]
  · simp [choiOutputTrace, identityChoi, Matrix.vecMulVec, hij]

theorem identityChoi_action (d : ℕ) (Y : ComplexMatrix d) :
    choiAction (identityChoi d) Y = Y := by
  classical
  ext k l
  simp [choiAction, identityChoi, Matrix.vecMulVec]

def coordinateDensity {d : ℕ} (i : Fin d) : ComplexMatrix d :=
  Matrix.vecMulVec (Pi.single i 1) (star (Pi.single i 1))

theorem coordinateDensity_isDensity {d : ℕ} (i : Fin d) :
    IsMatrixDensity (coordinateDensity i) := by
  classical
  refine ⟨Matrix.posSemidef_vecMulVec_self_star _, ?_⟩
  simp [coordinateDensity, Matrix.trace, Matrix.diag, Matrix.vecMulVec, Pi.single_apply]

def defaultChoiInstrument (d : ℕ) (B : Type*) [Nonempty B] : B → ChoiMatrix d := by
  classical
  exact fun a => if a = Classical.choice (inferInstance : Nonempty B) then identityChoi d else 0

theorem defaultChoiInstrument_normalized (d : ℕ) (B : Type*)
    [Fintype B] [Nonempty B] : IsNormalizedChoiInstrument (defaultChoiInstrument d B) := by
  classical
  constructor
  · intro a
    unfold defaultChoiInstrument
    split_ifs
    · exact identityChoi_positive d
    · exact Matrix.PosSemidef.zero
  · have hz : choiOutputTrace (0 : ChoiMatrix d) = 0 := by
      ext i j
      simp [choiOutputTrace]
    simp only [defaultChoiInstrument, apply_ite, identityChoi_outputTrace, hz]
    simp

def defaultFiniteCPModel (d : ℕ) (hd : 0 < d) (P X : Type*) (A : X → Type*)
    [∀ x, Nonempty (A x)] : RawFiniteCPModel d P X A :=
  (fun _ => coordinateDensity ⟨0, hd⟩, fun x => defaultChoiInstrument d (A x))

theorem defaultFiniteCPModel_normalized (d : ℕ) (hd : 0 < d) (P X : Type*)
    (A : X → Type*) [∀ x, Fintype (A x)] [∀ x, Nonempty (A x)] :
    IsNormalizedFiniteCPModel (defaultFiniteCPModel d hd P X A) := by
  refine ⟨fun _ => coordinateDensity_isDensity _, ?_, ?_⟩
  · intro x a
    exact (defaultChoiInstrument_normalized d (A x)).1 a
  · intro x
    exact (defaultChoiInstrument_normalized d (A x)).2

end AlbertSequential
