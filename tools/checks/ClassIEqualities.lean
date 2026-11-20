module

import EqualityClassIUniverses

noncomputable section

open AlbertSequential AlbertSequential.AppF
open scoped Matrix

universe u v

example {n : ℕ} (c : Word (Fin n) →₀ ℝ) :
    (∀ f : Word (Fin n) → ℝ,
      (f ∈ hilbertProjectiveTables.{u} ℝ n ∨ f ∈ hilbertProjectiveTables.{u} ℂ n ∨
        f ∈ quaternionicProjectiveTables.{u} n) →
      c.sum (fun w a => a * f w) = 0) ↔
    freeProductImage c = 0 :=
  classIEquality_iff_freeProductZero.{u} c

example {n : ℕ} (c : Word (Fin n) →₀ ℝ) :
    IsClassIProjectiveEquality.{u} c ↔ IsClassIProjectiveEquality.{v + 1} c :=
  (classIEquality_iff_finiteRealVectorStates.{u} c).trans
    (classIEquality_iff_finiteRealVectorStates.{v + 1} c).symm

example {n N : ℕ} (P : Fin n → Matrix (Fin N) (Fin N) ℝ)
    (hP : ∀ i, (P i)ᵀ = P i ∧ P i * P i = P i)
    (v : Fin N → ℝ) (hv : dotProduct v v = 1) :
    (fun w => dotProduct v (wordOperator P w *ᵥ v)) ∈ finiteHilbertProjectiveTables.{u + 1} ℝ n :=
  finiteRealVectorTable_mem.{u + 1} P hP v hv

#check @classIEquality_native_le_six.{u}

#print axioms finiteRealVectorTable_mem
#print axioms algebraic_wordSum_eq_zero_of_freeProductZero
#print axioms classIEquality_iff_finiteRealVectorStates
#print axioms classIEquality_iff_freeProductZero
#print axioms classIEquality_native_le_six
