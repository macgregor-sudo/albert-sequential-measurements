module

public import Defs
public import DiagPeirceAnchor
public import NativePeircePropagation
public import TetrahedronEngine
public import FixedSBinding
public import Mathlib.Tactic.NormNum

/-!
# Unconditional Native Albert Zero-Homomorphism Endpoint

Proves `AlbertSequential.albertJordanHom_eq_zero`: every real-linear Jordan
homomorphism from `AlbertSequential.Albert` into an arbitrary possibly nonunital,
possibly zero, possibly noncommutative associative real algebra is zero.
-/

@[expose] public section
noncomputable section

namespace AlbertSequential

/-- Every real-linear Jordan homomorphism from the compact Albert algebra into
a possibly nonunital associative real algebra is identically zero. -/
theorem albertJordanHom_eq_zero
    (A : Type*) [NonUnitalRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    (η : Albert →ₗ[ℝ] A) (hη : IsJordanHom η) : η = 0 := by
  have hdisc :
      tetrahedronDiscriminant (nativeOverlaps fixedS)
          (nativeTriangles fixedS) (nativeCornerQ fixedS) • η (fixedS 0) = 0 :=
    tetrahedron_annihilates_base (fun i => η (fixedS i))
      (nativeOverlaps fixedS) (nativeTriangles fixedS) (nativeCornerQ fixedS)
      (fixedS_cornerRelations η hη)
  rw [fixedS_discriminant] at hdisc
  have h0 : η (diagAtom 0) = 0 := by
    calc
      η (diagAtom 0) = η (fixedS 0) := rfl
      _ = (1 : ℝ) • η (fixedS 0) := (one_smul ℝ _).symm
      _ = ((104976 : ℝ) * (1 / 104976 : ℝ)) • η (fixedS 0) := by norm_num
      _ = (104976 : ℝ) • ((1 / 104976 : ℝ) • η (fixedS 0)) := mul_smul _ _ _
      _ = (104976 : ℝ) • (0 : A) := by rw [hdisc]
      _ = 0 := smul_zero _
  exact jordanHom_eq_zero_of_diagAtom0 η hη h0

end AlbertSequential
