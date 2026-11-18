module

public import Defs
public import Mathlib.Tactic.Module

/-! Pure homomorphism transport. These proofs use only real linearity and
Jordan-product preservation, without native Jordan, trace, or purity laws. -/

@[expose] public section
noncomputable section
namespace AlbertSequential

theorem jordanHom_map_square
    {A : Type*} [NonUnitalRing A] [Module ℝ A]
    (η : Albert →ₗ[ℝ] A) (hη : IsJordanHom η) (x : Albert) :
    η (jordanMul x x) = η x * η x := by
  rw [hη]
  module

theorem jordanHom_map_idempotent
    {A : Type*} [NonUnitalRing A] [Module ℝ A]
    (η : Albert →ₗ[ℝ] A) (hη : IsJordanHom η) (p : Albert)
    (hp : jordanMul p p = p) :
    η p * η p = η p := by
  rw [← jordanHom_map_square η hη p, hp]

theorem jordanHom_map_atom_idempotent
    {A : Type*} [NonUnitalRing A] [Module ℝ A]
    (η : Albert →ₗ[ℝ] A) (hη : IsJordanHom η) (p : Albert)
    (hp : IsAtom p) : η p * η p = η p :=
  jordanHom_map_idempotent η hη p hp.1

theorem jordanHom_map_quadratic
    {A : Type*} [NonUnitalRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    (η : Albert →ₗ[ℝ] A) (hη : IsJordanHom η) (x y : Albert) :
    η (quadraticMap x y) = η x * η y * η x := by
  unfold IsJordanHom at hη
  simp only [quadraticMap, map_sub, map_nsmul, hη]
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_assoc]
  module

/-- Native compression is an explicit hypothesis, not an assumed purity law. -/
theorem jordanHom_map_compression
    {A : Type*} [NonUnitalRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    (η : Albert →ₗ[ℝ] A) (hη : IsJordanHom η) (x y : Albert) (c : ℝ)
    (h : quadraticMap x y = c • x) :
    η x * η y * η x = c • η x := by
  rw [← jordanHom_map_quadratic η hη x y, h, map_smul]

end AlbertSequential
