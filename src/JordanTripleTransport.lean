module

public import JordanHomTransport
public import Interfaces.AlgebraicReconstruction

/-! The existing native Jordan triple convention, transported by a linear
Jordan homomorphism to its reversal-symmetric associative formula. -/

@[expose] public section
noncomputable section
namespace AlbertSequential

theorem jordanHom_map_triple
    {A : Type*} [NonUnitalRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    (η : Albert →ₗ[ℝ] A) (hη : IsJordanHom η) (x y z : Albert) :
    η (jordanTriple x y z) =
      (1 / 2 : ℝ) • (η x * η y * η z + η z * η y * η x) := by
  unfold IsJordanHom at hη
  simp only [jordanTriple, map_sub, map_add, hη]
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_assoc]
  module

end AlbertSequential
