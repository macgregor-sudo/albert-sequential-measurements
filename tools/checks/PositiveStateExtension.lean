module

import HermitianPositiveStateExtension

open AlbertSequential
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
example {d : ℕ} (S : Submodule ℝ (Matrix (Fin d) (Fin d) ℂ)) (he : 1 ∈ S)
    (hsa : ∀ x : S, IsSelfAdjoint x.val) (f : S →ₗ[ℝ] ℝ)
    (hp : ∀ x : S, 0 ≤ x.val → 0 ≤ f x) (hf : f ⟨1,he⟩ = 1) :
    ∃ σ : Matrix (Fin d) (Fin d) ℂ, σ.PosSemidef ∧ σ.trace = 1 ∧
      ∀ x : S, (σ * x.val).trace = (f x : ℂ) := by
  obtain ⟨G,σ,hGS,_,_,_,hσ,ht,hrep⟩ := positive_state_extension_density d S he hsa f hp hf
  refine ⟨σ,hσ,ht,fun x => ?_⟩
  rw [hrep x.val (hsa x),hGS x]

#print axioms AlbertSequential.positive_state_extension
#print axioms AlbertSequential.positive_state_extension_density
