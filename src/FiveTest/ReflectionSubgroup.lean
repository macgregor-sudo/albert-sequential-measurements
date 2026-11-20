/- SPDX-License-Identifier: Apache-2.0 -/
module
public import FiveTest.DenseOrbit

@[expose] public section
noncomputable section
namespace AlbertSequential
open NativeAnalysis WindowProbability
variable {I : Type*} (p : I → Albert) (hp : ∀ i, IsAtom (p i))

def reflectionGroupWord (w : List I) : AlbertAutomorphismGroup :=
  nativeAutoToCompactAuto (nativeReflectionWordAutomorphism p hp w)

private theorem reflectionGroupWord_nil : reflectionGroupWord p hp [] = 1 := by
  apply AlbertAutomorphismGroup.aut_eq_of_apply_eq
  intro x
  change recoveredCoordinateEquiv (recoveredCoordinateEquiv.symm x) = x
  exact recoveredCoordinateEquiv.apply_symm_apply x

private theorem reflectionGroupWord_append (v w : List I) :
    reflectionGroupWord p hp (v ++ w) = reflectionGroupWord p hp v * reflectionGroupWord p hp w := by
  apply AlbertAutomorphismGroup.aut_eq_of_apply_eq
  intro x
  change (nativeAutoToCompactAuto _).equiv x =
    (nativeAutoToCompactAuto _).equiv ((nativeAutoToCompactAuto _).equiv x)
  simp only [nativeAutoToCompactAuto_apply, LinearEquiv.symm_apply_apply, nativeReflectionWord_append]

private theorem reflectionGroupWord_reverse (w : List I) :
    reflectionGroupWord p hp w.reverse = (reflectionGroupWord p hp w)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  apply AlbertAutomorphismGroup.aut_eq_of_apply_eq
  intro x
  change (nativeAutoToCompactAuto _).equiv ((nativeAutoToCompactAuto _).equiv x) = x
  simp only [nativeAutoToCompactAuto_apply, LinearEquiv.symm_apply_apply,
    nativeReflectionWord_reverse_left, LinearEquiv.apply_symm_apply]

def menuReflectionSubgroup : Subgroup AlbertAutomorphismGroup :=
  Subgroup.closure (Set.range (fun i => reflectionGroupWord p hp [i]))

theorem menuReflectionSubgroup_eq_wordRange :
    (menuReflectionSubgroup p hp : Set AlbertAutomorphismGroup) = Set.range (reflectionGroupWord p hp) := by
  let S : Subgroup AlbertAutomorphismGroup :=
    { carrier := Set.range (reflectionGroupWord p hp)
      one_mem' := ⟨[], reflectionGroupWord_nil p hp⟩
      mul_mem' := by rintro _ _ ⟨v,rfl⟩ ⟨w,rfl⟩; exact ⟨v ++ w, reflectionGroupWord_append p hp v w⟩
      inv_mem' := by rintro _ ⟨w,rfl⟩; exact ⟨w.reverse, reflectionGroupWord_reverse p hp w⟩ }
  apply Set.Subset.antisymm
  · change menuReflectionSubgroup p hp ≤ S
    apply (Subgroup.closure_le (K := S)).2
    rintro _ ⟨i,rfl⟩
    exact ⟨[i],rfl⟩
  · rintro _ ⟨w,rfl⟩
    induction w with
    | nil => rw [reflectionGroupWord_nil]; exact (menuReflectionSubgroup p hp).one_mem
    | cons i w ih =>
      rw [show i :: w = [i] ++ w from rfl, reflectionGroupWord_append]
      exact (menuReflectionSubgroup p hp).mul_mem (Subgroup.subset_closure ⟨i,rfl⟩) ih

theorem positive_quad_finite_depth_of_dense_subgroup (i : I)
    (hd : Dense (menuReflectionSubgroup p hp : Set AlbertAutomorphismGroup)) :
    ∃ (d : ℕ) (w : Fin 4 → List I), (∀ k, (w k).length ≤ d) ∧
      0 < fourPointInvariant (fun k => nativeOrbitPoint p hp (w k,i)) := by
  rw [menuReflectionSubgroup_eq_wordRange] at hd
  obtain ⟨w,hw⟩ := exists_positive_reflection_quad_of_dense p hp i hd
  exact ⟨Finset.univ.sup (fun k => (w k).length), w,
    fun k => Finset.le_sup (f := fun k => (w k).length) (Finset.mem_univ k), hw⟩

end AlbertSequential
