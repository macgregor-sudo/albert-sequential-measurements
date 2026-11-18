/- SPDX-License-Identifier: Apache-2.0 -/
module
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! Explicit finite orthogonal component maps and their actual inverse sum.
Zero-dimensional and empty families are included by the spanning premise. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.OrthogonalSubspaceComponents
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] (I : ι → Submodule ℝ E)

def components : E →ₗ[ℝ] ((i : ι) → I i) :=
  LinearMap.pi (fun i => (I i).orthogonalProjectionOnto.toLinearMap)

def sumComponents : ((i : ι) → I i) →ₗ[ℝ] E where
  toFun x := ∑ i,(x i).val
  map_add' x y := by simp only [Pi.add_apply,Submodule.coe_add,Finset.sum_add_distrib]
  map_smul' r x := by simp only [Pi.smul_apply,Submodule.coe_smul,Finset.smul_sum,RingHom.id_apply]

theorem components_sumComponents (horth : ∀ i j,i≠j → I i≤(I j)ᗮ)
    (x : (i : ι) → I i) : components I (sumComponents I x)=x := by
  classical
  funext i
  change (I i).orthogonalProjectionOnto (∑ j,(x j).val)=x i
  rw [map_sum,Finset.sum_eq_single i]
  · exact (I i).orthogonalProjectionOnto_mem_subspace_eq_self (x i)
  · intro j _ hji
    exact Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal (horth j i hji (x j).property)
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

theorem sumComponents_components (horth : ∀ i j,i≠j → I i≤(I j)ᗮ)
    (htop : (⨆ i,I i)=⊤) (x : E) : sumComponents I (components I x)=x := by
  let r := x-sumComponents I (components I x)
  have hcomp : components I r=0 := by
    simp only [r,map_sub,components_sumComponents I horth,sub_self]
  have hr (i : ι) : r∈(I i)ᗮ := by
    have hi : (I i).orthogonalProjectionOnto r=0 := congrFun hcomp i
    have hiv : (I i).starProjection r=0 := congrArg Subtype.val hi
    simpa only [hiv,sub_zero] using (I i).sub_starProjection_mem_orthogonal r
  have hall : r∈⨅ i,(I i)ᗮ := by simpa only [Submodule.mem_iInf] using hr
  rw [Submodule.iInf_orthogonal,htop,Submodule.top_orthogonal_eq_bot] at hall
  exact (sub_eq_zero.mp hall).symm

def decompositionEquiv (horth : ∀ i j,i≠j → I i≤(I j)ᗮ)
    (htop : (⨆ i,I i)=⊤) : E ≃ₗ[ℝ] ((i : ι) → I i) where
  __ := components I
  invFun := sumComponents I
  left_inv := sumComponents_components I horth htop
  right_inv := components_sumComponents I horth

@[simp] theorem decompositionEquiv_apply
    (horth : ∀ i j,i≠j → I i≤(I j)ᗮ) (htop : (⨆ i,I i)=⊤) (x : E) (i : ι) :
    decompositionEquiv I horth htop x i=(I i).orthogonalProjectionOnto x := rfl

end AlbertSequential.OrthogonalSubspaceComponents
