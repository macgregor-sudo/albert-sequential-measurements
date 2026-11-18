/- SPDX-License-Identifier: Apache-2.0 -/
module

public import JordanGeneratedAlgebra
public import JordanAssociativeSpectral

/-! Distinct real spectral resolution of an arbitrary element in the genuine
finite-dimensional positive-associative-inner-form setting. The proof uses the
single generated associative algebra and transports its literal product/unit. -/

@[expose] public section
noncomputable section
namespace AlbertSequential.UnitalJordanProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (P : UnitalJordanProduct E)

theorem spectral_resolution
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (a : E) :
    ∃ (n : ℕ) (lam : Fin n → ℝ) (c : Fin n → E), Function.Injective lam ∧
      (∀ i, c i≠0 ∧ P.product (c i) (c i)=c i) ∧
      (∀ i j, i≠j → P.product (c i) (c j)=0) ∧
      (∑ i, c i)=P.unit ∧ a=∑ i, lam i • c i := by
  have hinnerW (x y z : P.powerSpan a) :
      inner ℝ ((P.powerSpanProduct a).product x y) z=
        inner ℝ x ((P.powerSpanProduct a).product y z) :=
    hinner x.val y.val z.val
  obtain ⟨n,lam,c,hlam,hc,horth,hsum,ha⟩ :=
    (P.powerSpanProduct a).associative_spectral_resolution
      (P.powerSpanProduct_associative a) hinnerW ⟨a,P.generator_mem_powerSpan a⟩
  refine ⟨n,lam,fun i => (c i).val,hlam,?_,?_,?_,?_⟩
  · intro i
    constructor
    · intro hzero
      exact (hc i).1 (Subtype.ext hzero)
    · exact congrArg Subtype.val (hc i).2
  · intro i j hne
    exact congrArg Subtype.val (horth i j hne)
  · have h := congrArg (P.powerSpan a).subtype hsum
    simpa only [map_sum,Submodule.subtype_apply,P.powerSpanProduct_unit] using h
  · have h := congrArg (P.powerSpan a).subtype ha
    simpa only [map_sum,map_smul,RingHom.id_apply,Submodule.subtype_apply] using h

end AlbertSequential.UnitalJordanProduct
