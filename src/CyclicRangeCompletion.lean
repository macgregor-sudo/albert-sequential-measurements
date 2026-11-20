/- SPDX-License-Identifier: Apache-2.0 -/
module
public import CyclicWordVectors
public import JordanSquareLifts

/-! Lift the algebraic cyclic image, including its state, into actual bounded Hilbert operators. -/
@[expose] public section
noncomputable section

open scoped InnerProductSpace

namespace AlbertSequential
variable {I A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
local instance : Algebra ℝ A := Algebra.ofModule smul_mul_assoc mul_smul_comm

theorem cyclicHilbert_eq_of_cyclic_eq (M : AlgebraicProjectiveData I A) (z w : CyclicWordAlgebra M)
    (h : cyclicRepresentation M (cyclicWordAlgebraEquiv M z) =
         cyclicRepresentation M (cyclicWordAlgebraEquiv M w)) :
    cyclicHilbertRepresentation M z = cyclicHilbertRepresentation M w := by
  apply cyclicHilbertOperator_ext M
  intro x
  change cyclicHilbertAction M z _ = cyclicHilbertAction M w _
  rw [cyclicHilbertAction_coe, cyclicHilbertAction_coe]
  congr 1
  change (cyclicPreHilbertLinearEquiv M).symm
    (cyclicRepresentation M (cyclicWordAlgebraEquiv M z) ((cyclicPreHilbertLinearEquiv M) x)) = _
  rw [h]
  rfl

private theorem liftLinearThroughRange
    {E V H : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup V] [Module ℝ V]
    [AddCommGroup H] [Module ℝ H] (f : E →ₗ[ℝ] V) (g : E →ₗ[ℝ] H)
    (hf : ∀ {x y}, f x = f y → g x = g y) :
    ∃ L : f.range →ₗ[ℝ] H, ∀ z, L (f.rangeRestrict z) = g z := by
  let R := f.rangeRestrict
  let representative (x : f.range) := (f.surjective_rangeRestrict x).choose
  have hRep (x : f.range) : R (representative x) = x :=
    (f.surjective_rangeRestrict x).choose_spec
  have hSame {x y : E} (h : R x = R y) : g x = g y :=
    hf (congrArg Subtype.val h)
  let L : f.range →ₗ[ℝ] H :=
    { toFun := fun x => g (representative x)
      map_add' := fun x y => by
        refine (hSame (y := representative x + representative y) ?_).trans (map_add g _ _)
        rw [hRep, map_add, hRep, hRep]
      map_smul' := fun r x => by
        change g (representative (r • x)) = r • g (representative x)
        refine (hSame (y := r • representative x) ?_).trans (map_smul g _ _)
        rw [hRep, map_smul, hRep] }
  exact ⟨L, fun z => hSame (hRep (R z))⟩

/-- Completion factors linearly through the actual algebraic cyclic range. -/
theorem exists_cyclic_range_completion (M : AlgebraicProjectiveData I A) :
    let R := (cyclicRepresentation M).toLinearMap
    ∃ F : R.range →ₗ[ℝ] (CyclicHilbert M →L[ℝ] CyclicHilbert M),
      ∀ z : wordSubalgebra M.projection, F (R.rangeRestrict z) =
        cyclicHilbertRepresentation M ((cyclicWordAlgebraEquiv M).symm z) := by
  let R := (cyclicRepresentation M).toLinearMap
  let G := ((cyclicHilbertRepresentation M).toAlgHom.comp
    (cyclicWordAlgebraEquiv M).symm.toAlgHom).toLinearMap
  have h {z w : wordSubalgebra M.projection} (hzw : R z = R w) : G z = G w := by
    change cyclicHilbertRepresentation M ((cyclicWordAlgebraEquiv M).symm z) =
      cyclicHilbertRepresentation M ((cyclicWordAlgebraEquiv M).symm w)
    apply cyclicHilbert_eq_of_cyclic_eq
    rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
    exact hzw
  exact liftLinearThroughRange R G h

/-- Completing an algebraic orbit reconstruction yields the actual bounded
self-adjoint representation, with its specified orbit values and vector state. -/
theorem exists_cyclicHilbertJordanMap_of_orbits
    {J κ : Type*} [AddCommGroup J] [Module ℝ J]
    (M : AlgebraicProjectiveData I A)
    (e : J) (q : κ → J) (Q : κ → wordSubalgebra M.projection)
    (jmul : J →ₗ[ℝ] J →ₗ[ℝ] J)
    (hspan : Submodule.span ℝ (Set.range (unitAndAtomLabels e q)) = ⊤)
    (hQstar : ∀ i, star (Q i : A) = Q i)
    (η : J →ₗ[ℝ] Module.End ℝ (CyclicWordSpace M))
    (hJordan : ∀ x y, η (jmul x y) = associativeJordanProduct (η x) (η y))
    (hUnit : η e = 1) (hGenerators : ∀ i, η (q i) = cyclicRepresentation M (Q i))
    (ω : J →ₗ[ℝ] ℝ)
    (hState : ∀ x, cyclicExpectation M (η x (cyclicVector M)) = ω x) :
    let H := CyclicHilbert M →L[ℝ] CyclicHilbert M
    ∃ ηH : J →ₗ[ℝ] selfAdjoint H,
      (∀ x y, (ηH (jmul x y) : H) = associativeJordanProduct (ηH x : H) (ηH y : H)) ∧
      (ηH e : H) = 1 ∧
      (∀ i, (ηH (q i) : H) = cyclicHilbertRepresentation M ((cyclicWordAlgebraEquiv M).symm (Q i))) ∧
      ∀ x, inner ℝ (cyclicHilbertVector M) ((ηH x : H) (cyclicHilbertVector M)) = ω x := by
  let H := CyclicHilbert M →L[ℝ] CyclicHilbert M
  let R := (cyclicRepresentation M).toLinearMap
  obtain ⟨F, hF⟩ := exists_cyclic_range_completion M
  have hrange (x : J) : η x ∈ R.range := by
    have hle : Submodule.span ℝ (Set.range (unitAndAtomLabels e q)) ≤ R.range.comap η := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      cases i with
      | none =>
        change η e ∈ R.range
        exact ⟨1, (map_one (cyclicRepresentation M)).trans hUnit.symm⟩
      | some i =>
        change η (q i) ∈ R.range
        exact ⟨Q i, (hGenerators i).symm⟩
    exact hle (hspan.symm ▸ Submodule.mem_top)
  let L : J →ₗ[ℝ] R.range := η.codRestrict R.range hrange
  let T : J →ₗ[ℝ] H := F.comp L
  have hTlift {x : J} {z : wordSubalgebra M.projection} (hz : cyclicRepresentation M z = η x) :
      T x = cyclicHilbertRepresentation M ((cyclicWordAlgebraEquiv M).symm z) := by
    change F (L x) = _
    rw [show L x = R.rangeRestrict z from Subtype.ext hz.symm]
    exact hF z
  have hTunit : T e = 1 := by
    have he : cyclicRepresentation M 1 = η e := (map_one (cyclicRepresentation M)).trans hUnit.symm
    rw [hTlift he, map_one, map_one]
  have hTq (i : κ) : T (q i) =
      cyclicHilbertRepresentation M ((cyclicWordAlgebraEquiv M).symm (Q i)) :=
    hTlift (hGenerators i).symm
  have hTsa (x : J) : T x ∈ selfAdjoint.submodule ℝ H := by
    have hle : Submodule.span ℝ (Set.range (unitAndAtomLabels e q)) ≤
        (selfAdjoint.submodule ℝ H).comap T := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      cases i with
      | none =>
        change star (T e) = T e
        rw [hTunit, star_one]
      | some i =>
        let z := (cyclicWordAlgebraEquiv M).symm (Q i)
        have hz : star z = z := Subtype.ext (hQstar i)
        change star (T (q i)) = T (q i)
        rw [hTq, ← map_star, hz]
    exact hle (hspan.symm ▸ Submodule.mem_top)
  let ηH : J →ₗ[ℝ] selfAdjoint H := T.codRestrict (selfAdjoint.submodule ℝ H) hTsa
  refine ⟨ηH, ?_, hTunit, hTq, ?_⟩
  · intro x y
    obtain ⟨zx, hx⟩ := hrange x
    obtain ⟨zy, hy⟩ := hrange y
    change cyclicRepresentation M zx = η x at hx
    change cyclicRepresentation M zy = η y at hy
    let z := associativeJordanProduct zx zy
    have hz : cyclicRepresentation M z = η (jmul x y) := by
      rw [hJordan]
      simp only [z, associativeJordanProduct, map_smul, map_add, map_mul, hx, hy]
    change T (jmul x y) = associativeJordanProduct (T x) (T y)
    rw [hTlift hz, hTlift hx, hTlift hy]
    simp only [z, associativeJordanProduct, map_smul, map_add, map_mul]
  · intro x
    obtain ⟨z, hz⟩ := hrange x
    change cyclicRepresentation M z = η x at hz
    change inner ℝ (cyclicHilbertVector M) (T x (cyclicHilbertVector M)) = ω x
    rw [hTlift hz, cyclicHilbert_vector_state, ← hState x, ← hz, cyclicExpectation_action_vector]
    rfl

end AlbertSequential
