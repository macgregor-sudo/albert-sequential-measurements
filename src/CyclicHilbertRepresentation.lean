/- SPDX-License-Identifier: Apache-2.0 -/
module
public import CyclicInnerProduct
public import ProjectiveWordProbabilities
public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The full bounded cyclic representation of the actual word star-algebra.
The null quotient is a vector space only; its representation acts by ordinary
bounded operators, and completion preserves all algebraic and star identities. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace AlbertSequential
section
variable {ι A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
local instance : Algebra ℝ A := Algebra.ofModule smul_mul_assoc mul_smul_comm

theorem star_mem_wordVectorSpan (M : AlgebraicProjectiveData ι A) {x : A}
    (hx : x ∈ WordVectorSpan M.projection) : star x ∈ WordVectorSpan M.projection := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨w,rfl⟩
    rw [wordAmplitude_star_reverse M.projection M.selfAdjoint]
    exact wordAmplitude_mem_wordVectorSpan M.projection _
  | zero => simpa only [star_zero] using (WordVectorSpan M.projection).zero_mem
  | add x y hx hy ihx ihy =>
    rw [star_add]
    exact (WordVectorSpan M.projection).add_mem ihx ihy
  | smul r x hx ih =>
    rw [star_smul,star_trivial]
    exact (WordVectorSpan M.projection).smul_mem r ih

def cyclicWordStarSubalgebra (M : AlgebraicProjectiveData ι A) : StarSubalgebra ℝ A where
  toSubalgebra := wordSubalgebra M.projection
  star_mem' := star_mem_wordVectorSpan M

abbrev CyclicWordAlgebra (M : AlgebraicProjectiveData ι A) : Type _ := cyclicWordStarSubalgebra M

/-- The star packaging changes none of the word-algebra elements. -/
def cyclicWordAlgebraEquiv (M : AlgebraicProjectiveData ι A) :
    CyclicWordAlgebra M ≃ₐ[ℝ] wordSubalgebra M.projection where
  toFun x := ⟨x.val,x.property⟩
  invFun x := ⟨x.val,x.property⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_mul' := fun _ _ => rfl
  map_add' := fun _ _ => rfl
  commutes' := fun _ => rfl

def cyclicPreRepresentation (M : AlgebraicProjectiveData ι A) :
    CyclicWordAlgebra M →ₐ[ℝ] Module.End ℝ (CyclicPreHilbert M) :=
  (((cyclicPreHilbertLinearEquiv M).symm.conjAlgEquiv ℝ).toAlgHom.comp
    (cyclicRepresentation M)).comp (cyclicWordAlgebraEquiv M).toAlgHom

@[simp] theorem cyclicPreRepresentation_mk (M : AlgebraicProjectiveData ι A)
    (z : CyclicWordAlgebra M) (x : wordSubalgebra M.projection) :
    cyclicPreRepresentation M z (cyclicPreHilbertMk M x) =
      cyclicPreHilbertMk M (cyclicWordAlgebraEquiv M z*x) := rfl

theorem cyclicPreHilbertMk_surjective (M : AlgebraicProjectiveData ι A) :
    Function.Surjective (cyclicPreHilbertMk M) := by
  intro q
  cases q with
  | mk q =>
    induction q using Submodule.Quotient.induction_on with
    | _ x => exact ⟨x,rfl⟩

def cyclicWordElement (M : AlgebraicProjectiveData ι A) (w : Word ι) : CyclicWordAlgebra M :=
  ⟨wordAmplitude M.projection w,wordAmplitude_mem_wordVectorSpan M.projection w⟩

theorem cyclicWordAlgebra_span_words (M : AlgebraicProjectiveData ι A) :
    Submodule.span ℝ (Set.range (cyclicWordElement M))=⊤ := by
  let S := Submodule.span ℝ (Set.range (cyclicWordElement M))
  let inc := (cyclicWordStarSubalgebra M).subtype.toAlgHom.toLinearMap
  have hword : Set.range (wordAmplitude M.projection) ⊆ S.map inc := by
    rintro _ ⟨w,rfl⟩
    exact ⟨cyclicWordElement M w,Submodule.subset_span ⟨w,rfl⟩,rfl⟩
  apply top_unique
  intro z _
  have hz : (z : A) ∈ S.map inc := Submodule.span_le.mpr hword z.property
  rcases hz with ⟨y,hy,he⟩
  have hyz : y=z := Subtype.ext he
  exact hyz ▸ hy

theorem cyclicPreRepresentation_word_contraction (M : AlgebraicProjectiveData ι A)
    (w : Word ι) (q : CyclicPreHilbert M) :
    ‖cyclicPreRepresentation M (cyclicWordElement M w) q‖ ≤ ‖q‖ := by
  obtain ⟨x,rfl⟩ := cyclicPreHilbertMk_surjective M q
  have hsq : ‖cyclicPreRepresentation M (cyclicWordElement M w) (cyclicPreHilbertMk M x)‖^2 ≤
      ‖cyclicPreHilbertMk M x‖^2 := by
    rw [cyclicPreRepresentation_mk,cyclicPreHilbert_norm_sq,cyclicPreHilbert_norm_sq]
    change M.squareMass (wordAmplitude M.projection w*(x : A)) ≤ M.squareMass (x : A)
    exact M.squareMass_word_le w (x : A)
  nlinarith [norm_nonneg (cyclicPreRepresentation M (cyclicWordElement M w) (cyclicPreHilbertMk M x)),
    norm_nonneg (cyclicPreHilbertMk M x)]

/-- Boundedness is closed under finite real linear combinations. No ambient
norm on A is assumed here; the sharper original operator bound is separate. -/
theorem cyclicPreRepresentation_bounded (M : AlgebraicProjectiveData ι A)
    (z : CyclicWordAlgebra M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q, ‖cyclicPreRepresentation M z q‖ ≤ C*‖q‖ := by
  let good : Submodule ℝ (CyclicWordAlgebra M) :=
    { carrier := {z | ∃ C : ℝ, 0 ≤ C ∧ ∀ q, ‖cyclicPreRepresentation M z q‖ ≤ C*‖q‖}
      zero_mem' := by
        refine ⟨0,le_rfl,?_⟩
        intro q
        simp only [map_zero,LinearMap.zero_apply,norm_zero,zero_mul,le_refl]
      add_mem' := by
        intro x y hx hy
        rcases hx with ⟨C,hC,hx⟩
        rcases hy with ⟨D,hD,hy⟩
        refine ⟨C+D,add_nonneg hC hD,?_⟩
        intro q
        change ‖((cyclicPreRepresentation M).toLinearMap (x+y)) q‖ ≤ (C+D)*‖q‖
        rw [map_add,LinearMap.add_apply,AlgHom.toLinearMap_apply,AlgHom.toLinearMap_apply]
        exact (norm_add_le _ _).trans (by simpa only [add_mul] using add_le_add (hx q) (hy q))
      smul_mem' := by
        intro r x hx
        rcases hx with ⟨C,hC,hx⟩
        refine ⟨|r| * C,mul_nonneg (abs_nonneg r) hC,?_⟩
        intro q
        change ‖((cyclicPreRepresentation M).toLinearMap (r • x)) q‖ ≤ |r| * C * ‖q‖
        rw [map_smul,LinearMap.smul_apply]
        change ‖r • cyclicPreRepresentation M x q‖ ≤ |r| * C * ‖q‖
        rw [norm_smul,Real.norm_eq_abs,mul_assoc]
        exact mul_le_mul_of_nonneg_left (hx q) (abs_nonneg r) }
  let inc := (cyclicWordStarSubalgebra M).subtype.toAlgHom.toLinearMap
  have hword : Set.range (wordAmplitude M.projection) ⊆ good.map inc := by
    rintro _ ⟨w,rfl⟩
    refine ⟨cyclicWordElement M w,?_,rfl⟩
    exact ⟨1,zero_le_one,fun q => by simpa only [one_mul] using cyclicPreRepresentation_word_contraction M w q⟩
  have hz : (z : A) ∈ good.map inc := Submodule.span_le.mpr hword z.property
  rcases hz with ⟨y,hy,he⟩
  have hyz : y=z := Subtype.ext he
  exact hyz ▸ hy

end
end AlbertSequential
