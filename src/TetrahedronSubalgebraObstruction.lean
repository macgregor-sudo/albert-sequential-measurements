/- SPDX-License-Identifier: Apache-2.0 -/
module
public import ThreeAtomAndFourPoint
public import AlbertExceptionality
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-! The nonunital subalgebra and homomorphism of core Corollary F.4. -/
@[expose] public section
noncomputable section
namespace AlbertSequential

private theorem adjoinUnit_product (x y : Albert) (a b : ℝ) :
    jordanMul (x + a • albertUnit) (y + b • albertUnit) =
      (jordanMul x y + b • x + a • y) + (a * b) • albertUnit := by
  simp only [jordanMul_add_left, jordanMul_add_right, jordanMul_smul_left,
    jordanMul_smul_right, jordanMul_albertUnit_left, jordanMul_albertUnit_right, smul_add, smul_smul, mul_comm b a]
  abel

/-- Unital generation by the tests forces generation without adjoining a unit.
Otherwise the scalar coordinate on the unitization would be a real character. -/
theorem submodule_eq_top_of_generatesAlbert {ι : Type*} {p : ι → Albert}
    (hgen : GeneratesAlbert p) (C : Submodule ℝ Albert)
    (hmul : ∀ x ∈ C, ∀ y ∈ C, jordanMul x y ∈ C) (hpC : ∀ i, p i ∈ C) : C = ⊤ := by
  let D : NativeJordanSubalgebra := {
    carrier := C ⊔ Submodule.span ℝ {albertUnit}
    unit_mem := Submodule.mem_sup_right (Submodule.subset_span (by simp))
    product_mem := by
      intro x hx y hy
      obtain ⟨x₀, hx₀, u, hu, rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨y₀, hy₀, v, hv, rfl⟩ := Submodule.mem_sup.mp hy
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
      obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hv
      rw [adjoinUnit_product]
      exact Submodule.mem_sup.mpr ⟨_, C.add_mem (C.add_mem (hmul _ hx₀ _ hy₀) (C.smul_mem b hx₀))
        (C.smul_mem a hy₀), _, Submodule.mem_span_singleton.mpr ⟨_, rfl⟩, rfl⟩ }
  have decomp (x : Albert) : ∃ y ∈ C, ∃ a : ℝ, y + a • albertUnit = x := by
    obtain ⟨y, hy, u, hu, h⟩ := Submodule.mem_sup.mp
      (hgen x D (fun i => Submodule.mem_sup_left (hpC i)))
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
    exact ⟨y, hy, a, h⟩
  have he : albertUnit ∈ C := by
    by_contra hn
    have hq : C.mkQ albertUnit ≠ 0 := by simpa [Submodule.mkQ_apply] using hn
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℝ hq
    let g := f.comp C.mkQ
    have gone : g albertUnit = 1 := hf
    have gz {z : Albert} (hz : z ∈ C) : g z = 0 := by
      change f (Submodule.Quotient.mk z) = 0
      rw [(Submodule.Quotient.mk_eq_zero C).mpr hz, map_zero]
    have hg : IsJordanHom g := by
      intro x y
      obtain ⟨u, hu, a, rfl⟩ := decomp x
      obtain ⟨v, hv, b, rfl⟩ := decomp y
      simp only [adjoinUnit_product, map_add, map_smul, gz (hmul _ hu _ hv), gz hu, gz hv, gone,
        smul_eq_mul]
      ring
    have hzero := LinearMap.congr_fun (albertJordanHom_eq_zero ℝ g hg) albertUnit
    simp [gone] at hzero
  apply top_unique
  intro x _
  obtain ⟨y, hy, a, rfl⟩ := decomp x
  exact C.add_mem hy (C.smul_mem a he)

/-- At any chosen base, a nonzero native discriminant forces every Jordan map
on any product-closed subspace containing the tests to vanish on the base. -/
theorem tetrahedron_subalgebra_obstruction {A : Type*} [NonUnitalRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (σ : Equiv.Perm (Fin 4))
    (hΔ : tetrahedronDiscriminant (nativeOverlaps (p ∘ σ)) (nativeTriangles (p ∘ σ))
      (nativeCornerQ (p ∘ σ)) ≠ 0)
    (C : Submodule ℝ Albert) (hm : ∀ x ∈ C, ∀ y ∈ C, jordanMul x y ∈ C) (hc : ∀ i, p i ∈ C)
    (η : C →ₗ[ℝ] A) (hη : ∀ x y : C, η ⟨jordanMul x y, hm _ x.2 _ y.2⟩ =
      (1 / 2 : ℝ) • (η x * η y + η y * η x)) :
    η ⟨p (σ 0), hc _⟩ = 0 ∧ ¬ Function.Injective η := by
  let q := p ∘ σ
  have hq : ∀ i, IsAtom (q i) := fun i => hp _
  rw [tetrahedronDiscriminant_eq_overlap_mul_fourPointInvariant] at hΔ
  have hn : fourPointInvariant q ≠ 0 := fun h => hΔ (by change _ * fourPointInvariant q = 0; rw [h, mul_zero])
  have hg := (fourPointInvariant_pos_iff q hq).mp (lt_of_le_of_ne (fourPointInvariant_nonneg q hq) hn.symm)
  have htop := submodule_eq_top_of_generatesAlbert hg C hm (fun i => hc _)
  let incl : Albert →ₗ[ℝ] C := LinearMap.id.codRestrict C (fun x => by rw [htop]; trivial)
  have h := albertJordanHom_eq_zero A (η.comp incl) (fun x y => hη (incl x) (incl y))
  have hz : η ⟨p (σ 0), hc _⟩ = 0 := LinearMap.congr_fun h (p (σ 0))
  refine ⟨hz, fun hinj => ?_⟩
  have hbase : p (σ 0) = 0 := congrArg Subtype.val (hinj (hz.trans η.map_zero.symm))
  have ht := (hp (σ 0)).2
  rw [hbase, NativeAnalysis.albertTrace_zero] at ht
  exact zero_ne_one ht

end AlbertSequential
