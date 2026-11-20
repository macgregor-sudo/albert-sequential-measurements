/- SPDX-License-Identifier: Apache-2.0 -/
module
public import JordanTripleTransport
public import TetrahedronEngine
public import ThreeAtomAndFourPoint

/-! Transport of the printed corner identities through a possibly nonunital domain. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.SubalgebraCorner
variable {A : Type*} [NonUnitalRing A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
variable (C : Submodule ℝ Albert) (hm : ∀ x ∈ C, ∀ y ∈ C, jordanMul x y ∈ C)
def prod (x y : C) : C := ⟨jordanMul x y, hm _ x.2 _ y.2⟩
def quad (x y : C) : C := 2 • prod C hm x (prod C hm x y) - prod C hm (prod C hm x x) y
def triple (x y z : C) : C :=
  prod C hm (prod C hm x y) z + prod C hm (prod C hm z y) x - prod C hm (prod C hm x z) y
variable (η : C →ₗ[ℝ] A) (hη : ∀ x y, η (prod C hm x y) = (1/2 : ℝ) • (η x * η y + η y * η x))
include hη
theorem map_quad (x y : C) : η (quad C hm x y) = η x * η y * η x := by
  simp only [quad, map_sub, map_nsmul, hη, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_assoc]
  module
theorem map_triple (x y z : C) : η (triple C hm x y z) =
    (1/2 : ℝ) • (η x * η y * η z + η z * η y * η x) := by
  simp only [triple, map_sub, map_add, hη, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_assoc]
  module

theorem atom_compression (x y : C) (hx : IsAtom x.val) :
    η x * η y * η x = tracePairing x y • η x := by
  have h : quad C hm x y = tracePairing x y • x :=
    Subtype.ext (AlbertSequential.quadraticMap_atom x y hx)
  rw [← map_quad C hm η hη, h, map_smul]

/-- Idempotence and R1–R3 for every ordered choice from the four given atoms. -/
theorem atom_corner_relations (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hc : ∀ i, p i ∈ C) :
    let X := fun i => η ⟨p i, hc i⟩
    (∀ a, X a * X a = X a) ∧
    (∀ a b, X a * X b * X a = nativeOverlaps p a b • X a) ∧
    (∀ a b c, X a * (X b * X c + X c * X b) * X a = (2 * nativeTriangles p a b c) • X a) ∧
    (∀ a b c d, X a * (X b * X c * X d + X d * X c * X b) * X a =
      (2 * tracePairing (p a) (jordanTriple (p b) (p c) (p d))) • X a) := by
  let q (i : Fin 4) : C := ⟨p i, hc i⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    have hid : prod C hm (q a) (q a) = q a := Subtype.ext (hp a).1
    have h := hη (q a) (q a)
    rw [hid] at h
    change η (q a) * η (q a) = η (q a)
    linear_combination (norm := module) -h
  · intro a b
    exact atom_compression C hm η hη (q a) (q b) (hp a)
  · intro a b c
    have h := atom_compression C hm η hη (q a) (prod C hm (q b) (q c)) (hp a)
    rw [hη, mul_smul_comm, smul_mul_assoc] at h
    change η (q a) * _ * η (q a) = (2 * tracePairing (q a) (prod C hm (q b) (q c))) • η (q a)
    linear_combination (norm := module) (2 : ℝ) • h
  · intro a b c d
    have h := atom_compression C hm η hη (q a) (triple C hm (q b) (q c) (q d)) (hp a)
    rw [map_triple C hm η hη, mul_smul_comm, smul_mul_assoc] at h
    change η (q a) * _ * η (q a) = (2 * tracePairing (q a) (triple C hm (q b) (q c) (q d))) • η (q a)
    linear_combination (norm := module) (2 : ℝ) • h

theorem discriminant_annihilates_subalgebra_base (p : Fin 4 → Albert)
    (hp : ∀ i, IsAtom (p i)) (hc : ∀ i, p i ∈ C) :
    tetrahedronDiscriminant (nativeOverlaps p) (nativeTriangles p) (nativeCornerQ p) •
      η ⟨p 0, hc 0⟩ = 0 := by
  obtain ⟨hid, ho, hR, hQ⟩ := atom_corner_relations C hm η hη p hp hc
  apply tetrahedron_annihilates_base (fun i => η ⟨p i, hc i⟩)
  exact {
    idempotent := hid
    overlap_symmetric := fpOverlap_symm p
    triangle_swap := fun i j k => by
      simp only [← fpTriangle_eq_nativeTriangles]
      exact ⟨fpTriangle_swap12 p i j k, fpTriangle_swap23 p i j k⟩
    pair := fun i j _ => ho i j
    triangle_012 := hR 0 1 2
    triangle_023 := hR 0 2 3
    triangle_031 := hR 0 3 1
    triangle_123 := hR 1 2 3
    quadruple_123 := hQ 0 1 2 3
    quadruple_231 := hQ 0 2 3 1
    quadruple_312 := hQ 0 3 1 2 }

end AlbertSequential.SubalgebraCorner
