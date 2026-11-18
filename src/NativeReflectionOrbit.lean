/- SPDX-License-Identifier: Apache-2.0 -/
module

public import OrbitProjectionLabels
public import LinearRelationDescent
public import NativeAtomReflections
public import NativePeirceIdentities
public import NativeWordDuality

/-!
Literal native reflection orbits for the full generated Jordan algebra.
This private binding uses the native atom/reflection modules. No fixed S,
dimension restriction or reconstruction axiom is introduced.
-/
@[expose] public section
noncomputable section
namespace AlbertSequential
open NativeAnalysis

section ReflectionOrbit
variable {ι : Type*} (p : ι → Albert) (hp : ∀ i, IsAtom (p i))

def nativeOutcomeUpdate (p : ι → Albert) (a : Outcome ι) : Module.End ℝ Albert :=
  quadraticMapLinear (nativeOutcome p a)

def nativeReflectionWordAutomorphism (p : ι → Albert) (hp : ∀ i, IsAtom (p i)) :
    List ι → NativeAlbertAutomorphism
  | [] => nativeAutomorphismIdentity
  | i :: g => nativeAutomorphismComposition (atomReflectionAutomorphism (p i) (hp i))
      (nativeReflectionWordAutomorphism p hp g)

def nativeOrbitPoint (p : ι → Albert) (hp : ∀ i, IsAtom (p i))
    (α : ReflectionOrbitLabel ι) : Albert :=
  (nativeReflectionWordAutomorphism p hp α.1).linearEquiv (p α.2)

theorem nativeOrbitPoint_isAtom (α : ReflectionOrbitLabel ι) :
    IsAtom (nativeOrbitPoint p hp α) :=
  nativeAutomorphism_atom _ _ (hp α.2)

theorem sequentialReflectionUpdate_native (i : ι) (x : Albert) :
    sequentialReflectionUpdate (nativeOutcomeUpdate p) i x =
      quadraticMap ((2 : ℝ) • p i - albertUnit) x := by
  change (2 : ℝ) • (quadraticMap (nativeOutcome p (i, true)) x +
    quadraticMap (nativeOutcome p (i, false)) x) - x = _
  simpa only [nativeOutcome, Bool.false_eq_true, ↓reduceIte] using
    (quadraticMap_symmetry (p i) x).symm

theorem reflectionWordUpdate_native (g : List ι) (x : Albert) :
    reflectionWordUpdate (nativeOutcomeUpdate p) g x =
      (nativeReflectionWordAutomorphism p hp g).linearEquiv x := by
  induction g with
  | nil => rfl
  | cons i g ih =>
      simp only [reflectionWordUpdate, LinearMap.comp_apply, ih,
        sequentialReflectionUpdate_native, nativeReflectionWordAutomorphism,
        nativeAutomorphismComposition_apply, atomReflectionAutomorphism_apply]

theorem nativeReflectionWord_append (g h : List ι) (x : Albert) :
    (nativeReflectionWordAutomorphism p hp (g ++ h)).linearEquiv x =
      (nativeReflectionWordAutomorphism p hp g).linearEquiv
        ((nativeReflectionWordAutomorphism p hp h).linearEquiv x) := by
  induction g with
  | nil => rfl
  | cons i g ih =>
      simp only [List.cons_append, nativeReflectionWordAutomorphism,
        nativeAutomorphismComposition_apply, ih]

theorem nativeReflectionWord_reverse_left (g : List ι) (x : Albert) :
    (nativeReflectionWordAutomorphism p hp g.reverse).linearEquiv
      ((nativeReflectionWordAutomorphism p hp g).linearEquiv x) = x := by
  induction g with
  | nil => rfl
  | cons i g ih =>
      simp only [List.reverse_cons, nativeReflectionWord_append,
        nativeReflectionWordAutomorphism, nativeAutomorphismComposition_apply,
        nativeAutomorphismIdentity_apply, atomReflectionAutomorphism_apply,
        atomReflection_involutive (p i) (hp i), ih]

theorem nativeReflectionWord_reverse_right (g : List ι) (x : Albert) :
    (nativeReflectionWordAutomorphism p hp g).linearEquiv
      ((nativeReflectionWordAutomorphism p hp g.reverse).linearEquiv x) = x := by
  simpa only [List.reverse_reverse] using nativeReflectionWord_reverse_left p hp g.reverse x

theorem orbitCornerUpdate_native (g : List ι) (i : ι) (x : Albert) :
    orbitCornerUpdate (nativeOutcomeUpdate p) g i x =
      quadraticMap (nativeOrbitPoint p hp (g, i)) x := by
  change reflectionWordUpdate (nativeOutcomeUpdate p) g
    (quadraticMap (nativeOutcome p (i, true))
      (reflectionWordUpdate (nativeOutcomeUpdate p) g.reverse x)) = _
  simp only [reflectionWordUpdate_native p hp, nativeOutcome, ↓reduceIte]
  rw [nativeAutomorphism_quadraticMap, nativeReflectionWord_reverse_right]
  rfl

theorem orbitReflectionUpdate_native (g : List ι) (i : ι) (x : Albert) :
    orbitReflectionUpdate (nativeOutcomeUpdate p) g i x =
      quadraticMap ((2 : ℝ) • nativeOrbitPoint p hp (g, i) - albertUnit) x := by
  change reflectionWordUpdate (nativeOutcomeUpdate p) g
    (sequentialReflectionUpdate (nativeOutcomeUpdate p) i
      (reflectionWordUpdate (nativeOutcomeUpdate p) g.reverse x)) = _
  simp only [reflectionWordUpdate_native p hp, sequentialReflectionUpdate_native]
  rw [nativeAutomorphism_reflection, nativeReflectionWord_reverse_right]
  rfl

theorem nativeOrbitPoint_reflected_label (α β : ReflectionOrbitLabel ι) :
    nativeOrbitPoint p hp (reflectedOrbitLabel α β) =
      quadraticMap ((2 : ℝ) • nativeOrbitPoint p hp α - albertUnit) (nativeOrbitPoint p hp β) := by
  change (nativeReflectionWordAutomorphism p hp
    (α.1 ++ [α.2] ++ α.1.reverse ++ β.1)).linearEquiv (p β.2) = _
  simp only [nativeReflectionWord_append, nativeReflectionWordAutomorphism,
    nativeAutomorphismComposition_apply, nativeAutomorphismIdentity_apply,
    atomReflectionAutomorphism_apply]
  rw [nativeAutomorphism_reflection]
  congr 1
  exact nativeReflectionWord_reverse_right p hp α.1 (nativeOrbitPoint p hp β)

def nativeOrbitSpan (p : ι → Albert) (hp : ∀ i, IsAtom (p i)) : Submodule ℝ Albert :=
  Submodule.span ℝ (Set.range (unitAndAtomLabels albertUnit (nativeOrbitPoint p hp)))

theorem nativeOrbitPoint_mem_span (α : ReflectionOrbitLabel ι) :
    nativeOrbitPoint p hp α ∈ nativeOrbitSpan p hp := Submodule.subset_span ⟨some α, rfl⟩

theorem nativeUnit_mem_orbitSpan : albertUnit ∈ nativeOrbitSpan p hp :=
  Submodule.subset_span ⟨none, rfl⟩

theorem nativeOrbitSpan_quadratic (α : ReflectionOrbitLabel ι) (x : Albert) :
    quadraticMap (nativeOrbitPoint p hp α) x ∈ nativeOrbitSpan p hp := by
  rw [quadraticMap_atom _ _ (nativeOrbitPoint_isAtom p hp α)]
  exact (nativeOrbitSpan p hp).smul_mem _ (nativeOrbitPoint_mem_span p hp α)

theorem nativeOrbitSpan_reflection (α : ReflectionOrbitLabel ι) {x : Albert}
    (hx : x ∈ nativeOrbitSpan p hp) :
    quadraticMap ((2 : ℝ) • nativeOrbitPoint p hp α - albertUnit) x ∈ nativeOrbitSpan p hp := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨i, rfl⟩
      cases i with
      | none =>
          rw [unitAndAtomLabels, idempotent_symmetry_unit _ (nativeOrbitPoint_isAtom p hp α).1]
          exact nativeUnit_mem_orbitSpan p hp
      | some β =>
          rw [unitAndAtomLabels, ← nativeOrbitPoint_reflected_label]
          exact nativeOrbitPoint_mem_span p hp _
  | zero => simpa only [quadraticMap_zero_right] using (nativeOrbitSpan p hp).zero_mem
  | add x y hx hy ihx ihy =>
      rw [quadraticMap_add_right]
      exact (nativeOrbitSpan p hp).add_mem ihx ihy
  | smul r x hx ih =>
      rw [quadraticMap_smul_right]
      exact (nativeOrbitSpan p hp).smul_mem r ih

theorem nativeOrbitSpan_product {x y : Albert}
    (hx : x ∈ nativeOrbitSpan p hp) (hy : y ∈ nativeOrbitSpan p hp) :
    jordanMul x y ∈ nativeOrbitSpan p hp := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨i, rfl⟩
      cases i with
      | none => simpa only [unitAndAtomLabels, jordanMul_albertUnit_left] using hy
      | some α =>
          rw [unitAndAtomLabels, peirce_identity]
          exact (nativeOrbitSpan p hp).add_mem (nativeOrbitSpan_quadratic p hp α y)
            ((nativeOrbitSpan p hp).smul_mem _ ((nativeOrbitSpan p hp).sub_mem hy
              (nativeOrbitSpan_reflection p hp α hy)))
  | zero => simpa only [jordanMul_zero_left] using (nativeOrbitSpan p hp).zero_mem
  | add x z hx hz ihx ihz => rw [jordanMul_add_left]; exact (nativeOrbitSpan p hp).add_mem ihx ihz
  | smul r x hx ih => rw [jordanMul_smul_left]; exact (nativeOrbitSpan p hp).smul_mem r ih

def nativeOrbitJordanSubalgebra : NativeJordanSubalgebra where
  carrier := nativeOrbitSpan p hp
  unit_mem := nativeUnit_mem_orbitSpan p hp
  product_mem := fun _ hx _ hy => nativeOrbitSpan_product p hp hx hy

theorem nativeQuadraticMap_mem_subalgebra (B : NativeJordanSubalgebra)
    {x y : Albert} (hx : x ∈ B.carrier) (hy : y ∈ B.carrier) :
    quadraticMap x y ∈ B.carrier := by
  unfold quadraticMap
  rw [two_smul]
  exact B.carrier.sub_mem
    (B.carrier.add_mem (B.product_mem x hx _ (B.product_mem x hx y hy))
      (B.product_mem x hx _ (B.product_mem x hx y hy)))
    (B.product_mem _ (B.product_mem x hx x hx) y hy)

theorem nativeReflectionWord_mem_subalgebra (B : NativeJordanSubalgebra)
    (hB : ∀ i, p i ∈ B.carrier) (g : List ι) {x : Albert} (hx : x ∈ B.carrier) :
    (nativeReflectionWordAutomorphism p hp g).linearEquiv x ∈ B.carrier := by
  induction g with
  | nil => exact hx
  | cons i g ih =>
      simp only [nativeReflectionWordAutomorphism, nativeAutomorphismComposition_apply,
        atomReflectionAutomorphism_apply]
      exact nativeQuadraticMap_mem_subalgebra B
        (B.carrier.sub_mem (B.carrier.smul_mem (2 : ℝ) (hB i)) B.unit_mem) ih

theorem nativeOrbitSpan_le_subalgebra (B : NativeJordanSubalgebra)
    (hB : ∀ i, p i ∈ B.carrier) : nativeOrbitSpan p hp ≤ B.carrier := by
  apply Submodule.span_le.mpr
  intro x hx
  rcases hx with ⟨i, rfl⟩
  cases i with
  | none => exact B.unit_mem
  | some α => exact nativeReflectionWord_mem_subalgebra p hp B hB α.1 (hB α.2)

/-- Equality with the FULL unital generated Jordan algebra, including proper
subalgebras. This is not a replacement by a fixed finite test configuration. -/
theorem nativeOrbitSpan_iff_generated (x : Albert) :
    x ∈ nativeOrbitSpan p hp ↔ InGeneratedAlgebra p x := by
  constructor
  · intro hx B hB
    exact nativeOrbitSpan_le_subalgebra p hp B hB hx
  · intro hx
    exact hx (nativeOrbitJordanSubalgebra p hp) (fun i => by
      change p i ∈ nativeOrbitSpan p hp
      simpa only [nativeOrbitPoint, nativeReflectionWordAutomorphism,
        nativeAutomorphismIdentity_apply] using nativeOrbitPoint_mem_span p hp ([], i))

theorem nativeOrbitSpan_eq_top_of_generates (hg : GeneratesAlbert p) : nativeOrbitSpan p hp = ⊤ := by
  apply top_unique
  intro x hx
  exact hg x (nativeOrbitJordanSubalgebra p hp) (fun i => by
    change p i ∈ nativeOrbitSpan p hp
    simpa only [nativeOrbitPoint, nativeReflectionWordAutomorphism,
      nativeAutomorphismIdentity_apply] using nativeOrbitPoint_mem_span p hp ([], i))

end ReflectionOrbit
end AlbertSequential
