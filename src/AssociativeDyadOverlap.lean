/- SPDX-License-Identifier: Apache-2.0 -/
module
public import SubalgebraCoordsAndLine
public import NativeWordPositivity
import Mathlib.Tactic.Ring

/-! Normalized dyads and their transition probability, core Appendix B. -/
@[expose] public section
noncomputable section
namespace AlbertSequential

def octColumnNormSq (u : Fin 3 → Octonion) : ℝ := ∑ i, octNormSq (u i)

def normalizedOctDyad (u : Fin 3 → Octonion) : Albert :=
  (1 / octColumnNormSq u : ℝ) • octDyad u

def octColumnInner (u v : Fin 3 → Octonion) : Octonion :=
  ∑ i, octonionMul (octonionConj (u i)) (v i)

private theorem embedding_norm (φ : Quaternion ℝ →ₗ[ℝ] Octonion) (hφ : IsQuatEmbedding φ)
    (q : Quaternion ℝ) : octNormSq (φ q) = quatNormSq q := by
  rw [octNormSq, octDot, ← hφ.map_star, ← hφ.map_mul, hφ.map_re]
  change (q * star q).re = q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2
  rw [Quaternion.re_mul]
  simp only [Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star]
  ring

private theorem embedding_dyad (φ : Quaternion ℝ →ₗ[ℝ] Octonion) (hφ : IsQuatEmbedding φ)
    (u : Fin 3 → Quaternion ℝ) :
    normalizedOctDyad (fun i => φ (u i)) = quatDyad φ u (octColumnNormSq (fun i => φ (u i))) := by
  rw [normalizedOctDyad, octDyad_eq_quatDyad φ hφ]
  simp only [quatDyad, div_one, one_smul]
  rfl

theorem normalizedOctDyad_atom_and_overlap (F : OctSubalgebra)
    (hF : ∀ x ∈ F.carrier, ∀ y ∈ F.carrier, ∀ z ∈ F.carrier, octAssociator x y z = 0)
    (u v : Fin 3 → Octonion) (hu : ∀ i, u i ∈ F.carrier) (hv : ∀ i, v i ∈ F.carrier)
    (hnu : octColumnNormSq u ≠ 0) (hnv : octColumnNormSq v ≠ 0) :
    IsAtom (normalizedOctDyad u) ∧ IsAtom (normalizedOctDyad v) ∧
      tracePairing (normalizedOctDyad u) (normalizedOctDyad v) =
        octNormSq (octColumnInner u v) / (octColumnNormSq u * octColumnNormSq v) := by
  obtain ⟨φ,hφ,hsub⟩ := F.exists_quaternion_copy_of_associative hF
  choose a ha using fun i => hsub (hu i)
  choose b hb using fun i => hsub (hv i)
  obtain rfl : (fun i => φ (a i)) = u := funext ha
  obtain rfl : (fun i => φ (b i)) = v := funext hb
  have hsum (c : Fin 3 → Quaternion ℝ) :
      ∑ i, quatNormSq (c i) = octColumnNormSq (fun i => φ (c i)) := by
    simp [octColumnNormSq, embedding_norm φ hφ]
  have hinner : octColumnInner (fun i => φ (a i)) (fun i => φ (b i)) =
      φ (∑ i, star (a i) * b i) := by simp [octColumnInner, hφ.map_mul, hφ.map_star]
  rw [embedding_dyad φ hφ, embedding_dyad φ hφ, hinner, embedding_norm φ hφ]
  have hA := quatDyad_isAtom φ hφ a _ hnu (hsum a)
  refine ⟨hA, quatDyad_isAtom φ hφ b _ hnv (hsum b), ?_⟩
  have ht := congrArg albertTrace (quadraticMap_quatDyad φ hφ a b _ (octColumnNormSq (fun i => φ (b i))) hnu (hsum a))
  rwa [NativeAnalysis.albertTrace_quadraticMap, hA.1, albertTrace_smul, hA.2, mul_one] at ht

end AlbertSequential
