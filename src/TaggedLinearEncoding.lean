/- SPDX-License-Identifier: Apache-2.0 -/
module

public import TaggedBlockStates

/-! Exact linear bookkeeping for tagged simulations. Each source piece has
its own decoder; this does not assume a positive encoding of an entire theory. -/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace AlbertSequential
variable {T E : Type*} [Fintype T] [DecidableEq T]
  {ι : T → Type*} [∀ t, Fintype (ι t)] [∀ t, DecidableEq (ι t)]
  [AddCommGroup E] [Module ℝ E]

def taggedLinearEncoding (e : ∀ t, E →ₗ[ℝ] Matrix (ι t) (ι t) ℝ) :
    (T → E) →ₗ[ℝ] Matrix (Sigma ι) (Sigma ι) ℝ where
  toFun x := taggedBlockState (fun t => e t (x t))
  map_add' x y := by
    unfold taggedBlockState
    simp only [Pi.add_apply, map_add, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' r x := by
    unfold taggedBlockState
    simp only [Pi.smul_apply, map_smul, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum,
      RingHom.id_apply]

theorem taggedLinearEncoding_apply (e : ∀ t, E →ₗ[ℝ] Matrix (ι t) (ι t) ℝ)
    (x : T → E) : taggedLinearEncoding e x = taggedBlockState (fun t => e t (x t)) := rfl

def taggedLinearDecoding (d : T → Module.End ℝ E) : (T → E) →ₗ[ℝ] E where
  toFun x := ∑ t, d t (x t)
  map_add' x y := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' r x := by simp only [Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]

theorem taggedLinearEncoding_extract (e : ∀ t, E →ₗ[ℝ] Matrix (ι t) (ι t) ℝ)
    (x : T → E) (t : T) :
    (taggedBlockInclusion (ι := ι) t).conjTranspose * taggedLinearEncoding e x *
      taggedBlockInclusion (ι := ι) t = e t (x t) := taggedBlockState_extract _ t

theorem taggedLinearEncoding_single (e : ∀ t, E →ₗ[ℝ] Matrix (ι t) (ι t) ℝ)
    (t : T) (x : E) :
    taggedLinearEncoding e (Pi.single t x) =
      taggedBlockInclusion (ι := ι) t * e t x * (taggedBlockInclusion (ι := ι) t).conjTranspose := by
  rw [taggedLinearEncoding_apply]
  have he : (fun s => e s ((Pi.single t x : T → E) s)) = Pi.single t (e t x) := by
    funext s
    by_cases hs : s = t
    · subst s
      rw [Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hs, Pi.single_eq_of_ne hs, map_zero]
  rw [he, taggedBlockState_single]

theorem taggedLinearDecoding_single (d : T → Module.End ℝ E) (t : T) (x : E) :
    taggedLinearDecoding d (Pi.single t x) = d t x := by
  change ∑ s, d s ((Pi.single t x : T → E) s) = _
  rw [Finset.sum_eq_single t]
  · rw [Pi.single_eq_same]
  · intro s _ hst
    rw [Pi.single_eq_of_ne hst, map_zero]
  · simp

theorem taggedLinearEncoding_trace (e : ∀ t, E →ₗ[ℝ] Matrix (ι t) (ι t) ℝ)
    (d : T → Module.End ℝ E) (ell : E →ₗ[ℝ] ℝ)
    (h : ∀ t x, Matrix.trace (e t x) = ell (d t x)) (x : T → E) :
    Matrix.trace (taggedLinearEncoding e x) = ell (taggedLinearDecoding d x) := by
  rw [taggedLinearEncoding_apply, taggedBlockState_trace]
  change (∑ s, Matrix.trace (e s (x s))) = ell (∑ s, d s (x s))
  simp only [h, map_sum]

def taggedLinearUpdate (t : T) (f : T → Module.End ℝ E) : (T → E) →ₗ[ℝ] (T → E) where
  toFun x := Pi.single t (∑ s, f s (x s))
  map_add' x y := by
    simp only [Pi.add_apply, map_add, Finset.sum_add_distrib, Pi.single_add]
  map_smul' r x := by
    simp only [Pi.smul_apply, map_smul, ← Finset.smul_sum, Pi.single_smul, RingHom.id_apply]

theorem taggedLinearUpdate_encoding (e : ∀ t, E →ₗ[ℝ] Matrix (ι t) (ι t) ℝ)
    (t : T) (f : T → Module.End ℝ E) (K : ∀ s, List (Matrix (ι t) (ι s) ℝ))
    (h : ∀ s x, rectangularKrausAction (K s) (e s x) = e t (f s x)) (x : T → E) :
    rectangularKrausAction (taggedKrausList t K) (taggedLinearEncoding e x) =
      taggedLinearEncoding e (taggedLinearUpdate t f x) := by
  rw [taggedKrausList_action]
  simp_rw [taggedLinearEncoding_extract, h]
  change (∑ s, taggedBlockInclusion (ι := ι) t * e t (f s (x s)) *
    (taggedBlockInclusion (ι := ι) t).conjTranspose) = taggedLinearEncoding e
      (Pi.single t (∑ s, f s (x s)))
  rw [taggedLinearEncoding_single, map_sum, Matrix.mul_sum, Matrix.sum_mul]

theorem taggedLinearUpdate_decoding (d : T → Module.End ℝ E)
    (t : T) (f : T → Module.End ℝ E) (B : Module.End ℝ E)
    (h : ∀ s x, d t (f s x) = B (d s x)) (x : T → E) :
    taggedLinearDecoding d (taggedLinearUpdate t f x) = B (taggedLinearDecoding d x) := by
  change taggedLinearDecoding d (Pi.single t (∑ s, f s (x s))) = _
  rw [taggedLinearDecoding_single, map_sum]
  simp only [h, taggedLinearDecoding, LinearMap.coe_mk, AddHom.coe_mk, map_sum]

end AlbertSequential
