/- SPDX-License-Identifier: Apache-2.0 -/
module

public import TaggedLinearEncoding

/-! All-history stationary transfer for a supplied tagged construction.
The first letter acts first; no positive mass or conditional state is required. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
variable {T E X : Type*} [Fintype T] [DecidableEq T]
  {ι : T → Type*} [∀ t, Fintype (ι t)] [∀ t, DecidableEq (ι t)]
  [AddCommGroup E] [Module ℝ E]

theorem taggedLinearWord_encoding
    (e : ∀ t, E →ₗ[ℝ] Matrix (ι t) (ι t) ℝ)
    (t : X → T) (f : X → T → Module.End ℝ E)
    (K : ∀ a s, List (Matrix (ι (t a)) (ι s) ℝ))
    (h : ∀ a s x, rectangularKrausAction (K a s) (e s x) = e (t a) (f a s x))
    (xs : T → E) (w : List X) :
    w.foldl (fun Y a => rectangularKrausAction (taggedKrausList (t a) (K a)) Y)
      (taggedLinearEncoding e xs) =
    taggedLinearEncoding e (w.foldl (fun ys a => taggedLinearUpdate (t a) (f a) ys) xs) := by
  induction w generalizing xs with
  | nil => rfl
  | cons a w ih =>
    simp only [List.foldl_cons]
    rw [taggedLinearUpdate_encoding e (t a) (f a) (K a) (h a), ih]

theorem taggedLinearWord_decoding (d : T → Module.End ℝ E)
    (t : X → T) (f : X → T → Module.End ℝ E) (B : X → Module.End ℝ E)
    (h : ∀ a s x, d (t a) (f a s x) = B a (d s x))
    (xs : T → E) (w : List X) :
    taggedLinearDecoding d (w.foldl (fun ys a => taggedLinearUpdate (t a) (f a) ys) xs) =
      w.foldl (fun y a => B a y) (taggedLinearDecoding d xs) := by
  induction w generalizing xs with
  | nil => rfl
  | cons a w ih =>
    simp only [List.foldl_cons]
    rw [ih, taggedLinearUpdate_decoding d (t a) (f a) (B a) (h a)]

theorem taggedAllWordSimulation
    (e : ∀ t, E →ₗ[ℝ] Matrix (ι t) (ι t) ℝ)
    (d : T → Module.End ℝ E) (ell : E →ₗ[ℝ] ℝ)
    (htrace : ∀ t x, Matrix.trace (e t x) = ell (d t x))
    (t : X → T) (f : X → T → Module.End ℝ E) (B : X → Module.End ℝ E)
    (K : ∀ a s, List (Matrix (ι (t a)) (ι s) ℝ))
    (hencode : ∀ a s x, rectangularKrausAction (K a s) (e s x) = e (t a) (f a s x))
    (hdecode : ∀ a s x, d (t a) (f a s x) = B a (d s x))
    (xs : T → E) (w : List X) :
    Matrix.trace (w.foldl (fun Y a => rectangularKrausAction (taggedKrausList (t a) (K a)) Y)
      (taggedLinearEncoding e xs)) =
    ell (w.foldl (fun y a => B a y) (taggedLinearDecoding d xs)) := by
  rw [taggedLinearWord_encoding e t f K hencode,
    taggedLinearEncoding_trace e d ell htrace,
    taggedLinearWord_decoding d t f B hdecode]

end AlbertSequential
