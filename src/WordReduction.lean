/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib.Data.List.GetD

/-! Chronological word reduction by old letters, identity and impossible
outcomes. Zero states are retained without conditioning or cancellation. -/
@[expose] public section
namespace AlbertSequential.WordReduction

inductive Step (B : Type*) where
  | impossible
  | skip
  | letter (b : B)

def translate {A B : Type*} (s : A → Step B) : List A → Option (List B)
  | [] => some []
  | a :: w => match s a with
    | .impossible => none
    | .skip => translate s w
    | .letter b => (translate s w).map (b :: ·)

def applyStep {B M : Type*} [Zero M] (f : B → M → M) : Step B → M → M
  | .impossible, _ => 0
  | .skip, x => x
  | .letter b, x => f b x

@[simp] theorem applyStep_impossible {B M : Type*} [Zero M] (f : B → M → M) (x : M) :
    applyStep f .impossible x = 0 := rfl

@[simp] theorem applyStep_skip {B M : Type*} [Zero M] (f : B → M → M) (x : M) :
    applyStep f .skip x = x := rfl

@[simp] theorem applyStep_letter {B M : Type*} [Zero M] (f : B → M → M) (b : B) (x : M) :
    applyStep f (.letter b) x = f b x := rfl

theorem foldl_zero {A B M : Type*} [Zero M] (f : B → M → M) (s : A → Step B)
    (hf : ∀ b, f b 0 = 0) (w : List A) :
    w.foldl (fun x a => applyStep f (s a) x) 0 = 0 := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [List.foldl_cons]
    cases hs : s a with
    | impossible => rw [applyStep_impossible]; exact ih
    | skip => rw [applyStep_skip]; exact ih
    | letter b => rw [applyStep_letter, hf]; exact ih

theorem foldl_translate {A B M : Type*} [Zero M] (f : B → M → M) (s : A → Step B)
    (hf : ∀ b, f b 0 = 0) (x : M) (w : List A) :
    w.foldl (fun y a => applyStep f (s a) y) x =
      match translate s w with
      | none => 0
      | some v => v.foldl (fun y b => f b y) x := by
  induction w generalizing x with
  | nil => rfl
  | cons a w ih =>
    rw [List.foldl_cons, translate]
    cases hs : s a with
    | impossible =>
      rw [applyStep_impossible]
      exact foldl_zero f s hf w
    | skip => rw [applyStep_skip]; exact ih x
    | letter b =>
      rw [applyStep_letter, ih]
      cases ht : translate s w <;> rfl

end AlbertSequential.WordReduction
