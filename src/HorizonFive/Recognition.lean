/- SPDX-License-Identifier: Apache-2.0
   Machine-generated file. -/
module

public import HorizonFive.RecogData1
public import HorizonFive.RecogData2
public import HorizonFive.RecogData3

/-! # lem:cer:h5:lift, per-class lifts (assembly)

The good words of length at most five, in the order of `(allWords 5).filter goodB`,
and the assembly `recognitionThroughFivePos`.  (Data modules:) each theorem `lw_<word>` gives an explicit Jordan expression `K` with `deg K ≤ |w|`, of degree one
in every letter occurring once in `w`, and `σ̂(K) = [w] - ℓ(w) [r_0r_1r_2r_3]`; the special value
is checked by expanding both sides in `ℝ[G]` (`lift_spec`), the degree and letter conditions and
`ℓ(w)` by kernel `decide`. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.HorizonFive

theorem forall_cons_of {P : List Test → Prop} {a : List Test} {l : List (List Test)}
    (h1 : P a) (h2 : ∀ x ∈ l, P x) : ∀ x ∈ a :: l, P x := by
  intro x hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact h1
  · exact h2 x hx

theorem forall_nil_of {P : List Test → Prop} : ∀ x ∈ ([] : List (List Test)), P x := by
  intro x hx
  simp at hx

/-- Good words, part 1. -/
def goodWords1 : List (List Test) :=
  [[0],
   [1],
   [2],
   [3],
   [1, 0],
   [2, 0],
   [3, 0],
   [0, 1],
   [2, 1],
   [3, 1],
   [0, 2],
   [1, 2],
   [3, 2],
   [0, 3],
   [1, 3],
   [2, 3],
   [0, 1, 0],
   [2, 1, 0],
   [3, 1, 0],
   [0, 2, 0],
   [1, 2, 0],
   [3, 2, 0],
   [0, 3, 0],
   [1, 3, 0],
   [2, 3, 0],
   [1, 0, 1],
   [2, 0, 1],
   [3, 0, 1],
   [0, 2, 1],
   [1, 2, 1],
   [3, 2, 1],
   [0, 3, 1],
   [1, 3, 1],
   [2, 3, 1],
   [1, 0, 2],
   [2, 0, 2],
   [3, 0, 2],
   [0, 1, 2],
   [2, 1, 2],
   [3, 1, 2],
   [0, 3, 2],
   [1, 3, 2],
   [2, 3, 2],
   [1, 0, 3],
   [2, 0, 3],
   [3, 0, 3],
   [0, 1, 3],
   [2, 1, 3],
   [3, 1, 3],
   [0, 2, 3],
   [1, 2, 3],
   [3, 2, 3],
   [2, 0, 1, 0],
   [3, 0, 1, 0],
   [0, 2, 1, 0],
   [1, 2, 1, 0],
   [3, 2, 1, 0],
   [0, 3, 1, 0],
   [1, 3, 1, 0],
   [2, 3, 1, 0],
   [1, 0, 2, 0],
   [3, 0, 2, 0],
   [0, 1, 2, 0],
   [2, 1, 2, 0],
   [3, 1, 2, 0],
   [0, 3, 2, 0],
   [1, 3, 2, 0],
   [2, 3, 2, 0],
   [1, 0, 3, 0],
   [2, 0, 3, 0],
   [0, 1, 3, 0],
   [2, 1, 3, 0],
   [3, 1, 3, 0],
   [0, 2, 3, 0],
   [1, 2, 3, 0],
   [3, 2, 3, 0],
   [2, 1, 0, 1],
   [3, 1, 0, 1],
   [0, 2, 0, 1],
   [1, 2, 0, 1]]

/-- Good words, part 2. -/
def goodWords2 : List (List Test) :=
  [[3, 2, 0, 1],
   [0, 3, 0, 1],
   [1, 3, 0, 1],
   [2, 3, 0, 1],
   [1, 0, 2, 1],
   [2, 0, 2, 1],
   [3, 0, 2, 1],
   [0, 1, 2, 1],
   [3, 1, 2, 1],
   [0, 3, 2, 1],
   [1, 3, 2, 1],
   [2, 3, 2, 1],
   [1, 0, 3, 1],
   [2, 0, 3, 1],
   [3, 0, 3, 1],
   [0, 1, 3, 1],
   [2, 1, 3, 1],
   [0, 2, 3, 1],
   [1, 2, 3, 1],
   [3, 2, 3, 1],
   [0, 1, 0, 2],
   [2, 1, 0, 2],
   [3, 1, 0, 2],
   [1, 2, 0, 2],
   [3, 2, 0, 2],
   [0, 3, 0, 2],
   [1, 3, 0, 2],
   [2, 3, 0, 2],
   [1, 0, 1, 2],
   [2, 0, 1, 2],
   [3, 0, 1, 2],
   [0, 2, 1, 2],
   [3, 2, 1, 2],
   [0, 3, 1, 2],
   [1, 3, 1, 2],
   [2, 3, 1, 2],
   [1, 0, 3, 2],
   [2, 0, 3, 2],
   [3, 0, 3, 2],
   [0, 1, 3, 2],
   [2, 1, 3, 2],
   [3, 1, 3, 2],
   [0, 2, 3, 2],
   [1, 2, 3, 2],
   [0, 1, 0, 3],
   [2, 1, 0, 3],
   [3, 1, 0, 3],
   [0, 2, 0, 3],
   [1, 2, 0, 3],
   [3, 2, 0, 3],
   [1, 3, 0, 3],
   [2, 3, 0, 3],
   [1, 0, 1, 3],
   [2, 0, 1, 3],
   [3, 0, 1, 3],
   [0, 2, 1, 3],
   [1, 2, 1, 3],
   [3, 2, 1, 3],
   [0, 3, 1, 3],
   [2, 3, 1, 3],
   [1, 0, 2, 3],
   [2, 0, 2, 3],
   [3, 0, 2, 3],
   [0, 1, 2, 3],
   [2, 1, 2, 3],
   [3, 1, 2, 3],
   [0, 3, 2, 3],
   [1, 3, 2, 3],
   [2, 1, 0, 1, 0],
   [3, 1, 0, 1, 0],
   [0, 2, 0, 1, 0],
   [1, 2, 0, 1, 0],
   [3, 2, 0, 1, 0],
   [0, 3, 0, 1, 0],
   [1, 3, 0, 1, 0],
   [2, 3, 0, 1, 0],
   [1, 0, 2, 1, 0],
   [2, 0, 2, 1, 0],
   [3, 0, 2, 1, 0],
   [0, 1, 2, 1, 0]]

/-- Good words, part 3. -/
def goodWords3 : List (List Test) :=
  [[2, 1, 2, 1, 0],
   [3, 1, 2, 1, 0],
   [0, 3, 2, 1, 0],
   [1, 3, 2, 1, 0],
   [2, 3, 2, 1, 0],
   [1, 0, 3, 1, 0],
   [2, 0, 3, 1, 0],
   [3, 0, 3, 1, 0],
   [0, 1, 3, 1, 0],
   [2, 1, 3, 1, 0],
   [3, 1, 3, 1, 0],
   [0, 2, 3, 1, 0],
   [1, 2, 3, 1, 0],
   [3, 2, 3, 1, 0],
   [0, 1, 0, 2, 0],
   [2, 1, 0, 2, 0],
   [3, 1, 0, 2, 0],
   [1, 2, 0, 2, 0],
   [3, 2, 0, 2, 0],
   [0, 3, 0, 2, 0],
   [1, 3, 0, 2, 0],
   [2, 3, 0, 2, 0],
   [1, 0, 1, 2, 0],
   [2, 0, 1, 2, 0],
   [3, 0, 1, 2, 0],
   [0, 2, 1, 2, 0],
   [1, 2, 1, 2, 0],
   [3, 2, 1, 2, 0],
   [0, 3, 1, 2, 0],
   [1, 3, 1, 2, 0],
   [2, 3, 1, 2, 0],
   [1, 0, 3, 2, 0],
   [2, 0, 3, 2, 0],
   [3, 0, 3, 2, 0],
   [0, 1, 3, 2, 0],
   [2, 1, 3, 2, 0],
   [3, 1, 3, 2, 0],
   [0, 2, 3, 2, 0],
   [1, 2, 3, 2, 0],
   [3, 2, 3, 2, 0],
   [0, 1, 0, 3, 0],
   [2, 1, 0, 3, 0],
   [3, 1, 0, 3, 0],
   [0, 2, 0, 3, 0],
   [1, 2, 0, 3, 0],
   [3, 2, 0, 3, 0],
   [1, 3, 0, 3, 0],
   [2, 3, 0, 3, 0],
   [1, 0, 1, 3, 0],
   [2, 0, 1, 3, 0],
   [3, 0, 1, 3, 0],
   [0, 2, 1, 3, 0],
   [1, 2, 1, 3, 0],
   [3, 2, 1, 3, 0],
   [0, 3, 1, 3, 0],
   [1, 3, 1, 3, 0],
   [2, 3, 1, 3, 0],
   [1, 0, 2, 3, 0],
   [2, 0, 2, 3, 0],
   [3, 0, 2, 3, 0],
   [0, 1, 2, 3, 0],
   [2, 1, 2, 3, 0],
   [3, 1, 2, 3, 0],
   [0, 3, 2, 3, 0],
   [1, 3, 2, 3, 0],
   [2, 3, 2, 3, 0],
   [2, 0, 1, 0, 1],
   [3, 0, 1, 0, 1],
   [0, 2, 1, 0, 1],
   [1, 2, 1, 0, 1],
   [3, 2, 1, 0, 1],
   [0, 3, 1, 0, 1],
   [1, 3, 1, 0, 1],
   [2, 3, 1, 0, 1],
   [1, 0, 2, 0, 1],
   [2, 0, 2, 0, 1],
   [3, 0, 2, 0, 1],
   [0, 1, 2, 0, 1],
   [2, 1, 2, 0, 1],
   [3, 1, 2, 0, 1]]

/-- Good words, part 4. -/
def goodWords4 : List (List Test) :=
  [[0, 3, 2, 0, 1],
   [1, 3, 2, 0, 1],
   [2, 3, 2, 0, 1],
   [1, 0, 3, 0, 1],
   [2, 0, 3, 0, 1],
   [3, 0, 3, 0, 1],
   [0, 1, 3, 0, 1],
   [2, 1, 3, 0, 1],
   [3, 1, 3, 0, 1],
   [0, 2, 3, 0, 1],
   [1, 2, 3, 0, 1],
   [3, 2, 3, 0, 1],
   [0, 1, 0, 2, 1],
   [2, 1, 0, 2, 1],
   [3, 1, 0, 2, 1],
   [0, 2, 0, 2, 1],
   [1, 2, 0, 2, 1],
   [3, 2, 0, 2, 1],
   [0, 3, 0, 2, 1],
   [1, 3, 0, 2, 1],
   [2, 3, 0, 2, 1],
   [1, 0, 1, 2, 1],
   [2, 0, 1, 2, 1],
   [3, 0, 1, 2, 1],
   [0, 2, 1, 2, 1],
   [3, 2, 1, 2, 1],
   [0, 3, 1, 2, 1],
   [1, 3, 1, 2, 1],
   [2, 3, 1, 2, 1],
   [1, 0, 3, 2, 1],
   [2, 0, 3, 2, 1],
   [3, 0, 3, 2, 1],
   [0, 1, 3, 2, 1],
   [2, 1, 3, 2, 1],
   [3, 1, 3, 2, 1],
   [0, 2, 3, 2, 1],
   [1, 2, 3, 2, 1],
   [3, 2, 3, 2, 1],
   [0, 1, 0, 3, 1],
   [2, 1, 0, 3, 1],
   [3, 1, 0, 3, 1],
   [0, 2, 0, 3, 1],
   [1, 2, 0, 3, 1],
   [3, 2, 0, 3, 1],
   [0, 3, 0, 3, 1],
   [1, 3, 0, 3, 1],
   [2, 3, 0, 3, 1],
   [1, 0, 1, 3, 1],
   [2, 0, 1, 3, 1],
   [3, 0, 1, 3, 1],
   [0, 2, 1, 3, 1],
   [1, 2, 1, 3, 1],
   [3, 2, 1, 3, 1],
   [0, 3, 1, 3, 1],
   [2, 3, 1, 3, 1],
   [1, 0, 2, 3, 1],
   [2, 0, 2, 3, 1],
   [3, 0, 2, 3, 1],
   [0, 1, 2, 3, 1],
   [2, 1, 2, 3, 1],
   [3, 1, 2, 3, 1],
   [0, 3, 2, 3, 1],
   [1, 3, 2, 3, 1],
   [2, 3, 2, 3, 1],
   [1, 0, 1, 0, 2],
   [2, 0, 1, 0, 2],
   [3, 0, 1, 0, 2],
   [0, 2, 1, 0, 2],
   [1, 2, 1, 0, 2],
   [3, 2, 1, 0, 2],
   [0, 3, 1, 0, 2],
   [1, 3, 1, 0, 2],
   [2, 3, 1, 0, 2],
   [1, 0, 2, 0, 2],
   [3, 0, 2, 0, 2],
   [0, 1, 2, 0, 2],
   [2, 1, 2, 0, 2],
   [3, 1, 2, 0, 2],
   [0, 3, 2, 0, 2],
   [1, 3, 2, 0, 2]]

/-- Good words, part 5. -/
def goodWords5 : List (List Test) :=
  [[2, 3, 2, 0, 2],
   [1, 0, 3, 0, 2],
   [2, 0, 3, 0, 2],
   [3, 0, 3, 0, 2],
   [0, 1, 3, 0, 2],
   [2, 1, 3, 0, 2],
   [3, 1, 3, 0, 2],
   [0, 2, 3, 0, 2],
   [1, 2, 3, 0, 2],
   [3, 2, 3, 0, 2],
   [0, 1, 0, 1, 2],
   [2, 1, 0, 1, 2],
   [3, 1, 0, 1, 2],
   [0, 2, 0, 1, 2],
   [1, 2, 0, 1, 2],
   [3, 2, 0, 1, 2],
   [0, 3, 0, 1, 2],
   [1, 3, 0, 1, 2],
   [2, 3, 0, 1, 2],
   [1, 0, 2, 1, 2],
   [2, 0, 2, 1, 2],
   [3, 0, 2, 1, 2],
   [0, 1, 2, 1, 2],
   [3, 1, 2, 1, 2],
   [0, 3, 2, 1, 2],
   [1, 3, 2, 1, 2],
   [2, 3, 2, 1, 2],
   [1, 0, 3, 1, 2],
   [2, 0, 3, 1, 2],
   [3, 0, 3, 1, 2],
   [0, 1, 3, 1, 2],
   [2, 1, 3, 1, 2],
   [3, 1, 3, 1, 2],
   [0, 2, 3, 1, 2],
   [1, 2, 3, 1, 2],
   [3, 2, 3, 1, 2],
   [0, 1, 0, 3, 2],
   [2, 1, 0, 3, 2],
   [3, 1, 0, 3, 2],
   [0, 2, 0, 3, 2],
   [1, 2, 0, 3, 2],
   [3, 2, 0, 3, 2],
   [0, 3, 0, 3, 2],
   [1, 3, 0, 3, 2],
   [2, 3, 0, 3, 2],
   [1, 0, 1, 3, 2],
   [2, 0, 1, 3, 2],
   [3, 0, 1, 3, 2],
   [0, 2, 1, 3, 2],
   [1, 2, 1, 3, 2],
   [3, 2, 1, 3, 2],
   [0, 3, 1, 3, 2],
   [1, 3, 1, 3, 2],
   [2, 3, 1, 3, 2],
   [1, 0, 2, 3, 2],
   [2, 0, 2, 3, 2],
   [3, 0, 2, 3, 2],
   [0, 1, 2, 3, 2],
   [2, 1, 2, 3, 2],
   [3, 1, 2, 3, 2],
   [0, 3, 2, 3, 2],
   [1, 3, 2, 3, 2],
   [1, 0, 1, 0, 3],
   [2, 0, 1, 0, 3],
   [3, 0, 1, 0, 3],
   [0, 2, 1, 0, 3],
   [1, 2, 1, 0, 3],
   [3, 2, 1, 0, 3],
   [0, 3, 1, 0, 3],
   [1, 3, 1, 0, 3],
   [2, 3, 1, 0, 3],
   [1, 0, 2, 0, 3],
   [2, 0, 2, 0, 3],
   [3, 0, 2, 0, 3],
   [0, 1, 2, 0, 3],
   [2, 1, 2, 0, 3],
   [3, 1, 2, 0, 3],
   [0, 3, 2, 0, 3],
   [1, 3, 2, 0, 3],
   [2, 3, 2, 0, 3]]

/-- Good words, part 6. -/
def goodWords6 : List (List Test) :=
  [[1, 0, 3, 0, 3],
   [2, 0, 3, 0, 3],
   [0, 1, 3, 0, 3],
   [2, 1, 3, 0, 3],
   [3, 1, 3, 0, 3],
   [0, 2, 3, 0, 3],
   [1, 2, 3, 0, 3],
   [3, 2, 3, 0, 3],
   [0, 1, 0, 1, 3],
   [2, 1, 0, 1, 3],
   [3, 1, 0, 1, 3],
   [0, 2, 0, 1, 3],
   [1, 2, 0, 1, 3],
   [3, 2, 0, 1, 3],
   [0, 3, 0, 1, 3],
   [1, 3, 0, 1, 3],
   [2, 3, 0, 1, 3],
   [1, 0, 2, 1, 3],
   [2, 0, 2, 1, 3],
   [3, 0, 2, 1, 3],
   [0, 1, 2, 1, 3],
   [2, 1, 2, 1, 3],
   [3, 1, 2, 1, 3],
   [0, 3, 2, 1, 3],
   [1, 3, 2, 1, 3],
   [2, 3, 2, 1, 3],
   [1, 0, 3, 1, 3],
   [2, 0, 3, 1, 3],
   [3, 0, 3, 1, 3],
   [0, 1, 3, 1, 3],
   [2, 1, 3, 1, 3],
   [0, 2, 3, 1, 3],
   [1, 2, 3, 1, 3],
   [3, 2, 3, 1, 3],
   [0, 1, 0, 2, 3],
   [2, 1, 0, 2, 3],
   [3, 1, 0, 2, 3],
   [0, 2, 0, 2, 3],
   [1, 2, 0, 2, 3],
   [3, 2, 0, 2, 3],
   [0, 3, 0, 2, 3],
   [1, 3, 0, 2, 3],
   [2, 3, 0, 2, 3],
   [1, 0, 1, 2, 3],
   [2, 0, 1, 2, 3],
   [3, 0, 1, 2, 3],
   [0, 2, 1, 2, 3],
   [1, 2, 1, 2, 3],
   [3, 2, 1, 2, 3],
   [0, 3, 1, 2, 3],
   [1, 3, 1, 2, 3],
   [2, 3, 1, 2, 3],
   [1, 0, 3, 2, 3],
   [2, 0, 3, 2, 3],
   [3, 0, 3, 2, 3],
   [0, 1, 3, 2, 3],
   [2, 1, 3, 2, 3],
   [3, 1, 3, 2, 3],
   [0, 2, 3, 2, 3],
   [1, 2, 3, 2, 3]]

theorem goodWords1_lift : ∀ l ∈ goodWords1, LiftP l := by
  unfold goodWords1
  exact forall_cons_of lw_0
    (forall_cons_of lw_1
    (forall_cons_of lw_2
    (forall_cons_of lw_3
    (forall_cons_of (liftP_rev lw_01 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_02 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_03 (by decide) (by decide))
    (forall_cons_of lw_01
    (forall_cons_of (liftP_rev lw_12 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_13 (by decide) (by decide))
    (forall_cons_of lw_02
    (forall_cons_of lw_12
    (forall_cons_of (liftP_rev lw_23 (by decide) (by decide))
    (forall_cons_of lw_03
    (forall_cons_of lw_13
    (forall_cons_of lw_23
    (forall_cons_of lw_010
    (forall_cons_of (liftP_rev lw_012 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_013 (by decide) (by decide))
    (forall_cons_of lw_020
    (forall_cons_of (liftP_rev lw_021 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_023 (by decide) (by decide))
    (forall_cons_of lw_030
    (forall_cons_of (liftP_rev lw_031 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_032 (by decide) (by decide))
    (forall_cons_of lw_101
    (forall_cons_of (liftP_rev lw_102 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_103 (by decide) (by decide))
    (forall_cons_of lw_021
    (forall_cons_of lw_121
    (forall_cons_of (liftP_rev lw_123 (by decide) (by decide))
    (forall_cons_of lw_031
    (forall_cons_of lw_131
    (forall_cons_of (liftP_rev lw_132 (by decide) (by decide))
    (forall_cons_of lw_102
    (forall_cons_of lw_202
    (forall_cons_of (liftP_rev lw_203 (by decide) (by decide))
    (forall_cons_of lw_012
    (forall_cons_of lw_212
    (forall_cons_of (liftP_rev lw_213 (by decide) (by decide))
    (forall_cons_of lw_032
    (forall_cons_of lw_132
    (forall_cons_of lw_232
    (forall_cons_of lw_103
    (forall_cons_of lw_203
    (forall_cons_of lw_303
    (forall_cons_of lw_013
    (forall_cons_of lw_213
    (forall_cons_of lw_313
    (forall_cons_of lw_023
    (forall_cons_of lw_123
    (forall_cons_of lw_323
    (forall_cons_of (liftP_rev lw_0102 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_0103 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_0120 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_0121 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_0123 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_0130 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_0131 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_0132 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_0201 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_0203 (by decide) (by decide))
    (forall_cons_of lw_0120
    (forall_cons_of (liftP_rev lw_0212 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_0213 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_0230 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_0231 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_0232 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_0301 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_0302 (by decide) (by decide))
    (forall_cons_of lw_0130
    (forall_cons_of (liftP_rev lw_0312 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_0313 (by decide) (by decide))
    (forall_cons_of lw_0230
    (forall_cons_of (liftP_rev lw_0321 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_0323 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_1012 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_1013 (by decide) (by decide))
    (forall_cons_of lw_0201
    (forall_cons_of (liftP_rev lw_1021 (by decide) (by decide))
    (forall_nil_of))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem goodWords2_lift : ∀ l ∈ goodWords2, LiftP l := by
  unfold goodWords2
  exact forall_cons_of (liftP_rev lw_1023 (by decide) (by decide))
    (forall_cons_of lw_0301
    (forall_cons_of (liftP_rev lw_1031 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_1032 (by decide) (by decide))
    (forall_cons_of lw_1021
    (forall_cons_of (liftP_rev lw_1202 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_1203 (by decide) (by decide))
    (forall_cons_of lw_0121
    (forall_cons_of (liftP_rev lw_1213 (by decide) (by decide))
    (forall_cons_of lw_0321
    (forall_cons_of (liftP_rev lw_1231 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_1232 (by decide) (by decide))
    (forall_cons_of lw_1031
    (forall_cons_of (liftP_rev lw_1302 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_1303 (by decide) (by decide))
    (forall_cons_of lw_0131
    (forall_cons_of (liftP_rev lw_1312 (by decide) (by decide))
    (forall_cons_of lw_0231
    (forall_cons_of lw_1231
    (forall_cons_of (liftP_rev lw_1323 (by decide) (by decide))
    (forall_cons_of lw_0102
    (forall_cons_of (liftP_rev lw_2012 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_2013 (by decide) (by decide))
    (forall_cons_of lw_1202
    (forall_cons_of (liftP_rev lw_2023 (by decide) (by decide))
    (forall_cons_of lw_0302
    (forall_cons_of lw_1302
    (forall_cons_of (liftP_rev lw_2032 (by decide) (by decide))
    (forall_cons_of lw_1012
    (forall_cons_of lw_2012
    (forall_cons_of (liftP_rev lw_2103 (by decide) (by decide))
    (forall_cons_of lw_0212
    (forall_cons_of (liftP_rev lw_2123 (by decide) (by decide))
    (forall_cons_of lw_0312
    (forall_cons_of lw_1312
    (forall_cons_of (liftP_rev lw_2132 (by decide) (by decide))
    (forall_cons_of lw_1032
    (forall_cons_of lw_2032
    (forall_cons_of (liftP_rev lw_2303 (by decide) (by decide))
    (forall_cons_of lw_0132
    (forall_cons_of lw_2132
    (forall_cons_of (liftP_rev lw_2313 (by decide) (by decide))
    (forall_cons_of lw_0232
    (forall_cons_of lw_1232
    (forall_cons_of lw_0103
    (forall_cons_of lw_2103
    (forall_cons_of (liftP_rev lw_3013 (by decide) (by decide))
    (forall_cons_of lw_0203
    (forall_cons_of lw_1203
    (forall_cons_of (liftP_rev lw_3023 (by decide) (by decide))
    (forall_cons_of lw_1303
    (forall_cons_of lw_2303
    (forall_cons_of lw_1013
    (forall_cons_of lw_2013
    (forall_cons_of lw_3013
    (forall_cons_of lw_0213
    (forall_cons_of lw_1213
    (forall_cons_of (liftP_rev lw_3123 (by decide) (by decide))
    (forall_cons_of lw_0313
    (forall_cons_of lw_2313
    (forall_cons_of lw_1023
    (forall_cons_of lw_2023
    (forall_cons_of lw_3023
    (forall_cons_of lw_0123
    (forall_cons_of lw_2123
    (forall_cons_of lw_3123
    (forall_cons_of lw_0323
    (forall_cons_of lw_1323
    (forall_cons_of (liftP_rev lw_01012 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_01013 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_01020 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_01021 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_01023 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_01030 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_01031 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_01032 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_01201 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_01202 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_01203 (by decide) (by decide))
    (forall_cons_of lw_01210
    (forall_nil_of))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem goodWords3_lift : ∀ l ∈ goodWords3, LiftP l := by
  unfold goodWords3
  exact forall_cons_of (liftP_rev lw_01212 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_01213 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_01230 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_01231 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_01232 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_01301 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_01302 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_01303 (by decide) (by decide))
    (forall_cons_of lw_01310
    (forall_cons_of (liftP_rev lw_01312 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_01313 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_01320 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_01321 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_01323 (by decide) (by decide))
    (forall_cons_of lw_01020
    (forall_cons_of (liftP_rev lw_02012 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_02013 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_02021 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_02023 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_02030 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_02031 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_02032 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_02101 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_02102 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_02103 (by decide) (by decide))
    (forall_cons_of lw_02120
    (forall_cons_of (liftP_rev lw_02121 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_02123 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_02130 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_02131 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_02132 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_02301 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_02302 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_02303 (by decide) (by decide))
    (forall_cons_of lw_01320
    (forall_cons_of (liftP_rev lw_02312 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_02313 (by decide) (by decide))
    (forall_cons_of lw_02320
    (forall_cons_of (liftP_rev lw_02321 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_02323 (by decide) (by decide))
    (forall_cons_of lw_01030
    (forall_cons_of (liftP_rev lw_03012 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_03013 (by decide) (by decide))
    (forall_cons_of lw_02030
    (forall_cons_of (liftP_rev lw_03021 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_03023 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_03031 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_03032 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_03101 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_03102 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_03103 (by decide) (by decide))
    (forall_cons_of lw_02130
    (forall_cons_of (liftP_rev lw_03121 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_03123 (by decide) (by decide))
    (forall_cons_of lw_03130
    (forall_cons_of (liftP_rev lw_03131 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_03132 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_03201 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_03202 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_03203 (by decide) (by decide))
    (forall_cons_of lw_01230
    (forall_cons_of (liftP_rev lw_03212 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_03213 (by decide) (by decide))
    (forall_cons_of lw_03230
    (forall_cons_of (liftP_rev lw_03231 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_03232 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_10102 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_10103 (by decide) (by decide))
    (forall_cons_of lw_02101
    (forall_cons_of (liftP_rev lw_10121 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_10123 (by decide) (by decide))
    (forall_cons_of lw_03101
    (forall_cons_of (liftP_rev lw_10131 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_10132 (by decide) (by decide))
    (forall_cons_of lw_10201
    (forall_cons_of (liftP_rev lw_10202 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_10203 (by decide) (by decide))
    (forall_cons_of lw_01201
    (forall_cons_of (liftP_rev lw_10212 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_10213 (by decide) (by decide))
    (forall_nil_of))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem goodWords4_lift : ∀ l ∈ goodWords4, LiftP l := by
  unfold goodWords4
  exact forall_cons_of lw_03201
    (forall_cons_of (liftP_rev lw_10231 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_10232 (by decide) (by decide))
    (forall_cons_of lw_10301
    (forall_cons_of (liftP_rev lw_10302 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_10303 (by decide) (by decide))
    (forall_cons_of lw_01301
    (forall_cons_of (liftP_rev lw_10312 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_10313 (by decide) (by decide))
    (forall_cons_of lw_02301
    (forall_cons_of (liftP_rev lw_10321 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_10323 (by decide) (by decide))
    (forall_cons_of lw_01021
    (forall_cons_of (liftP_rev lw_12012 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_12013 (by decide) (by decide))
    (forall_cons_of lw_02021
    (forall_cons_of lw_12021
    (forall_cons_of (liftP_rev lw_12023 (by decide) (by decide))
    (forall_cons_of lw_03021
    (forall_cons_of (liftP_rev lw_12031 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_12032 (by decide) (by decide))
    (forall_cons_of lw_10121
    (forall_cons_of (liftP_rev lw_12102 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_12103 (by decide) (by decide))
    (forall_cons_of lw_02121
    (forall_cons_of (liftP_rev lw_12123 (by decide) (by decide))
    (forall_cons_of lw_03121
    (forall_cons_of (liftP_rev lw_12131 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_12132 (by decide) (by decide))
    (forall_cons_of lw_10321
    (forall_cons_of (liftP_rev lw_12302 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_12303 (by decide) (by decide))
    (forall_cons_of lw_01321
    (forall_cons_of (liftP_rev lw_12312 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_12313 (by decide) (by decide))
    (forall_cons_of lw_02321
    (forall_cons_of lw_12321
    (forall_cons_of (liftP_rev lw_12323 (by decide) (by decide))
    (forall_cons_of lw_01031
    (forall_cons_of (liftP_rev lw_13012 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_13013 (by decide) (by decide))
    (forall_cons_of lw_02031
    (forall_cons_of lw_12031
    (forall_cons_of (liftP_rev lw_13023 (by decide) (by decide))
    (forall_cons_of lw_03031
    (forall_cons_of lw_13031
    (forall_cons_of (liftP_rev lw_13032 (by decide) (by decide))
    (forall_cons_of lw_10131
    (forall_cons_of (liftP_rev lw_13102 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_13103 (by decide) (by decide))
    (forall_cons_of lw_02131
    (forall_cons_of lw_12131
    (forall_cons_of (liftP_rev lw_13123 (by decide) (by decide))
    (forall_cons_of lw_03131
    (forall_cons_of (liftP_rev lw_13132 (by decide) (by decide))
    (forall_cons_of lw_10231
    (forall_cons_of (liftP_rev lw_13202 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_13203 (by decide) (by decide))
    (forall_cons_of lw_01231
    (forall_cons_of (liftP_rev lw_13212 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_13213 (by decide) (by decide))
    (forall_cons_of lw_03231
    (forall_cons_of lw_13231
    (forall_cons_of (liftP_rev lw_13232 (by decide) (by decide))
    (forall_cons_of lw_10102
    (forall_cons_of lw_20102
    (forall_cons_of (liftP_rev lw_20103 (by decide) (by decide))
    (forall_cons_of lw_02102
    (forall_cons_of lw_12102
    (forall_cons_of (liftP_rev lw_20123 (by decide) (by decide))
    (forall_cons_of lw_03102
    (forall_cons_of lw_13102
    (forall_cons_of (liftP_rev lw_20132 (by decide) (by decide))
    (forall_cons_of lw_10202
    (forall_cons_of (liftP_rev lw_20203 (by decide) (by decide))
    (forall_cons_of lw_01202
    (forall_cons_of (liftP_rev lw_20212 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_20213 (by decide) (by decide))
    (forall_cons_of lw_03202
    (forall_cons_of lw_13202
    (forall_nil_of))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem goodWords5_lift : ∀ l ∈ goodWords5, LiftP l := by
  unfold goodWords5
  exact forall_cons_of (liftP_rev lw_20232 (by decide) (by decide))
    (forall_cons_of lw_10302
    (forall_cons_of lw_20302
    (forall_cons_of (liftP_rev lw_20303 (by decide) (by decide))
    (forall_cons_of lw_01302
    (forall_cons_of (liftP_rev lw_20312 (by decide) (by decide))
    (forall_cons_of (liftP_rev lw_20313 (by decide) (by decide))
    (forall_cons_of lw_02302
    (forall_cons_of lw_12302
    (forall_cons_of (liftP_rev lw_20323 (by decide) (by decide))
    (forall_cons_of lw_01012
    (forall_cons_of lw_21012
    (forall_cons_of (liftP_rev lw_21013 (by decide) (by decide))
    (forall_cons_of lw_02012
    (forall_cons_of lw_12012
    (forall_cons_of (liftP_rev lw_21023 (by decide) (by decide))
    (forall_cons_of lw_03012
    (forall_cons_of lw_13012
    (forall_cons_of (liftP_rev lw_21032 (by decide) (by decide))
    (forall_cons_of lw_10212
    (forall_cons_of lw_20212
    (forall_cons_of (liftP_rev lw_21203 (by decide) (by decide))
    (forall_cons_of lw_01212
    (forall_cons_of (liftP_rev lw_21213 (by decide) (by decide))
    (forall_cons_of lw_03212
    (forall_cons_of lw_13212
    (forall_cons_of (liftP_rev lw_21232 (by decide) (by decide))
    (forall_cons_of lw_10312
    (forall_cons_of lw_20312
    (forall_cons_of (liftP_rev lw_21303 (by decide) (by decide))
    (forall_cons_of lw_01312
    (forall_cons_of lw_21312
    (forall_cons_of (liftP_rev lw_21313 (by decide) (by decide))
    (forall_cons_of lw_02312
    (forall_cons_of lw_12312
    (forall_cons_of (liftP_rev lw_21323 (by decide) (by decide))
    (forall_cons_of lw_01032
    (forall_cons_of lw_21032
    (forall_cons_of (liftP_rev lw_23013 (by decide) (by decide))
    (forall_cons_of lw_02032
    (forall_cons_of lw_12032
    (forall_cons_of (liftP_rev lw_23023 (by decide) (by decide))
    (forall_cons_of lw_03032
    (forall_cons_of lw_13032
    (forall_cons_of lw_23032
    (forall_cons_of lw_10132
    (forall_cons_of lw_20132
    (forall_cons_of (liftP_rev lw_23103 (by decide) (by decide))
    (forall_cons_of lw_02132
    (forall_cons_of lw_12132
    (forall_cons_of (liftP_rev lw_23123 (by decide) (by decide))
    (forall_cons_of lw_03132
    (forall_cons_of lw_13132
    (forall_cons_of lw_23132
    (forall_cons_of lw_10232
    (forall_cons_of lw_20232
    (forall_cons_of (liftP_rev lw_23203 (by decide) (by decide))
    (forall_cons_of lw_01232
    (forall_cons_of lw_21232
    (forall_cons_of (liftP_rev lw_23213 (by decide) (by decide))
    (forall_cons_of lw_03232
    (forall_cons_of lw_13232
    (forall_cons_of lw_10103
    (forall_cons_of lw_20103
    (forall_cons_of lw_30103
    (forall_cons_of lw_02103
    (forall_cons_of lw_12103
    (forall_cons_of (liftP_rev lw_30123 (by decide) (by decide))
    (forall_cons_of lw_03103
    (forall_cons_of lw_13103
    (forall_cons_of lw_23103
    (forall_cons_of lw_10203
    (forall_cons_of lw_20203
    (forall_cons_of lw_30203
    (forall_cons_of lw_01203
    (forall_cons_of lw_21203
    (forall_cons_of (liftP_rev lw_30213 (by decide) (by decide))
    (forall_cons_of lw_03203
    (forall_cons_of lw_13203
    (forall_cons_of lw_23203
    (forall_nil_of))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem goodWords6_lift : ∀ l ∈ goodWords6, LiftP l := by
  unfold goodWords6
  exact forall_cons_of lw_10303
    (forall_cons_of lw_20303
    (forall_cons_of lw_01303
    (forall_cons_of lw_21303
    (forall_cons_of (liftP_rev lw_30313 (by decide) (by decide))
    (forall_cons_of lw_02303
    (forall_cons_of lw_12303
    (forall_cons_of (liftP_rev lw_30323 (by decide) (by decide))
    (forall_cons_of lw_01013
    (forall_cons_of lw_21013
    (forall_cons_of lw_31013
    (forall_cons_of lw_02013
    (forall_cons_of lw_12013
    (forall_cons_of (liftP_rev lw_31023 (by decide) (by decide))
    (forall_cons_of lw_03013
    (forall_cons_of lw_13013
    (forall_cons_of lw_23013
    (forall_cons_of lw_10213
    (forall_cons_of lw_20213
    (forall_cons_of lw_30213
    (forall_cons_of lw_01213
    (forall_cons_of lw_21213
    (forall_cons_of lw_31213
    (forall_cons_of lw_03213
    (forall_cons_of lw_13213
    (forall_cons_of lw_23213
    (forall_cons_of lw_10313
    (forall_cons_of lw_20313
    (forall_cons_of lw_30313
    (forall_cons_of lw_01313
    (forall_cons_of lw_21313
    (forall_cons_of lw_02313
    (forall_cons_of lw_12313
    (forall_cons_of (liftP_rev lw_31323 (by decide) (by decide))
    (forall_cons_of lw_01023
    (forall_cons_of lw_21023
    (forall_cons_of lw_31023
    (forall_cons_of lw_02023
    (forall_cons_of lw_12023
    (forall_cons_of lw_32023
    (forall_cons_of lw_03023
    (forall_cons_of lw_13023
    (forall_cons_of lw_23023
    (forall_cons_of lw_10123
    (forall_cons_of lw_20123
    (forall_cons_of lw_30123
    (forall_cons_of lw_02123
    (forall_cons_of lw_12123
    (forall_cons_of lw_32123
    (forall_cons_of lw_03123
    (forall_cons_of lw_13123
    (forall_cons_of lw_23123
    (forall_cons_of lw_10323
    (forall_cons_of lw_20323
    (forall_cons_of lw_30323
    (forall_cons_of lw_01323
    (forall_cons_of lw_21323
    (forall_cons_of lw_31323
    (forall_cons_of lw_02323
    (forall_cons_of lw_12323
    (forall_nil_of))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem goodWords_eq : (allWords 5).filter goodB = goodWords1 ++ (goodWords2 ++ (goodWords3 ++ (goodWords4 ++ (goodWords5 ++ (goodWords6))))) := by
  decide +kernel

theorem liftP_all (l : List Test) (hr : reducedB l = true) (hlen : l.length ≤ 5) (j : Test)
    (hj : l.count j = 1) : LiftP l := by
  have hmem : l ∈ (allWords 5).filter goodB :=
    List.mem_filter.2 ⟨mem_allWords 5 l hlen, goodB_of hr hj⟩
  rw [goodWords_eq] at hmem
  simp only [List.mem_append] at hmem
  rcases hmem with h | h | h | h | h | h
  · exact goodWords1_lift l h
  · exact goodWords2_lift l h
  · exact goodWords3_lift l h
  · exact goodWords4_lift l h
  · exact goodWords5_lift l h
  · exact goodWords6_lift l h

/-! ## Assembly -/

/-- A sum of Jordan expressions that keeps degree one in `x_j` (its base term is `0 • x_j`). -/
def linSum {ι : Type} (j : Test) (c : ι → ℝ) (P : ι → JPoly Test) : List ι → JPoly Test
  | [] => .smul 0 (.var j)
  | i :: l => .add (.smul (c i) (P i)) (linSum j c P l)

theorem specialEval_linSum {ι : Type} (j : Test) (c : ι → ℝ) (P : ι → JPoly Test) (l : List ι) :
    specialEval (linSum j c P l) = (l.map fun i => c i • specialEval (P i)).sum := by
  induction l with
  | nil => exact zero_smul ℝ _
  | cons i l ih =>
    change c i • specialEval (P i) + specialEval (linSum j c P l) = _
    rw [ih, List.map_cons, List.sum_cons]

theorem linSum_deg {ι : Type} (j : Test) (c : ι → ℝ) (P : ι → JPoly Test) (n : ℕ) (hn : 1 ≤ n)
    (l : List ι) (h : ∀ i ∈ l, (P i).deg ≤ n) : (linSum j c P l).deg ≤ n := by
  induction l with
  | nil => simpa [linSum, JPoly.deg] using hn
  | cons i l ih =>
    simp only [linSum, JPoly.deg, max_le_iff]
    exact ⟨h i (by simp), ih fun k hk => h k (by simp [hk])⟩

theorem linSum_linear {ι : Type} (j : Test) (c : ι → ℝ) (P : ι → JPoly Test) (l : List ι)
    (h : ∀ i ∈ l, (P i).LinearIn j) : (linSum j c P l).LinearIn j := by
  induction l with
  | nil => exact .smul _ _ .var
  | cons i l ih => exact .add _ _ (.smul _ _ (h i (by simp))) (ih fun k hk => h k (by simp [hk]))

/-- **lem:cer:h5:lift (proved, for `1 ≤ n ≤ 5`).** Elementary: explicit lifts for each reversal
class (no Cohn theorem). -/
theorem recognitionThroughFivePos : RecognitionThroughFivePos := by
  classical
  intro n hn1 hn5 j y hsupp hrev hvol
  have hK : ∀ l, ∃ K : JPoly Test, l ∈ y.support → (K.deg ≤ l.length ∧ K.LinearIn j ∧
      specialEval K = classElt l - (cliffVol l : ℝ) • classElt wordRef) := by
    intro l
    by_cases hl : l ∈ y.support
    · obtain ⟨hr, hlen, hc⟩ := hsupp l hl
      obtain ⟨K, h1, h2, h3⟩ := liftP_all l hr (le_trans hlen hn5) j hc
      exact ⟨K, fun _ => ⟨h1, h2 j hc, h3⟩⟩
    · exact ⟨.one, fun h => absurd h hl⟩
  choose Kf hKf using hK
  refine ⟨linSum j (fun l => y l) Kf y.support.toList, ?_, ?_, ?_⟩
  · refine linSum_deg j _ Kf n hn1 _ fun l hl => ?_
    have hl' := Finset.mem_toList.1 hl
    exact le_trans (hKf l hl').1 (hsupp l hl').2.1
  · exact linSum_linear j _ Kf _ fun l hl => (hKf l (Finset.mem_toList.1 hl)).2.1
  · rw [specialEval_linSum, Finset.sum_map_toList]
    rw [Finset.sum_congr rfl fun l hl => by rw [(hKf l hl).2.2]]
    simp only [smul_sub, Finset.sum_sub_distrib, smul_smul]
    rw [← Finset.sum_smul]
    have hv : ∑ l ∈ y.support, y l * (cliffVol l : ℝ) = 0 := hvol
    rw [hv, zero_smul, sub_zero]
    have hrevsum : ∑ l ∈ y.support, y l • groupElt l.reverse =
        ∑ l ∈ y.support, y l • groupElt l := by
      refine Finset.sum_nbij' List.reverse List.reverse ?_ ?_ ?_ ?_ ?_
      · intro l hl
        simp only [Finset.mem_coe, Finsupp.mem_support_iff] at hl ⊢
        rwa [hrev]
      · intro l hl
        simp only [Finset.mem_coe, Finsupp.mem_support_iff] at hl ⊢
        rwa [hrev]
      · intro l _; exact List.reverse_reverse l
      · intro l _; exact List.reverse_reverse l
      · intro l _; rw [hrev]
    calc ∑ l ∈ y.support, y l • classElt l
        = (1 / 2 : ℝ) • (∑ l ∈ y.support, y l • groupElt l +
            ∑ l ∈ y.support, y l • groupElt l.reverse) := by
          rw [← Finset.sum_add_distrib, Finset.smul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          simp only [classElt, smul_add, smul_smul]
          module
      _ = ∑ l ∈ y.support, y l • groupElt l := by rw [hrevsum]; module
      _ = y.sum fun l a => a • groupElt l := rfl

end AlbertSequential.HorizonFive
