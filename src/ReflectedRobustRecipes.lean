/- SPDX-License-Identifier: Apache-2.0 -/
module
public import ReflectedRobustTranscript

/-! Factored exact recipes for the reflected Gram transcript. Append and
scale retain all table and defect occurrences, including repeated words. -/

set_option autoImplicit false
@[expose] public section
namespace AlbertSequential.FiveTest
open LengthSeven LengthSeven.Robust

structure ReflectedRecipe where
  tables : List (ℚ × TabWord)
  defects : List Defect

def appendRecipe (a b : ReflectedRecipe) : ReflectedRecipe :=
  ⟨a.tables ++ b.tables, a.defects ++ b.defects⟩

def scaleRecipe (c : ℚ) (a : ReflectedRecipe) : ReflectedRecipe :=
  ⟨a.tables.map (fun m => (c * m.1, m.2)),
    a.defects.map (fun d => {d with y := c * d.y})⟩

def reflectedGramEntry (c : ℚ) (u v : List ℕ) (r : ReflectedRecipe) : ℚ × Entry :=
  (c, mkE u v r.tables r.defects)

def reflectedRecipe0 : ReflectedRecipe :=
  (⟨[mkY (1) 1 [1, 2, 3, 0]], []⟩ : ReflectedRecipe)

def reflectedRecipe1 : ReflectedRecipe :=
  (⟨[mkY (1) 1 [1]], []⟩ : ReflectedRecipe)

def reflectedRecipe2 : ReflectedRecipe :=
  (scaleRecipe (5/18 : ℚ) reflectedRecipe1)

def reflectedRecipe3 : ReflectedRecipe :=
  (scaleRecipe (1/2 : ℚ) (appendRecipe reflectedRecipe2 (⟨[], [mkD (1) 1 [1] [] 1 [3] (5) 18, mkD (-1) 1 [1] [] 1 [6, 3] (5) 36, mkD (1) 1 [1] [] 1 [2, 3] (5) 36]⟩ : ReflectedRecipe)))

def reflectedRecipe4 : ReflectedRecipe :=
  (scaleRecipe (5/18 : ℚ) reflectedRecipe3)

def reflectedRecipe5 : ReflectedRecipe :=
  (⟨[mkY (1) 1 []], []⟩ : ReflectedRecipe)

def reflectedRecipe6 : ReflectedRecipe :=
  (scaleRecipe (5/18 : ℚ) reflectedRecipe5)

def reflectedRecipe7 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [] [] 0 [2] (5) 18, mkD (-1) 1 [] [] 0 [5, 2] (5) 36, mkD (1) 1 [] [] 0 [1, 2] (5) 36]⟩ : ReflectedRecipe)

def reflectedRecipe8 : ReflectedRecipe :=
  (scaleRecipe (1/2 : ℚ) (appendRecipe reflectedRecipe6 reflectedRecipe7))

def reflectedRecipe9 : ReflectedRecipe :=
  (scaleRecipe (5/18 : ℚ) reflectedRecipe8)

def reflectedRecipe10 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [] [] 0 [3] (5) 18, mkD (-1) 1 [] [] 0 [5, 3] (5) 36, mkD (1) 1 [] [] 0 [1, 3] (5) 36]⟩ : ReflectedRecipe)

def reflectedRecipe11 : ReflectedRecipe :=
  (scaleRecipe (1/2 : ℚ) (appendRecipe reflectedRecipe6 reflectedRecipe10))

def reflectedRecipe12 : ReflectedRecipe :=
  (scaleRecipe (5/18 : ℚ) reflectedRecipe11)

def reflectedRecipe13 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (scaleRecipe (17/81 : ℚ) reflectedRecipe5) (scaleRecipe (-1 : ℚ) reflectedRecipe1)) reflectedRecipe6) reflectedRecipe6)

def reflectedRecipe14 : ReflectedRecipe :=
  (scaleRecipe (1/2 : ℚ) (appendRecipe reflectedRecipe13 (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [] [] 0 [2, 3, 1] (25) 648]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [] [] 0 [2, 7, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [] [] 0 [6, 3, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [] [] 0 [6, 7, 1] (161) 648]⟩ : ReflectedRecipe)) reflectedRecipe7) reflectedRecipe10)))

def reflectedRecipe15 : ReflectedRecipe :=
  (scaleRecipe (1/2 : ℚ) (appendRecipe reflectedRecipe13 (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [] [] 0 [3, 2, 1] (25) 648]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [] [] 0 [3, 6, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [] [] 0 [7, 2, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [] [] 0 [7, 6, 1] (161) 648]⟩ : ReflectedRecipe)) reflectedRecipe10) reflectedRecipe7)))

def reflectedRecipe16 : ReflectedRecipe :=
  (⟨[mkY (1) 1 [3]], []⟩ : ReflectedRecipe)

def reflectedRecipe17 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [] [] 0 [3] (5) 18, mkD (-1) 1 [] [] 0 [6, 3] (5) 36, mkD (1) 1 [] [] 0 [2, 3] (5) 36]⟩ : ReflectedRecipe)

def reflectedRecipe18 : ReflectedRecipe :=
  (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe (appendRecipe (appendRecipe (scaleRecipe (0 : ℚ) reflectedRecipe5) (scaleRecipe (-1 : ℚ) reflectedRecipe16)) reflectedRecipe6) reflectedRecipe6) (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [] [] 0 [1, 2, 3] (5) 72]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [] [] 0 [1, 6, 3] (5) 72]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [] [] 0 [5, 2, 3] (5) 72]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [] [] 0 [5, 6, 3] (5) 72]⟩ : ReflectedRecipe)) reflectedRecipe10) reflectedRecipe17)))

def reflectedRecipe19 : ReflectedRecipe :=
  (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe14 reflectedRecipe15) (scaleRecipe (-1 : ℚ) reflectedRecipe18)))

def reflectedRecipe20 : ReflectedRecipe :=
  (scaleRecipe (1/2 : ℚ) reflectedRecipe19)

def reflectedRecipe21 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe4 (scaleRecipe (-1 : ℚ) (appendRecipe (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe9 (scaleRecipe (-1 : ℚ) (appendRecipe (appendRecipe reflectedRecipe12 (scaleRecipe (-1 : ℚ) (appendRecipe reflectedRecipe20 (⟨[], [mkD (1) 1 [3, 1, 2] [] 0 [1] (1) 2]⟩ : ReflectedRecipe)))) (⟨[], [mkD (1) 1 [3] [] 1 [2] (5) 18, mkD (-1) 1 [3] [] 1 [4, 2] (5) 36, mkD (1) 1 [3] [] 1 [0, 2] (5) 36]⟩ : ReflectedRecipe)))) (⟨[], [mkD (1) 1 [1, 2] [] 0 [3] (5) 18, mkD (-1) 1 [1, 2] [] 0 [5, 3] (5) 36, mkD (1) 1 [1, 2] [] 0 [1, 3] (5) 36]⟩ : ReflectedRecipe))) (⟨[], [mkD (1) 1 [1, 3, 0] [1] 2 [3] (1) 2]⟩ : ReflectedRecipe)))) (⟨[], [mkD (1) 1 [1, 2] [1] 3 [0] (5) 18, mkD (-1) 1 [1, 2] [1] 3 [6, 0] (5) 36, mkD (1) 1 [1, 2] [1] 3 [2, 0] (5) 36]⟩ : ReflectedRecipe))

def reflectedRecipe22 : ReflectedRecipe :=
  (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe18 reflectedRecipe14) (scaleRecipe (-1 : ℚ) reflectedRecipe15)))

def reflectedRecipe23 : ReflectedRecipe :=
  (scaleRecipe (5/18 : ℚ) reflectedRecipe22)

def reflectedRecipe24 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe23 (⟨[], [mkD (1) 1 [1, 3] [] 2 [1] (5) 18]⟩ : ReflectedRecipe))

def reflectedRecipe25 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe9 (scaleRecipe (-1 : ℚ) reflectedRecipe24)) (⟨[], [mkD (1) 1 [] [2] 1 [3] (5) 18, mkD (-1) 1 [] [2] 1 [6, 3] (5) 36, mkD (1) 1 [] [2] 1 [2, 3] (5) 36]⟩ : ReflectedRecipe))

def reflectedRecipe26 : ReflectedRecipe :=
  (scaleRecipe (5/18 : ℚ) reflectedRecipe25)

def reflectedRecipe27 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe26 (⟨[], [mkD (1) 1 [1, 2] [2, 1] 3 [0] (5) 18]⟩ : ReflectedRecipe))

def reflectedRecipe28 : ReflectedRecipe :=
  (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe18 reflectedRecipe15) (scaleRecipe (-1 : ℚ) reflectedRecipe14)))

def reflectedRecipe29 : ReflectedRecipe :=
  (scaleRecipe (5/36 : ℚ) reflectedRecipe28)

def reflectedRecipe30 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [1, 2, 3, 0] [] 0 [3] (5) 18, mkD (-1) 1 [1, 2, 3, 0] [] 0 [5, 3] (5) 36, mkD (1) 1 [1, 2, 3, 0] [] 0 [1, 3] (5) 36]⟩ : ReflectedRecipe)

def reflectedRecipe31 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [1, 2, 3, 0] [] 0 [1, 2, 3] (5) 72]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [1, 2, 3, 0] [] 0 [1, 6, 3] (5) 72]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [1, 2, 3, 0] [] 0 [5, 2, 3] (5) 72]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [1, 2, 3, 0] [] 0 [5, 6, 3] (5) 72]⟩ : ReflectedRecipe)) reflectedRecipe30) (⟨[], [mkD (1) 1 [1, 2, 3, 0] [] 0 [3] (5) 18, mkD (-1) 1 [1, 2, 3, 0] [] 0 [6, 3] (5) 36, mkD (1) 1 [1, 2, 3, 0] [] 0 [2, 3] (5) 36]⟩ : ReflectedRecipe)) (scaleRecipe (-1 : ℚ) (⟨[], [mkD (1) 1 [1, 2, 3, 0] [] 0 [3] (5) 18]⟩ : ReflectedRecipe)))

def reflectedRecipe32 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [1, 2, 3, 0] [] 0 [2] (5) 18, mkD (-1) 1 [1, 2, 3, 0] [] 0 [5, 2] (5) 36, mkD (1) 1 [1, 2, 3, 0] [] 0 [1, 2] (5) 36]⟩ : ReflectedRecipe)

def reflectedRecipe33 : ReflectedRecipe :=
  (scaleRecipe (-1 : ℚ) (⟨[], [mkD (1) 1 [1, 2, 3, 0] [] 0 [1] (1) 2]⟩ : ReflectedRecipe))

def reflectedRecipe34 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [1, 2, 3, 0] [] 0 [2, 3, 1] (25) 648]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [1, 2, 3, 0] [] 0 [2, 7, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [1, 2, 3, 0] [] 0 [6, 3, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [1, 2, 3, 0] [] 0 [6, 7, 1] (161) 648]⟩ : ReflectedRecipe)) reflectedRecipe32) reflectedRecipe30) reflectedRecipe33)

def reflectedRecipe35 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [1, 2, 3, 0] [] 0 [3, 2, 1] (25) 648]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [1, 2, 3, 0] [] 0 [3, 6, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [1, 2, 3, 0] [] 0 [7, 2, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [1, 2, 3, 0] [] 0 [7, 6, 1] (161) 648]⟩ : ReflectedRecipe)) reflectedRecipe30) reflectedRecipe32) reflectedRecipe33)

def reflectedRecipe36 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe29 (scaleRecipe (-1 : ℚ) reflectedRecipe21)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe31 reflectedRecipe34) (scaleRecipe (-1 : ℚ) reflectedRecipe35))))

def reflectedRecipe37 : ReflectedRecipe :=
  (scaleRecipe (41/324 : ℚ) reflectedRecipe28)

def reflectedRecipe38 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe37 (scaleRecipe (-1 : ℚ) reflectedRecipe27)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe34 reflectedRecipe35) (scaleRecipe (-1 : ℚ) reflectedRecipe31))))

def reflectedRecipe39 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe29 (scaleRecipe (-1 : ℚ) reflectedRecipe0)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe31 reflectedRecipe35) (scaleRecipe (-1 : ℚ) reflectedRecipe34))))

def reflectedRecipe40 : ReflectedRecipe :=
  (⟨[mkY (1) 2 [1, 2, 3, 0], mkY (1) 2 [1, 2, 3, 1, 0], mkO (-1) 2 [1, 2, 3] 1 0 []], []⟩ : ReflectedRecipe)

def reflectedRecipe41 : ReflectedRecipe :=
  (scaleRecipe (1/2 : ℚ) (appendRecipe reflectedRecipe2 (⟨[], [mkD (1) 1 [1] [] 1 [2] (5) 18, mkD (-1) 1 [1] [] 1 [7, 2] (5) 36, mkD (1) 1 [1] [] 1 [3, 2] (5) 36]⟩ : ReflectedRecipe)))

def reflectedRecipe42 : ReflectedRecipe :=
  (scaleRecipe (5/36 : ℚ) reflectedRecipe41)

def reflectedRecipe43 : ReflectedRecipe :=
  (scaleRecipe (1/2 : ℚ) reflectedRecipe11)

def reflectedRecipe44 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe43 (⟨[], [mkD (1) 1 [1] [] 3 [2] (1) 2]⟩ : ReflectedRecipe))

def reflectedRecipe45 : ReflectedRecipe :=
  (scaleRecipe (5/18 : ℚ) reflectedRecipe44)

def reflectedRecipe46 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe45 (⟨[], [mkD (1) 1 [1, 3] [3] 2 [1] (5) 18]⟩ : ReflectedRecipe))

def reflectedRecipe47 : ReflectedRecipe :=
  (appendRecipe (scaleRecipe (1/2 : ℚ) reflectedRecipe46) (⟨[], [mkD (1) 1 [1, 3, 2] [3, 2] 1 [0] (1) 2]⟩ : ReflectedRecipe))

def reflectedRecipe48 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [1, 3, 2, 1] [] 0 [3] (5) 18, mkD (-1) 1 [1, 3, 2, 1] [] 0 [5, 3] (5) 36, mkD (1) 1 [1, 3, 2, 1] [] 0 [1, 3] (5) 36]⟩ : ReflectedRecipe)

def reflectedRecipe49 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [1, 3, 2, 1] [] 0 [1, 2, 3] (5) 72]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [1, 3, 2, 1] [] 0 [1, 6, 3] (5) 72]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [1, 3, 2, 1] [] 0 [5, 2, 3] (5) 72]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [1, 3, 2, 1] [] 0 [5, 6, 3] (5) 72]⟩ : ReflectedRecipe)) reflectedRecipe48) (⟨[], [mkD (1) 1 [1, 3, 2, 1] [] 0 [3] (5) 18, mkD (-1) 1 [1, 3, 2, 1] [] 0 [6, 3] (5) 36, mkD (1) 1 [1, 3, 2, 1] [] 0 [2, 3] (5) 36]⟩ : ReflectedRecipe)) (scaleRecipe (-1 : ℚ) (⟨[], [mkD (1) 1 [1, 3, 2, 1] [] 0 [3] (5) 18]⟩ : ReflectedRecipe)))

def reflectedRecipe50 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [1, 3, 2, 1] [] 0 [2] (5) 18, mkD (-1) 1 [1, 3, 2, 1] [] 0 [5, 2] (5) 36, mkD (1) 1 [1, 3, 2, 1] [] 0 [1, 2] (5) 36]⟩ : ReflectedRecipe)

def reflectedRecipe51 : ReflectedRecipe :=
  (scaleRecipe (-1 : ℚ) (⟨[], [mkD (1) 1 [1, 3, 2, 1] [] 0 [1] (1) 2]⟩ : ReflectedRecipe))

def reflectedRecipe52 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [1, 3, 2, 1] [] 0 [3, 2, 1] (25) 648]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [1, 3, 2, 1] [] 0 [3, 6, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [1, 3, 2, 1] [] 0 [7, 2, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [1, 3, 2, 1] [] 0 [7, 6, 1] (161) 648]⟩ : ReflectedRecipe)) reflectedRecipe48) reflectedRecipe50) reflectedRecipe51)

def reflectedRecipe53 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [1, 3, 2, 1] [] 0 [2, 3, 1] (25) 648]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [1, 3, 2, 1] [] 0 [2, 7, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [1, 3, 2, 1] [] 0 [6, 3, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [1, 3, 2, 1] [] 0 [6, 7, 1] (161) 648]⟩ : ReflectedRecipe)) reflectedRecipe50) reflectedRecipe48) reflectedRecipe51)

def reflectedRecipe54 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe42 (scaleRecipe (-1 : ℚ) reflectedRecipe47)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe49 reflectedRecipe52) (scaleRecipe (-1 : ℚ) reflectedRecipe53))))

def reflectedRecipe55 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe9 (scaleRecipe (-1 : ℚ) (appendRecipe reflectedRecipe23 (⟨[], [mkD (1) 1 [2, 3] [] 1 [2] (5) 18]⟩ : ReflectedRecipe)))) (⟨[], [mkD (1) 1 [] [1] 2 [1] (5) 18, mkD (-1) 1 [] [1] 2 [7, 1] (5) 36, mkD (1) 1 [] [1] 2 [3, 1] (5) 36]⟩ : ReflectedRecipe))

def reflectedRecipe56 : ReflectedRecipe :=
  (scaleRecipe (5/18 : ℚ) reflectedRecipe55)

def reflectedRecipe57 : ReflectedRecipe :=
  (scaleRecipe (5/18 : ℚ) reflectedRecipe19)

def reflectedRecipe58 : ReflectedRecipe :=
  (⟨[mkY (1) 1 [2, 1]], []⟩ : ReflectedRecipe)

def reflectedRecipe59 : ReflectedRecipe :=
  (scaleRecipe (5/18 : ℚ) reflectedRecipe58)

def reflectedRecipe60 : ReflectedRecipe :=
  (⟨[mkY (1) 2 [2, 1, 0], mkY (1) 2 [2, 1, 3, 0], mkO (-1) 2 [2, 1] 3 0 []], []⟩ : ReflectedRecipe)

def reflectedRecipe61 : ReflectedRecipe :=
  (scaleRecipe (-1 : ℚ) reflectedRecipe60)

def reflectedRecipe62 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [2, 1, 3, 0] [] 0 [2] (5) 18, mkD (-1) 1 [2, 1, 3, 0] [] 0 [5, 2] (5) 36, mkD (1) 1 [2, 1, 3, 0] [] 0 [1, 2] (5) 36]⟩ : ReflectedRecipe)

def reflectedRecipe63 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe56 (scaleRecipe (-1 : ℚ) (appendRecipe (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe57 (scaleRecipe (-1 : ℚ) (appendRecipe (appendRecipe reflectedRecipe59 reflectedRecipe61) (⟨[], [mkD (1) 1 [2] [2] 1 [3] (5) 18, mkD (-1) 1 [2] [2] 1 [4, 3] (5) 36, mkD (1) 1 [2] [2] 1 [0, 3] (5) 36]⟩ : ReflectedRecipe)))) reflectedRecipe62)) (⟨[], [mkD (1) 1 [1, 2, 0] [2, 1] 3 [2] (1) 2]⟩ : ReflectedRecipe)))) (⟨[], [mkD (1) 1 [2, 1, 3] [1] 2 [0] (5) 18, mkD (-1) 1 [2, 1, 3] [1] 2 [7, 0] (5) 36, mkD (1) 1 [2, 1, 3] [1] 2 [3, 0] (5) 36]⟩ : ReflectedRecipe))

def reflectedRecipe64 : ReflectedRecipe :=
  (scaleRecipe (1/2 : ℚ) (appendRecipe (scaleRecipe (5/18 : ℚ) (⟨[mkY (1) 1 [2]], []⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [2] [] 2 [1] (5) 18, mkD (-1) 1 [2] [] 2 [7, 1] (5) 36, mkD (1) 1 [2] [] 2 [3, 1] (5) 36]⟩ : ReflectedRecipe)))

def reflectedRecipe65 : ReflectedRecipe :=
  (scaleRecipe (5/36 : ℚ) reflectedRecipe64)

def reflectedRecipe66 : ReflectedRecipe :=
  (scaleRecipe (1/2 : ℚ) (appendRecipe reflectedRecipe6 reflectedRecipe17))

def reflectedRecipe67 : ReflectedRecipe :=
  (scaleRecipe (5/18 : ℚ) reflectedRecipe66)

def reflectedRecipe68 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe20 (⟨[], [mkD (1) 1 [2, 1] [] 3 [2] (1) 2]⟩ : ReflectedRecipe))

def reflectedRecipe69 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe67 (scaleRecipe (-1 : ℚ) reflectedRecipe68)) (⟨[], [mkD (1) 1 [] [3] 2 [1] (5) 18, mkD (-1) 1 [] [3] 2 [7, 1] (5) 36, mkD (1) 1 [] [3] 2 [3, 1] (5) 36]⟩ : ReflectedRecipe))

def reflectedRecipe70 : ReflectedRecipe :=
  (scaleRecipe (5/18 : ℚ) reflectedRecipe69)

def reflectedRecipe71 : ReflectedRecipe :=
  (⟨[mkY (1) 1 [2, 3]], []⟩ : ReflectedRecipe)

def reflectedRecipe72 : ReflectedRecipe :=
  (scaleRecipe (5/18 : ℚ) reflectedRecipe71)

def reflectedRecipe73 : ReflectedRecipe :=
  (⟨[mkY (1) 2 [2, 3, 0], mkY (1) 2 [2, 3, 1, 0], mkO (-1) 2 [2, 3] 1 0 []], []⟩ : ReflectedRecipe)

def reflectedRecipe74 : ReflectedRecipe :=
  (scaleRecipe (-1 : ℚ) reflectedRecipe73)

def reflectedRecipe75 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [2, 3, 1, 0] [] 0 [3] (5) 18, mkD (-1) 1 [2, 3, 1, 0] [] 0 [6, 3] (5) 36, mkD (1) 1 [2, 3, 1, 0] [] 0 [2, 3] (5) 36]⟩ : ReflectedRecipe)

def reflectedRecipe76 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe70 (scaleRecipe (-1 : ℚ) (appendRecipe (scaleRecipe (5/18 : ℚ) (appendRecipe (appendRecipe reflectedRecipe23 (scaleRecipe (-1 : ℚ) (appendRecipe (appendRecipe reflectedRecipe72 reflectedRecipe74) (⟨[], [mkD (1) 1 [2] [2] 3 [0] (5) 18, mkD (-1) 1 [2] [2] 3 [5, 0] (5) 36, mkD (1) 1 [2] [2] 3 [1, 0] (5) 36]⟩ : ReflectedRecipe)))) reflectedRecipe75)) (⟨[], [mkD (1) 1 [3, 2, 0] [2, 3] 1 [2] (5) 18]⟩ : ReflectedRecipe)))) (⟨[], [mkD (1) 1 [2, 3, 1] [3] 2 [1] (5) 18, mkD (-1) 1 [2, 3, 1] [3] 2 [4, 1] (5) 36, mkD (1) 1 [2, 3, 1] [3] 2 [0, 1] (5) 36]⟩ : ReflectedRecipe))

def reflectedRecipe77 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [2, 3, 1, 2] [] 0 [3] (5) 18, mkD (-1) 1 [2, 3, 1, 2] [] 0 [5, 3] (5) 36, mkD (1) 1 [2, 3, 1, 2] [] 0 [1, 3] (5) 36]⟩ : ReflectedRecipe)

def reflectedRecipe78 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [2, 3, 1, 2] [] 0 [1, 2, 3] (5) 72]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [2, 3, 1, 2] [] 0 [1, 6, 3] (5) 72]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [2, 3, 1, 2] [] 0 [5, 2, 3] (5) 72]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [2, 3, 1, 2] [] 0 [5, 6, 3] (5) 72]⟩ : ReflectedRecipe)) reflectedRecipe77) (⟨[], [mkD (1) 1 [2, 3, 1, 2] [] 0 [3] (5) 18, mkD (-1) 1 [2, 3, 1, 2] [] 0 [6, 3] (5) 36, mkD (1) 1 [2, 3, 1, 2] [] 0 [2, 3] (5) 36]⟩ : ReflectedRecipe)) (scaleRecipe (-1 : ℚ) (⟨[], [mkD (1) 1 [2, 3, 1, 2] [] 0 [3] (5) 18]⟩ : ReflectedRecipe)))

def reflectedRecipe79 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [2, 3, 1, 2] [] 0 [2] (5) 18, mkD (-1) 1 [2, 3, 1, 2] [] 0 [5, 2] (5) 36, mkD (1) 1 [2, 3, 1, 2] [] 0 [1, 2] (5) 36]⟩ : ReflectedRecipe)

def reflectedRecipe80 : ReflectedRecipe :=
  (scaleRecipe (-1 : ℚ) (⟨[], [mkD (1) 1 [2, 3, 1, 2] [] 0 [1] (1) 2]⟩ : ReflectedRecipe))

def reflectedRecipe81 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [2, 3, 1, 2] [] 0 [3, 2, 1] (25) 648]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [2, 3, 1, 2] [] 0 [3, 6, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [2, 3, 1, 2] [] 0 [7, 2, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [2, 3, 1, 2] [] 0 [7, 6, 1] (161) 648]⟩ : ReflectedRecipe)) reflectedRecipe77) reflectedRecipe79) reflectedRecipe80)

def reflectedRecipe82 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [2, 3, 1, 2] [] 0 [2, 3, 1] (25) 648]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [2, 3, 1, 2] [] 0 [2, 7, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [2, 3, 1, 2] [] 0 [6, 3, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [2, 3, 1, 2] [] 0 [6, 7, 1] (161) 648]⟩ : ReflectedRecipe)) reflectedRecipe79) reflectedRecipe77) reflectedRecipe80)

def reflectedRecipe83 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe65 (scaleRecipe (-1 : ℚ) reflectedRecipe76)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe78 reflectedRecipe81) (scaleRecipe (-1 : ℚ) reflectedRecipe82))))

def reflectedRecipe84 : ReflectedRecipe :=
  (appendRecipe (scaleRecipe (1/2 : ℚ) (appendRecipe reflectedRecipe12 (⟨[], [mkD (1) 1 [3] [] 1 [2] (5) 18]⟩ : ReflectedRecipe))) (⟨[], [mkD (1) 1 [3, 1] [1] 2 [3] (1) 2]⟩ : ReflectedRecipe))

def reflectedRecipe85 : ReflectedRecipe :=
  (scaleRecipe (5/18 : ℚ) reflectedRecipe84)

def reflectedRecipe86 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe85 (⟨[], [mkD (1) 1 [3, 1, 2] [1, 2] 3 [0] (5) 18]⟩ : ReflectedRecipe))

def reflectedRecipe87 : ReflectedRecipe :=
  (scaleRecipe (1/2 : ℚ) (appendRecipe (scaleRecipe (5/18 : ℚ) reflectedRecipe16) (⟨[], [mkD (1) 1 [3] [] 3 [1] (5) 18, mkD (-1) 1 [3] [] 3 [6, 1] (5) 36, mkD (1) 1 [3] [] 3 [2, 1] (5) 36]⟩ : ReflectedRecipe)))

def reflectedRecipe88 : ReflectedRecipe :=
  (scaleRecipe (5/36 : ℚ) reflectedRecipe87)

def reflectedRecipe89 : ReflectedRecipe :=
  (⟨[mkY (1) 2 [3, 2, 1, 0], mkY (1) 2 [3, 2, 1, 3, 0], mkO (-1) 2 [3, 2, 1] 3 0 []], []⟩ : ReflectedRecipe)

def reflectedRecipe90 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [3, 2, 1, 3] [] 0 [3] (5) 18, mkD (-1) 1 [3, 2, 1, 3] [] 0 [5, 3] (5) 36, mkD (1) 1 [3, 2, 1, 3] [] 0 [1, 3] (5) 36]⟩ : ReflectedRecipe)

def reflectedRecipe91 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [3, 2, 1, 3] [] 0 [1, 2, 3] (5) 72]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [3, 2, 1, 3] [] 0 [1, 6, 3] (5) 72]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [3, 2, 1, 3] [] 0 [5, 2, 3] (5) 72]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [3, 2, 1, 3] [] 0 [5, 6, 3] (5) 72]⟩ : ReflectedRecipe)) reflectedRecipe90) (⟨[], [mkD (1) 1 [3, 2, 1, 3] [] 0 [3] (5) 18, mkD (-1) 1 [3, 2, 1, 3] [] 0 [6, 3] (5) 36, mkD (1) 1 [3, 2, 1, 3] [] 0 [2, 3] (5) 36]⟩ : ReflectedRecipe)) (scaleRecipe (-1 : ℚ) (⟨[], [mkD (1) 1 [3, 2, 1, 3] [] 0 [3] (5) 18]⟩ : ReflectedRecipe)))

def reflectedRecipe92 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [3, 2, 1, 3] [] 0 [2] (5) 18, mkD (-1) 1 [3, 2, 1, 3] [] 0 [5, 2] (5) 36, mkD (1) 1 [3, 2, 1, 3] [] 0 [1, 2] (5) 36]⟩ : ReflectedRecipe)

def reflectedRecipe93 : ReflectedRecipe :=
  (scaleRecipe (-1 : ℚ) (⟨[], [mkD (1) 1 [3, 2, 1, 3] [] 0 [1] (1) 2]⟩ : ReflectedRecipe))

def reflectedRecipe94 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [3, 2, 1, 3] [] 0 [3, 2, 1] (25) 648]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [3, 2, 1, 3] [] 0 [3, 6, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [3, 2, 1, 3] [] 0 [7, 2, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [3, 2, 1, 3] [] 0 [7, 6, 1] (161) 648]⟩ : ReflectedRecipe)) reflectedRecipe90) reflectedRecipe92) reflectedRecipe93)

def reflectedRecipe95 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [3, 2, 1, 3] [] 0 [2, 3, 1] (25) 648]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [3, 2, 1, 3] [] 0 [2, 7, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [3, 2, 1, 3] [] 0 [6, 3, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [3, 2, 1, 3] [] 0 [6, 7, 1] (161) 648]⟩ : ReflectedRecipe)) reflectedRecipe92) reflectedRecipe90) reflectedRecipe93)

def reflectedRecipe96 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe88 (scaleRecipe (-1 : ℚ) reflectedRecipe89)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe91 reflectedRecipe94) (scaleRecipe (-1 : ℚ) reflectedRecipe95))))

def reflectedRecipe97 : ReflectedRecipe :=
  (scaleRecipe (1/2 : ℚ) reflectedRecipe8)

def reflectedRecipe98 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe97 (⟨[], [mkD (1) 1 [1] [] 2 [3] (1) 2]⟩ : ReflectedRecipe))

def reflectedRecipe99 : ReflectedRecipe :=
  (scaleRecipe (5/18 : ℚ) reflectedRecipe98)

def reflectedRecipe100 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe99 (⟨[], [mkD (1) 1 [1, 2] [2] 3 [0] (5) 18]⟩ : ReflectedRecipe))

def reflectedRecipe101 : ReflectedRecipe :=
  (scaleRecipe (5/36 : ℚ) reflectedRecipe8)

def reflectedRecipe102 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [3] [] 2 [1] (5) 18]⟩ : ReflectedRecipe)

def reflectedRecipe103 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe67 reflectedRecipe102)

def reflectedRecipe104 : ReflectedRecipe :=
  (appendRecipe (scaleRecipe (1/2 : ℚ) reflectedRecipe103) (⟨[], [mkD (1) 1 [3, 2] [2] 1 [0] (1) 2]⟩ : ReflectedRecipe))

def reflectedRecipe105 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [2, 1] [] 0 [3] (5) 18, mkD (-1) 1 [2, 1] [] 0 [5, 3] (5) 36, mkD (1) 1 [2, 1] [] 0 [1, 3] (5) 36]⟩ : ReflectedRecipe)

def reflectedRecipe106 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [2, 1] [] 0 [1, 2, 3] (5) 72]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [2, 1] [] 0 [1, 6, 3] (5) 72]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [2, 1] [] 0 [5, 2, 3] (5) 72]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [2, 1] [] 0 [5, 6, 3] (5) 72]⟩ : ReflectedRecipe)) reflectedRecipe105) (⟨[], [mkD (1) 1 [2, 1] [] 0 [3] (5) 18, mkD (-1) 1 [2, 1] [] 0 [6, 3] (5) 36, mkD (1) 1 [2, 1] [] 0 [2, 3] (5) 36]⟩ : ReflectedRecipe)) (scaleRecipe (-1 : ℚ) (⟨[], [mkD (1) 1 [2, 1] [] 0 [3] (5) 18]⟩ : ReflectedRecipe)))

def reflectedRecipe107 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [2, 1] [] 0 [2] (5) 18, mkD (-1) 1 [2, 1] [] 0 [5, 2] (5) 36, mkD (1) 1 [2, 1] [] 0 [1, 2] (5) 36]⟩ : ReflectedRecipe)

def reflectedRecipe108 : ReflectedRecipe :=
  (scaleRecipe (-1 : ℚ) (⟨[], [mkD (1) 1 [2, 1] [] 0 [1] (1) 2]⟩ : ReflectedRecipe))

def reflectedRecipe109 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [2, 1] [] 0 [3, 2, 1] (25) 648]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [2, 1] [] 0 [3, 6, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [2, 1] [] 0 [7, 2, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [2, 1] [] 0 [7, 6, 1] (161) 648]⟩ : ReflectedRecipe)) reflectedRecipe105) reflectedRecipe107) reflectedRecipe108)

def reflectedRecipe110 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [2, 1] [] 0 [2, 3, 1] (25) 648]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [2, 1] [] 0 [2, 7, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [2, 1] [] 0 [6, 3, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [2, 1] [] 0 [6, 7, 1] (161) 648]⟩ : ReflectedRecipe)) reflectedRecipe107) reflectedRecipe105) reflectedRecipe108)

def reflectedRecipe111 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe101 (scaleRecipe (-1 : ℚ) reflectedRecipe104)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe106 reflectedRecipe109) (scaleRecipe (-1 : ℚ) reflectedRecipe110))))

def reflectedRecipe112 : ReflectedRecipe :=
  (scaleRecipe (1/2 : ℚ) (appendRecipe reflectedRecipe6 (⟨[], [mkD (1) 1 [] [] 0 [2] (5) 18, mkD (-1) 1 [] [] 0 [7, 2] (5) 36, mkD (1) 1 [] [] 0 [3, 2] (5) 36]⟩ : ReflectedRecipe)))

def reflectedRecipe113 : ReflectedRecipe :=
  (scaleRecipe (5/36 : ℚ) reflectedRecipe112)

def reflectedRecipe114 : ReflectedRecipe :=
  (⟨[mkY (1) 2 [3, 2, 0], mkY (1) 2 [3, 2, 1, 0], mkO (-1) 2 [3, 2] 1 0 []], []⟩ : ReflectedRecipe)

def reflectedRecipe115 : ReflectedRecipe :=
  (scaleRecipe (-1 : ℚ) reflectedRecipe114)

def reflectedRecipe116 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [3, 2] [] 0 [3] (5) 18, mkD (-1) 1 [3, 2] [] 0 [5, 3] (5) 36, mkD (1) 1 [3, 2] [] 0 [1, 3] (5) 36]⟩ : ReflectedRecipe)

def reflectedRecipe117 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [3, 2] [] 0 [1, 2, 3] (5) 72]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [3, 2] [] 0 [1, 6, 3] (5) 72]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [3, 2] [] 0 [5, 2, 3] (5) 72]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [3, 2] [] 0 [5, 6, 3] (5) 72]⟩ : ReflectedRecipe)) reflectedRecipe116) (⟨[], [mkD (1) 1 [3, 2] [] 0 [3] (5) 18, mkD (-1) 1 [3, 2] [] 0 [6, 3] (5) 36, mkD (1) 1 [3, 2] [] 0 [2, 3] (5) 36]⟩ : ReflectedRecipe)) (scaleRecipe (-1 : ℚ) (⟨[], [mkD (1) 1 [3, 2] [] 0 [3] (5) 18]⟩ : ReflectedRecipe)))

def reflectedRecipe118 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [3, 2] [] 0 [2] (5) 18, mkD (-1) 1 [3, 2] [] 0 [5, 2] (5) 36, mkD (1) 1 [3, 2] [] 0 [1, 2] (5) 36]⟩ : ReflectedRecipe)

def reflectedRecipe119 : ReflectedRecipe :=
  (scaleRecipe (-1 : ℚ) (⟨[], [mkD (1) 1 [3, 2] [] 0 [1] (1) 2]⟩ : ReflectedRecipe))

def reflectedRecipe120 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [3, 2] [] 0 [3, 2, 1] (25) 648]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [3, 2] [] 0 [3, 6, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [3, 2] [] 0 [7, 2, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [3, 2] [] 0 [7, 6, 1] (161) 648]⟩ : ReflectedRecipe)) reflectedRecipe116) reflectedRecipe118) reflectedRecipe119)

def reflectedRecipe121 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [3, 2] [] 0 [2, 3, 1] (25) 648]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [3, 2] [] 0 [2, 7, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [3, 2] [] 0 [6, 3, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [3, 2] [] 0 [6, 7, 1] (161) 648]⟩ : ReflectedRecipe)) reflectedRecipe118) reflectedRecipe116) reflectedRecipe119)

def reflectedRecipe122 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe113 reflectedRecipe115) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe117 reflectedRecipe120) (scaleRecipe (-1 : ℚ) reflectedRecipe121))))

def reflectedRecipe123 : ReflectedRecipe :=
  (scaleRecipe (5/36 : ℚ) reflectedRecipe11)

def reflectedRecipe124 : ReflectedRecipe :=
  (scaleRecipe (1/2 : ℚ) reflectedRecipe87)

def reflectedRecipe125 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe124 (⟨[], [mkD (1) 1 [3, 2] [3] 1 [0] (1) 2]⟩ : ReflectedRecipe))

def reflectedRecipe126 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [3, 1] [] 0 [3] (5) 18, mkD (-1) 1 [3, 1] [] 0 [5, 3] (5) 36, mkD (1) 1 [3, 1] [] 0 [1, 3] (5) 36]⟩ : ReflectedRecipe)

def reflectedRecipe127 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [3, 1] [] 0 [3] (5) 18, mkD (-1) 1 [3, 1] [] 0 [6, 3] (5) 36, mkD (1) 1 [3, 1] [] 0 [2, 3] (5) 36]⟩ : ReflectedRecipe)

def reflectedRecipe128 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [3, 1] [] 0 [1, 2, 3] (5) 72]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [3, 1] [] 0 [1, 6, 3] (5) 72]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [3, 1] [] 0 [5, 2, 3] (5) 72]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [3, 1] [] 0 [5, 6, 3] (5) 72]⟩ : ReflectedRecipe)) reflectedRecipe126) reflectedRecipe127) (scaleRecipe (-1 : ℚ) (⟨[], [mkD (1) 1 [3, 1] [] 0 [3] (5) 18]⟩ : ReflectedRecipe)))

def reflectedRecipe129 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [3, 1] [] 0 [2] (5) 18, mkD (-1) 1 [3, 1] [] 0 [5, 2] (5) 36, mkD (1) 1 [3, 1] [] 0 [1, 2] (5) 36]⟩ : ReflectedRecipe)

def reflectedRecipe130 : ReflectedRecipe :=
  (scaleRecipe (-1 : ℚ) (⟨[], [mkD (1) 1 [3, 1] [] 0 [1] (1) 2]⟩ : ReflectedRecipe))

def reflectedRecipe131 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [3, 1] [] 0 [3, 2, 1] (25) 648]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [3, 1] [] 0 [3, 6, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [3, 1] [] 0 [7, 2, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [3, 1] [] 0 [7, 6, 1] (161) 648]⟩ : ReflectedRecipe)) reflectedRecipe126) reflectedRecipe129) reflectedRecipe130)

def reflectedRecipe132 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [3, 1] [] 0 [2, 3, 1] (25) 648]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [3, 1] [] 0 [2, 7, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [3, 1] [] 0 [6, 3, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [3, 1] [] 0 [6, 7, 1] (161) 648]⟩ : ReflectedRecipe)) reflectedRecipe129) reflectedRecipe126) reflectedRecipe130)

def reflectedRecipe133 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe123 (scaleRecipe (-1 : ℚ) reflectedRecipe125)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe128 reflectedRecipe131) (scaleRecipe (-1 : ℚ) reflectedRecipe132))))

def reflectedRecipe134 : ReflectedRecipe :=
  (scaleRecipe (5/18 : ℚ) reflectedRecipe41)

def reflectedRecipe135 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe134 (scaleRecipe (-1 : ℚ) (appendRecipe (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe12 (scaleRecipe (-1 : ℚ) (appendRecipe (appendRecipe reflectedRecipe9 (scaleRecipe (-1 : ℚ) (appendRecipe reflectedRecipe20 (⟨[], [mkD (1) 1 [2, 1, 3] [] 0 [1] (1) 2]⟩ : ReflectedRecipe)))) (⟨[], [mkD (1) 1 [2] [] 1 [3] (5) 18, mkD (-1) 1 [2] [] 1 [4, 3] (5) 36, mkD (1) 1 [2] [] 1 [0, 3] (5) 36]⟩ : ReflectedRecipe)))) (⟨[], [mkD (1) 1 [1, 3] [] 0 [2] (5) 18, mkD (-1) 1 [1, 3] [] 0 [5, 2] (5) 36, mkD (1) 1 [1, 3] [] 0 [1, 2] (5) 36]⟩ : ReflectedRecipe))) (⟨[], [mkD (1) 1 [1, 2, 0] [1] 3 [2] (1) 2]⟩ : ReflectedRecipe)))) (⟨[], [mkD (1) 1 [1, 3] [1] 2 [0] (5) 18, mkD (-1) 1 [1, 3] [1] 2 [7, 0] (5) 36, mkD (1) 1 [1, 3] [1] 2 [3, 0] (5) 36]⟩ : ReflectedRecipe))

def reflectedRecipe136 : ReflectedRecipe :=
  (⟨[mkY (1) 1 [1, 3, 2, 0]], []⟩ : ReflectedRecipe)

def reflectedRecipe137 : ReflectedRecipe :=
  (scaleRecipe (41/324 : ℚ) reflectedRecipe22)

def reflectedRecipe138 : ReflectedRecipe :=
  (scaleRecipe (5/18 : ℚ) reflectedRecipe28)

def reflectedRecipe139 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe138 (⟨[], [mkD (1) 1 [1, 2] [] 3 [1] (5) 18]⟩ : ReflectedRecipe))

def reflectedRecipe140 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe12 (scaleRecipe (-1 : ℚ) reflectedRecipe139)) (⟨[], [mkD (1) 1 [] [3] 1 [2] (5) 18, mkD (-1) 1 [] [3] 1 [7, 2] (5) 36, mkD (1) 1 [] [3] 1 [3, 2] (5) 36]⟩ : ReflectedRecipe))

def reflectedRecipe141 : ReflectedRecipe :=
  (scaleRecipe (5/18 : ℚ) reflectedRecipe140)

def reflectedRecipe142 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe141 (⟨[], [mkD (1) 1 [1, 3] [3, 1] 2 [0] (5) 18]⟩ : ReflectedRecipe))

def reflectedRecipe143 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [1, 3, 2, 0] [] 0 [2] (5) 18, mkD (-1) 1 [1, 3, 2, 0] [] 0 [5, 2] (5) 36, mkD (1) 1 [1, 3, 2, 0] [] 0 [1, 2] (5) 36]⟩ : ReflectedRecipe)

def reflectedRecipe144 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [1, 3, 2, 0] [] 0 [3] (5) 18, mkD (-1) 1 [1, 3, 2, 0] [] 0 [5, 3] (5) 36, mkD (1) 1 [1, 3, 2, 0] [] 0 [1, 3] (5) 36]⟩ : ReflectedRecipe)

def reflectedRecipe145 : ReflectedRecipe :=
  (scaleRecipe (-1 : ℚ) (⟨[], [mkD (1) 1 [1, 3, 2, 0] [] 0 [1] (1) 2]⟩ : ReflectedRecipe))

def reflectedRecipe146 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [1, 3, 2, 0] [] 0 [2, 3, 1] (25) 648]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [1, 3, 2, 0] [] 0 [2, 7, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [1, 3, 2, 0] [] 0 [6, 3, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [1, 3, 2, 0] [] 0 [6, 7, 1] (161) 648]⟩ : ReflectedRecipe)) reflectedRecipe143) reflectedRecipe144) reflectedRecipe145)

def reflectedRecipe147 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [1, 3, 2, 0] [] 0 [3, 2, 1] (25) 648]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [1, 3, 2, 0] [] 0 [3, 6, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [1, 3, 2, 0] [] 0 [7, 2, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [1, 3, 2, 0] [] 0 [7, 6, 1] (161) 648]⟩ : ReflectedRecipe)) reflectedRecipe144) reflectedRecipe143) reflectedRecipe145)

def reflectedRecipe148 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [1, 3, 2, 0] [] 0 [1, 2, 3] (5) 72]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [1, 3, 2, 0] [] 0 [1, 6, 3] (5) 72]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [1, 3, 2, 0] [] 0 [5, 2, 3] (5) 72]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [1, 3, 2, 0] [] 0 [5, 6, 3] (5) 72]⟩ : ReflectedRecipe)) reflectedRecipe144) (⟨[], [mkD (1) 1 [1, 3, 2, 0] [] 0 [3] (5) 18, mkD (-1) 1 [1, 3, 2, 0] [] 0 [6, 3] (5) 36, mkD (1) 1 [1, 3, 2, 0] [] 0 [2, 3] (5) 36]⟩ : ReflectedRecipe)) (scaleRecipe (-1 : ℚ) (⟨[], [mkD (1) 1 [1, 3, 2, 0] [] 0 [3] (5) 18]⟩ : ReflectedRecipe)))

def reflectedRecipe149 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe137 (scaleRecipe (-1 : ℚ) reflectedRecipe142)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe146 reflectedRecipe147) (scaleRecipe (-1 : ℚ) reflectedRecipe148))))

def reflectedRecipe150 : ReflectedRecipe :=
  (scaleRecipe (5/36 : ℚ) reflectedRecipe22)

def reflectedRecipe151 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe150 (scaleRecipe (-1 : ℚ) reflectedRecipe136)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe148 reflectedRecipe146) (scaleRecipe (-1 : ℚ) reflectedRecipe147))))

def reflectedRecipe152 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe150 (scaleRecipe (-1 : ℚ) reflectedRecipe135)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe148 reflectedRecipe147) (scaleRecipe (-1 : ℚ) reflectedRecipe146))))

def reflectedRecipe153 : ReflectedRecipe :=
  (scaleRecipe (5/36 : ℚ) reflectedRecipe3)

def reflectedRecipe154 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe99 (⟨[], [mkD (1) 1 [1, 2] [2] 3 [1] (5) 18]⟩ : ReflectedRecipe))

def reflectedRecipe155 : ReflectedRecipe :=
  (appendRecipe (scaleRecipe (1/2 : ℚ) reflectedRecipe154) (⟨[], [mkD (1) 1 [1, 2, 3] [2, 3] 1 [0] (1) 2]⟩ : ReflectedRecipe))

def reflectedRecipe156 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [1, 2, 3, 1] [] 0 [3] (5) 18, mkD (-1) 1 [1, 2, 3, 1] [] 0 [5, 3] (5) 36, mkD (1) 1 [1, 2, 3, 1] [] 0 [1, 3] (5) 36]⟩ : ReflectedRecipe)

def reflectedRecipe157 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [1, 2, 3, 1] [] 0 [1, 2, 3] (5) 72]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [1, 2, 3, 1] [] 0 [1, 6, 3] (5) 72]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [1, 2, 3, 1] [] 0 [5, 2, 3] (5) 72]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [1, 2, 3, 1] [] 0 [5, 6, 3] (5) 72]⟩ : ReflectedRecipe)) reflectedRecipe156) (⟨[], [mkD (1) 1 [1, 2, 3, 1] [] 0 [3] (5) 18, mkD (-1) 1 [1, 2, 3, 1] [] 0 [6, 3] (5) 36, mkD (1) 1 [1, 2, 3, 1] [] 0 [2, 3] (5) 36]⟩ : ReflectedRecipe)) (scaleRecipe (-1 : ℚ) (⟨[], [mkD (1) 1 [1, 2, 3, 1] [] 0 [3] (5) 18]⟩ : ReflectedRecipe)))

def reflectedRecipe158 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [1, 2, 3, 1] [] 0 [2] (5) 18, mkD (-1) 1 [1, 2, 3, 1] [] 0 [5, 2] (5) 36, mkD (1) 1 [1, 2, 3, 1] [] 0 [1, 2] (5) 36]⟩ : ReflectedRecipe)

def reflectedRecipe159 : ReflectedRecipe :=
  (scaleRecipe (-1 : ℚ) (⟨[], [mkD (1) 1 [1, 2, 3, 1] [] 0 [1] (1) 2]⟩ : ReflectedRecipe))

def reflectedRecipe160 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [1, 2, 3, 1] [] 0 [2, 3, 1] (25) 648]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [1, 2, 3, 1] [] 0 [2, 7, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [1, 2, 3, 1] [] 0 [6, 3, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [1, 2, 3, 1] [] 0 [6, 7, 1] (161) 648]⟩ : ReflectedRecipe)) reflectedRecipe158) reflectedRecipe156) reflectedRecipe159)

def reflectedRecipe161 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [1, 2, 3, 1] [] 0 [3, 2, 1] (25) 648]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [1, 2, 3, 1] [] 0 [3, 6, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [1, 2, 3, 1] [] 0 [7, 2, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [1, 2, 3, 1] [] 0 [7, 6, 1] (161) 648]⟩ : ReflectedRecipe)) reflectedRecipe156) reflectedRecipe158) reflectedRecipe159)

def reflectedRecipe162 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe153 (scaleRecipe (-1 : ℚ) reflectedRecipe155)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe157 reflectedRecipe160) (scaleRecipe (-1 : ℚ) reflectedRecipe161))))

def reflectedRecipe163 : ReflectedRecipe :=
  (⟨[mkY (1) 2 [1, 3, 2, 0], mkY (1) 2 [1, 3, 2, 1, 0], mkO (-1) 2 [1, 3, 2] 1 0 []], []⟩ : ReflectedRecipe)

def reflectedRecipe164 : ReflectedRecipe :=
  (appendRecipe (scaleRecipe (1/2 : ℚ) (appendRecipe reflectedRecipe9 (⟨[], [mkD (1) 1 [2] [] 1 [3] (5) 18]⟩ : ReflectedRecipe))) (⟨[], [mkD (1) 1 [2, 1] [1] 3 [2] (1) 2]⟩ : ReflectedRecipe))

def reflectedRecipe165 : ReflectedRecipe :=
  (scaleRecipe (5/18 : ℚ) reflectedRecipe164)

def reflectedRecipe166 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe165 (⟨[], [mkD (1) 1 [2, 1, 3] [1, 3] 2 [0] (5) 18]⟩ : ReflectedRecipe))

def reflectedRecipe167 : ReflectedRecipe :=
  (⟨[mkY (1) 2 [2, 3, 1, 0], mkY (1) 2 [2, 3, 1, 2, 0], mkO (-1) 2 [2, 3, 1] 2 0 []], []⟩ : ReflectedRecipe)

def reflectedRecipe168 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe65 (scaleRecipe (-1 : ℚ) reflectedRecipe167)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe78 reflectedRecipe82) (scaleRecipe (-1 : ℚ) reflectedRecipe81))))

def reflectedRecipe169 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe12 (scaleRecipe (-1 : ℚ) (appendRecipe reflectedRecipe138 (⟨[], [mkD (1) 1 [3, 2] [] 1 [3] (5) 18]⟩ : ReflectedRecipe)))) (⟨[], [mkD (1) 1 [] [1] 3 [1] (5) 18, mkD (-1) 1 [] [1] 3 [6, 1] (5) 36, mkD (1) 1 [] [1] 3 [2, 1] (5) 36]⟩ : ReflectedRecipe))

def reflectedRecipe170 : ReflectedRecipe :=
  (scaleRecipe (5/18 : ℚ) reflectedRecipe169)

def reflectedRecipe171 : ReflectedRecipe :=
  (⟨[mkY (1) 1 [3, 1]], []⟩ : ReflectedRecipe)

def reflectedRecipe172 : ReflectedRecipe :=
  (scaleRecipe (5/18 : ℚ) reflectedRecipe171)

def reflectedRecipe173 : ReflectedRecipe :=
  (⟨[mkY (1) 2 [3, 1, 0], mkY (1) 2 [3, 1, 2, 0], mkO (-1) 2 [3, 1] 2 0 []], []⟩ : ReflectedRecipe)

def reflectedRecipe174 : ReflectedRecipe :=
  (scaleRecipe (-1 : ℚ) reflectedRecipe173)

def reflectedRecipe175 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [3, 1, 2, 0] [] 0 [3] (5) 18, mkD (-1) 1 [3, 1, 2, 0] [] 0 [5, 3] (5) 36, mkD (1) 1 [3, 1, 2, 0] [] 0 [1, 3] (5) 36]⟩ : ReflectedRecipe)

def reflectedRecipe176 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe170 (scaleRecipe (-1 : ℚ) (appendRecipe (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe57 (scaleRecipe (-1 : ℚ) (appendRecipe (appendRecipe reflectedRecipe172 reflectedRecipe174) (⟨[], [mkD (1) 1 [3] [3] 1 [2] (5) 18, mkD (-1) 1 [3] [3] 1 [4, 2] (5) 36, mkD (1) 1 [3] [3] 1 [0, 2] (5) 36]⟩ : ReflectedRecipe)))) reflectedRecipe175)) (⟨[], [mkD (1) 1 [1, 3, 0] [3, 1] 2 [3] (1) 2]⟩ : ReflectedRecipe)))) (⟨[], [mkD (1) 1 [3, 1, 2] [1] 3 [0] (5) 18, mkD (-1) 1 [3, 1, 2] [1] 3 [6, 0] (5) 36, mkD (1) 1 [3, 1, 2] [1] 3 [2, 0] (5) 36]⟩ : ReflectedRecipe))

def reflectedRecipe177 : ReflectedRecipe :=
  (scaleRecipe (5/18 : ℚ) reflectedRecipe112)

def reflectedRecipe178 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe20 (⟨[], [mkD (1) 1 [3, 1] [] 2 [3] (1) 2]⟩ : ReflectedRecipe))

def reflectedRecipe179 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe177 (scaleRecipe (-1 : ℚ) reflectedRecipe178)) (⟨[], [mkD (1) 1 [] [2] 3 [1] (5) 18, mkD (-1) 1 [] [2] 3 [6, 1] (5) 36, mkD (1) 1 [] [2] 3 [2, 1] (5) 36]⟩ : ReflectedRecipe))

def reflectedRecipe180 : ReflectedRecipe :=
  (scaleRecipe (5/18 : ℚ) reflectedRecipe179)

def reflectedRecipe181 : ReflectedRecipe :=
  (⟨[mkY (1) 1 [3, 2]], []⟩ : ReflectedRecipe)

def reflectedRecipe182 : ReflectedRecipe :=
  (scaleRecipe (5/18 : ℚ) reflectedRecipe181)

def reflectedRecipe183 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe180 (scaleRecipe (-1 : ℚ) (appendRecipe (scaleRecipe (5/18 : ℚ) (appendRecipe (appendRecipe reflectedRecipe138 (scaleRecipe (-1 : ℚ) (appendRecipe (appendRecipe reflectedRecipe182 reflectedRecipe115) (⟨[], [mkD (1) 1 [3] [3] 2 [0] (5) 18, mkD (-1) 1 [3] [3] 2 [5, 0] (5) 36, mkD (1) 1 [3] [3] 2 [1, 0] (5) 36]⟩ : ReflectedRecipe)))) (⟨[], [mkD (1) 1 [3, 2, 1, 0] [] 0 [2] (5) 18, mkD (-1) 1 [3, 2, 1, 0] [] 0 [7, 2] (5) 36, mkD (1) 1 [3, 2, 1, 0] [] 0 [3, 2] (5) 36]⟩ : ReflectedRecipe))) (⟨[], [mkD (1) 1 [2, 3, 0] [3, 2] 1 [3] (5) 18]⟩ : ReflectedRecipe)))) (⟨[], [mkD (1) 1 [3, 2, 1] [2] 3 [1] (5) 18, mkD (-1) 1 [3, 2, 1] [2] 3 [4, 1] (5) 36, mkD (1) 1 [3, 2, 1] [2] 3 [0, 1] (5) 36]⟩ : ReflectedRecipe))

def reflectedRecipe184 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe88 (scaleRecipe (-1 : ℚ) reflectedRecipe183)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe91 reflectedRecipe95) (scaleRecipe (-1 : ℚ) reflectedRecipe94))))

def reflectedRecipe185 : ReflectedRecipe :=
  (scaleRecipe (5/36 : ℚ) reflectedRecipe66)

def reflectedRecipe186 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [2, 3] [] 0 [3] (5) 18, mkD (-1) 1 [2, 3] [] 0 [5, 3] (5) 36, mkD (1) 1 [2, 3] [] 0 [1, 3] (5) 36]⟩ : ReflectedRecipe)

def reflectedRecipe187 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [2, 3] [] 0 [1, 2, 3] (5) 72]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [2, 3] [] 0 [1, 6, 3] (5) 72]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [2, 3] [] 0 [5, 2, 3] (5) 72]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [2, 3] [] 0 [5, 6, 3] (5) 72]⟩ : ReflectedRecipe)) reflectedRecipe186) (⟨[], [mkD (1) 1 [2, 3] [] 0 [3] (5) 18, mkD (-1) 1 [2, 3] [] 0 [6, 3] (5) 36, mkD (1) 1 [2, 3] [] 0 [2, 3] (5) 36]⟩ : ReflectedRecipe)) (scaleRecipe (-1 : ℚ) (⟨[], [mkD (1) 1 [2, 3] [] 0 [3] (5) 18]⟩ : ReflectedRecipe)))

def reflectedRecipe188 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [2, 3] [] 0 [2] (5) 18, mkD (-1) 1 [2, 3] [] 0 [5, 2] (5) 36, mkD (1) 1 [2, 3] [] 0 [1, 2] (5) 36]⟩ : ReflectedRecipe)

def reflectedRecipe189 : ReflectedRecipe :=
  (scaleRecipe (-1 : ℚ) (⟨[], [mkD (1) 1 [2, 3] [] 0 [1] (1) 2]⟩ : ReflectedRecipe))

def reflectedRecipe190 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [2, 3] [] 0 [2, 3, 1] (25) 648]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [2, 3] [] 0 [2, 7, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [2, 3] [] 0 [6, 3, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [2, 3] [] 0 [6, 7, 1] (161) 648]⟩ : ReflectedRecipe)) reflectedRecipe188) reflectedRecipe186) reflectedRecipe189)

def reflectedRecipe191 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [2, 3] [] 0 [3, 2, 1] (25) 648]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [2, 3] [] 0 [3, 6, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [2, 3] [] 0 [7, 2, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [2, 3] [] 0 [7, 6, 1] (161) 648]⟩ : ReflectedRecipe)) reflectedRecipe186) reflectedRecipe188) reflectedRecipe189)

def reflectedRecipe192 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe185 reflectedRecipe74) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe187 reflectedRecipe190) (scaleRecipe (-1 : ℚ) reflectedRecipe191))))

def reflectedRecipe193 : ReflectedRecipe :=
  (scaleRecipe (1/2 : ℚ) reflectedRecipe64)

def reflectedRecipe194 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe193 (⟨[], [mkD (1) 1 [2, 3] [2] 1 [0] (1) 2]⟩ : ReflectedRecipe))

def reflectedRecipe195 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe101 (scaleRecipe (-1 : ℚ) reflectedRecipe194)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe106 reflectedRecipe110) (scaleRecipe (-1 : ℚ) reflectedRecipe109))))

def reflectedRecipe196 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe45 (⟨[], [mkD (1) 1 [1, 3] [3] 2 [0] (5) 18]⟩ : ReflectedRecipe))

def reflectedRecipe197 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [2] [] 3 [1] (5) 18]⟩ : ReflectedRecipe)

def reflectedRecipe198 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe177 reflectedRecipe197)

def reflectedRecipe199 : ReflectedRecipe :=
  (appendRecipe (scaleRecipe (1/2 : ℚ) reflectedRecipe198) (⟨[], [mkD (1) 1 [2, 3] [3] 1 [0] (1) 2]⟩ : ReflectedRecipe))

def reflectedRecipe200 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe123 (scaleRecipe (-1 : ℚ) reflectedRecipe199)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe128 reflectedRecipe132) (scaleRecipe (-1 : ℚ) reflectedRecipe131))))

def reflectedRecipe201 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe56 (⟨[], [mkD (1) 1 [2, 1] [1, 2] 3 [0] (5) 18]⟩ : ReflectedRecipe))

def reflectedRecipe202 : ReflectedRecipe :=
  (scaleRecipe (5/36 : ℚ) reflectedRecipe19)

def reflectedRecipe203 : ReflectedRecipe :=
  (scaleRecipe (5/18 : ℚ) reflectedRecipe64)

def reflectedRecipe204 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe203 (scaleRecipe (-1 : ℚ) (appendRecipe (scaleRecipe (5/18 : ℚ) (appendRecipe (appendRecipe reflectedRecipe9 (scaleRecipe (-1 : ℚ) (appendRecipe (appendRecipe reflectedRecipe177 (scaleRecipe (-1 : ℚ) (appendRecipe reflectedRecipe138 (⟨[], [mkD (1) 1 [3, 2, 1] [] 0 [2] (5) 18]⟩ : ReflectedRecipe)))) (⟨[], [mkD (1) 1 [3] [] 2 [1] (5) 18, mkD (-1) 1 [3] [] 2 [4, 1] (5) 36, mkD (1) 1 [3] [] 2 [0, 1] (5) 36]⟩ : ReflectedRecipe)))) (⟨[], [mkD (1) 1 [2, 1] [] 0 [2] (5) 18, mkD (-1) 1 [2, 1] [] 0 [7, 2] (5) 36, mkD (1) 1 [2, 1] [] 0 [3, 2] (5) 36]⟩ : ReflectedRecipe))) (⟨[], [mkD (1) 1 [2, 3, 0] [2] 1 [3] (5) 18]⟩ : ReflectedRecipe)))) (⟨[], [mkD (1) 1 [2, 1] [2] 3 [1] (5) 18, mkD (-1) 1 [2, 1] [2] 3 [4, 1] (5) 36, mkD (1) 1 [2, 1] [2] 3 [0, 1] (5) 36]⟩ : ReflectedRecipe))

def reflectedRecipe205 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [2, 1, 3, 0] [] 0 [3] (5) 18, mkD (-1) 1 [2, 1, 3, 0] [] 0 [5, 3] (5) 36, mkD (1) 1 [2, 1, 3, 0] [] 0 [1, 3] (5) 36]⟩ : ReflectedRecipe)

def reflectedRecipe206 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [2, 1, 3, 0] [] 0 [1, 2, 3] (5) 72]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [2, 1, 3, 0] [] 0 [1, 6, 3] (5) 72]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [2, 1, 3, 0] [] 0 [5, 2, 3] (5) 72]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [2, 1, 3, 0] [] 0 [5, 6, 3] (5) 72]⟩ : ReflectedRecipe)) reflectedRecipe205) (⟨[], [mkD (1) 1 [2, 1, 3, 0] [] 0 [3] (5) 18, mkD (-1) 1 [2, 1, 3, 0] [] 0 [6, 3] (5) 36, mkD (1) 1 [2, 1, 3, 0] [] 0 [2, 3] (5) 36]⟩ : ReflectedRecipe)) (scaleRecipe (-1 : ℚ) (⟨[], [mkD (1) 1 [2, 1, 3, 0] [] 0 [3] (5) 18]⟩ : ReflectedRecipe)))

def reflectedRecipe207 : ReflectedRecipe :=
  (scaleRecipe (-1 : ℚ) (⟨[], [mkD (1) 1 [2, 1, 3, 0] [] 0 [1] (1) 2]⟩ : ReflectedRecipe))

def reflectedRecipe208 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [2, 1, 3, 0] [] 0 [2, 3, 1] (25) 648]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [2, 1, 3, 0] [] 0 [2, 7, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [2, 1, 3, 0] [] 0 [6, 3, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [2, 1, 3, 0] [] 0 [6, 7, 1] (161) 648]⟩ : ReflectedRecipe)) reflectedRecipe62) reflectedRecipe205) reflectedRecipe207)

def reflectedRecipe209 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [2, 1, 3, 0] [] 0 [3, 2, 1] (25) 648]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [2, 1, 3, 0] [] 0 [3, 6, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [2, 1, 3, 0] [] 0 [7, 2, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [2, 1, 3, 0] [] 0 [7, 6, 1] (161) 648]⟩ : ReflectedRecipe)) reflectedRecipe205) reflectedRecipe62) reflectedRecipe207)

def reflectedRecipe210 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe202 (scaleRecipe (-1 : ℚ) reflectedRecipe204)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe206 reflectedRecipe208) (scaleRecipe (-1 : ℚ) reflectedRecipe209))))

def reflectedRecipe211 : ReflectedRecipe :=
  (⟨[mkY (1) 1 [2, 1, 3, 0]], []⟩ : ReflectedRecipe)

def reflectedRecipe212 : ReflectedRecipe :=
  (scaleRecipe (41/324 : ℚ) reflectedRecipe19)

def reflectedRecipe213 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe212 (scaleRecipe (-1 : ℚ) reflectedRecipe211)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe208 reflectedRecipe209) (scaleRecipe (-1 : ℚ) reflectedRecipe206))))

def reflectedRecipe214 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe202 (scaleRecipe (-1 : ℚ) reflectedRecipe201)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe206 reflectedRecipe209) (scaleRecipe (-1 : ℚ) reflectedRecipe208))))

def reflectedRecipe215 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe26 (scaleRecipe (-1 : ℚ) (appendRecipe (scaleRecipe (5/18 : ℚ) (appendRecipe (appendRecipe reflectedRecipe138 (scaleRecipe (-1 : ℚ) (appendRecipe (appendRecipe (scaleRecipe (5/18 : ℚ) (⟨[mkY (1) 1 [1, 2]], []⟩ : ReflectedRecipe)) (scaleRecipe (-1 : ℚ) (⟨[mkY (1) 2 [1, 2, 0], mkY (1) 2 [1, 2, 3, 0], mkO (-1) 2 [1, 2] 3 0 []], []⟩ : ReflectedRecipe))) (⟨[], [mkD (1) 1 [1] [1] 2 [0] (5) 18, mkD (-1) 1 [1] [1] 2 [7, 0] (5) 36, mkD (1) 1 [1] [1] 2 [3, 0] (5) 36]⟩ : ReflectedRecipe)))) reflectedRecipe32)) (⟨[], [mkD (1) 1 [2, 1, 0] [1, 2] 3 [1] (5) 18]⟩ : ReflectedRecipe)))) (⟨[], [mkD (1) 1 [1, 2, 3] [2] 1 [3] (5) 18, mkD (-1) 1 [1, 2, 3] [2] 1 [4, 3] (5) 36, mkD (1) 1 [1, 2, 3] [2] 1 [0, 3] (5) 36]⟩ : ReflectedRecipe))

def reflectedRecipe216 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe141 (scaleRecipe (-1 : ℚ) (appendRecipe (scaleRecipe (5/18 : ℚ) (appendRecipe (appendRecipe reflectedRecipe23 (scaleRecipe (-1 : ℚ) (appendRecipe (appendRecipe (scaleRecipe (5/18 : ℚ) (⟨[mkY (1) 1 [1, 3]], []⟩ : ReflectedRecipe)) (scaleRecipe (-1 : ℚ) (⟨[mkY (1) 2 [1, 3, 0], mkY (1) 2 [1, 3, 2, 0], mkO (-1) 2 [1, 3] 2 0 []], []⟩ : ReflectedRecipe))) (⟨[], [mkD (1) 1 [1] [1] 3 [0] (5) 18, mkD (-1) 1 [1] [1] 3 [6, 0] (5) 36, mkD (1) 1 [1] [1] 3 [2, 0] (5) 36]⟩ : ReflectedRecipe)))) reflectedRecipe144)) (⟨[], [mkD (1) 1 [3, 1, 0] [1, 3] 2 [1] (5) 18]⟩ : ReflectedRecipe)))) (⟨[], [mkD (1) 1 [1, 3, 2] [3] 1 [2] (5) 18, mkD (-1) 1 [1, 3, 2] [3] 1 [4, 2] (5) 36, mkD (1) 1 [1, 3, 2] [3] 1 [0, 2] (5) 36]⟩ : ReflectedRecipe))

def reflectedRecipe217 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (scaleRecipe (41/324 : ℚ) reflectedRecipe41) (scaleRecipe (-1 : ℚ) reflectedRecipe216)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe53 reflectedRecipe52) (scaleRecipe (-1 : ℚ) reflectedRecipe49))))

def reflectedRecipe218 : ReflectedRecipe :=
  (⟨[mkY (1) 2 [2, 1, 3, 0], mkY (1) 2 [2, 1, 3, 2, 0], mkO (-1) 2 [2, 1, 3] 2 0 []], []⟩ : ReflectedRecipe)

def reflectedRecipe219 : ReflectedRecipe :=
  (scaleRecipe (41/324 : ℚ) reflectedRecipe64)

def reflectedRecipe220 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe67 reflectedRecipe197)

def reflectedRecipe221 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [2, 3] [3] 1 [2] (5) 18]⟩ : ReflectedRecipe)

def reflectedRecipe222 : ReflectedRecipe :=
  (appendRecipe (scaleRecipe (5/18 : ℚ) reflectedRecipe220) reflectedRecipe221)

def reflectedRecipe223 : ReflectedRecipe :=
  (appendRecipe (scaleRecipe (5/18 : ℚ) reflectedRecipe222) (⟨[], [mkD (1) 1 [2, 3, 1] [3, 1] 2 [0] (5) 18]⟩ : ReflectedRecipe))

def reflectedRecipe224 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe219 (scaleRecipe (-1 : ℚ) reflectedRecipe223)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe82 reflectedRecipe81) (scaleRecipe (-1 : ℚ) reflectedRecipe78))))

def reflectedRecipe225 : ReflectedRecipe :=
  (scaleRecipe (41/324 : ℚ) reflectedRecipe87)

def reflectedRecipe226 : ReflectedRecipe :=
  (⟨[mkY (1) 2 [3, 1, 2, 0], mkY (1) 2 [3, 1, 2, 3, 0], mkO (-1) 2 [3, 1, 2] 3 0 []], []⟩ : ReflectedRecipe)

def reflectedRecipe227 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [3, 1, 2, 3] [] 0 [2] (5) 18, mkD (-1) 1 [3, 1, 2, 3] [] 0 [5, 2] (5) 36, mkD (1) 1 [3, 1, 2, 3] [] 0 [1, 2] (5) 36]⟩ : ReflectedRecipe)

def reflectedRecipe228 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [3, 1, 2, 3] [] 0 [3] (5) 18, mkD (-1) 1 [3, 1, 2, 3] [] 0 [5, 3] (5) 36, mkD (1) 1 [3, 1, 2, 3] [] 0 [1, 3] (5) 36]⟩ : ReflectedRecipe)

def reflectedRecipe229 : ReflectedRecipe :=
  (scaleRecipe (-1 : ℚ) (⟨[], [mkD (1) 1 [3, 1, 2, 3] [] 0 [1] (1) 2]⟩ : ReflectedRecipe))

def reflectedRecipe230 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [3, 1, 2, 3] [] 0 [2, 3, 1] (25) 648]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [3, 1, 2, 3] [] 0 [2, 7, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [3, 1, 2, 3] [] 0 [6, 3, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [3, 1, 2, 3] [] 0 [6, 7, 1] (161) 648]⟩ : ReflectedRecipe)) reflectedRecipe227) reflectedRecipe228) reflectedRecipe229)

def reflectedRecipe231 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [3, 1, 2, 3] [] 0 [3, 2, 1] (25) 648]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [3, 1, 2, 3] [] 0 [3, 6, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [3, 1, 2, 3] [] 0 [7, 2, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [3, 1, 2, 3] [] 0 [7, 6, 1] (161) 648]⟩ : ReflectedRecipe)) reflectedRecipe228) reflectedRecipe227) reflectedRecipe229)

def reflectedRecipe232 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [3, 1, 2, 3] [] 0 [1, 2, 3] (5) 72]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [3, 1, 2, 3] [] 0 [1, 6, 3] (5) 72]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [3, 1, 2, 3] [] 0 [5, 2, 3] (5) 72]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [3, 1, 2, 3] [] 0 [5, 6, 3] (5) 72]⟩ : ReflectedRecipe)) reflectedRecipe228) (⟨[], [mkD (1) 1 [3, 1, 2, 3] [] 0 [3] (5) 18, mkD (-1) 1 [3, 1, 2, 3] [] 0 [6, 3] (5) 36, mkD (1) 1 [3, 1, 2, 3] [] 0 [2, 3] (5) 36]⟩ : ReflectedRecipe)) (scaleRecipe (-1 : ℚ) (⟨[], [mkD (1) 1 [3, 1, 2, 3] [] 0 [3] (5) 18]⟩ : ReflectedRecipe)))

def reflectedRecipe233 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe225 (scaleRecipe (-1 : ℚ) reflectedRecipe226)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe230 reflectedRecipe231) (scaleRecipe (-1 : ℚ) reflectedRecipe232))))

def reflectedRecipe234 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe177 reflectedRecipe102)

def reflectedRecipe235 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [3, 2] [2] 1 [3] (5) 18]⟩ : ReflectedRecipe)

def reflectedRecipe236 : ReflectedRecipe :=
  (appendRecipe (scaleRecipe (5/18 : ℚ) reflectedRecipe234) reflectedRecipe235)

def reflectedRecipe237 : ReflectedRecipe :=
  (appendRecipe (scaleRecipe (5/18 : ℚ) reflectedRecipe236) (⟨[], [mkD (1) 1 [3, 2, 1] [2, 1] 3 [0] (5) 18]⟩ : ReflectedRecipe))

def reflectedRecipe238 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe203 (⟨[], [mkD (1) 1 [2, 1] [2] 3 [0] (5) 18]⟩ : ReflectedRecipe))

def reflectedRecipe239 : ReflectedRecipe :=
  (scaleRecipe (5/18 : ℚ) reflectedRecipe87)

def reflectedRecipe240 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe239 (⟨[], [mkD (1) 1 [3, 1] [3] 2 [0] (5) 18]⟩ : ReflectedRecipe))

def reflectedRecipe241 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (scaleRecipe (41/324 : ℚ) reflectedRecipe112) (scaleRecipe (-1 : ℚ) reflectedRecipe240)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe121 reflectedRecipe120) (scaleRecipe (-1 : ℚ) reflectedRecipe117))))

def reflectedRecipe242 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (scaleRecipe (41/324 : ℚ) reflectedRecipe11) reflectedRecipe174) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe132 reflectedRecipe131) (scaleRecipe (-1 : ℚ) reflectedRecipe128))))

def reflectedRecipe243 : ReflectedRecipe :=
  (appendRecipe (scaleRecipe (1/2 : ℚ) reflectedRecipe69) (⟨[], [mkD (1) 1 [2, 3] [3, 2] 1 [0] (1) 2]⟩ : ReflectedRecipe))

def reflectedRecipe244 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [2, 3, 1, 0] [] 0 [3] (5) 18, mkD (-1) 1 [2, 3, 1, 0] [] 0 [5, 3] (5) 36, mkD (1) 1 [2, 3, 1, 0] [] 0 [1, 3] (5) 36]⟩ : ReflectedRecipe)

def reflectedRecipe245 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [2, 3, 1, 0] [] 0 [1, 2, 3] (5) 72]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [2, 3, 1, 0] [] 0 [1, 6, 3] (5) 72]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [2, 3, 1, 0] [] 0 [5, 2, 3] (5) 72]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [2, 3, 1, 0] [] 0 [5, 6, 3] (5) 72]⟩ : ReflectedRecipe)) reflectedRecipe244) reflectedRecipe75) (scaleRecipe (-1 : ℚ) (⟨[], [mkD (1) 1 [2, 3, 1, 0] [] 0 [3] (5) 18]⟩ : ReflectedRecipe)))

def reflectedRecipe246 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [2, 3, 1, 0] [] 0 [2] (5) 18, mkD (-1) 1 [2, 3, 1, 0] [] 0 [5, 2] (5) 36, mkD (1) 1 [2, 3, 1, 0] [] 0 [1, 2] (5) 36]⟩ : ReflectedRecipe)

def reflectedRecipe247 : ReflectedRecipe :=
  (scaleRecipe (-1 : ℚ) (⟨[], [mkD (1) 1 [2, 3, 1, 0] [] 0 [1] (1) 2]⟩ : ReflectedRecipe))

def reflectedRecipe248 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [2, 3, 1, 0] [] 0 [3, 2, 1] (25) 648]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [2, 3, 1, 0] [] 0 [3, 6, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [2, 3, 1, 0] [] 0 [7, 2, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [2, 3, 1, 0] [] 0 [7, 6, 1] (161) 648]⟩ : ReflectedRecipe)) reflectedRecipe244) reflectedRecipe246) reflectedRecipe247)

def reflectedRecipe249 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [2, 3, 1, 0] [] 0 [2, 3, 1] (25) 648]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [2, 3, 1, 0] [] 0 [2, 7, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [2, 3, 1, 0] [] 0 [6, 3, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [2, 3, 1, 0] [] 0 [6, 7, 1] (161) 648]⟩ : ReflectedRecipe)) reflectedRecipe246) reflectedRecipe244) reflectedRecipe247)

def reflectedRecipe250 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe150 (scaleRecipe (-1 : ℚ) reflectedRecipe243)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe245 reflectedRecipe248) (scaleRecipe (-1 : ℚ) reflectedRecipe249))))

def reflectedRecipe251 : ReflectedRecipe :=
  (⟨[mkY (1) 1 [2, 3, 1, 0]], []⟩ : ReflectedRecipe)

def reflectedRecipe252 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe150 (scaleRecipe (-1 : ℚ) reflectedRecipe251)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe245 reflectedRecipe249) (scaleRecipe (-1 : ℚ) reflectedRecipe248))))

def reflectedRecipe253 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe203 (scaleRecipe (-1 : ℚ) (appendRecipe (scaleRecipe (5/18 : ℚ) (appendRecipe (appendRecipe reflectedRecipe67 (scaleRecipe (-1 : ℚ) (appendRecipe (appendRecipe reflectedRecipe9 (scaleRecipe (-1 : ℚ) (appendRecipe reflectedRecipe138 (⟨[], [mkD (1) 1 [1, 2, 3] [] 0 [2] (5) 18]⟩ : ReflectedRecipe)))) (⟨[], [mkD (1) 1 [1] [] 2 [0] (5) 18, mkD (-1) 1 [1] [] 2 [7, 0] (5) 36, mkD (1) 1 [1] [] 2 [3, 0] (5) 36]⟩ : ReflectedRecipe)))) reflectedRecipe188)) (⟨[], [mkD (1) 1 [2, 1, 0] [2] 3 [1] (5) 18]⟩ : ReflectedRecipe)))) (⟨[], [mkD (1) 1 [2, 3] [2] 1 [3] (5) 18, mkD (-1) 1 [2, 3] [2] 1 [4, 3] (5) 36, mkD (1) 1 [2, 3] [2] 1 [0, 3] (5) 36]⟩ : ReflectedRecipe))

def reflectedRecipe254 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe137 (scaleRecipe (-1 : ℚ) reflectedRecipe253)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe249 reflectedRecipe248) (scaleRecipe (-1 : ℚ) reflectedRecipe245))))

def reflectedRecipe255 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe42 (scaleRecipe (-1 : ℚ) reflectedRecipe163)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe49 reflectedRecipe53) (scaleRecipe (-1 : ℚ) reflectedRecipe52))))

def reflectedRecipe256 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [2, 1, 3, 2] [] 0 [3] (5) 18, mkD (-1) 1 [2, 1, 3, 2] [] 0 [5, 3] (5) 36, mkD (1) 1 [2, 1, 3, 2] [] 0 [1, 3] (5) 36]⟩ : ReflectedRecipe)

def reflectedRecipe257 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [2, 1, 3, 2] [] 0 [1, 2, 3] (5) 72]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [2, 1, 3, 2] [] 0 [1, 6, 3] (5) 72]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [2, 1, 3, 2] [] 0 [5, 2, 3] (5) 72]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [2, 1, 3, 2] [] 0 [5, 6, 3] (5) 72]⟩ : ReflectedRecipe)) reflectedRecipe256) (⟨[], [mkD (1) 1 [2, 1, 3, 2] [] 0 [3] (5) 18, mkD (-1) 1 [2, 1, 3, 2] [] 0 [6, 3] (5) 36, mkD (1) 1 [2, 1, 3, 2] [] 0 [2, 3] (5) 36]⟩ : ReflectedRecipe)) (scaleRecipe (-1 : ℚ) (⟨[], [mkD (1) 1 [2, 1, 3, 2] [] 0 [3] (5) 18]⟩ : ReflectedRecipe)))

def reflectedRecipe258 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [2, 1, 3, 2] [] 0 [2] (5) 18, mkD (-1) 1 [2, 1, 3, 2] [] 0 [5, 2] (5) 36, mkD (1) 1 [2, 1, 3, 2] [] 0 [1, 2] (5) 36]⟩ : ReflectedRecipe)

def reflectedRecipe259 : ReflectedRecipe :=
  (scaleRecipe (-1 : ℚ) (⟨[], [mkD (1) 1 [2, 1, 3, 2] [] 0 [1] (1) 2]⟩ : ReflectedRecipe))

def reflectedRecipe260 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [2, 1, 3, 2] [] 0 [2, 3, 1] (25) 648]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [2, 1, 3, 2] [] 0 [2, 7, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [2, 1, 3, 2] [] 0 [6, 3, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [2, 1, 3, 2] [] 0 [6, 7, 1] (161) 648]⟩ : ReflectedRecipe)) reflectedRecipe258) reflectedRecipe256) reflectedRecipe259)

def reflectedRecipe261 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [2, 1, 3, 2] [] 0 [3, 2, 1] (25) 648]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [2, 1, 3, 2] [] 0 [3, 6, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [2, 1, 3, 2] [] 0 [7, 2, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [2, 1, 3, 2] [] 0 [7, 6, 1] (161) 648]⟩ : ReflectedRecipe)) reflectedRecipe256) reflectedRecipe258) reflectedRecipe259)

def reflectedRecipe262 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe65 (scaleRecipe (-1 : ℚ) reflectedRecipe166)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe257 reflectedRecipe260) (scaleRecipe (-1 : ℚ) reflectedRecipe261))))

def reflectedRecipe263 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe88 (scaleRecipe (-1 : ℚ) reflectedRecipe176)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe232 reflectedRecipe230) (scaleRecipe (-1 : ℚ) reflectedRecipe231))))

def reflectedRecipe264 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe113 (scaleRecipe (-1 : ℚ) reflectedRecipe196)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe117 reflectedRecipe121) (scaleRecipe (-1 : ℚ) reflectedRecipe120))))

def reflectedRecipe265 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe239 (scaleRecipe (-1 : ℚ) (appendRecipe (scaleRecipe (5/18 : ℚ) (appendRecipe (appendRecipe reflectedRecipe12 (scaleRecipe (-1 : ℚ) (appendRecipe (appendRecipe reflectedRecipe67 (scaleRecipe (-1 : ℚ) (appendRecipe reflectedRecipe23 (⟨[], [mkD (1) 1 [2, 3, 1] [] 0 [3] (5) 18]⟩ : ReflectedRecipe)))) (⟨[], [mkD (1) 1 [2] [] 3 [1] (5) 18, mkD (-1) 1 [2] [] 3 [4, 1] (5) 36, mkD (1) 1 [2] [] 3 [0, 1] (5) 36]⟩ : ReflectedRecipe)))) reflectedRecipe127)) (⟨[], [mkD (1) 1 [3, 2, 0] [3] 1 [2] (5) 18]⟩ : ReflectedRecipe)))) (⟨[], [mkD (1) 1 [3, 1] [3] 2 [1] (5) 18, mkD (-1) 1 [3, 1] [3] 2 [4, 1] (5) 36, mkD (1) 1 [3, 1] [3] 2 [0, 1] (5) 36]⟩ : ReflectedRecipe))

def reflectedRecipe266 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [3, 1, 2, 0] [] 0 [1, 2, 3] (5) 72]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [3, 1, 2, 0] [] 0 [1, 6, 3] (5) 72]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [3, 1, 2, 0] [] 0 [5, 2, 3] (5) 72]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [3, 1, 2, 0] [] 0 [5, 6, 3] (5) 72]⟩ : ReflectedRecipe)) reflectedRecipe175) (⟨[], [mkD (1) 1 [3, 1, 2, 0] [] 0 [3] (5) 18, mkD (-1) 1 [3, 1, 2, 0] [] 0 [6, 3] (5) 36, mkD (1) 1 [3, 1, 2, 0] [] 0 [2, 3] (5) 36]⟩ : ReflectedRecipe)) (scaleRecipe (-1 : ℚ) (⟨[], [mkD (1) 1 [3, 1, 2, 0] [] 0 [3] (5) 18]⟩ : ReflectedRecipe)))

def reflectedRecipe267 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [3, 1, 2, 0] [] 0 [2] (5) 18, mkD (-1) 1 [3, 1, 2, 0] [] 0 [5, 2] (5) 36, mkD (1) 1 [3, 1, 2, 0] [] 0 [1, 2] (5) 36]⟩ : ReflectedRecipe)

def reflectedRecipe268 : ReflectedRecipe :=
  (scaleRecipe (-1 : ℚ) (⟨[], [mkD (1) 1 [3, 1, 2, 0] [] 0 [1] (1) 2]⟩ : ReflectedRecipe))

def reflectedRecipe269 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [3, 1, 2, 0] [] 0 [3, 2, 1] (25) 648]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [3, 1, 2, 0] [] 0 [3, 6, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [3, 1, 2, 0] [] 0 [7, 2, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [3, 1, 2, 0] [] 0 [7, 6, 1] (161) 648]⟩ : ReflectedRecipe)) reflectedRecipe175) reflectedRecipe267) reflectedRecipe268)

def reflectedRecipe270 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [3, 1, 2, 0] [] 0 [2, 3, 1] (25) 648]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [3, 1, 2, 0] [] 0 [2, 7, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [3, 1, 2, 0] [] 0 [6, 3, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [3, 1, 2, 0] [] 0 [6, 7, 1] (161) 648]⟩ : ReflectedRecipe)) reflectedRecipe267) reflectedRecipe175) reflectedRecipe268)

def reflectedRecipe271 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe202 (scaleRecipe (-1 : ℚ) reflectedRecipe265)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe266 reflectedRecipe269) (scaleRecipe (-1 : ℚ) reflectedRecipe270))))

def reflectedRecipe272 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe170 (⟨[], [mkD (1) 1 [3, 1] [1, 3] 2 [0] (5) 18]⟩ : ReflectedRecipe))

def reflectedRecipe273 : ReflectedRecipe :=
  (⟨[mkY (1) 1 [3, 1, 2, 0]], []⟩ : ReflectedRecipe)

def reflectedRecipe274 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe212 (scaleRecipe (-1 : ℚ) reflectedRecipe273)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe270 reflectedRecipe269) (scaleRecipe (-1 : ℚ) reflectedRecipe266))))

def reflectedRecipe275 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe202 (scaleRecipe (-1 : ℚ) reflectedRecipe272)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe266 reflectedRecipe270) (scaleRecipe (-1 : ℚ) reflectedRecipe269))))

def reflectedRecipe276 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (scaleRecipe (41/324 : ℚ) reflectedRecipe3) (scaleRecipe (-1 : ℚ) reflectedRecipe215)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe160 reflectedRecipe161) (scaleRecipe (-1 : ℚ) reflectedRecipe157))))

def reflectedRecipe277 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe219 (scaleRecipe (-1 : ℚ) reflectedRecipe218)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe260 reflectedRecipe261) (scaleRecipe (-1 : ℚ) reflectedRecipe257))))

def reflectedRecipe278 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe225 (scaleRecipe (-1 : ℚ) reflectedRecipe237)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe95 reflectedRecipe94) (scaleRecipe (-1 : ℚ) reflectedRecipe91))))

def reflectedRecipe279 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (scaleRecipe (41/324 : ℚ) reflectedRecipe66) (scaleRecipe (-1 : ℚ) reflectedRecipe238)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe190 reflectedRecipe191) (scaleRecipe (-1 : ℚ) reflectedRecipe187))))

def reflectedRecipe280 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (scaleRecipe (41/324 : ℚ) reflectedRecipe8) reflectedRecipe61) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe110 reflectedRecipe109) (scaleRecipe (-1 : ℚ) reflectedRecipe106))))

def reflectedRecipe281 : ReflectedRecipe :=
  (⟨[mkY (1) 1 [3, 2, 1, 0]], []⟩ : ReflectedRecipe)

def reflectedRecipe282 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [3, 2, 1, 0] [] 0 [3] (5) 18, mkD (-1) 1 [3, 2, 1, 0] [] 0 [5, 3] (5) 36, mkD (1) 1 [3, 2, 1, 0] [] 0 [1, 3] (5) 36]⟩ : ReflectedRecipe)

def reflectedRecipe283 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [3, 2, 1, 0] [] 0 [1, 2, 3] (5) 72]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [3, 2, 1, 0] [] 0 [1, 6, 3] (5) 72]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [3, 2, 1, 0] [] 0 [5, 2, 3] (5) 72]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [3, 2, 1, 0] [] 0 [5, 6, 3] (5) 72]⟩ : ReflectedRecipe)) reflectedRecipe282) (⟨[], [mkD (1) 1 [3, 2, 1, 0] [] 0 [3] (5) 18, mkD (-1) 1 [3, 2, 1, 0] [] 0 [6, 3] (5) 36, mkD (1) 1 [3, 2, 1, 0] [] 0 [2, 3] (5) 36]⟩ : ReflectedRecipe)) (scaleRecipe (-1 : ℚ) (⟨[], [mkD (1) 1 [3, 2, 1, 0] [] 0 [3] (5) 18]⟩ : ReflectedRecipe)))

def reflectedRecipe284 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [3, 2, 1, 0] [] 0 [2] (5) 18, mkD (-1) 1 [3, 2, 1, 0] [] 0 [5, 2] (5) 36, mkD (1) 1 [3, 2, 1, 0] [] 0 [1, 2] (5) 36]⟩ : ReflectedRecipe)

def reflectedRecipe285 : ReflectedRecipe :=
  (scaleRecipe (-1 : ℚ) (⟨[], [mkD (1) 1 [3, 2, 1, 0] [] 0 [1] (1) 2]⟩ : ReflectedRecipe))

def reflectedRecipe286 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [3, 2, 1, 0] [] 0 [3, 2, 1] (25) 648]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [3, 2, 1, 0] [] 0 [3, 6, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [3, 2, 1, 0] [] 0 [7, 2, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [3, 2, 1, 0] [] 0 [7, 6, 1] (161) 648]⟩ : ReflectedRecipe)) reflectedRecipe282) reflectedRecipe284) reflectedRecipe285)

def reflectedRecipe287 : ReflectedRecipe :=
  (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (appendRecipe (⟨[], [mkD (1) 1 [3, 2, 1, 0] [] 0 [2, 3, 1] (25) 648]⟩ : ReflectedRecipe) (⟨[], [mkD (-1) 1 [3, 2, 1, 0] [] 0 [2, 7, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (-1) 1 [3, 2, 1, 0] [] 0 [6, 3, 1] (25) 648]⟩ : ReflectedRecipe)) (⟨[], [mkD (1) 1 [3, 2, 1, 0] [] 0 [6, 7, 1] (161) 648]⟩ : ReflectedRecipe)) reflectedRecipe284) reflectedRecipe282) reflectedRecipe285)

def reflectedRecipe288 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe29 (scaleRecipe (-1 : ℚ) reflectedRecipe281)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe283 reflectedRecipe286) (scaleRecipe (-1 : ℚ) reflectedRecipe287))))

def reflectedRecipe289 : ReflectedRecipe :=
  (appendRecipe (scaleRecipe (1/2 : ℚ) reflectedRecipe179) (⟨[], [mkD (1) 1 [3, 2] [2, 3] 1 [0] (1) 2]⟩ : ReflectedRecipe))

def reflectedRecipe290 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe29 (scaleRecipe (-1 : ℚ) reflectedRecipe289)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe283 reflectedRecipe287) (scaleRecipe (-1 : ℚ) reflectedRecipe286))))

def reflectedRecipe291 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe239 (scaleRecipe (-1 : ℚ) (appendRecipe (scaleRecipe (5/18 : ℚ) (appendRecipe (appendRecipe reflectedRecipe177 (scaleRecipe (-1 : ℚ) (appendRecipe (appendRecipe reflectedRecipe12 (scaleRecipe (-1 : ℚ) (appendRecipe reflectedRecipe23 (⟨[], [mkD (1) 1 [1, 3, 2] [] 0 [3] (5) 18]⟩ : ReflectedRecipe)))) (⟨[], [mkD (1) 1 [1] [] 3 [0] (5) 18, mkD (-1) 1 [1] [] 3 [6, 0] (5) 36, mkD (1) 1 [1] [] 3 [2, 0] (5) 36]⟩ : ReflectedRecipe)))) reflectedRecipe116)) (⟨[], [mkD (1) 1 [3, 1, 0] [3] 2 [1] (5) 18]⟩ : ReflectedRecipe)))) (⟨[], [mkD (1) 1 [3, 2] [3] 1 [2] (5) 18, mkD (-1) 1 [3, 2] [3] 1 [4, 2] (5) 36, mkD (1) 1 [3, 2] [3] 1 [0, 2] (5) 36]⟩ : ReflectedRecipe))

def reflectedRecipe292 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe37 (scaleRecipe (-1 : ℚ) reflectedRecipe291)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe287 reflectedRecipe286) (scaleRecipe (-1 : ℚ) reflectedRecipe283))))

def reflectedRecipe293 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe153 (scaleRecipe (-1 : ℚ) reflectedRecipe40)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe157 reflectedRecipe161) (scaleRecipe (-1 : ℚ) reflectedRecipe160))))

def reflectedRecipe294 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe65 (scaleRecipe (-1 : ℚ) reflectedRecipe63)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe257 reflectedRecipe261) (scaleRecipe (-1 : ℚ) reflectedRecipe260))))

def reflectedRecipe295 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe88 (scaleRecipe (-1 : ℚ) reflectedRecipe86)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe232 reflectedRecipe231) (scaleRecipe (-1 : ℚ) reflectedRecipe230))))

def reflectedRecipe296 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe185 (scaleRecipe (-1 : ℚ) reflectedRecipe100)) (scaleRecipe (1/2 : ℚ) (appendRecipe (appendRecipe reflectedRecipe187 reflectedRecipe191) (scaleRecipe (-1 : ℚ) reflectedRecipe190))))

def reflectedRecipe297 : ReflectedRecipe :=
  (⟨[mkY (1) 1 [1, 2, 3, 1]], []⟩ : ReflectedRecipe)

def reflectedRecipe298 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe4 (scaleRecipe (-1 : ℚ) reflectedRecipe297))

def reflectedRecipe299 : ReflectedRecipe :=
  (appendRecipe (scaleRecipe (5/18 : ℚ) reflectedRecipe154) (⟨[], [mkD (1) 1 [1, 2, 3] [2, 3] 1 [2] (5) 18]⟩ : ReflectedRecipe))

def reflectedRecipe300 : ReflectedRecipe :=
  (scaleRecipe (-1 : ℚ) reflectedRecipe299)

def reflectedRecipe301 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe85 (⟨[], [mkD (1) 1 [3, 1, 2] [1, 2] 3 [1] (5) 18]⟩ : ReflectedRecipe))

def reflectedRecipe302 : ReflectedRecipe :=
  (scaleRecipe (5/18 : ℚ) (appendRecipe reflectedRecipe138 (⟨[], [mkD (1) 1 [] [1, 2] 3 [1] (5) 18]⟩ : ReflectedRecipe)))

def reflectedRecipe303 : ReflectedRecipe :=
  (scaleRecipe (-1 : ℚ) reflectedRecipe301)

def reflectedRecipe304 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe298 (⟨[], [mkD (1) 1 [1, 2, 3] [] 1 [3] (5) 18, mkD (-1) 1 [1, 2, 3] [] 1 [6, 3] (5) 36, mkD (1) 1 [1, 2, 3] [] 1 [2, 3] (5) 36]⟩ : ReflectedRecipe))

def reflectedRecipe305 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe26 (⟨[], [mkD (1) 1 [1, 2, 3] [2] 1 [3] (5) 18]⟩ : ReflectedRecipe))

def reflectedRecipe306 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe302 (⟨[], [mkD (1) 1 [1, 2, 3] [3] 1 [2] (5) 18]⟩ : ReflectedRecipe))

def reflectedRecipe307 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe138 (scaleRecipe (-1 : ℚ) (appendRecipe (scaleRecipe (5/18 : ℚ) (appendRecipe reflectedRecipe43 (⟨[], [mkD (1) 1 [] [1] 3 [2] (1) 2]⟩ : ReflectedRecipe))) (⟨[], [mkD (1) 1 [3] [1, 3] 2 [1] (5) 18]⟩ : ReflectedRecipe)))) (⟨[], [mkD (1) 1 [3, 2] [] 1 [2] (5) 18, mkD (-1) 1 [3, 2] [] 1 [7, 2] (5) 36, mkD (1) 1 [3, 2] [] 1 [3, 2] (5) 36]⟩ : ReflectedRecipe))

def reflectedRecipe308 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe138 (scaleRecipe (-1 : ℚ) reflectedRecipe46)) (⟨[], [mkD (1) 1 [3, 2] [] 1 [3] (5) 18, mkD (-1) 1 [3, 2] [] 1 [6, 3] (5) 36, mkD (1) 1 [3, 2] [] 1 [2, 3] (5) 36]⟩ : ReflectedRecipe))

def reflectedRecipe309 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe12 (scaleRecipe (-1 : ℚ) reflectedRecipe169)) (⟨[], [mkD (1) 1 [3, 1] [] 1 [3] (5) 18, mkD (-1) 1 [3, 1] [] 1 [6, 3] (5) 36, mkD (1) 1 [3, 1] [] 1 [2, 3] (5) 36]⟩ : ReflectedRecipe))

def reflectedRecipe310 : ReflectedRecipe :=
  (⟨[mkY (1) 1 [1, 3, 2, 1]], []⟩ : ReflectedRecipe)

def reflectedRecipe311 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe134 (scaleRecipe (-1 : ℚ) reflectedRecipe310))

def reflectedRecipe312 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe165 (⟨[], [mkD (1) 1 [2, 1, 3] [1, 3] 2 [1] (5) 18]⟩ : ReflectedRecipe))

def reflectedRecipe313 : ReflectedRecipe :=
  (scaleRecipe (5/18 : ℚ) (appendRecipe reflectedRecipe23 (⟨[], [mkD (1) 1 [] [1, 3] 2 [1] (5) 18]⟩ : ReflectedRecipe)))

def reflectedRecipe314 : ReflectedRecipe :=
  (scaleRecipe (-1 : ℚ) reflectedRecipe312)

def reflectedRecipe315 : ReflectedRecipe :=
  (appendRecipe (scaleRecipe (5/18 : ℚ) reflectedRecipe46) (⟨[], [mkD (1) 1 [1, 3, 2] [3, 2] 1 [3] (5) 18]⟩ : ReflectedRecipe))

def reflectedRecipe316 : ReflectedRecipe :=
  (scaleRecipe (-1 : ℚ) reflectedRecipe315)

def reflectedRecipe317 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe311 (⟨[], [mkD (1) 1 [1, 3, 2] [] 1 [2] (5) 18, mkD (-1) 1 [1, 3, 2] [] 1 [7, 2] (5) 36, mkD (1) 1 [1, 3, 2] [] 1 [3, 2] (5) 36]⟩ : ReflectedRecipe))

def reflectedRecipe318 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe313 (⟨[], [mkD (1) 1 [1, 3, 2] [2] 1 [3] (5) 18]⟩ : ReflectedRecipe))

def reflectedRecipe319 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe23 (scaleRecipe (-1 : ℚ) (appendRecipe (scaleRecipe (5/18 : ℚ) (appendRecipe reflectedRecipe97 (⟨[], [mkD (1) 1 [] [1] 2 [3] (1) 2]⟩ : ReflectedRecipe))) (⟨[], [mkD (1) 1 [2] [1, 2] 3 [1] (5) 18]⟩ : ReflectedRecipe)))) (⟨[], [mkD (1) 1 [2, 3] [] 1 [3] (5) 18, mkD (-1) 1 [2, 3] [] 1 [6, 3] (5) 36, mkD (1) 1 [2, 3] [] 1 [2, 3] (5) 36]⟩ : ReflectedRecipe))

def reflectedRecipe320 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe141 (⟨[], [mkD (1) 1 [1, 3, 2] [3] 1 [2] (5) 18]⟩ : ReflectedRecipe))

def reflectedRecipe321 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe23 (scaleRecipe (-1 : ℚ) reflectedRecipe154)) (⟨[], [mkD (1) 1 [2, 3] [] 1 [2] (5) 18, mkD (-1) 1 [2, 3] [] 1 [7, 2] (5) 36, mkD (1) 1 [2, 3] [] 1 [3, 2] (5) 36]⟩ : ReflectedRecipe))

def reflectedRecipe322 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe9 (scaleRecipe (-1 : ℚ) reflectedRecipe55)) (⟨[], [mkD (1) 1 [2, 1] [] 1 [2] (5) 18, mkD (-1) 1 [2, 1] [] 1 [7, 2] (5) 36, mkD (1) 1 [2, 1] [] 1 [3, 2] (5) 36]⟩ : ReflectedRecipe))

def reflectedRecipe323 : ReflectedRecipe :=
  (⟨[mkY (1) 1 [2, 1, 3, 2]], []⟩ : ReflectedRecipe)

def reflectedRecipe324 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe203 (scaleRecipe (-1 : ℚ) reflectedRecipe323))

def reflectedRecipe325 : ReflectedRecipe :=
  (scaleRecipe (5/18 : ℚ) (appendRecipe reflectedRecipe20 (⟨[], [mkD (1) 1 [] [2, 1] 3 [2] (1) 2]⟩ : ReflectedRecipe)))

def reflectedRecipe326 : ReflectedRecipe :=
  (appendRecipe (scaleRecipe (1/2 : ℚ) reflectedRecipe236) (⟨[], [mkD (1) 1 [3, 2, 1] [2, 1] 3 [2] (1) 2]⟩ : ReflectedRecipe))

def reflectedRecipe327 : ReflectedRecipe :=
  (scaleRecipe (-1 : ℚ) reflectedRecipe326)

def reflectedRecipe328 : ReflectedRecipe :=
  (appendRecipe (scaleRecipe (1/2 : ℚ) reflectedRecipe55) (⟨[], [mkD (1) 1 [2, 1, 3] [1] 2 [3] (1) 2]⟩ : ReflectedRecipe))

def reflectedRecipe329 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe324 (⟨[], [mkD (1) 1 [2, 1, 3] [] 2 [1] (5) 18, mkD (-1) 1 [2, 1, 3] [] 2 [7, 1] (5) 36, mkD (1) 1 [2, 1, 3] [] 2 [3, 1] (5) 36]⟩ : ReflectedRecipe))

def reflectedRecipe330 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [3, 1] [] 2 [1] (5) 18, mkD (-1) 1 [3, 1] [] 2 [7, 1] (5) 36, mkD (1) 1 [3, 1] [] 2 [3, 1] (5) 36]⟩ : ReflectedRecipe)

def reflectedRecipe331 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe57 (scaleRecipe (-1 : ℚ) (appendRecipe (scaleRecipe (5/18 : ℚ) (appendRecipe reflectedRecipe177 (⟨[], [mkD (1) 1 [] [2] 3 [1] (5) 18]⟩ : ReflectedRecipe))) (⟨[], [mkD (1) 1 [3] [2, 3] 1 [2] (5) 18]⟩ : ReflectedRecipe)))) reflectedRecipe330)

def reflectedRecipe332 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe325 (⟨[], [mkD (1) 1 [2, 1, 3] [3] 2 [1] (5) 18]⟩ : ReflectedRecipe))

def reflectedRecipe333 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe193 (⟨[], [mkD (1) 1 [2, 3, 1] [] 2 [3] (1) 2]⟩ : ReflectedRecipe))

def reflectedRecipe334 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe72 (scaleRecipe (-1 : ℚ) reflectedRecipe333)) (⟨[], [mkD (1) 1 [2, 3] [] 2 [1] (5) 18, mkD (-1) 1 [2, 3] [] 2 [7, 1] (5) 36, mkD (1) 1 [2, 3] [] 2 [3, 1] (5) 36]⟩ : ReflectedRecipe))

def reflectedRecipe335 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe203 (⟨[], [mkD (1) 1 [2, 1, 3] [] 2 [1] (5) 18]⟩ : ReflectedRecipe))

def reflectedRecipe336 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe177 (scaleRecipe (-1 : ℚ) reflectedRecipe179)) (⟨[], [mkD (1) 1 [3, 2] [] 2 [1] (5) 18, mkD (-1) 1 [3, 2] [] 2 [7, 1] (5) 36, mkD (1) 1 [3, 2] [] 2 [3, 1] (5) 36]⟩ : ReflectedRecipe))

def reflectedRecipe337 : ReflectedRecipe :=
  (appendRecipe (scaleRecipe (5/18 : ℚ) reflectedRecipe198) reflectedRecipe221)

def reflectedRecipe338 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe57 (scaleRecipe (-1 : ℚ) reflectedRecipe337)) reflectedRecipe330)

def reflectedRecipe339 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe23 (⟨[], [mkD (1) 1 [] [2, 3] 1 [2] (5) 18]⟩ : ReflectedRecipe))

def reflectedRecipe340 : ReflectedRecipe :=
  (⟨[mkY (1) 1 [2, 3, 1, 2]], []⟩ : ReflectedRecipe)

def reflectedRecipe341 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe203 (scaleRecipe (-1 : ℚ) reflectedRecipe340))

def reflectedRecipe342 : ReflectedRecipe :=
  (appendRecipe (scaleRecipe (1/2 : ℚ) reflectedRecipe222) (⟨[], [mkD (1) 1 [2, 3, 1] [3, 1] 2 [3] (1) 2]⟩ : ReflectedRecipe))

def reflectedRecipe343 : ReflectedRecipe :=
  (scaleRecipe (-1 : ℚ) reflectedRecipe342)

def reflectedRecipe344 : ReflectedRecipe :=
  (appendRecipe (scaleRecipe (1/2 : ℚ) reflectedRecipe339) (⟨[], [mkD (1) 1 [2, 3, 1] [1] 2 [3] (1) 2]⟩ : ReflectedRecipe))

def reflectedRecipe345 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe23 (scaleRecipe (-1 : ℚ) (appendRecipe (scaleRecipe (1/2 : ℚ) (appendRecipe reflectedRecipe9 (⟨[], [mkD (1) 1 [] [2] 1 [3] (5) 18]⟩ : ReflectedRecipe))) (⟨[], [mkD (1) 1 [1] [2, 1] 3 [2] (1) 2]⟩ : ReflectedRecipe)))) (⟨[], [mkD (1) 1 [1, 3] [] 2 [1] (5) 18, mkD (-1) 1 [1, 3] [] 2 [7, 1] (5) 36, mkD (1) 1 [1, 3] [] 2 [3, 1] (5) 36]⟩ : ReflectedRecipe))

def reflectedRecipe346 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe341 (⟨[], [mkD (1) 1 [2, 3, 1] [] 2 [1] (5) 18, mkD (-1) 1 [2, 3, 1] [] 2 [7, 1] (5) 36, mkD (1) 1 [2, 3, 1] [] 2 [3, 1] (5) 36]⟩ : ReflectedRecipe))

def reflectedRecipe347 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe70 (⟨[], [mkD (1) 1 [2, 3, 1] [3] 2 [1] (5) 18]⟩ : ReflectedRecipe))

def reflectedRecipe348 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe59 (scaleRecipe (-1 : ℚ) reflectedRecipe335)) (⟨[], [mkD (1) 1 [2, 1] [] 2 [1] (5) 18, mkD (-1) 1 [2, 1] [] 2 [7, 1] (5) 36, mkD (1) 1 [2, 1] [] 2 [3, 1] (5) 36]⟩ : ReflectedRecipe))

def reflectedRecipe349 : ReflectedRecipe :=
  (scaleRecipe (5/18 : ℚ) (appendRecipe reflectedRecipe20 (⟨[], [mkD (1) 1 [] [3, 1] 2 [3] (1) 2]⟩ : ReflectedRecipe)))

def reflectedRecipe350 : ReflectedRecipe :=
  (⟨[mkY (1) 1 [3, 1, 2, 3]], []⟩ : ReflectedRecipe)

def reflectedRecipe351 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe239 (scaleRecipe (-1 : ℚ) reflectedRecipe350))

def reflectedRecipe352 : ReflectedRecipe :=
  (appendRecipe (scaleRecipe (1/2 : ℚ) reflectedRecipe169) (⟨[], [mkD (1) 1 [3, 1, 2] [1] 3 [2] (1) 2]⟩ : ReflectedRecipe))

def reflectedRecipe353 : ReflectedRecipe :=
  (⟨[], [mkD (1) 1 [2, 1] [] 3 [1] (5) 18, mkD (-1) 1 [2, 1] [] 3 [6, 1] (5) 36, mkD (1) 1 [2, 1] [] 3 [2, 1] (5) 36]⟩ : ReflectedRecipe)

def reflectedRecipe354 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe57 (scaleRecipe (-1 : ℚ) (appendRecipe (scaleRecipe (5/18 : ℚ) (appendRecipe reflectedRecipe67 (⟨[], [mkD (1) 1 [] [3] 2 [1] (5) 18]⟩ : ReflectedRecipe))) (⟨[], [mkD (1) 1 [2] [3, 2] 1 [3] (5) 18]⟩ : ReflectedRecipe)))) reflectedRecipe353)

def reflectedRecipe355 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe349 (⟨[], [mkD (1) 1 [3, 1, 2] [2] 3 [1] (5) 18]⟩ : ReflectedRecipe))

def reflectedRecipe356 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe351 (⟨[], [mkD (1) 1 [3, 1, 2] [] 3 [1] (5) 18, mkD (-1) 1 [3, 1, 2] [] 3 [6, 1] (5) 36, mkD (1) 1 [3, 1, 2] [] 3 [2, 1] (5) 36]⟩ : ReflectedRecipe))

def reflectedRecipe357 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe67 (scaleRecipe (-1 : ℚ) reflectedRecipe69)) (⟨[], [mkD (1) 1 [2, 3] [] 3 [1] (5) 18, mkD (-1) 1 [2, 3] [] 3 [6, 1] (5) 36, mkD (1) 1 [2, 3] [] 3 [2, 1] (5) 36]⟩ : ReflectedRecipe))

def reflectedRecipe358 : ReflectedRecipe :=
  (appendRecipe (scaleRecipe (5/18 : ℚ) reflectedRecipe103) reflectedRecipe235)

def reflectedRecipe359 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe57 (scaleRecipe (-1 : ℚ) reflectedRecipe358)) reflectedRecipe353)

def reflectedRecipe360 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe124 (⟨[], [mkD (1) 1 [3, 2, 1] [] 3 [2] (1) 2]⟩ : ReflectedRecipe))

def reflectedRecipe361 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe182 (scaleRecipe (-1 : ℚ) reflectedRecipe360)) (⟨[], [mkD (1) 1 [3, 2] [] 3 [1] (5) 18, mkD (-1) 1 [3, 2] [] 3 [6, 1] (5) 36, mkD (1) 1 [3, 2] [] 3 [2, 1] (5) 36]⟩ : ReflectedRecipe))

def reflectedRecipe362 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe239 (⟨[], [mkD (1) 1 [3, 1, 2] [] 3 [1] (5) 18]⟩ : ReflectedRecipe))

def reflectedRecipe363 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe138 (⟨[], [mkD (1) 1 [] [3, 2] 1 [3] (5) 18]⟩ : ReflectedRecipe))

def reflectedRecipe364 : ReflectedRecipe :=
  (⟨[mkY (1) 1 [3, 2, 1, 3]], []⟩ : ReflectedRecipe)

def reflectedRecipe365 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe239 (scaleRecipe (-1 : ℚ) reflectedRecipe364))

def reflectedRecipe366 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe138 (scaleRecipe (-1 : ℚ) (appendRecipe (scaleRecipe (1/2 : ℚ) (appendRecipe reflectedRecipe12 (⟨[], [mkD (1) 1 [] [3] 1 [2] (5) 18]⟩ : ReflectedRecipe))) (⟨[], [mkD (1) 1 [1] [3, 1] 2 [3] (1) 2]⟩ : ReflectedRecipe)))) (⟨[], [mkD (1) 1 [1, 2] [] 3 [1] (5) 18, mkD (-1) 1 [1, 2] [] 3 [6, 1] (5) 36, mkD (1) 1 [1, 2] [] 3 [2, 1] (5) 36]⟩ : ReflectedRecipe))

def reflectedRecipe367 : ReflectedRecipe :=
  (appendRecipe (scaleRecipe (1/2 : ℚ) reflectedRecipe363) (⟨[], [mkD (1) 1 [3, 2, 1] [1] 3 [2] (1) 2]⟩ : ReflectedRecipe))

def reflectedRecipe368 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe180 (⟨[], [mkD (1) 1 [3, 2, 1] [2] 3 [1] (5) 18]⟩ : ReflectedRecipe))

def reflectedRecipe369 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe365 (⟨[], [mkD (1) 1 [3, 2, 1] [] 3 [1] (5) 18, mkD (-1) 1 [3, 2, 1] [] 3 [6, 1] (5) 36, mkD (1) 1 [3, 2, 1] [] 3 [2, 1] (5) 36]⟩ : ReflectedRecipe))

def reflectedRecipe370 : ReflectedRecipe :=
  (appendRecipe (appendRecipe reflectedRecipe172 (scaleRecipe (-1 : ℚ) reflectedRecipe362)) (⟨[], [mkD (1) 1 [3, 1] [] 3 [1] (5) 18, mkD (-1) 1 [3, 1] [] 3 [6, 1] (5) 36, mkD (1) 1 [3, 1] [] 3 [2, 1] (5) 36]⟩ : ReflectedRecipe))

def reflectedRecipe371 : ReflectedRecipe :=
  (appendRecipe (scaleRecipe (1/2 : ℚ) reflectedRecipe28) (⟨[], [mkD (1) 1 [1, 2] [] 3 [2] (1) 2]⟩ : ReflectedRecipe))

def reflectedRecipe372 : ReflectedRecipe :=
  (appendRecipe (scaleRecipe (1/2 : ℚ) reflectedRecipe22) (⟨[], [mkD (1) 1 [1, 3] [] 2 [3] (1) 2]⟩ : ReflectedRecipe))

def reflectedRecipe373 : ReflectedRecipe :=
  (⟨[mkY (1) 1 [2, 1, 3]], []⟩ : ReflectedRecipe)

def reflectedRecipe374 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe57 (⟨[], [mkD (1) 1 [2, 1] [] 3 [1] (5) 18]⟩ : ReflectedRecipe))

def reflectedRecipe375 : ReflectedRecipe :=
  (⟨[mkY (1) 1 [2, 3, 1]], []⟩ : ReflectedRecipe)

def reflectedRecipe376 : ReflectedRecipe :=
  (⟨[mkY (1) 1 [3, 1, 2]], []⟩ : ReflectedRecipe)

def reflectedRecipe377 : ReflectedRecipe :=
  (appendRecipe reflectedRecipe57 (⟨[], [mkD (1) 1 [3, 1] [] 2 [1] (5) 18]⟩ : ReflectedRecipe))

def reflectedRecipe378 : ReflectedRecipe :=
  (⟨[mkY (1) 1 [3, 2, 1]], []⟩ : ReflectedRecipe)

end AlbertSequential.FiveTest
