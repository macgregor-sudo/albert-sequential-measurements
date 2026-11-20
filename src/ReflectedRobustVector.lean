/- SPDX-License-Identifier: Apache-2.0 -/
module
public import ReflectedRobustTranscript

@[expose] public section
namespace AlbertSequential.FiveTest
open LengthSeven LengthSeven.Robust

/-- The actual 22 terms of the frozen reflected vector, in printed order. -/
def reflectedRobustVector : List (ℚ × List Letter) :=
  [((2 : ℚ), [1, 2, 3, 0].map lt),
    ((-2 : ℚ), [1, 3, 2, 0].map lt),
    ((-3 : ℚ), [2, 1, 3, 0].map lt),
    ((2 : ℚ), [2, 3, 1, 0].map lt),
    ((3 : ℚ), [3, 1, 2, 0].map lt),
    ((-2 : ℚ), [3, 2, 1, 0].map lt),
    ((4 : ℚ), [1, 2, 3, 1].map lt),
    ((-4 : ℚ), [1, 3, 2, 1].map lt),
    ((-6 : ℚ), [2, 1, 3, 2].map lt),
    ((6 : ℚ), [2, 3, 1, 2].map lt),
    ((6 : ℚ), [3, 1, 2, 3].map lt),
    ((-6 : ℚ), [3, 2, 1, 3].map lt),
    ((-4 : ℚ), [1, 2, 3].map lt),
    ((4 : ℚ), [1, 3, 2].map lt),
    ((7 : ℚ), [2, 1, 3].map lt),
    ((-4 : ℚ), [2, 3, 1].map lt),
    ((-7 : ℚ), [3, 1, 2].map lt),
    ((4 : ℚ), [3, 2, 1].map lt),
    ((-10/9 : ℚ), [2, 3].map lt),
    ((1/2 : ℚ), [2, 1].map lt),
    ((10/9 : ℚ), [3, 2].map lt),
    ((-1/2 : ℚ), [3, 1].map lt)]

end AlbertSequential.FiveTest
