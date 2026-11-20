module

import ScheduleMatchingAffinity
open AlbertSequential AlbertSequential.MatchingModels
attribute [local irreducible] fourPointInvariant
example (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (s : List (Fin 4)) (hs : s.length = 7) :
    ∃ M : HilbertProjectiveData (Fin 4) ℂ (EuclideanSpace ℂ (Fin 12)),
      ∀ w : Word (Fin 4), w.length ≤ 6 ∨ w.map Prod.fst = s →
        M.probability w = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w :=
  prop_cer_schedule_a p hp hA s hs
#print axioms prop_cer_schedule_a
#print axioms prop_cer_schedule_a_two_schedules
#print axioms nativeWordProbability_e3_affine_on_schedule
