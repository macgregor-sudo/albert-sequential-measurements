module

import ScheduleMatchingMixture
open AlbertSequential AlbertSequential.MatchingModels
example : scheduleFirstRoundTrip =
    [(0,true),(2,false),(1,false),(3,true),(1,false),(2,false),(0,true)] := rfl
example : scheduleSecondRoundTrip =
    [(0,true),(1,false),(2,false),(3,true),(2,false),(1,false),(0,true)] := rfl
#print axioms prop_cer_schedule_b
#print axioms prop_cer_schedule_b_native
#print axioms scheduleRoundTrip_mixture_eq
