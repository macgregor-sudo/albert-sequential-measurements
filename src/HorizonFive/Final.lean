/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HorizonFive.Seven
public import HorizonFive.Recognition
public import HorizonFive.ReflA

/-! # The horizon-five clause, unconditionally (core `rem:cer:fivestep`)

* `transferThroughSeven : TransferThroughSeven` (lem:cer:h5:seven), from
  `transferThroughSeven_of_lift` (Steps 1-3) and `recognitionThroughFivePos` (lem:cer:h5:lift,
  explicit lifts, no Cohn theorem);
* `horizonFiveClause : HorizonFiveClause`, from `horizonFive_of_seven` (refl(a)
  without Serre, refl(b), degree nine and eight). -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.HorizonFive

/-- **lem:cer:h5:seven (proved).** -/
theorem transferThroughSeven : TransferThroughSeven :=
  transferThroughSeven_of_lift recognitionThroughFivePos

/-- **Horizon five (proved, no hypotheses).** For any four atoms of the Albert algebra, every
projective equality supported on words of length at most five holds for every state. -/
theorem horizonFiveClause : HorizonFiveClause :=
  horizonFive_of_seven transferThroughSeven

end AlbertSequential.HorizonFive
