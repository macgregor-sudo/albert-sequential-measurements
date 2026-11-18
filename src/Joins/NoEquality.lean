/- SPDX-License-Identifier: Apache-2.0 -/
module

public import BlockA.SecondOrderResidual
public import HorizonFive.Final

/-!
# rem:cer:fivestep, without `E(c) = 0`

Paper (core, remark `rem:cer:fivestep`, first sentence): "For any four atoms of `J`, in particular
those of `S`, no projective equality supported on words of length at most five is violated from
any state of `J`."

`HorizonFive.horizonFiveClause` proves this with the hypothesis `E(c) = 0` in the universal
algebra of four projections (`specialValue c = 0`); part (a), `AppF.prop_cer_noequality_a`,
shows that this hypothesis is equivalent to `c` being a projective equality
(`AppF.IsProjectiveEquality`: vanishing in every real finite-dimensional representation with a
vector state). Since every sequential projective representation in the paper's sense includes
those, the hypothesis used here is implied by the paper's.
-/

@[expose] public section
noncomputable section

namespace AlbertSequential.HorizonFive

/-- **rem:cer:fivestep, first sentence** (projective-equality form). For any four atoms and any
combination `c` of words of length at most five that is a projective equality (vanishes in every real
finite-dimensional projective representation with a vector state), the combination vanishes on
the octonionic table from every state. -/
theorem horizonFive_projectiveEquality (p : Test → Albert) (hp : ∀ i, IsAtom (p i))
    (c : WordCombination) (hc : SupportedWithin c 5) (hproj : AppF.IsProjectiveEquality c)
    (ρ : Albert) (hρ : IsDensity ρ) : nativeTableValue p ρ c = 0 := by
  have hE : specialValue c = 0 := ((AppF.prop_cer_noequality_a c).out 1 4).mp hproj
  exact horizonFiveClause p hp c hc hE ρ hρ

end AlbertSequential.HorizonFive
