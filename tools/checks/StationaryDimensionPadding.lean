module

import StationaryDimensionPadding

open AlbertSequential Matrix
open scoped BigOperators ComplexOrder

example {d D : ℕ} {B : Type*} [DecidableEq B]
    (V : Matrix (Fin D) (Fin d) ℂ) (a₀ : B) (K : B → List (ComplexMatrix d))
    (a : B) (Y Z : ComplexMatrix D)
    (h₁ : Vᴴ * Y * V = Vᴴ * Z * V)
    (h₂ : (1 - V * Vᴴ) * Y * (1 - V * Vᴴ) = (1 - V * Vᴴ) * Z * (1 - V * Vᴴ)) :
    krausAction (paddedInstrumentKraus V a₀ K a) Y = krausAction (paddedInstrumentKraus V a₀ K a) Z := by
  rw [paddedInstrumentKraus_action, paddedInstrumentKraus_action, h₁, h₂]

example {d D : ℕ} {P X : Type*} {A : X → Type*} [∀ x, Fintype (A x)] [∀ x, Nonempty (A x)]
    (t : P → InstrumentWord A → ℝ) (hd : d ≤ D)
    (h : HasStationaryKrausRealization d t) : HasStationaryKrausRealization D t :=
  h.of_le_dim hd

example {D : ℕ} (hD : 0 < D) {P X : Type*} {A : X → Type*} [∀ x, Fintype (A x)]
    [∀ x, Nonempty (A x)] (t : P → InstrumentWord A → ℝ)
    (hlocal : ∀ (ps : Finset P) (xs : Finset X), ∃ d ≤ D,
      HasStationaryKrausRealization d
        (fun (p : {p // p ∈ ps}) (w : InstrumentWord (fun x : {x // x ∈ xs} => A x.val)) =>
          t p.val (includeMenuWord xs w))) :
    ∃ r : RawFiniteCPModel D P X A, IsNormalizedFiniteCPModel r ∧ MatchesAllWords r t :=
  (stationaryKrausRealization_iff_choi t).mp
    ((stationaryKraus_global_iff_local_finite_menus_dim_le D hD t).mpr hlocal)

#print axioms paddedInstrumentKraus_action
#print axioms paddedInstrumentKraus_completelyPositive
#print axioms paddedInstrumentKraus_normalized
#print axioms paddedInstrumentKraus_action_on_occupied
#print axioms paddedStationaryWordState
#print axioms paddedStationaryWordProbability
#print axioms HasStationaryKrausRealization.of_le_dim
#print axioms stationaryKraus_global_iff_local_finite_menus_dim_le
