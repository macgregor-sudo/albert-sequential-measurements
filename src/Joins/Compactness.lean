/- SPDX-License-Identifier: Apache-2.0 -/
module

public import PaperFixedDimensionCompactness

/-!
# prop:ins:compactness, second paragraph, for realizations of the finite menu

Companion `prop:ins:compactness`, second paragraph: "If no global realization exists at this
fixed `D`, there are finitely many pairs `(p_i, w_i)` and a number `δ > 0` such that every
`D`-dimensional stationary CP realization of their finite menu has
`max_i |Pr(p_i, w_i) − t(p_i, w_i)| ≥ δ`."

`stationaryKraus_finite_positive_error_gap` gives the bound for realizations on all labels. Here a
realization of the finite menu (preparation labels `ps`, test labels `xs`: those occurring in the
pairs) is extended to all labels with `extendFiniteMenuModel` (unused labels get arbitrary
normalized defaults); the extension reproduces the menu realization on every menu word
(`finiteMenuExtension_wordProbability`), so the global bound applies to it.
-/

@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder
namespace AlbertSequential

/-- **prop:ins:compactness, error gap on the finite menu.** If `t` has no stationary
`d`-dimensional Kraus realization, there are finite sets of preparation labels `ps` and test
labels `xs`, finitely many pairs `F` (each a preparation in `ps` and a word over `xs`) and `δ > 0`
such that every stationary `d`-dimensional Kraus realization of the menu `(ps, xs)` misses some
pair of `F` by at least `δ`. -/
theorem stationaryKraus_finite_menu_error_gap (d : ℕ) (hd : 0 < d)
    {P X : Type*} {A : X → Type*} [∀ x, Fintype (A x)] [∀ x, Nonempty (A x)]
    (t : P → InstrumentWord A → ℝ) (hnone : ¬ HasStationaryKrausRealization d t) :
    ∃ (ps : Finset P) (xs : Finset X) (F : Finset (P × InstrumentWord A)) (δ : ℝ), 0 < δ ∧
      (∀ q ∈ F, q.1 ∈ ps ∧ ∀ a ∈ q.2, a.1 ∈ xs) ∧
      ∀ (rho : {p // p ∈ ps} → ComplexMatrix d)
        (K : (x : {x // x ∈ xs}) → A x.val → List (ComplexMatrix d)),
        (∀ p, IsMatrixDensity (rho p)) →
        (∀ x, ∑ a, krausEffect (K x a) = 1) →
        ∃ q ∈ F, ∃ (p : {p // p ∈ ps}) (v : InstrumentWord (fun x : {x // x ∈ xs} => A x.val)),
          p.val = q.1 ∧ includeMenuWord xs v = q.2 ∧
          δ ≤ |finiteKrausWordProbability rho K p v - t q.1 q.2| := by
  classical
  have hnchoi : ¬ ∃ r : RawFiniteCPModel d P X A,
      IsNormalizedFiniteCPModel r ∧ MatchesAllWords r t :=
    fun h => hnone ((stationaryKrausRealization_iff_choi t).mpr h)
  obtain ⟨F, δ, hδ, hF⟩ := (fixedDimensionCompactness d P X A).finite_error_gap hd t hnchoi
  let ps : Finset P := F.image Prod.fst
  let xs : Finset X := F.biUnion fun q => (q.2.map Sigma.fst).toFinset
  have hmenu : ∀ q ∈ F, q.1 ∈ ps ∧ ∀ a ∈ q.2, a.1 ∈ xs := by
    intro q hq
    refine ⟨Finset.mem_image_of_mem _ hq, fun a ha => ?_⟩
    exact Finset.mem_biUnion.mpr ⟨q, hq, List.mem_toFinset.mpr (List.mem_map_of_mem ha)⟩
  refine ⟨ps, xs, F, δ, hδ, hmenu, fun rho K hrho hK => ?_⟩
  let rloc := stationaryKrausToChoi rho K
  have hloc : IsNormalizedFiniteCPModel rloc := stationaryKrausToChoi_normalized rho K hrho hK
  obtain ⟨q, hq, herr⟩ := hF (extendFiniteMenuModel hd ps xs rloc)
    (extendFiniteMenuModel_normalized hd ps xs rloc hloc)
  obtain ⟨hq1, hq2⟩ := hmenu q hq
  obtain ⟨v, hv⟩ := exists_localMenuWord xs q.2 hq2
  refine ⟨q, hq, ⟨q.1, hq1⟩, v, rfl, hv, ?_⟩
  have hact : ∀ x a Y, choiAction (rloc.2 x a) Y = krausAction (K x a) Y :=
    fun x a Y => krausChoi_action (K x a) Y
  have hext := finiteMenuExtension_wordProbability hd ps xs rloc ⟨q.1, hq1⟩ v
  rw [hv] at hext
  rw [hext, choiWordProbability_eq_krausWordProbability rloc K hact] at herr
  exact herr

end AlbertSequential
