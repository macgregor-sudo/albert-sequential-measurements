module

public import FixedDimensionCompactness
public import FiniteMenuExtension

/-! The finite positive error gap for models defined only on the witness menu.
The returned finite pairs intrinsically belong to that menu; unused global
coordinates and any arbitrary extension have disappeared from the conclusion.
-/
@[expose] public section
noncomputable section
namespace AlbertSequential

theorem finite_positive_error_gap_on_local_menu (d : ℕ) (hd : 0 < d)
    {P X : Type*} {A : X → Type*} [∀ x, Fintype (A x)] [∀ x, Nonempty (A x)]
    (t : P → InstrumentWord A → ℝ)
    (hnone : ¬ ∃ r : RawFiniteCPModel d P X A,
      IsNormalizedFiniteCPModel r ∧ MatchesAllWords r t) :
    ∃ (ps : Finset P) (xs : Finset X)
      (F : Finset ({p // p ∈ ps} × InstrumentWord (fun x : {x // x ∈ xs} => A x.val)))
      (δ : ℝ), 0 < δ ∧
      ∀ r : RawFiniteCPModel d {p // p ∈ ps} {x // x ∈ xs} (fun x => A x.val),
        IsNormalizedFiniteCPModel r →
        ∃ q ∈ F, δ ≤ |finiteCPWordProbability r q.1 q.2 -
          t q.1.val (includeMenuWord xs q.2)| := by
  classical
  obtain ⟨G, δ, hδ, hG⟩ := (fixedDimensionCompactness d P X A).finite_error_gap hd t hnone
  let ps : Finset P := G.image Prod.fst
  let xs : Finset X := G.biUnion (fun q => q.2.toFinset.image Sigma.fst)
  have hp (q : {q // q ∈ G}) : q.val.1 ∈ ps :=
    Finset.mem_image.mpr ⟨q.val, q.property, rfl⟩
  have hx (q : {q // q ∈ G}) : ∀ a ∈ q.val.2, a.1 ∈ xs := by
    intro a ha
    exact Finset.mem_biUnion.mpr ⟨q.val, q.property,
      Finset.mem_image.mpr ⟨a, List.mem_toFinset.mpr ha, rfl⟩⟩
  let lift : {q // q ∈ G} →
      ({p // p ∈ ps} × InstrumentWord (fun x : {x // x ∈ xs} => A x.val)) :=
    fun q => (⟨q.val.1, hp q⟩, Classical.choose (exists_localMenuWord xs q.val.2 (hx q)))
  have hlift (q : {q // q ∈ G}) : includeMenuWord xs (lift q).2 = q.val.2 :=
    Classical.choose_spec (exists_localMenuWord xs q.val.2 (hx q))
  refine ⟨ps, xs, G.attach.image lift, δ, hδ, fun r hr => ?_⟩
  obtain ⟨q, hq, herr⟩ := hG (extendFiniteMenuModel hd ps xs r)
    (extendFiniteMenuModel_normalized hd ps xs r hr)
  let qlocal := lift ⟨q, hq⟩
  refine ⟨qlocal, Finset.mem_image.mpr ⟨⟨q, hq⟩, Finset.mem_attach G ⟨q, hq⟩, rfl⟩, ?_⟩
  have hprep : qlocal.1.val = q.1 := rfl
  have hword : includeMenuWord xs qlocal.2 = q.2 := hlift ⟨q, hq⟩
  have hext := finiteMenuExtension_wordProbability hd ps xs r qlocal.1 qlocal.2
  have hbound : δ ≤ |finiteCPWordProbability (extendFiniteMenuModel hd ps xs r)
      qlocal.1.val (includeMenuWord xs qlocal.2) -
      t qlocal.1.val (includeMenuWord xs qlocal.2)| := by
    simpa only [hprep, hword] using herr
  rwa [hext] at hbound

end AlbertSequential
