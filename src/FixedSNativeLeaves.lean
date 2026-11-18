/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ConstructedLeafCalibration
public import FixedSCornerConditions
public import FiniteCornerWitness

/-! Native evaluation of the actual constructed leaves, under arbitrary label
maps and raw preparation elements. No positivity/normalization is needed for
leaf vanishing; native purity is used only at the stored yes-atom base. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace AlbertSequential
open NativeAnalysis ConstructorCalibration

theorem nativeOutcome_relabel {ι κ : Type*} (p : κ → Albert) (f : ι → κ) (a : Outcome ι) :
    nativeOutcome p (relabelOutcome f a) = nativeOutcome (p ∘ f) a := rfl

theorem nativeBranchState_relabel {ι κ : Type*} (p : κ → Albert) (f : ι → κ)
    (ρ : Albert) (w : Word ι) :
    nativeBranchState p ρ (relabelWord f w) = nativeBranchState (p ∘ f) ρ w := by
  induction w generalizing ρ with
  | nil => rfl
  | cons a w ih =>
    rw [relabelWord_cons, nativeBranchState_cons, nativeBranchState_cons,
      nativeOutcome_relabel, ih]

theorem nativeWordProbability_relabel {ι κ : Type*} (p : κ → Albert) (f : ι → κ)
    (ρ : Albert) (w : Word ι) :
    nativeWordProbability p ρ (relabelWord f w) = nativeWordProbability (p ∘ f) ρ w :=
  congrArg albertTrace (nativeBranchState_relabel p f ρ w)

theorem fixedSCorner_leaf_native_zero (j : Fin 4) (ρ : Albert)
    (l : SupportedPurityLeaf (Fin 4)) (hl : LeafCalibrated (fixedSCornerScalar j) l) :
    l.wordFunctional.evaluate (nativeWordProbability (fixedSCornerMenu j) ρ) = 0 := by
  have ha : nativeOutcome (fixedSCornerMenu j) l.outcome = fixedSCornerMenu j l.outcome.1 := by
    change (if l.outcome.2 then _ else _) = _
    rw [hl.1]
    rfl
  apply l.wordFunctional_native_zero (fixedSCornerMenu j)
    (fun a => (fixedSCorner_isAtom j a).1) ρ
  · rw [ha]
    exact fixedSCorner_isAtom j l.outcome.1
  · rw [hl.2, ha]
    exact nativeWordProbability_eq_pairing _ _ _

theorem fixedSCorner_constructor_native_zero (j : Fin 4) (ρ : Albert) :
    ∀ o ∈ cornerResidualTelescopeOccurrences (fixedSCornerData j) (fixedSCornerScalar j),
      o.leaf.wordFunctional.evaluate (nativeWordProbability (fixedSCornerMenu j) ρ) = 0 := by
  intro o ho
  exact fixedSCorner_leaf_native_zero j ρ o.leaf
    (ConstructorCalibration.cornerResidualTelescope_calibrated _ _ o ho)

theorem fixedS_combined_leaves_native_zero (ρ : Albert) :
    ∀ o ∈ combinedCornerOccurrences fixedSCornerData fixedSCornerScalar
        (fun j a => fixedSCornerRelabelling j a) (fun _ => 1),
      o.leaf.wordFunctional.evaluate (nativeWordProbability fixedS ρ) = 0 := by
  intro o ho
  rcases List.mem_flatten.mp ho with ⟨es, hes, ho⟩
  rcases List.mem_ofFn.mp hes with ⟨j, rfl⟩
  rcases List.mem_map.mp ho with ⟨u, hu, rfl⟩
  rcases List.mem_map.mp hu with ⟨v, hv, rfl⟩
  change (SupportedPurityLeaf.relabel (fixedSCornerRelabelling j) v.leaf).wordFunctional.evaluate _ = 0
  rw [SupportedPurityLeaf.wordFunctional_relabel, FiniteRealWordFunctional.evaluate_relabel]
  have hz := fixedSCorner_constructor_native_zero j ρ v hv
  simpa only [nativeWordProbability_relabel, fixedSCornerMenu] using hz

end AlbertSequential
