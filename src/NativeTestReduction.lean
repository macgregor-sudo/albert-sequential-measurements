/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeIdempotentClassification
public import ReducedBinaryKrausModel

/-! Literal native tests for fixed direct/complement/deterministic reductions.
All-word semantics uses the same partial word translation as the Kraus model. -/
@[expose] public section
noncomputable section
namespace AlbertSequential

def BinaryTestReduction.nativeEffect (m : BinaryTestReduction) (p : Albert) : Albert :=
  match m with
  | .direct => p
  | .complement => albertUnit - p
  | .deterministic c => if c then albertUnit else 0

def BinaryTestReduction.nativeMenu {X : Type*} (m : X → BinaryTestReduction) (p : X → Albert) :
    X → Albert := fun x => (m x).nativeEffect (p x)

namespace NativeAnalysis

theorem exists_atom_test_reduction (q : Albert) (hq : jordanMul q q = q) :
    ∃ p : Albert, IsAtom p ∧ ∃ m : BinaryTestReduction, q = m.nativeEffect p := by
  rcases native_idempotent_classification q hq with h0 | he | ha | hc
  · exact ⟨diagAtom 0, diagAtom_isAtom 0, .deterministic false, h0⟩
  · exact ⟨diagAtom 0, diagAtom_isAtom 0, .deterministic true, he⟩
  · exact ⟨q,ha,.direct,rfl⟩
  · refine ⟨albertUnit - q,hc,.complement,?_⟩
    change q = albertUnit - (albertUnit - q)
    module

theorem exists_atom_menu_reduction {X : Type*} (q : X → Albert)
    (hq : ∀ i, jordanMul (q i) (q i) = q i) :
    ∃ p : X → Albert, (∀ i, IsAtom (p i)) ∧
      ∃ m : X → BinaryTestReduction, q = BinaryTestReduction.nativeMenu m p := by
  let p i := Classical.choose (exists_atom_test_reduction (q i) (hq i))
  have hp i : IsAtom (p i) := (Classical.choose_spec (exists_atom_test_reduction (q i) (hq i))).1
  let m i := Classical.choose ((Classical.choose_spec (exists_atom_test_reduction (q i) (hq i))).2)
  refine ⟨p,hp,m,?_⟩
  funext i
  exact Classical.choose_spec ((Classical.choose_spec (exists_atom_test_reduction (q i) (hq i))).2)

private theorem quadraticMap_unit_left (x : Albert) : quadraticMap albertUnit x = x := by
  unfold quadraticMap
  rw [jordanMul_albertUnit_left, jordanMul_albertUnit_left, jordanMul_albertUnit_left,
    jordanMul_albertUnit_left]
  module

theorem quadraticMap_zero_left (x : Albert) : quadraticMap 0 x = 0 := by
  simp [quadraticMap, jordanMul_zero_left]

theorem BinaryTestReduction.native_action {X : Type*} (p : X → Albert)
    (m : X → BinaryTestReduction) (a : Outcome X) (x : Albert) :
    quadraticMap (nativeOutcome (BinaryTestReduction.nativeMenu m p) a) x =
      WordReduction.applyStep (fun b => quadraticMap (nativeOutcome p b))
        (BinaryTestReduction.outcomeStep m a) x := by
  rcases a with ⟨i,b⟩
  cases hm : m i with
  | direct => simp [BinaryTestReduction.nativeMenu, BinaryTestReduction.nativeEffect,
      nativeOutcome, BinaryTestReduction.outcomeStep, hm, WordReduction.applyStep]
  | complement =>
    have he : albertUnit - (albertUnit - p i) = p i := by module
    cases b <;> simp [BinaryTestReduction.nativeMenu, BinaryTestReduction.nativeEffect,
      nativeOutcome, BinaryTestReduction.outcomeStep, hm, WordReduction.applyStep, he]
  | deterministic c =>
    cases b <;> cases c <;>
      simp [BinaryTestReduction.nativeMenu, BinaryTestReduction.nativeEffect,
        nativeOutcome, BinaryTestReduction.outcomeStep, hm, WordReduction.applyStep,
        quadraticMap_unit_left, quadraticMap_zero_left]

theorem BinaryTestReduction.native_state {X : Type*} (p : X → Albert)
    (m : X → BinaryTestReduction) (ρ : Albert) (w : Word X) :
    nativeBranchState (BinaryTestReduction.nativeMenu m p) ρ w =
      match WordReduction.translate (BinaryTestReduction.outcomeStep m) w with
      | none => 0
      | some v => nativeBranchState p ρ v := by
  unfold nativeBranchState
  simp_rw [BinaryTestReduction.native_action]
  have h := WordReduction.foldl_translate (A := Outcome X) (B := Outcome X) (M := Albert)
    (fun a x => quadraticMap (nativeOutcome p a) x) (BinaryTestReduction.outcomeStep m)
    (fun _ => quadraticMap_zero_right _) ρ w
  cases ht : WordReduction.translate (BinaryTestReduction.outcomeStep m) w <;>
    simpa only [ht] using h

theorem BinaryTestReduction.native_probability {X : Type*} (p : X → Albert)
    (m : X → BinaryTestReduction) (ρ : Albert) (w : Word X) :
    nativeWordProbability (BinaryTestReduction.nativeMenu m p) ρ w =
      match WordReduction.translate (BinaryTestReduction.outcomeStep m) w with
      | none => 0
      | some v => nativeWordProbability p ρ v := by
  unfold nativeWordProbability
  rw [BinaryTestReduction.native_state]
  cases h : WordReduction.translate (BinaryTestReduction.outcomeStep m) w
  · exact albertTrace_zero
  · rfl

theorem BinaryTestReduction.matches_native {d : ℕ} {X : Type*}
    (r : BinaryKrausRealization d X) (p : X → Albert) (m : X → BinaryTestReduction) (ρ : Albert)
    (h : ∀ w, binaryKrausProbability r w = nativeWordProbability p ρ w) (w : Word X) :
    binaryKrausProbability (BinaryTestReduction.model r m) w =
      nativeWordProbability (BinaryTestReduction.nativeMenu m p) ρ w := by
  rw [BinaryTestReduction.probability, BinaryTestReduction.native_probability]
  cases hword : WordReduction.translate (BinaryTestReduction.outcomeStep m) w
  · rfl
  · exact h _

end NativeAnalysis
end AlbertSequential
