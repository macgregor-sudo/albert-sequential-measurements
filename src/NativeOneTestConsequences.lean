/- SPDX-License-Identifier: Apache-2.0 -/
module

public import BlockB.ElevenSupport
public import CyclicHilbertModel
public import AcceptedRootAtomAdapter
public import NativeAutomorphisms

/-! One input test has persistent answers, and one fixed first yes can be unobserved. -/
@[expose] public section
noncomputable section

namespace AlbertSequential.NativeAnalysis

theorem native_same_test_branchState {I : Type*} (p : I → Albert)
    (hp : ∀ i, jordanMul (p i) (p i) = p i) (i : I) (ρ : Albert) (b : Bool) (bs : List Bool) :
    nativeBranchState p ρ ((i, b) :: bs.map (fun t => (i, t))) =
      if bs.all (fun t => t == b) then quadraticMap (nativeOutcome p (i, b)) ρ else 0 := by
  let X := quadraticMap (nativeOutcome p (i, b)) ρ
  change nativeBranchState p X (bs.map (fun t => (i, t))) = if bs.all (fun t => t == b) then X else 0
  have hfix : quadraticMap (nativeOutcome p (i, b)) X = X :=
    quadraticMap_idempotent_comp _ _ (nativeOutcome_idempotent p hp _)
  induction bs with
  | nil => rfl
  | cons a bs ih =>
    by_cases h : a = b
    · subst a
      rw [List.map_cons, nativeBranchState_cons, hfix, ih]
      simp
    · rw [List.map_cons, nativeBranchState_cons,
        show quadraticMap (nativeOutcome p (i, a)) X = 0 from
          BlockB.quadraticMap_nativeOutcome_opposite p hp i a b h ρ, nativeBranchState_zero]
      simp [h]

theorem native_same_test_postStates (p ρ : Albert) (hp : IsAtom p) :
    quadraticMap p ρ = tracePairing p ρ • p ∧
      jordanMul p (quadraticMap (albertUnit - p) ρ) = 0 := by
  refine ⟨quadraticMap_atom _ _ hp, ?_⟩
  have h := native_idempotent_quadratic_mem_one (albertUnit - p) ρ
    (complementary_idempotent p hp.1)
  rw [jordanMul_sub_left, jordanMul_albertUnit_left] at h
  exact sub_eq_self.mp h

/-- A two-state chain with identity transition and deterministic emission of its bit. -/
def persistentAnswerProbability (initial : Bool → ℝ) : List Bool → ℝ
  | [] => initial true + initial false
  | b :: bs => if bs.all (fun t => t == b) then initial b else 0

theorem native_same_test_two_state_model (p ρ : Albert) (hp : IsAtom p) (bs : List Bool) :
    nativeWordProbability (fun _ : Unit => p) ρ (bs.map (fun b => ((), b))) =
      persistentAnswerProbability
        (fun b => tracePairing ρ (nativeOutcome (fun _ : Unit => p) ((), b))) bs := by
  let f : Unit → Albert := fun _ => p
  cases bs with
  | nil =>
    change albertTrace ρ = tracePairing ρ p + tracePairing ρ (albertUnit - p)
    have h : p + (albertUnit - p) = albertUnit := by abel
    rw [← tracePairing_add_right, h]
    unfold tracePairing
    rw [jordanMul_albertUnit_right]
  | cons b bs =>
    change albertTrace (nativeBranchState f ρ (((), b) :: bs.map (fun t => ((), t)))) = _
    rw [native_same_test_branchState f (fun _ => hp.1)]
    by_cases h : bs.all (fun t => t == b)
    · simp only [persistentAnswerProbability, h, ↓reduceIte]
      rw [albertTrace_quadraticMap, nativeOutcome_idempotent f (fun _ => hp.1), tracePairing_comm]
    · simp [persistentAnswerProbability, h, albertTrace_zero]

/-- Any prescribed first yes has a density and a real projective realization
matching all of the words starting with that yes. -/
theorem native_fixedHead_matches_some_density {I : Type*} (p : I → Albert) (i : I) (hi : IsAtom (p i)) :
    ∃ (ρ : Albert) (M : AlgebraicProjectiveData I ℝ), IsDensity ρ ∧
      ∀ w : Word I,
        (cyclicHilbertModel M).toAlgebraic.probability ((i, true) :: w) =
          nativeWordProbability p ρ ((i, true) :: w) := by
  obtain ⟨g, hg⟩ := atom_to_diagAtom0 (p i) hi
  let ρ := g.linearEquiv.symm (diagAtom 1)
  have hρ : g.linearEquiv ρ = diagAtom 1 := g.linearEquiv.apply_symm_apply _
  have ha : IsAtom ρ := by
    constructor
    · apply g.linearEquiv.injective
      rw [g.preserves_product, hρ, (diagAtom_isAtom 1).1]
    · rw [← g.preserves_trace ρ, hρ]
      exact (diagAtom_isAtom 1).2
  have ht : tracePairing (p i) ρ = 0 := by
    rw [← g.map_tracePairing, hg, hρ]
    unfold tracePairing
    rw [diagAtom_orthogonal (by decide), albertTrace_zero]
  let M : AlgebraicProjectiveData I ℝ :=
    { projection := fun _ => 0
      idempotent := fun _ => mul_zero 0
      selfAdjoint := fun _ => star_zero _
      state := LinearMap.id
      state_unit := rfl
      state_star := fun _ => rfl
      state_positive := fun x => mul_self_nonneg x }
  refine ⟨ρ, M, ⟨⟨ρ, ha.1.symm⟩, ha.2⟩, fun w => ?_⟩
  rw [cyclicHilbertModel_probability]
  have hzero : M.probability ((i, true) :: w) = 0 := by
    unfold AlgebraicProjectiveData.probability
    rw [wordOperator_cons M.projection M.selfAdjoint]
    simp [M, algebraicOutcome]
  rw [hzero]
  change 0 = albertTrace (nativeBranchState p ρ ((i, true) :: w))
  rw [nativeBranchState_cons]
  change 0 = albertTrace (nativeBranchState p (quadraticMap (p i) ρ) w)
  rw [quadraticMap_atom _ _ hi, ht, zero_smul, nativeBranchState_zero, albertTrace_zero]

end AlbertSequential.NativeAnalysis
