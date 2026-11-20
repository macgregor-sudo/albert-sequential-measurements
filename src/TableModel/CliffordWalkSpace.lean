/- SPDX-License-Identifier: Apache-2.0 -/
module

public import TableModel.CliffordComparison
public import TableModel.CliffordNativeGram
public import TableModel.CliffordVolumeCoordinates
public import TableModel.WalkUpsilon

@[expose] public section
noncomputable section

namespace LemmaB

/-- The basis consisting of the eight words printed for the comparison Clifford algebra. -/
def printedCliffordBasis (p : Params ℝ) : Module.Basis (Fin 8) ℝ (ComparisonClifford p) :=
  (Pi.basisFun ℝ (Fin 8)).map (cliffordCoordinateEquiv p).symm

theorem printedCliffordBasis_apply (p : Params ℝ) (i : Fin 8) :
    printedCliffordBasis p i = cliffordBasisWords p i := by
  apply (cliffordCoordinateEquiv p).injective
  rw [printedCliffordBasis, Module.Basis.map_apply, LinearEquiv.apply_symm_apply, Pi.basisFun_apply,
    cliffordCoordinateEquiv_apply, cliffordCoordinates_basisWords]

/-- The second ghost pairing, in the cyclic order of the printed bivectors. -/
theorem cliffordPairing_ghostMate (p : Params ℝ) (a : ComparisonClifford p) (i : Fin 3) :
    cliffordPairing p a (-(cliffordGenerator p i * cliffordGhost p)) =
      p.Dhat * cliffordCoordinates p a (![4, 5, 6] i) := by
  have h (v : C8 ℝ) (i : Fin 3) : W p v (-epsilonAction p i gee) = p.Dhat * v (![4, 5, 6] i) := by
    fin_cases i
    · change W p v (-epsilonAction p 0 gee) = p.Dhat * v 4
      rw [epsilonAction_zero, W_g1]
    · change W p v (-epsilonAction p 1 gee) = p.Dhat * v 5
      rw [epsilonAction_one, W_g2]
    · change W p v (-epsilonAction p 2 gee) = p.Dhat * v 6
      rw [epsilonAction_two, W_g3]
  rw [cliffordPairing_eq_W, map_neg, cliffordCoordinates_generator_mul, cliffordCoordinates_ghost]
  have he : Pi.single (7 : Fin 8) (1 : ℝ) = (gee : C8 ℝ) := by
    funext j
    fin_cases j <;> simp [gee]
  rw [he]
  exact h (cliffordCoordinates p a) i

theorem cliffordReflection_selfAdjoint (p : Params ℝ) (a b : ComparisonClifford p) :
    cliffordPairing p a (cliffordReflection p b) = cliffordPairing p (cliffordReflection p a) b := by
  rw [cliffordPairing_eq_W, cliffordPairing_eq_W, cliffordCoordinates_reflection,
    cliffordCoordinates_reflection, W_sig]

theorem cliffordReflection_involutive (p : Params ℝ) : Function.Involutive (cliffordReflection p) := by
  intro a
  apply (cliffordCoordinateEquiv p).injective
  simp only [cliffordCoordinateEquiv_apply, cliffordCoordinates_reflection]
  funext j
  fin_cases j <;> simp [sig]

end LemmaB

namespace AlbertSequential.LengthSeven.TableModel

open LemmaB

variable (τ : TraceData)
variable (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)

local notation "p" => comparisonParams τ
local notation "E" => cliffordFrameEquiv p
local notation "W" => comparisonWalkSpace τ hB hC hD

def transportedComparisonProjection (x : Letter) : CliffordFrames p →ₗ[ℝ] CliffordFrames p :=
  (E).symm.toLinearMap.comp (((W).P x).comp (E).toLinearMap)

private theorem transportedComparisonProjection_equiv (x : Letter) (F : CliffordFrames p) :
    E (transportedComparisonProjection τ hB hC hD x F) = (W).P x (E F) :=
  (E).apply_symm_apply _

/-- The non-positive comparison walk space on the actual abstract Clifford frames. -/
def cliffordComparisonWalkSpace : AlgebraicWalkSpace (CliffordFrames p) where
  form := LinearMap.compl₁₂ (W).form (E).toLinearMap (E).toLinearMap
  symm F G := (W).symm (E F) (E G)
  P := transportedComparisonProjection τ hB hC hD
  idem x F := by
    apply (E).injective
    simp only [transportedComparisonProjection_equiv, (W).idem]
  selfAdj x F G := by
    change (W).form (E (transportedComparisonProjection τ hB hC hD x F)) (E G) =
      (W).form (E F) (E (transportedComparisonProjection τ hB hC hD x G))
    rw [transportedComparisonProjection_equiv, transportedComparisonProjection_equiv, (W).selfAdj]
  ξ := (E).symm (W).ξ
  fixA := by
    apply (E).injective
    rw [transportedComparisonProjection_equiv, (E).apply_symm_apply, (W).fixA]
  unit := by
    change (W).form (E ((E).symm (W).ξ)) (E ((E).symm (W).ξ)) = 1
    rw [(E).apply_symm_apply, (W).unit]

local notation "CW" => cliffordComparisonWalkSpace τ hB hC hD

private theorem cliffordProjection_equiv (x : Letter) (F : CliffordFrames p) :
    E ((CW).P x F) = (W).P x (E F) :=
  transportedComparisonProjection_equiv τ hB hC hD x F

private theorem cliffordAnchor_equiv : E (CW).ξ = (W).ξ :=
  (E).apply_symm_apply _

theorem cliffordComparisonWalkSpace_form (F G : CliffordFrames p) :
    (CW).form F G = cliffordComparisonForm p F G := by
  change Q p (E F) (E G) = _
  rw [cliffordFrameEquiv_apply, cliffordFrameEquiv_apply, cliffordComparisonForm_eq_Q]

theorem cliffordComparisonWalkSpace_projection (x : Letter) (F : CliffordFrames p) :
    (CW).P x F = cliffordComparisonProjection p x F := by
  apply (E).injective
  change E (transportedComparisonProjection τ hB hC hD x F) = _
  rw [transportedComparisonProjection_equiv, cliffordFrameEquiv_apply p (cliffordComparisonProjection p x F),
    cliffordCoordinates_projection, ← cliffordFrameEquiv_apply]
  rfl

theorem cliffordComparisonWalkSpace_anchor : (CW).ξ = Pi.single 0 1 := by
  apply (E).injective
  change E ((E).symm (W).ξ) = _
  rw [(E).apply_symm_apply, cliffordFrameEquiv_apply, cliffordCoordinates_anchor]
  rfl

theorem cliffordComparison_R1 (x y : Letter) (hxy : x ≠ y) (F : CliffordFrames p) :
    (CW).P x ((CW).P y ((CW).P x F)) = τ.o x y • (CW).P x F := by
  apply (E).injective
  have har := comparison_R1 τ hB hC hD x y hxy (E F)
  change (W).P x ((W).P y ((W).P x (E F))) = τ.o x y • (W).P x (E F) at har
  simpa only [map_smul, cliffordProjection_equiv] using har

private theorem cliffordWalkSpace_prodL (w : List Letter) (F : CliffordFrames p) :
    E ((CW).prodL w F) = (W).prodL w (E F) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    simp only [AlgebraicWalkSpace.prodL_cons_apply, cliffordProjection_equiv, ih]

private theorem cliffordWalkSpace_path_equiv (w : List Letter) :
    E ((CW).pathVec w) = (W).pathVec w := by
  unfold AlgebraicWalkSpace.pathVec
  rw [cliffordWalkSpace_prodL]
  change (W).prodL w.reverse (E ((E).symm (W).ξ)) = _
  rw [(E).apply_symm_apply]

theorem cliffordComparisonWalkSpace_pathVec (w : List Letter) :
    (CW).pathVec w = cliffordComparisonPath p w := by
  apply (E).injective
  rw [cliffordWalkSpace_path_equiv, comparison_pathVec, cliffordFrameEquiv_apply, cliffordCoordinates_path]

private theorem cliffordComparisonWalkSpace_L (w : List Letter) : (CW).L w = (W).L w := by
  change (W).form (E (CW).ξ) (E ((CW).prodL w (CW).ξ)) = _
  rw [cliffordWalkSpace_prodL]
  change (W).form (E ((E).symm (W).ξ)) ((W).prodL w (E ((E).symm (W).ξ))) = _
  rw [(E).apply_symm_apply]
  rfl

/-- The two scalar values and all three short relations hold on the abstract comparison space. -/
theorem cliffordComparison_hypotheses : AlgebraicWalkHypotheses (CW) τ := by
  have hc := comparison_hypotheses τ hB hC hD
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [cliffordComparisonWalkSpace_L]
    exact hc.singleton x hx
  · intro x y z hxyz
    rw [cliffordComparisonWalkSpace_L]
    exact hc.six x y z hxyz
  · intro t q v hqv ht
    dsimp only
    apply (E).injective
    simpa only [map_smul, cliffordProjection_equiv, cliffordWalkSpace_path_equiv] using hc.r1 t q v hqv ht
  · intro t q v w hqv hvw hqw ht
    dsimp only
    apply (E).injective
    simpa only [map_add, map_smul, cliffordProjection_equiv, cliffordWalkSpace_path_equiv] using hc.r2 t q v w hqv hvw hqw ht
  · intro x y z hxyz
    apply (E).injective
    simpa only [map_add, map_smul, cliffordProjection_equiv, cliffordAnchor_equiv] using hc.r3 x y z hxyz

include hB hC hD in
theorem cliffordComparisonGram_eq_upsilon (u v : List Letter) (hu : u.length ≤ 4) (hv : v.length ≤ 4) :
    cliffordComparisonForm p (cliffordComparisonPath p u) (cliffordComparisonPath p v) =
      MvPolynomial.eval₂ (Int.castRingHom ℝ) (walkTraceCoordinates τ) (walkUpsilon (u ++ v.reverse)) := by
  rw [← cliffordComparisonWalkSpace_pathVec τ hB hC hD u,
    ← cliffordComparisonWalkSpace_pathVec τ hB hC hD v, ← cliffordComparisonWalkSpace_form]
  exact algebraicWalk_gram_eq_upsilon _ _ (cliffordComparison_hypotheses τ hB hC hD) u v hu hv

attribute [local irreducible] fourPointInvariant

/-- The literal comparison walk space of core Lemma 6.7 on the native trace data. -/
def nativeCliffordWalkSpace (q : Fin 4 → Albert) (hq : ∀ i, IsAtom (q i)) (hA : 0 < fourPointInvariant q) :
    AlgebraicWalkSpace (CliffordFrames (nativeCliffordParams q)) :=
  cliffordComparisonWalkSpace (nativeTraceData q)
    (ne_of_gt (overlap_bounds_of_fourPoint_pos q hq hA 0 1 (by decide)).1)
    (ne_of_gt (overlap_bounds_of_fourPoint_pos q hq hA 0 2 (by decide)).1)
    (ne_of_gt (overlap_bounds_of_fourPoint_pos q hq hA 0 3 (by decide)).1)

theorem native_cliffordComparison_hypotheses (q : Fin 4 → Albert) (hq : ∀ i, IsAtom (q i))
    (hA : 0 < fourPointInvariant q) :
    AlgebraicWalkHypotheses (nativeCliffordWalkSpace q hq hA) (nativeTraceData q) :=
  cliffordComparison_hypotheses _ _ _ _

theorem native_cliffordComparisonGram_eq_upsilon (q : Fin 4 → Albert) (hq : ∀ i, IsAtom (q i))
    (hA : 0 < fourPointInvariant q) (u v : List Letter) (hu : u.length ≤ 4) (hv : v.length ≤ 4) :
    cliffordComparisonForm (nativeCliffordParams q) (cliffordComparisonPath (nativeCliffordParams q) u)
        (cliffordComparisonPath (nativeCliffordParams q) v) =
      MvPolynomial.eval₂ (Int.castRingHom ℝ) (walkTraceCoordinates (nativeTraceData q))
        (walkUpsilon (u ++ v.reverse)) :=
  cliffordComparisonGram_eq_upsilon (nativeTraceData q)
    (ne_of_gt (overlap_bounds_of_fourPoint_pos q hq hA 0 1 (by decide)).1)
    (ne_of_gt (overlap_bounds_of_fourPoint_pos q hq hA 0 2 (by decide)).1)
    (ne_of_gt (overlap_bounds_of_fourPoint_pos q hq hA 0 3 (by decide)).1) u v hu hv

theorem native_gram_eq_cliffordComparison_of_gram28Hyp {V : Type*} [AddCommGroup V] [Module ℝ V]
    (W' : WalkForm V) (q : Fin 4 → Albert) (hq : ∀ i, IsAtom (q i)) (hA : 0 < fourPointInvariant q)
    (S : Set (Word Letter)) (h : Gram28Hyp W' (nativeTraceData q) S)
    (hrep : W'.Reproduces S (nativeWordProbability q (q 0)))
    (u v : List Letter) (hu : u.length ≤ 4) (hv : v.length ≤ 4) :
    W'.form (W'.pathVec u) (W'.pathVec v) =
      cliffordComparisonForm (nativeCliffordParams q) (cliffordComparisonPath (nativeCliffordParams q) u)
        (cliffordComparisonPath (nativeCliffordParams q) v) := by
  rw [cliffordComparisonPath_gram]
  exact native_gram_eq_comparison_of_gram28Hyp W' q hq hA S h hrep u v hu hv

end AlbertSequential.LengthSeven.TableModel
