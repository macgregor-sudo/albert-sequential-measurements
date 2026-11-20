/- SPDX-License-Identifier: Apache-2.0 -/
module

public import LengthSeven.WalkToleranceRules
public import LengthSeven.LemmaA.Main

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace AlbertSequential.LengthSeven.LemmaA

open WalkForm

/-- The data used in the quantitative replay of the finite Lemma A reduction. -/
structure ShortTableInput {V : Type*} [AddCommGroup V] [Module ℝ V]
    (W : WalkForm V) (τ : TraceData) (ε : ℝ) : Prop where
  nonneg : 0 ≤ ε
  le_one : ε ≤ 1
  table : ∃ f, TableValues τ f ∧ W.Approximates wordsE3 f ε

namespace ShortTableInput

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {W : WalkForm V}
  {τ : TraceData} {ε : ℝ}

theorem le_sqrt (h : ShortTableInput W τ ε) : ε ≤ Real.sqrt ε := by
  have h₀ := Real.sqrt_nonneg ε
  have hs := Real.sq_sqrt h.nonneg
  have h₁ : Real.sqrt ε ≤ 1 := by nlinarith only [h₀, hs, h.le_one]
  nlinarith only [mul_nonneg h₀ (sub_nonneg.mpr h₁), hs]

private theorem ξ_le : W.normSq W.ξ ≤ 1 := by rw [normSq, W.unit]

variable {x y z : Letter}

theorem stepR1Within {t : List PL} {q v : PL} (h : ShortTableInput W τ ε)
    (hc : PatInst.Covered wordsE3 x y z (.r1 t q v))
    (e w1 w2 : List PL) (h1 : equivW (t ++ q :: v :: q :: e) w1 = true)
    (h2 : equivW (t ++ q :: e) w2 = true) :
    Within (Real.sqrt ε) (r1Cost τ (PL.ev x y z q) (PL.ev x y z v))
      (W.L (w1.map (PL.ev x y z)))
      (τ.o (PL.ev x y z q) (PL.ev x y z v) * W.L (w2.map (PL.ev x y z))) := by
  obtain ⟨f, hT, hf⟩ := h.table
  rw [← L_conv W _ rfl _ _ h1, ← L_conv W _ rfl _ _ h2]
  simpa [yesWord, ← vec_yes, ← form_pathVec_xi] using r1_within hf hT h.nonneg
    (yesWord (t.map (PL.ev x y z))) (PL.ev x y z q) (PL.ev x y z v)
    (by exact hc) (yesWord (e.map (PL.ev x y z))) W.ξ ξ_le

def stepR2Cost (τ : TraceData) (q s m : Letter) : ℝ := max (r2Cost τ q s m) (r2Cost τ q m s)

theorem stepR2Within {t : List PL} {q s m : PL} (h : ShortTableInput W τ ε)
    (hc : PatInst.Covered wordsE3 x y z (.r2 t q s m))
    (e w1 w2 w3 : List PL) (h1 : equivW (t ++ q :: s :: m :: q :: e) w1 = true)
    (h2 : equivW (t ++ q :: m :: s :: q :: e) w2 = true) (h3 : equivW (t ++ q :: e) w3 = true) :
    Within (Real.sqrt ε) (stepR2Cost τ (PL.ev x y z q) (PL.ev x y z s) (PL.ev x y z m))
      (W.L (w1.map (PL.ev x y z)) + W.L (w2.map (PL.ev x y z)))
      (2 * τ.R (PL.ev x y z q) (PL.ev x y z s) (PL.ev x y z m) * W.L (w3.map (PL.ev x y z))) := by
  obtain ⟨f, hT, hf⟩ := h.table
  rw [← L_conv W _ rfl _ _ h1, ← L_conv W _ rfl _ _ h2, ← L_conv W _ rfl _ _ h3]
  let σ := PL.ev x y z
  cases hc with
  | inl hs =>
    have b := r2_within hf hT h.nonneg (yesWord (t.map σ)) (σ q) (σ s) (σ m) hs
      (yesWord (e.map σ)) W.ξ ξ_le
    have b' := b.widen (Real.sqrt_nonneg ε) (le_max_left _ (r2Cost τ (σ q) (σ m) (σ s)))
    simpa [σ, stepR2Cost, yesWord, ← vec_yes, ← form_pathVec_xi] using b'
  | inr hs =>
    have b := r2_within hf hT h.nonneg (yesWord (t.map σ)) (σ q) (σ m) (σ s) hs
      (yesWord (e.map σ)) W.ξ ξ_le
    have b' := b.widen (Real.sqrt_nonneg ε) (le_max_right (r2Cost τ (σ q) (σ s) (σ m)) _)
    rw [τ.R_symm23, add_comm (W.vec _)] at b'
    simpa [σ, stepR2Cost, yesWord, ← vec_yes, ← form_pathVec_xi] using b'

theorem stepL2Within {a b c : PL} (h : ShortTableInput W τ ε)
    (ho : IsOrderingBCD (PL.ev x y z a) (PL.ev x y z b) (PL.ev x y z c))
    (e w1 w2 w3 : List PL) (h1 : equivW (a :: b :: c :: .A :: e) w1 = true)
    (h2 : equivW (c :: b :: a :: .A :: e) w2 = true) (h3 : equivW e w3 = true) :
    Within (Real.sqrt ε) (r3Cost τ)
      (W.L (w1.map (PL.ev x y z)) + W.L (w2.map (PL.ev x y z)))
      (2 * τ.om (PL.ev x y z b) * W.L (w3.map (PL.ev x y z))) := by
  obtain ⟨f, hT, hf⟩ := h.table
  rw [← L_conv W _ rfl _ _ h1, ← L_conv W _ rfl _ _ h2, ← L_conv W _ rfl _ _ h3]
  simpa [yesWord, piC, ← vec_yes, ← form_pathVec_xi] using r3_within hf hT h.nonneg
    p3_e3.1 p3_e3.2.1 p3_e3.2.2 _ _ _ ho (yesWord (e.map (PL.ev x y z))) W.ξ ξ_le

theorem stepYWithin {u : List PL} (h : ShortTableInput W τ ε)
    (hc : PatInst.Covered wordsE3 x y z (.chain u))
    (w : List PL) (hw : equivW (u ++ u.reverse) w = true) :
    Within (Real.sqrt ε) 1 (W.L (w.map (PL.ev x y z)))
      (τ.chainProd (0 :: u.map (PL.ev x y z))) := by
  obtain ⟨f, hT, hf⟩ := h.table
  rw [← L_conv W _ rfl _ _ hw, List.map_append, List.map_reverse, ← W.form_pathVec]
  have b := hf.on hT (yesWord (u.map (PL.ev x y z))) (hc _ (by simp [PatInst.toRule, RuleInstance.forcingWords]))
  rw [hT.chain] at b
  unfold Within
  rw [one_mul]
  exact b.trans h.le_sqrt

theorem stepDWithin {u : List PL} {a n : PL} {r : List PL} (h : ShortTableInput W τ ε)
    (hc : PatInst.Covered wordsE3 x y z (.delete u a n r))
    (w : List PL) (hw : equivW ((u ++ a :: n :: r) ++ (u ++ n :: r).reverse) w = true) :
    Within (Real.sqrt ε) (3 / 2) (W.L (w.map (PL.ev x y z)))
      (τ.R ((u.map (PL.ev x y z)).getLastD 0) (PL.ev x y z a) (PL.ev x y z n) *
        τ.chainProd (0 :: u.map (PL.ev x y z)) * τ.chainProd (PL.ev x y z n :: r.map (PL.ev x y z))) := by
  obtain ⟨f, hT, hf⟩ := h.table
  rw [← L_conv W _ rfl _ _ hw, List.map_append, List.map_append, List.map_reverse,
    List.map_append, ← W.form_pathVec]
  have b := delete_within hf hT (u.map (PL.ev x y z)) (PL.ev x y z a) (PL.ev x y z n) (r.map (PL.ev x y z)) hc
  exact b.trans (mul_le_mul_of_nonneg_left h.le_sqrt (by norm_num))

end ShortTableInput
end AlbertSequential.LengthSeven.LemmaA
