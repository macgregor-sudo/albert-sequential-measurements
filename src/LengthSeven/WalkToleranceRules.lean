/- SPDX-License-Identifier: Apache-2.0 -/
module

public import LengthSeven.WalkTolerance

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace AlbertSequential.LengthSeven
namespace Within

theorem transport {d C D a b x y : ℝ} (h : Within d C a b) (hC : D = C)
    (ha : x = a) (hb : y = b) : Within d D x y := by rwa [hC, ha, hb]

end Within
namespace WalkForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {W : WalkForm V}
  {τ : TraceData} {S : Set (Word Letter)} {f : Word Letter → ℝ} {ε : ℝ}

def r1Cost (τ : TraceData) (q v : Letter) : ℝ := 1 + |τ.o q v|

def r2Cost (τ : TraceData) (q s m : Letter) : ℝ :=
  r1Cost τ q m + (1 + |τ.c2 false q s m|) + (1 + |τ.c2 true q s m|)

def p3Cost (τ : TraceData) (x y z : Letter) : ℝ :=
  (1 + |τ.c3 false false x y z|) + (1 + |τ.c3 false true x y z|) +
  (1 + |τ.c3 true false x y z|) + (1 + |τ.c3 true true x y z|) +
  r1Cost τ 0 z + r2Cost τ 0 y z + r2Cost τ 0 x z

def r3Cost (τ : TraceData) : ℝ := (p3Cost τ 1 2 3 + p3Cost τ 2 3 1 + p3Cost τ 3 2 1) / 2

/-- Quantitative R1, with its literal purity constant and its original forcing words. -/
theorem r1_within (h : W.Approximates S f ε) (hT : TableValues τ f)
    (hε : 0 ≤ ε) (t : Word Letter) (q v : Letter) (hS : Covers S (r1Words t q v))
    (r : Word Letter) (a : V) (ha : W.normSq a ≤ 1) :
    Within (Real.sqrt ε) (r1Cost τ q v)
      (W.form (W.vec (t ++ [(q, true), (v, true), (q, true)] ++ r)) a)
      (τ.o q v * W.form (W.vec (t ++ [(q, true)] ++ r)) a) := by
  have hf : f (t ++ [((q : Letter), true)] ++ [(v, true)] ++ purityMirror [(v, true)] ++ [(q, true)]) -
      2 * τ.o q v * f (t ++ [(q, true)] ++ [(v, true)]) +
      τ.o q v ^ 2 * f (t ++ [(q, true)]) = 0 := by
    have e₁ : t ++ [(q, true)] ++ [(v, true)] ++ purityMirror [(v, true)] ++ [(q, true)] =
        t ++ [(q, true), (v, true), (q, true)] := by simp [purityMirror]
    have e₂ : t ++ [(q, true)] ++ [(v, true)] = t ++ [(q, true), (v, true)] := by simp
    rw [e₁, e₂, hT.long1, hT.mid1]
    ring
  simpa [purityMirror, r1Cost] using
    W.purity_pair_within h hT hε t (q, true) [(v, true)] (τ.o q v) hS hf r a ha

/-- Quantitative R2, from the three defects in the expansion of the two crossed products. -/
theorem r2_within (h : W.Approximates S f ε) (hT : TableValues τ f)
    (hε : 0 ≤ ε) (t : Word Letter) (q s m : Letter) (hS : Covers S (r2Words t q s m))
    (r : Word Letter) (a : V) (ha : W.normSq a ≤ 1) :
    Within (Real.sqrt ε) (r2Cost τ q s m)
      (W.form (W.vec (t ++ [(q, true), (s, true), (m, true), (q, true)] ++ r) +
        W.vec (t ++ [(q, true), (m, true), (s, true), (q, true)] ++ r)) a)
      ((2 * τ.R q s m) * W.form (W.vec (t ++ [(q, true)] ++ r)) a) := by
  have h₁ := r1_within h hT hε t q m hS.left.left r a ha
  have h₂ (b : Bool) (hc : Covers S (purityWords t (q, true) [(s, b), (m, true)])) :
      Within (Real.sqrt ε) (1 + |τ.c2 b q s m|)
        (W.form (W.vec (t ++ [(q, true), (s, b), (m, true), (s, b), (q, true)] ++ r)) a)
        (τ.c2 b q s m * W.form (W.vec (t ++ [(q, true)] ++ r)) a) := by
    have hp := W.purity_pair_within h hT hε t (q, true) [(s, b), (m, true)] (τ.c2 b q s m) hc
      (by
        have e : t ++ [(q, true)] ++ [(s, b), (m, true)] ++ purityMirror [(s, b), (m, true)] ++
            [(q, true)] = t ++ [(q, true), (s, b), (m, true), (s, b), (q, true)] := by simp [purityMirror]
        rw [e, show t ++ [(q, true)] ++ [(s, b), (m, true)] =
          t ++ [(q, true), (s, b), (m, true)] by simp, hT.long2, hT.mid2]
        ring) r a ha
    simpa [purityMirror] using hp
  have h₀ := (h₁.sub (h₂ false hS.left.right)).add (h₂ true hS.right)
  have he :
      W.form (W.vec (t ++ [(q, true), (s, true), (m, true), (q, true)] ++ r) +
        W.vec (t ++ [(q, true), (m, true), (s, true), (q, true)] ++ r)) a =
      W.form (W.vec (t ++ [(q, true), (m, true), (q, true)] ++ r)) a -
        W.form (W.vec (t ++ [(q, true), (s, false), (m, true), (s, false), (q, true)] ++ r)) a +
        W.form (W.vec (t ++ [(q, true), (s, true), (m, true), (s, true), (q, true)] ++ r)) a := by
    have he := congrArg (fun v => W.form (W.seqL r v) a) (W.r2_identity q s m (W.vec (t ++ [(q, true)])))
    simpa only [W.vec_split, map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply] using he
  have ht : τ.o q m - τ.c2 false q s m + τ.c2 true q s m = 2 * τ.R q s m := by
    simp [TraceData.c2, TraceData.noConst]
    ring
  rw [he, ← ht, add_mul, sub_mul]
  exact h₀

/-- Quantitative P3, using the actual four length-seven palindromes before deleting yes A. -/
theorem p3_within (h : W.Approximates S f ε) (hT : TableValues τ f)
    (hε : 0 ≤ ε) (x y z : Letter) (ho : IsOrderingBCD x y z)
    (hS : Covers S (p3Words x y z)) (r : Word Letter) (a : V) (ha : W.normSq a ≤ 1) :
    Within (Real.sqrt ε) (p3Cost τ x y z)
      (W.form (W.piC x y z r + W.piC x z y r) a)
      (2 * (τ.om y + τ.om z) * W.form (W.vec r) a) := by
  unfold p3Words p3PurityWords at hS
  have hpur (b c : Bool)
      (hc : Covers S (purityWords [] (0, true) [(x, b), (y, c), (z, true)])) :
      Within (Real.sqrt ε) (1 + |τ.c3 b c x y z|)
        (W.form (W.vec ([(x, b), (y, c), (z, true), (y, c), (x, b), (0, true)] ++ r)) a)
        (τ.c3 b c x y z * W.form (W.vec r) a) := by
    have hf : f ([] ++ [(0, true)] ++ [(x, b), (y, c), (z, true)] ++
        purityMirror [(x, b), (y, c), (z, true)] ++ [(0, true)]) -
        2 * τ.c3 b c x y z * f ([] ++ [(0, true)] ++ [(x, b), (y, c), (z, true)]) +
        (τ.c3 b c x y z) ^ 2 * f ([] ++ [(0, true)]) = 0 := by
      have e : ([] : Word Letter) ++ [(0, true)] ++ [(x, b), (y, c), (z, true)] ++
          purityMirror [(x, b), (y, c), (z, true)] ++ [(0, true)] =
          [] ++ [(0, true), (x, b), (y, c), (z, true), (y, c), (x, b), (0, true)] := by simp [purityMirror]
      rw [e, show ([] : Word Letter) ++ [(0, true)] ++ [(x, b), (y, c), (z, true)] =
        [] ++ [(0, true), (x, b), (y, c), (z, true)] by rfl, hT.long3 [] x y z b c ho, hT.mid3 [] x y z b c ho]
      ring
    simpa [purityMirror] using W.purity_pair_within h hT hε [] (0, true) _ _ hc hf r a ha
  have bFF := hpur false false hS.left.left.left.left.left.left
  have bFT := hpur false true hS.left.left.left.left.left.right
  have bTF := hpur true false hS.left.left.left.left.right
  have bTT := hpur true true hS.left.left.left.right
  have b1 := r1_within h hT hε [] 0 z hS.left.left.right r a ha
  have b2y := r2_within h hT hε [] 0 y z hS.left.right r a ha
  have b2x := r2_within h hT hε [] 0 x z hS.right r a ha
  have key := congrArg (fun v => W.form (W.seqL r v) a) (W.p3_identity x y z W.ξ)
  have key' := τ.c3_signed_sum x y z
  simp only [TraceData.p3Const, TraceData.dpair] at key'
  have b := ((((((bFF.sub bFT).sub bTF).add bTT).sub b1).add b2y).add b2x)
  refine b.transport rfl ?_ ?_
  · have hseq (w : Word Letter) : W.seqL r (W.seqL w W.ξ) = W.vec (w ++ r) :=
      (W.vec_append w r).symm
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply, hseq,
      List.cons_append, List.nil_append] at key
    simp only [piC, List.nil_append, List.cons_append, vec_cons_yesA, map_add, LinearMap.add_apply]
    linear_combination -key
  · simp only [List.nil_append, List.cons_append, vec_cons_yesA]
    linear_combination (W.form (W.vec r) a) * (-key')

/-- Solve the three pair equations for the middle-letter defect. -/
theorem r3_within (h : W.Approximates S f ε) (hT : TableValues τ f)
    (hε : 0 ≤ ε) (hB : Covers S (p3Words 1 2 3))
    (hC : Covers S (p3Words 2 3 1)) (hD : Covers S (p3Words 3 2 1))
    (x y z : Letter) (ho : IsOrderingBCD x y z) (r : Word Letter) (a : V)
    (ha : W.normSq a ≤ 1) :
    Within (Real.sqrt ε) (r3Cost τ)
      (W.form (W.piC x y z r) a) ((2 * τ.om y) * W.form (W.vec r) a) := by
  have hc (i j k : Letter) (hh : IsOrderingBCD i j k) :
      W.piC i j k r = W.piMid j r := W.piC_eq_piMid i j k hh r
  have b := p3_within h hT hε 1 2 3 (by decide) hB r a ha
  have c := p3_within h hT hε 2 3 1 (by decide) hC r a ha
  have d := p3_within h hT hε 3 2 1 (by decide) hD r a ha
  rw [hc 1 2 3 (by decide), hc 1 3 2 (by decide)] at b
  rw [hc 2 3 1 (by decide), hc 2 1 3 (by decide)] at c
  rw [hc 3 1 2 (by decide), hc 3 2 1 (by decide)] at d
  rw [hc x y z ho]
  have finish (u : Letter) (hu : u = 1 ∨ u = 2 ∨ u = 3) :
      Within (Real.sqrt ε) (r3Cost τ)
        (W.form (W.piMid u r) a) (2 * τ.om u * W.form (W.vec r) a) := by
    rcases hu with rfl | rfl | rfl
    · have h := ((c.add d).sub b).scale (1 / 2)
      refine h.transport ?_ ?_ ?_ <;> simp [r3Cost] <;> ring
    · have h := ((d.add b).sub c).scale (1 / 2)
      refine h.transport ?_ ?_ ?_ <;> simp [r3Cost] <;> ring
    · have h := ((b.add c).sub d).scale (1 / 2)
      refine h.transport ?_ ?_ ?_ <;> simp [r3Cost] <;> ring
  apply finish
  fin_cases y
  · exact (ho.2.1 rfl).elim
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)

/-- Lemma D's error is half the sum of the three probability errors. -/
theorem delete_within (h : W.Approximates S f ε) (hT : TableValues τ f)
    (u : List Letter) (a n : Letter) (r : List Letter) (hS : Covers S (lemmaDWords u a n r)) :
    Within ε (3 / 2) (W.form (W.pathVec (u ++ a :: n :: r)) (W.pathVec (u ++ n :: r)))
      (τ.R (u.getLastD 0) a n * τ.chainProd (0 :: u) * τ.chainProd (n :: r)) := by
  have hpol := W.lemmaD_polar u a n r
  have b1 : Within ε 1 (W.normSq (W.pathVec (u ++ a :: n :: r))) (f (yesWord (u ++ a :: n :: r))) := by
    simpa only [Within, pathVec, one_mul] using h.on hT _ (hS _ (by simp [lemmaDWords]))
  have b2 : Within ε 1 (W.normSq (W.pathVec (u ++ n :: r))) (f (yesWord (u ++ n :: r))) := by
    simpa only [Within, pathVec, one_mul] using h.on hT _ (hS _ (by simp [lemmaDWords]))
  have b3 : Within ε 1 (W.normSq (W.vec (yesWord u ++ (a, false) :: yesWord (n :: r))))
      (f (yesWord u ++ (a, false) :: yesWord (n :: r))) := by
    simpa only [Within, one_mul] using h.on hT _ (hS _ (by simp [lemmaDWords]))
  have b := ((b1.add b2).sub b3).scale (1 / 2)
  refine b.transport ?_ ?_ ?_
  · norm_num
  · linear_combination hpol / 2
  · rw [hT.chain, hT.chain, hT.oneNo, τ.chainProd_split, τ.chainProd_split, TraceData.chainProd_cons_cons]
    simp only [TraceData.noConst]
    ring

end WalkForm
end AlbertSequential.LengthSeven
