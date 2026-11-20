/- SPDX-License-Identifier: Apache-2.0 -/
module
public import GeneralEJAFrameTransport
public import JordanPeirceFusion
public import JordanIdeals

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (P : UnitalJordanProduct E)

/-- In a simple finite EJA every pair of distinct primitive frame members has
a nonzero connecting Peirce space. -/
theorem frameOffDiagonal_ne_bot_of_simple {n : ℕ} (c : Fin n → E)
    (hc : ∀ r, P.IsPrimitive (c r)) (hor : ∀ r s, r ≠ s → P.product (c r) (c s) = 0)
    (hunit : ∑ r, c r = P.unit)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (hsimple : P.IsSimpleJordan) (i j : Fin n) (hij : i ≠ j) :
    P.frameJointSpace c (frameOffDiagonalPattern i j) ≠ ⊥ := by
  classical
  let hfr := P.formallyReal_of_associative_inner hinner
  let W (r s : Fin n) := P.frameJointSpace c (frameOffDiagonalPattern r s)
  let R (r s : Fin n) : Prop := r = s ∨ W r s ≠ ⊥
  have hRswap {r s : Fin n} (h : R r s) : R s r := by
    change r = s ∨ W r s ≠ ⊥ at h
    change s = r ∨ W s r ≠ ⊥
    have hW : W s r = W r s := congrArg (P.frameJointSpace c) (frameOffDiagonalPattern_comm s r)
    rw [hW, eq_comm]
    exact h
  have hRtrans {r s t : Fin n} (hrs : R r s) (hst : R s t) : R r t := by
    change r = s ∨ W r s ≠ ⊥ at hrs
    change s = t ∨ W s t ≠ ⊥ at hst
    by_cases heq : r = t
    · exact Or.inl heq
    by_cases hrs' : r = s
    · subst s
      exact hst
    by_cases hst' : s = t
    · subst t
      exact hrs
    obtain ⟨x, hx, hx0⟩ := (W r s).ne_bot_iff.mp (hrs.resolve_left hrs')
    obtain ⟨y, hy, hy0⟩ := (W s t).ne_bot_iff.mp (hst.resolve_left hst')
    have hz : P.product x y ∈ W r t :=
      P.frameOffDiagonal_product_mem_of_shared c (fun u => (hc u).1) hunit hrs' heq hst' hx hy
    have hτ := P.canonicalTraceOfFormallyReal_square_positive hfr x hx0
    have hz0 : P.product x y ≠ 0 := by
      intro hzero
      have ht := P.frameOffDiagonal_product_twice_of_shared hfr c hc hor hunit hrs' heq hst' hx hy
      rw [hzero, map_zero] at ht
      exact (smul_ne_zero (ne_of_gt (div_pos hτ (by norm_num))) hy0) ht.symm
    exact Or.inr ((W r t).ne_bot_iff.mpr ⟨P.product x y, hz, hz0⟩)
  let a (r : Fin n) : ℝ := if R i r then 1 else 0
  let q := ∑ r, a r • c r
  have ha (r : Fin n) : a r ^ 2 = a r := by
    by_cases hr : R i r <;> simp [a, hr]
  have hq : P.product q q = q := by
    change P.product (∑ r, a r • c r) (∑ r, a r • c r) = _
    rw [P.square_of_orthogonal_expansion c a (fun r => (hc r).1) hor]
    simp only [ha, q]
  have hdiag (r : Fin n) : P.product q (c r) = a r • c r := by
    calc
      _ = ∑ s, a s • P.product (c s) (c r) := by
        simp only [q, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
      _ = a r • P.product (c r) (c r) :=
        Finset.sum_eq_single r (fun s _ hsr => by rw [hor s r hsr, smul_zero])
          (fun h => (h (Finset.mem_univ r)).elim)
      _ = _ := by rw [(hc r).1]
  have hoff {r s : Fin n} (hrs : r ≠ s) {x : E} (hx : x ∈ W r s) :
      P.product q x = ((a r + a s) / 2) • x := by
    have hpat (u : Fin n) : a u * frameOffDiagonalPattern r s u =
        (if u = r then a u / 2 else 0) + (if u = s then a u / 2 else 0) := by
      by_cases hr : u = r
      · subst u
        simp [frameOffDiagonalPattern, hrs, div_eq_mul_inv]
      · by_cases hs : u = s
        · subst u
          simp [frameOffDiagonalPattern, hr, div_eq_mul_inv]
        · simp [frameOffDiagonalPattern, hr, hs]
    have hsum : ∑ u, a u * frameOffDiagonalPattern r s u = (a r + a s) / 2 := by
      simp only [hpat, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      ring
    calc
      _ = ∑ u, a u • P.product (c u) x := by
        simp only [q, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
      _ = (∑ u, a u * frameOffDiagonalPattern r s u) • x := by
        rw [Finset.sum_smul]
        apply Finset.sum_congr rfl
        intro u _
        rw [(P.mem_frameJointSpace c _).mp hx u, smul_smul]
      _ = _ := by rw [hsum]
  let T : E →ₗ[ℝ] E := (P.product q).comp (P.product q) - P.product q
  have hdiagKer (r : Fin n) : Submodule.span ℝ {c r} ≤ T.ker := by
    apply Submodule.span_le.mpr
    rintro _ rfl
    apply LinearMap.mem_ker.mpr
    change P.product q (P.product q (c r)) - P.product q (c r) = 0
    have h : P.product q (P.product q (c r)) = a r • c r := by
      rw [hdiag, map_smul, hdiag, smul_smul, ← pow_two, ha]
    rw [h, hdiag, sub_self]
  have hoffKer (rs : {rs : Fin n × Fin n // rs.1 < rs.2}) : W rs.val.1 rs.val.2 ≤ T.ker := by
    intro x hx
    apply LinearMap.mem_ker.mpr
    change P.product q (P.product q x) - P.product q x = 0
    by_cases hx0 : x = 0
    · simp [hx0]
    have hrel : R rs.val.1 rs.val.2 := Or.inr ((W rs.val.1 rs.val.2).ne_bot_iff.mpr ⟨x, hx, hx0⟩)
    have hiff : R i rs.val.1 ↔ R i rs.val.2 :=
      ⟨fun h => hRtrans h hrel, fun h => hRtrans h (hRswap hrel)⟩
    have heq : a rs.val.1 = a rs.val.2 := by simp only [a, hiff]
    have hL : P.product q x = a rs.val.1 • x := by
      rw [hoff (ne_of_lt rs.property) hx, ← heq]
      congr 1
      ring
    rw [hL, map_smul, hL, smul_smul, ← pow_two, ha, sub_self]
  have hproj (x : E) : P.product q (P.product q x) = P.product q x := by
    have htop : ⊤ ≤ T.ker := by
      rw [← P.framePeirce_spanning c hc hor hunit hinner]
      exact sup_le (iSup_le hdiagKer) (iSup_le hoffKer)
    exact sub_eq_zero.mp (LinearMap.mem_ker.mp (htop (show x ∈ (⊤ : Submodule ℝ E) from trivial)))
  have hideal : P.IsJordanIdeal (P.peirceOne q) := by
    intro y hy x
    rw [P.mem_peirceOne] at hy ⊢
    have hx0 : P.product q (x - P.product q x) = 0 := by rw [map_sub, hproj, sub_self]
    have hzero := P.peirceOne_zero_product q y (x - P.product q x) hq hy hx0
    rw [map_sub, sub_eq_zero] at hzero
    rw [P.commutative x y, P.peirceOne_commute q y x hq hy]
    exact hzero.symm
  have hi : c i ∈ P.peirceOne q := by
    rw [P.mem_peirceOne, hdiag]
    simp [a, R]
  rcases hsimple.2 _ hideal with hbot | htop
  · rw [hbot, Submodule.mem_bot] at hi
    exact ((hc i).2.1 hi).elim
  · have hj : c j ∈ P.peirceOne q := by rw [htop]; trivial
    by_contra hbot
    have hn : ¬ R i j := fun h => (h.resolve_left hij) hbot
    rw [P.mem_peirceOne, hdiag, show a j = 0 by simp [a, hn], zero_smul] at hj
    exact (hc j).2.1 hj.symm

end AlbertSequential.UnitalJordanProduct
