/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CompanionProjectiveRayMaps

@[expose] public section
noncomputable section

namespace AlbertSequential.ProjectiveMetricInvariant

open NativeAnalysis WindowProbability

private theorem diag_sum_smul (p : Fin 3 → Albert) (w : Fin 3 → ℝ) (i : Fin 3) :
    (∑ j, w j • p j).1 i = ∑ j, w j * (p j).1 i := by
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  rfl

private theorem offdiag_sum_smul (p : Fin 3 → Albert) (w : Fin 3 → ℝ) (i : Fin 3) :
    (∑ j, w j • p j).2 i = ∑ j, w j • (p j).2 i := by
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  rfl

theorem cubicNorm_weightedAtoms_eq_zero_iff (p : Fin 3 → AlbertAtomSpace)
    (w : Fin 3 → ℝ) (hw : ∀ j, 0 < w j) :
    albertCubicNorm (∑ j, w j • (p j).val) = 0 ↔
      ∃ q : AlbertAtomSpace, ∀ j, tracePairing (p j).val q.val = 0 := by
  constructor
  · intro hn
    obtain ⟨g, d, hd⟩ := nativeDiagonalization (∑ j, w j • (p j).val)
    have hsum : g.linearEquiv (∑ j, w j • (p j).val) =
        ∑ j, w j • g.linearEquiv (p j).val := by simp [map_sum]
    have hd' (i : Fin 3) : d i = ∑ j, w j * (g.linearEquiv (p j).val).1 i :=
      (congrArg (fun x : Albert => x.1 i) (hd.symm.trans hsum)).trans (diag_sum_smul _ _ _)
    rw [← g.map_cubicNorm, hd, diagonalElement, albertCubicNorm_diag] at hn
    obtain ⟨i, hi⟩ : ∃ i : Fin 3, d i = 0 := by
      rcases mul_eq_zero.mp hn with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact ⟨0, h⟩
        · exact ⟨1, h⟩
      · exact ⟨2, h⟩
    let q : AlbertAtomSpace :=
      ⟨g.symm.linearEquiv (diagAtom i), g.symm.map_isAtom (diagAtom_isAtom i)⟩
    refine ⟨q, fun j => ?_⟩
    have hterm : ∀ k : Fin 3, 0 ≤ w k * (g.linearEquiv (p k).val).1 i :=
      fun k => mul_nonneg (hw k).le (isAtom_diag_nonneg (g.map_isAtom (p k).property) i)
    have hj : w j * (g.linearEquiv (p j).val).1 i ≤ ∑ k, w k * (g.linearEquiv (p k).val).1 i :=
      Finset.single_le_sum (fun k _ => hterm k) (Finset.mem_univ j)
    rw [← hd', hi] at hj
    have hz := (mul_eq_zero.mp (le_antisymm hj (hterm j))).resolve_left (hw j).ne'
    rw [tracePairing_comm, ← g.map_tracePairing,
      show g.linearEquiv q.val = diagAtom i from g.linearEquiv.apply_symm_apply _,
      tracePairing_diagAtom]
    exact hz
  · rintro ⟨q, hq⟩
    obtain ⟨g, hg⟩ := nativeAtomNormalizer_first q.val q.property
    let p' (j : Fin 3) := g.linearEquiv (p j).val
    have hz (j : Fin 3) : (p' j).1 0 = 0 ∧ (p' j).2 0 = 0 ∧ (p' j).2 1 = 0 := by
      have h := hq j
      rw [tracePairing_comm, ← g.map_tracePairing, hg, tracePairing_diagAtom] at h
      exact ⟨h, isAtom_zero_row0 (g.map_isAtom (p j).property) h⟩
    let x := ∑ j, w j • p' j
    have h0 : x.1 0 = 0 := by
      rw [diag_sum_smul]
      simp [(hz _).1]
    have h01 : x.2 0 = 0 := by
      rw [offdiag_sum_smul]
      simp [(hz _).2.1]
    have h02 : x.2 1 = 0 := by
      rw [offdiag_sum_smul]
      simp [(hz _).2.2]
    rw [← g.map_cubicNorm, map_sum]
    simp only [map_smul]
    change albertCubicNorm x = 0
    have hn : octNormSq 0 = 0 := (octNormSq_eq_zero 0).mpr rfl
    simp [albertCubicNorm, h0, h01, h02, hn, octonionMul_zero_left, octDot_zero_right]

theorem CubicRayEquiv.pointMap_quadrangle (g : CubicRayEquiv)
    {p : Fin 4 → AlbertAtomSpace} (hp : p ∈ quadrangleLocus) :
    (fun i => g.pointMap (p i)) ∈ quadrangleLocus := by
  intro t h
  let a (j : Fin 3) := p (t j)
  have hn := (cubicNorm_weightedAtoms_eq_zero_iff (fun j => g.pointMap (a j))
    (fun j => albertTrace (g.linearEquiv (a j).val)) (fun j => g.trace_pos (a j))).mpr h
  simp only [← g.raw_pointMap, ← map_sum] at hn
  have hsource : albertCubicNorm (∑ j, (1 : ℝ) • (a j).val) = 0 := by
    simp only [one_smul]
    rw [g.map_norm] at hn
    exact (mul_eq_zero.mp hn).resolve_left g.scale_pos.ne'
  exact hp t ((cubicNorm_weightedAtoms_eq_zero_iff a _ (fun _ => zero_lt_one)).mp hsource)

private theorem weightedAtom_sum_is_unit_frame (a : Fin 3 → AlbertAtomSpace)
    (w : Fin 3 → ℝ) (hw : ∀ i, 0 < w i) {d : ℝ} (hd : 0 < d)
    (hs : ∑ i, w i • (a i).val = d • albertUnit) :
    ∃ F : NativeJordanFrame, F.atom = fun i => (a i).val := by
  have hself (i : Fin 3) : tracePairing (a i).val (a i).val = 1 := by
    unfold tracePairing
    rw [(a i).property.1, (a i).property.2]
  have hnonneg (i j : Fin 3) : 0 ≤ tracePairing (a i).val (a j).val :=
    tracePairing_positive_nonnegative _ _ ⟨_, (a i).property.1.symm⟩ ⟨_, (a j).property.1.symm⟩
  have hpair (j : Fin 3) : ∑ i, w i * tracePairing (a i).val (a j).val = d := by
    have h := congrArg (fun x : Albert => tracePairing x (a j).val) hs
    change tracePairing (∑ i, w i • (a i).val) (a j).val =
      tracePairing (d • albertUnit) (a j).val at h
    rw [Fin.sum_univ_three] at h ⊢
    simp only [tracePairing_add_left, tracePairing_smul_left,
      tracePairing_comm albertUnit, tracePairing_unit_right, (a j).property.2, mul_one] at h
    exact h
  have hle (i : Fin 3) : w i ≤ d := by
    rw [← hpair i, ← mul_one (w i), ← hself i]
    exact Finset.single_le_sum (fun j _ => mul_nonneg (hw j).le (hnonneg j i)) (Finset.mem_univ i)
  have hsum : w 0 + w 1 + w 2 = d * 3 := by
    have h := congrArg albertTrace hs
    rw [Fin.sum_univ_three] at h
    rw [albertTrace_add, albertTrace_add, albertTrace_smul, albertTrace_smul, albertTrace_smul,
      albertTrace_smul, (a 0).property.2, (a 1).property.2, (a 2).property.2] at h
    norm_num [albertTrace, Fin.sum_univ_three, albertUnit] at h ⊢
    exact h
  have he (i : Fin 3) : w i = d := by
    fin_cases i
    · change w 0 = d
      linarith [hle 0, hle 1, hle 2]
    · change w 1 = d
      linarith [hle 0, hle 1, hle 2]
    · change w 2 = d
      linarith [hle 0, hle 1, hle 2]
  have ho (i j : Fin 3) (hij : i ≠ j) : jordanMul (a i).val (a j).val = 0 := by
    apply (atom_tracePairing_eq_zero_iff _ _ (a i).property (a j).property).mp
    have hz : w i * tracePairing (a i).val (a j).val + w j * tracePairing (a j).val (a j).val ≤
        ∑ k, w k * tracePairing (a k).val (a j).val := by
      let f (k : Fin 3) := w k * tracePairing (a k).val (a j).val
      change f i + f j ≤ ∑ k, f k
      have hs_pair : ∑ k ∈ ({i, j} : Finset (Fin 3)), f k = f i + f j := Finset.sum_pair hij
      rw [← hs_pair]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun k _ _ =>
        mul_nonneg (hw k).le (hnonneg k j))
    rw [hpair j, hself j, he j, mul_one] at hz
    exact (mul_eq_zero.mp (le_antisymm (by linarith) (mul_nonneg (hw i).le (hnonneg i j)))).resolve_left
      (hw i).ne'
  have hu : ∑ i, (a i).val = albertUnit := by
    simp only [he, ← Finset.smul_sum] at hs
    exact (smul_right_inj hd.ne').mp hs
  exact ⟨⟨fun i => (a i).val, fun i => (a i).property, ho, hu⟩, rfl⟩

private def initialTriple : Fin 3 ↪ Fin 4 :=
  ⟨Fin.castSucc, Fin.castSucc_injective _⟩

/-- A projective change of coordinates sends the first three labelled points to the axes. -/
theorem quadrangle_first_three_axes (p : Fin 4 → AlbertAtomSpace) (hp : p ∈ quadrangleLocus) :
    ∃ g : CubicRayEquiv, ∀ i : Fin 3, g.pointMap (p i.castSucc) = quadrangleAxis i := by
  let a (i : Fin 3) := p i.castSucc
  let x : Albert := ∑ i, (a i).val
  have hn : albertCubicNorm x ≠ 0 := by
    intro hz
    have h : albertCubicNorm (∑ i, (1 : ℝ) • (a i).val) = 0 := by simpa [x] using hz
    exact hp initialTriple ((cubicNorm_weightedAtoms_eq_zero_iff a _ (fun _ => zero_lt_one)).mp h)
  obtain ⟨g, d, hg⟩ := nativeDiagonalization x
  have hd : ∀ i, 0 < d i := by
    have hnon (i : Fin 3) : 0 ≤ d i := by
      have h : d i = ∑ j, (g.linearEquiv (a j).val).1 i := by
        change (diagonalElement d).1 i = _
        rw [← hg]
        dsimp only [x]
        rw [map_sum, Fin.sum_univ_three, Fin.sum_univ_three]
        rfl
      rw [h]
      exact Finset.sum_nonneg (fun j _ => isAtom_diag_nonneg (g.map_isAtom (a j).property) i)
    rw [← g.map_cubicNorm, hg, diagonalElement, albertCubicNorm_diag] at hn
    have hne := mul_ne_zero_iff.mp hn
    have hne' := mul_ne_zero_iff.mp hne.1
    intro i
    fin_cases i
    · exact lt_of_le_of_ne (hnon _) hne'.1.symm
    · exact lt_of_le_of_ne (hnon _) hne'.2.symm
    · exact lt_of_le_of_ne (hnon _) hne.2.symm
  let u := Real.sqrt (d 0 / d 1)
  let v := Real.sqrt (d 0 / d 2)
  have hu := Real.sqrt_pos.mpr (div_pos (hd 0) (hd 1))
  have hv := Real.sqrt_pos.mpr (div_pos (hd 0) (hd 2))
  let H := (CubicRayEquiv.ofAutomorphism g).trans (positiveDiagonalCongruence u v hu hv)
  have hbal : H.linearEquiv x = d 0 • albertUnit := by
    change diagScale u v (g.linearEquiv x) = _
    rw [hg]
    have h1 : u^2 * d 1 = d 0 := by
      dsimp [u]
      rw [Real.sq_sqrt (div_nonneg (hd 0).le (hd 1).le), div_mul_cancel₀ _ (hd 1).ne']
    have h2 : v^2 * d 2 = d 0 := by
      dsimp [v]
      rw [Real.sq_sqrt (div_nonneg (hd 0).le (hd 2).le), div_mul_cancel₀ _ (hd 2).ne']
    apply Prod.ext <;> funext i <;> fin_cases i
    all_goals first
      | change _ = d 0 * 1
        simp [diagScale, diagonalElement, h1, h2]
      | change _ = d 0 • (0 : Octonion)
        simp [diagScale, diagonalElement]
  have hre : ∑ i, albertTrace (H.linearEquiv (a i).val) • (H.pointMap (a i)).val =
      d 0 • albertUnit := by
    simp only [← H.raw_pointMap, ← map_sum]
    exact hbal
  obtain ⟨F, hF⟩ := weightedAtom_sum_is_unit_frame _ _ (fun i => H.trace_pos (a i)) (hd 0) hre
  obtain ⟨k, hk⟩ := frame_to_standardFrame acceptedAtomAndRankOneBridge F
  refine ⟨H.trans (CubicRayEquiv.ofAutomorphism k), fun i => ?_⟩
  rw [CubicRayEquiv.pointMap_trans]
  apply Subtype.ext
  rw [CubicRayEquiv.pointMap_ofAutomorphism_val]
  exact congrArg k.linearEquiv (congrFun hF i).symm |>.trans (hk i)

end AlbertSequential.ProjectiveMetricInvariant
