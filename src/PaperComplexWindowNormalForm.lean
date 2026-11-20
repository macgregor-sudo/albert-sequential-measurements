/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ComplexWindowDeterminantAndMax
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

@[expose] public section
noncomputable section

namespace AlbertSequential

open NativeAnalysis

/-- The native orthogonal projection onto the carrier of a complex window. -/
def nativeWindowOrthogonalProjection (W : ComplexWindow) : Albert →ₗ[ℝ] Albert :=
  W.embedding.comp (windowProj W)

theorem nativeWindowOrthogonalProjection_mem (W : ComplexWindow) (y : Albert) :
    W.Contains (nativeWindowOrthogonalProjection W y) :=
  ⟨windowProj W y, rfl⟩

theorem nativeWindowOrthogonalProjection_fixes (W : ComplexWindow) {y : Albert}
    (hy : W.Contains y) :
    nativeWindowOrthogonalProjection W y = y := by
  obtain ⟨M, rfl⟩ := hy
  change W.embedding (windowProj W (W.embedding M)) = W.embedding M
  rw [windowProj_embedding]

theorem nativeWindowOrthogonalProjection_residual (W : ComplexWindow) (y z : Albert)
    (hz : W.Contains z) :
    tracePairing (y - nativeWindowOrthogonalProjection W y) z = 0 := by
  obtain ⟨M, rfl⟩ := hz
  change tracePairing (y - W.embedding (windowProj W y)) (W.embedding M) = 0
  rw [tracePairing_sub_left, ← windowProj_tracePairing W y M,
    ← windowProj_tracePairing W (W.embedding (windowProj W y)) M, windowProj_embedding,
    sub_self]

theorem nativeWindowOrthogonalProjection_transport (W : ComplexWindow)
    (g : NativeAlbertAutomorphism) :
    (nativeWindowOrthogonalProjection (W.transport g)).comp g.linearEquiv.toLinearMap =
      g.linearEquiv.toLinearMap.comp (nativeWindowOrthogonalProjection W) := by
  apply LinearMap.ext
  intro y
  change g.linearEquiv (W.embedding (windowProj (W.transport g) (g.linearEquiv y))) =
    g.linearEquiv (W.embedding (windowProj W y))
  rw [windowProj_transport]

/-- The first three atoms are pairwise distinct and nonorthogonal. -/
def IsWindowTrianglePairwise (p : Fin 4 → Albert) : Prop :=
  ∀ i j : Fin 4, i ≠ 3 → j ≠ 3 → i ≠ j →
    p i ≠ p j ∧ jordanMul (p i) (p j) ≠ 0

private theorem generated_three_membership {p : Fin 4 → Albert}
    (σ : Equiv.Perm (Fin 4)) (hσ : σ 3 = 3) (x : Albert) :
    InGeneratedAlgebra ![p (σ 0), p (σ 1), p (σ 2)] x ↔
      InGeneratedAlgebra ![p 0, p 1, p 2] x := by
  have hm (r : Fin 4 → Albert) (B : NativeJordanSubalgebra) (ρ : Equiv.Perm (Fin 4)) (hρ : ρ 3 = 3)
      (hB : ∀ i : Fin 3, ![r 0, r 1, r 2] i ∈ B.carrier)
      (i : Fin 4) (hi : i ≠ 3) : r (ρ i) ∈ B.carrier := by
    have hj := ρ.injective.ne hi
    rw [hρ] at hj
    revert hj
    generalize ρ i = j
    intro hj
    fin_cases j
    · exact hB 0
    · exact hB 1
    · exact hB 2
    · exact (hj rfl).elim
  constructor
  · intro h B hB
    apply h B
    intro i
    fin_cases i
    · exact hm p B σ hσ hB 0 (by decide)
    · exact hm p B σ hσ hB 1 (by decide)
    · exact hm p B σ hσ hB 2 (by decide)
  · intro h B hB
    apply h B
    have hs : σ.symm 3 = 3 := σ.symm_apply_eq.mpr hσ.symm
    let q := p ∘ σ
    have hq : ∀ i : Fin 4, i ≠ 3 → q (σ.symm i) ∈ B.carrier :=
      fun i hi => hm q B σ.symm hs hB i hi
    intro i
    fin_cases i
    · change p 0 ∈ B.carrier
      simpa only [q, Function.comp_apply, Equiv.apply_symm_apply] using hq 0 (by decide)
    · change p 1 ∈ B.carrier
      simpa only [q, Function.comp_apply, Equiv.apply_symm_apply] using hq 1 (by decide)
    · change p 2 ∈ B.carrier
      simpa only [q, Function.comp_apply, Equiv.apply_symm_apply] using hq 2 (by decide)

/-- The full sparse normal form for a window triangle, with the fourth atom fixed. -/
structure WindowTriangleNormalForm (p : Fin 4 → Albert) where
  permutation : Equiv.Perm (Fin 4)
  fixesFourth : permutation 3 = 3
  fourthOverlap : 0 < tracePairing (p (permutation 0)) (p 3)
  automorphism : NativeAlbertAutomorphism
  B₀ : ℝ
  B₁ : ℝ
  C₀ : ℝ
  C₁ : ℝ
  C₂ : ℝ
  C₃ : ℝ
  D₀ : ℝ
  x₀ : ℝ
  x₁ : ℝ
  x₂ : ℝ
  y₀ : ℝ
  y₁ : ℝ
  y₂ : ℝ
  y₃ : ℝ
  y₄ : ℝ
  B₀_pos : 0 < B₀
  B₁_pos : 0 < B₁
  C₀_pos : 0 < C₀
  C₂_nonneg : 0 ≤ C₂
  C₃_nonneg : 0 ≤ C₃
  D₀_pos : 0 < D₀
  x₂_nonneg : 0 ≤ x₂
  y₄_nonneg : 0 ≤ y₄
  normB : B₀ ^ 2 + B₁ ^ 2 = 1
  normC : C₀ ^ 2 + C₁ ^ 2 + C₂ ^ 2 + C₃ ^ 2 = 1
  normD : D₀ ^ 2 + x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 + y₀ ^ 2 + y₁ ^ 2 + y₂ ^ 2 + y₃ ^ 2 + y₄ ^ 2 = 1
  mapConfig : (fun i => automorphism.linearEquiv (p (permutation i))) =
    sparseFourConfig B₀ B₁ C₀ C₁ C₂ C₃ D₀ x₀ x₁ x₂
      (y₀ • octOne + y₁ • octI + y₂ • octJ + y₃ • octK + y₄ • octL)
  deltaRelabel : tripleDelta (p (permutation 0)) (p (permutation 1)) (p (permutation 2)) =
    tripleDelta (p 0) (p 1) (p 2)
  delta : tripleDelta (p 0) (p 1) (p 2) = B₀ ^ 2 * B₁ ^ 4 * C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2

theorem WindowTriangleNormalForm.windowDelta {p : Fin 4 → Albert}
    (N : WindowTriangleNormalForm p) (W : ComplexWindow) :
    windowDelta W (p 0) (p 1) (p 2) = N.B₀ ^ 2 * N.B₁ ^ 4 * N.C₀ ^ 2 * N.C₂ ^ 2 * N.C₃ ^ 2 :=
  (windowDelta_eq_tripleDelta W (p 0) (p 1) (p 2)).trans N.delta

theorem WindowTriangleNormalForm.invariant_relabel {p : Fin 4 → Albert}
    (N : WindowTriangleNormalForm p) :
    fourPointInvariant (fun i => p (N.permutation i)) = fourPointInvariant p :=
  fourPointInvariant_perm_invariant N.permutation p

theorem WindowTriangleNormalForm.generated_relabel {p : Fin 4 → Albert}
    (N : WindowTriangleNormalForm p) (x : Albert) :
    InGeneratedAlgebra ![p (N.permutation 0), p (N.permutation 1), p (N.permutation 2)] x ↔
      InGeneratedAlgebra ![p 0, p 1, p 2] x :=
  generated_three_membership N.permutation N.fixesFourth x

private theorem atom_overlap_pos_of_nonorthogonal {p q : Albert}
    (hp : IsAtom p) (hq : IsAtom q) (hn : jordanMul p q ≠ 0) :
    0 < tracePairing p q :=
  lt_of_le_of_ne (atom_tracePairing_bounds p q hp hq).1
    (Ne.symm (mt (atom_tracePairing_eq_zero_iff p q hp hq).mp hn))

private theorem exists_triangle_normal_form {p : Fin 4 → Albert} (hp : ∀ i, IsAtom (p i))
    (hpair : IsWindowTrianglePairwise p)
    (hfourth : 0 < tracePairing (p 0) (p 3) ∨ 0 < tracePairing (p 1) (p 3) ∨
      0 < tracePairing (p 2) (p 3)) :
    Nonempty (WindowTriangleNormalForm p) := by
  suffices make : ∀ (σ : Equiv.Perm (Fin 4)), σ 3 = 3 →
      0 < tracePairing (p (σ 0)) (p 3) →
      tripleDelta (p (σ 0)) (p (σ 1)) (p (σ 2)) = tripleDelta (p 0) (p 1) (p 2) →
      Nonempty (WindowTriangleNormalForm p) by
    rcases hfourth with h | h | h
    · exact make 1 rfl h rfl
    · have h0 : Equiv.swap (0 : Fin 4) 1 0 = 1 := by decide
      have h1 : Equiv.swap (0 : Fin 4) 1 1 = 0 := by decide
      have h2 : Equiv.swap (0 : Fin 4) 1 2 = 2 := by decide
      exact make (Equiv.swap 0 1) (by decide) (by rwa [h0])
        (by rw [h0, h1, h2, tripleDelta_symm_12])
    · have h0 : Equiv.swap (0 : Fin 4) 2 0 = 2 := by decide
      have h1 : Equiv.swap (0 : Fin 4) 2 1 = 1 := by decide
      have h2 : Equiv.swap (0 : Fin 4) 2 2 = 0 := by decide
      exact make (Equiv.swap 0 2) (by decide) (by rwa [h0])
        (by rw [h0, h1, h2, tripleDelta_symm_13])
  intro σ hσ hover hδ
  let q := p ∘ σ
  have hq : ∀ i, IsAtom (q i) := fun i => hp (σ i)
  have hne (i : Fin 4) (hi : i ≠ 3) : σ i ≠ 3 := hσ ▸ σ.injective.ne hi
  have h01 := hpair (σ 0) (σ 1) (hne 0 (by decide)) (hne 1 (by decide))
    (σ.injective.ne (by decide))
  have h02 := hpair (σ 0) (σ 2) (hne 0 (by decide)) (hne 2 (by decide))
    (σ.injective.ne (by decide))
  have h01' : tracePairing (q 0) (q 1) < 1 :=
    (atom_tracePairing_bounds _ _ (hq 0) (hq 1)).2.lt_of_ne
      (mt (atom_tracePairing_eq_one_iff _ _ (hq 0) (hq 1)).mp h01.1)
  have h03 : 0 < tracePairing (q 0) (q 3) := by
    change 0 < tracePairing (p (σ 0)) (p (σ 3))
    rwa [hσ]
  obtain ⟨g, B₀, B₁, C₀, C₁, C₂, C₃, D₀, x₀, x₁, x₂, y₀, y₁, y₂, y₃, y₄,
    hB₀, hB₁, hC₀, hC₂, hC₃, hD₀, hx₂, hy₄, hB, hC, hD, hcfg⟩ :=
    lemma_A_normal q hq (atom_overlap_pos_of_nonorthogonal (hq 0) (hq 1) h01.2) h01'
      (atom_overlap_pos_of_nonorthogonal (hq 0) (hq 2) h02.2) h03
  have hg0 : g.linearEquiv (q 0) = diagAtom 0 :=
    (congrFun hcfg 0).trans (sparseFourConfigOct_zero _ _ _ _ _ _ _ _ _)
  have hg1 : g.linearEquiv (q 1) = octDyad ![octonionScalar B₀, octonionScalar B₁, 0] :=
    congrFun hcfg 1
  have hg2 : g.linearEquiv (q 2) =
      octDyad ![octonionScalar C₀, octonionScalar C₁ + C₂ • octI, octonionScalar C₃] :=
    congrFun hcfg 2
  refine ⟨⟨σ, hσ, hover, g, B₀, B₁, C₀, C₁, C₂, C₃, D₀, x₀, x₁, x₂, y₀, y₁, y₂, y₃, y₄,
    hB₀, hB₁, hC₀, hC₂, hC₃, hD₀, hx₂, hy₄, hB, hC, hD, hcfg, hδ, ?_⟩⟩
  rw [← hδ]
  change tripleDelta (q 0) (q 1) (q 2) = _
  rw [← tripleDelta_automorphism g (q 0) (q 1) (q 2), hg0, hg1, hg2]
  exact tripleDelta_normal_form B₀ B₁ C₀ C₁ C₂ C₃

/-- Lemma A.9(a) with the actual relabelling and normal-form data. -/
theorem paperWindowTriangle_a {p : Fin 4 → Albert} (hp : ∀ i, IsAtom (p i))
    (hpair : IsWindowTrianglePairwise p)
    (hfourth : jordanMul (p 0) (p 3) ≠ 0 ∨ jordanMul (p 1) (p 3) ≠ 0 ∨
      jordanMul (p 2) (p 3) ≠ 0) :
    Nonempty (WindowTriangleNormalForm p) := by
  rcases hfourth with h | h | h
  · exact exists_triangle_normal_form hp hpair (.inl (atom_overlap_pos_of_nonorthogonal (hp 0) (hp 3) h))
  · exact exists_triangle_normal_form hp hpair
      (.inr (.inl (atom_overlap_pos_of_nonorthogonal (hp 1) (hp 3) h)))
  · exact exists_triangle_normal_form hp hpair
      (.inr (.inr (atom_overlap_pos_of_nonorthogonal (hp 2) (hp 3) h)))

private theorem transported_standard_contains (g : NativeAlbertAutomorphism) (x : Albert) :
    (standardComplexWindow.transport g.symm).Contains x ↔
      standardComplexWindow.Contains (g.linearEquiv x) := by
  rw [ComplexWindow.contains_transport_iff]
  rfl

theorem WindowTriangleNormalForm.generated {p : Fin 4 → Albert} (N : WindowTriangleNormalForm p)
    (hp : ∀ i, IsAtom (p i)) (hδ : tripleDelta (p 0) (p 1) (p 2) ≠ 0) :
    ∃ W : ComplexWindow,
      (∀ x : Albert, W.Contains x ↔ InGeneratedAlgebra ![p 0, p 1, p 2] x) ∧
      (W.transport N.automorphism).toSubalgebra.carrier =
        standardComplexWindow.toSubalgebra.carrier ∧
      (nativeWindowOrthogonalProjection standardComplexWindow).comp
        N.automorphism.linearEquiv.toLinearMap =
          N.automorphism.linearEquiv.toLinearMap.comp (nativeWindowOrthogonalProjection W) := by
  let g := N.automorphism
  let W := standardComplexWindow.transport g.symm
  have hC₂ : N.C₂ ≠ 0 := fun h => hδ (by rw [N.delta, h]; ring)
  have hC₃ : N.C₃ ≠ 0 := fun h => hδ (by rw [N.delta, h]; ring)
  let q := sparseFourConfig N.B₀ N.B₁ N.C₀ N.C₁ N.C₂ N.C₃ N.D₀ N.x₀ N.x₁ N.x₂
    (N.y₀ • octOne + N.y₁ • octI + N.y₂ • octJ + N.y₃ • octK + N.y₄ • octL)
  have hgen : ∀ x, InGeneratedAlgebra ![q 0, q 1, q 2] x ↔ standardComplexWindow.Contains x :=
    lemma_A_generate_three _ _ _ _ _ _ _ _ _ _ _ N.B₀_pos N.B₁_pos N.C₀_pos hC₂ hC₃
  have hq (i : Fin 4) : g.linearEquiv (p (N.permutation i)) = q i := congrFun N.mapConfig i
  have hmem (i : Fin 4) (hi : i ≠ 3) : W.Contains (p (N.permutation i)) := by
    rw [transported_standard_contains, hq, ← hgen]
    intro B hB
    fin_cases i
    · exact hB 0
    · exact hB 1
    · exact hB 2
    · exact (hi rfl).elim
  have hall (i : Fin 4) (hi : i ≠ 3) : W.Contains (p i) := by
    have hj : N.permutation.symm i ≠ 3 := by
      intro he
      exact hi (by rw [← N.fixesFourth, ← he, Equiv.apply_symm_apply])
    simpa only [Equiv.apply_symm_apply] using hmem (N.permutation.symm i) hj
  have hcar : (W.transport g).embedding = standardComplexWindow.embedding := by
    apply LinearMap.ext
    intro x
    change g.linearEquiv (g.linearEquiv.symm (standardComplexWindow.embedding x)) =
      standardComplexWindow.embedding x
    exact g.linearEquiv.apply_symm_apply _
  have hsub : (W.transport g).toSubalgebra.carrier = standardComplexWindow.toSubalgebra.carrier :=
    congrArg LinearMap.range hcar
  have hproj : nativeWindowOrthogonalProjection (W.transport g) =
      nativeWindowOrthogonalProjection standardComplexWindow := by
    apply LinearMap.ext
    intro x
    exact windowProj_eq_of_subalgebra_eq _ _ hsub x
  obtain ⟨_, _, _, _, _, hW⟩ := lemma_A_window_generated (hp 0) (hp 1) (hp 2) hδ
  refine ⟨W, hW W (hall 0 (by decide)) (hall 1 (by decide)) (hall 2 (by decide)), hsub, ?_⟩
  rw [← hproj]
  exact nativeWindowOrthogonalProjection_transport W g

/-- Lemma A.9(b): nonzero determinant supplies the native generated window in the same normal form. -/
theorem paperWindowTriangle_b {p : Fin 4 → Albert} (hp : ∀ i, IsAtom (p i))
    (hδ : tripleDelta (p 0) (p 1) (p 2) ≠ 0) :
    IsWindowTrianglePairwise p ∧
    (∀ i j : Fin 4, i ≠ 3 → j ≠ 3 → i ≠ j →
      0 < tracePairing (p i) (p j) ∧ tracePairing (p i) (p j) < 1) ∧
    ∃ (N : WindowTriangleNormalForm p) (W : ComplexWindow),
      (∀ x : Albert, W.Contains x ↔ InGeneratedAlgebra ![p 0, p 1, p 2] x) ∧
      (W.transport N.automorphism).toSubalgebra.carrier =
        standardComplexWindow.toSubalgebra.carrier ∧
      (nativeWindowOrthogonalProjection standardComplexWindow).comp
        N.automorphism.linearEquiv.toLinearMap =
          N.automorphism.linearEquiv.toLinearMap.comp (nativeWindowOrthogonalProjection W) := by
  obtain ⟨_, h01, h02, h12, _, _⟩ := lemma_A_window_generated (hp 0) (hp 1) (hp 2) hδ
  have hover i j (hi : i ≠ 3) (hj : j ≠ 3) (hij : i ≠ j) :
      0 < tracePairing (p i) (p j) ∧ tracePairing (p i) (p j) < 1 := by
    fin_cases i <;> fin_cases j <;>
      first
      | exact (hi rfl).elim
      | exact (hj rfl).elim
      | exact (hij rfl).elim
      | exact h01
      | exact h02
      | exact h12
      | exact (tracePairing_comm _ _) ▸ h01
      | exact (tracePairing_comm _ _) ▸ h02
      | exact (tracePairing_comm _ _) ▸ h12
  have hpair : IsWindowTrianglePairwise p := by
    intro i j hi hj hij
    exact ⟨mt (atom_tracePairing_eq_one_iff _ _ (hp i) (hp j)).mpr
      (ne_of_lt (hover i j hi hj hij).2), mt (atom_tracePairing_eq_zero_iff _ _ (hp i) (hp j)).mpr
      (ne_of_gt (hover i j hi hj hij).1)⟩
  have hfourth := tripleDelta_nonzero_some_overlap (hp 0) (hp 1) (hp 2) (hp 3) hδ
  obtain ⟨N⟩ := exists_triangle_normal_form hp hpair hfourth
  obtain ⟨W, hW, hgW, hP⟩ := N.generated hp hδ
  exact ⟨hpair, hover, N, W, hW, hgW, hP⟩

/-- Lemma A.9(c), including coincident and orthogonal atoms. -/
theorem paperWindowTriangle_c (W : ComplexWindow) {p : Fin 4 → Albert} (hp : ∀ i, IsAtom (p i))
    (hδ : windowDelta W (p 0) (p 1) (p 2) = 0) :
    fourPointInvariant p = 0 := by
  rw [windowDelta_eq_tripleDelta] at hδ
  have hη : ![p 0, p 1, p 2, p 3] = p := by
    funext i
    fin_cases i <;> rfl
  rw [← hη]
  exact prop_windowdet_zero (hp 0) (hp 1) (hp 2) (hp 3) hδ

end AlbertSequential
