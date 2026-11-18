/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CanonicalGramTables
public import RealGramTopology
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.Order.Compact

/-! Compactness and convexity of complete finite-horizon projective tables.
The matrix feasible set retains all M1--M3 constraints and singular matrices.
Restriction to selected words is an image theorem, not sparse reconstruction. -/

@[expose] public section
noncomputable section
namespace AlbertSequential

-- Mathlib puts the RCLike scalar star-order instance, also for ℝ, in this
-- scope. No spectral/Loewner order is installed on the matrix coordinate space.
open scoped ComplexOrder

theorem canonicalGramConstraints_iff {n L : ℕ}
    (G : Matrix (ReducedGramIndex n L) (ReducedGramIndex n L) ℝ) :
    CanonicalGramConstraints G ↔
      G.PosSemidef ∧
      G (emptyReducedGramIndex n L) (emptyReducedGramIndex n L) = 1 ∧
      (∀ u, 0 ≤ G u u ∧ G u u ≤ 1) ∧
      (∀ (u v : ReducedGramIndex n L) (i : Fin n),
        v.val.length < L → IsReducedWord (v.val ++ [(i, true)]) →
        ∀ (hy : v.val ++ [(i, true)] ∈ reducedWordsUpTo (Fin n) L)
          (hn : v.val ++ [(i, false)] ∈ reducedWordsUpTo (Fin n) L),
          G u ⟨v.val ++ [(i, true)], hy⟩ +
            G u ⟨v.val ++ [(i, false)], hn⟩ = G u v) ∧
      (∀ (u v : ReducedGramIndex n L) i,
        u.val.getLast? = some (i, true) → v.val.getLast? = some (i, false) →
        G u v = 0) := by
  exact ⟨fun h => ⟨h.positive, h.normalized, h.probabilities, h.complement, h.orthogonal⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩⟩

theorem isClosed_canonicalGramMatrices (n L : ℕ) :
    IsClosed (canonicalGramMatrices n L) := by
  classical
  simp only [canonicalGramMatrices, canonicalGramConstraints_iff, Set.ofPred_and,
    Set.ofPred_forall]
  refine isClosed_realGramPSD.inter ((isClosed_eq ?_ continuous_const).inter
    ((isClosed_iInter fun u => (isClosed_le continuous_const ?_).inter
      (isClosed_le ?_ continuous_const)).inter
    ((isClosed_iInter fun u => isClosed_iInter fun v => isClosed_iInter fun i =>
      isClosed_iInter fun hlen => isClosed_iInter fun hred =>
      isClosed_iInter fun hy => isClosed_iInter fun hn => isClosed_eq ?_ ?_).inter
      (isClosed_iInter fun u => isClosed_iInter fun v => isClosed_iInter fun i =>
      isClosed_iInter fun hu => isClosed_iInter fun hv => isClosed_eq ?_ continuous_const))))
  all_goals fun_prop

theorem isCompact_canonicalGramMatrices (n L : ℕ) :
    IsCompact (canonicalGramMatrices n L) := by
  classical
  have hbox : IsCompact {G : Matrix (ReducedGramIndex n L) (ReducedGramIndex n L) ℝ |
      ∀ u v, G u v ∈ Set.Icc (-1 : ℝ) 1} :=
    isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => isCompact_Icc
  apply hbox.of_isClosed_subset (isClosed_canonicalGramMatrices n L)
  intro G hG u v
  exact realGram_entry_bounds hG.positive (fun i => (hG.probabilities i).2) u v

theorem convex_canonicalGramMatrices (n L : ℕ) :
    Convex ℝ (canonicalGramMatrices n L) := by
  intro G hG H hH a b ha hb hab
  refine {
    positive := (hG.positive.smul ha).add (hH.positive.smul hb)
    normalized := ?_
    probabilities := ?_
    complement := ?_
    orthogonal := ?_ }
  · change a * G _ _ + b * H _ _ = 1
    rw [hG.normalized, hH.normalized]
    linarith
  · intro u
    change 0 ≤ a * G u u + b * H u u ∧ a * G u u + b * H u u ≤ 1
    obtain ⟨hGlo, hGhi⟩ := hG.probabilities u
    obtain ⟨hHlo, hHhi⟩ := hH.probabilities u
    constructor
    · exact add_nonneg (mul_nonneg ha hGlo) (mul_nonneg hb hHlo)
    · nlinarith
  · intro u v i hlen hred hy hn
    have hGM := hG.complement u v i hlen hred hy hn
    have hHM := hH.complement u v i hlen hred hy hn
    change (a * G u _ + b * H u _) + (a * G u _ + b * H u _) =
      a * G u v + b * H u v
    calc
      _ = a * (G u ⟨v.val ++ [(i, true)], hy⟩ + G u ⟨v.val ++ [(i, false)], hn⟩) +
          b * (H u ⟨v.val ++ [(i, true)], hy⟩ + H u ⟨v.val ++ [(i, false)], hn⟩) := by ring
      _ = _ := by rw [hGM, hHM]
  · intro u v i hu hv
    change a * G u v + b * H u v = 0
    rw [hG.orthogonal u v i hu hv, hH.orthogonal u v i hu hv]
    ring

theorem continuous_gramDiagonal (n L : ℕ) :
    Continuous (gramDiagonal (n := n) (L := L)) := by
  unfold gramDiagonal
  fun_prop

theorem isCompact_finiteRealProjectiveTables (n L : ℕ) :
    IsCompact (finiteRealProjectiveTables n L) := by
  rw [finiteRealProjectiveTables_eq_diagonal_image]
  exact (isCompact_canonicalGramMatrices n L).image (continuous_gramDiagonal n L)

theorem convex_finiteRealProjectiveTables (n L : ℕ) :
    Convex ℝ (finiteRealProjectiveTables n L) := by
  rw [finiteRealProjectiveTables_eq_diagonal_image]
  rintro t ⟨G, hG, rfl⟩ s ⟨H, hH, rfl⟩ a b ha hb hab
  refine ⟨a • G + b • H, convex_canonicalGramMatrices n L hG hH ha hb hab, ?_⟩
  rfl

/-- Selection means full extendibility. In particular this definition does not
impose M1--M3 on a possibly nonclosed sparse list and declare it sufficient. -/
def selectedFiniteRealProjectiveTables {J : Type*} (n L : ℕ)
    (select : J → ReducedGramIndex n L) : Set (J → ℝ) :=
  (fun t : ReducedGramIndex n L → ℝ => t ∘ select) '' finiteRealProjectiveTables n L

theorem isCompact_selectedFiniteRealProjectiveTables {J : Type*} (n L : ℕ)
    (select : J → ReducedGramIndex n L) :
    IsCompact (selectedFiniteRealProjectiveTables n L select) := by
  apply (isCompact_finiteRealProjectiveTables n L).image
  fun_prop

theorem convex_selectedFiniteRealProjectiveTables {J : Type*} (n L : ℕ)
    (select : J → ReducedGramIndex n L) :
    Convex ℝ (selectedFiniteRealProjectiveTables n L select) := by
  rintro t ⟨t', ht', rfl⟩ s ⟨s', hs', rfl⟩ a b ha hb hab
  refine ⟨a • t' + b • s', convex_finiteRealProjectiveTables n L ht' hs' ha hb hab, ?_⟩
  rfl

end AlbertSequential
