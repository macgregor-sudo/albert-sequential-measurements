/- SPDX-License-Identifier: Apache-2.0 -/
module

public import PentadArityAndHelly
public import ThreeAtomAndFourPoint
import SubalgebraCoordsAndLine

public section
noncomputable section

namespace AlbertSequential

/-- Keep the first four atoms of the deposited pentad and use the third
diagonal atom as the fifth. All five lie in the standard quaternionic window. -/
def quaternionicComparisonPentad (i : Fin 5) : Albert :=
  if i = 4 then diagAtom 2 else pentadF i

theorem quaternionicComparisonPentad_isAtom (i : Fin 5) : IsAtom (quaternionicComparisonPentad i) := by
  unfold quaternionicComparisonPentad
  split
  · exact diagAtom_isAtom 2
  · exact pentadF_isAtom i

private theorem dyad_mem_standardQuaternionicWindow (v : Fin 3 → Octonion)
    (hv : ∀ j, (v j).2 = 0) : octDyad v ∈ standardQuaternionicWindow.subalgebra.carrier := by
  rw [mem_standardQuaternionicWindow_iff]
  have h (j k : Fin 3) : (octonionMul (v j) (octonionConj (v k))).2 = 0 := by
    simp [octonionMul, octonionConj, hv]
  exact ⟨h 0 1, h 0 2, h 1 2⟩

theorem quaternionicComparisonPentad_mem (i : Fin 5) :
    quaternionicComparisonPentad i ∈ standardQuaternionicWindow.subalgebra.carrier := by
  have hd (j : Fin 3) : diagAtom j ∈ standardQuaternionicWindow.subalgebra.carrier :=
    (mem_standardQuaternionicWindow_iff _).mpr ⟨rfl, rfl, rfl⟩
  fin_cases i
  · exact hd 0
  · change (1 / 2 : ℝ) • octDyad ![octOne, octOne, 0] ∈ _
    exact Submodule.smul_mem _ _ (dyad_mem_standardQuaternionicWindow _ (fun j => by fin_cases j <;> rfl))
  · change (1 / 3 : ℝ) • octDyad ![octOne, octI, octOne] ∈ _
    exact Submodule.smul_mem _ _ (dyad_mem_standardQuaternionicWindow _ (fun j => by fin_cases j <;> rfl))
  · change (1 / 2 : ℝ) • octDyad ![octOne, octJ, 0] ∈ _
    exact Submodule.smul_mem _ _ (dyad_mem_standardQuaternionicWindow _ (fun j => by fin_cases j <;> rfl))
  · exact hd 2

theorem pentadF_distinct : Function.Injective pentadF := by
  intro i j h
  by_contra hij
  have hsub : Set.range pentadF ⊆ Set.range (pentadDrop i) := by
    rintro _ ⟨k, rfl⟩
    by_cases hki : k = i
    · subst k
      obtain ⟨z,hz⟩ := Fin.exists_succAbove_eq (Ne.symm hij)
      exact ⟨z,by rw [pentadDrop, hz, h]⟩
    · obtain ⟨z,hz⟩ := Fin.exists_succAbove_eq hki
      exact ⟨z,by rw [pentadDrop, hz]⟩
  have htop : generatedSubalgebra (Set.range (pentadDrop i)) = ⊤ := by
    have hle : (⊤ : NativeJordanSubalgebra).carrier ≤
        (generatedSubalgebra (Set.range (pentadDrop i))).carrier := by
      rw [← (generatesAlbert_iff_generatedSubalgebra_eq_top pentadF).mp pentadF_generatesAlbert]
      exact generatedSubalgebra_mono hsub
    ext x
    exact ⟨fun _ => Submodule.mem_top, fun _ => hle Submodule.mem_top⟩
  exact pentadDrop_not_generatesAlbert i ((generatesAlbert_iff_generatedSubalgebra_eq_top _).mpr htop)

private theorem pentadF_ne_third_axis (i : Fin 5) (hi : i ≠ 4) : pentadF i ≠ diagAtom 2 := by
  intro h
  have h2 := congrArg (fun a : Albert => a.1 2) h
  have hz : octNormSq 0 = 0 := (octNormSq_eq_zero 0).mpr rfl
  fin_cases i
  · exact zero_ne_one h2
  · change (1 / 2 : ℝ) * octNormSq 0 = 1 at h2
    norm_num [hz] at h2
  · change (1 / 3 : ℝ) * octNormSq octOne = 1 at h2
    norm_num [octNormSq_one] at h2
  · change (1 / 2 : ℝ) * octNormSq 0 = 1 at h2
    norm_num [hz] at h2
  · exact hi rfl

theorem quaternionicComparisonPentad_distinct : Function.Injective quaternionicComparisonPentad := by
  intro i j h
  by_cases hi : i = 4 <;> by_cases hj : j = 4
  · exact hi.trans hj.symm
  · simp only [quaternionicComparisonPentad, hi, hj, ite_true, ite_false] at h
    exact (pentadF_ne_third_axis j hj h.symm).elim
  · simp only [quaternionicComparisonPentad, hi, hj, ite_true, ite_false] at h
    exact (pentadF_ne_third_axis i hi h).elim
  · exact pentadF_distinct (by simpa only [quaternionicComparisonPentad, hi, hj, ite_false] using h)

theorem quaternionicComparisonPentad_not_generates : ¬ GeneratesAlbert quaternionicComparisonPentad := by
  intro hg
  let : Module.Finite ℝ Octonion :=
    inferInstanceAs (FiniteDimensional ℝ (Quaternion ℝ × Quaternion ℝ))
  let : Module.Finite ℝ Albert :=
    inferInstanceAs (FiniteDimensional ℝ ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
  have hle : generatedSubalgebra (Set.range quaternionicComparisonPentad) ≤ H3Subalgebra .H := by
    apply generatedSubalgebra_le
    rintro _ ⟨i,rfl⟩
    rw [H3Subalgebra_H_eq_standardQuaternionicWindow]
    exact quaternionicComparisonPentad_mem i
  rw [(generatesAlbert_iff_generatedSubalgebra_eq_top _).mp hg, ← H3Subalgebra_O_eq_top] at hle
  have h := Submodule.finrank_mono (show (H3Subalgebra .O).carrier ≤ (H3Subalgebra .H).carrier from hle)
  rw [finrank_H3Subalgebra .H, finrank_H3Subalgebra .O] at h
  change 27 ≤ 15 at h
  omega

/-- Each labeled deletion has the same invariant for the generating pentad and
the quaternionic one, even though their full generated algebras differ. -/
theorem pentad_quaternionic_same_deleted_invariants :
    (∀ k : Fin 5, fourPointInvariant (pentadDrop k) =
      fourPointInvariant (fun j : Fin 4 => quaternionicComparisonPentad (k.succAbove j))) ∧
    GeneratesAlbert pentadF ∧ ¬ GeneratesAlbert quaternionicComparisonPentad := by
  refine ⟨fun k => ?_, pentadF_generatesAlbert, quaternionicComparisonPentad_not_generates⟩
  rw [pentadDrop_fourPointInvariant_eq_zero]
  symm
  apply lemma_A_zero_of_quat standardQuaternionicWindow
  · exact fun j => quaternionicComparisonPentad_isAtom (k.succAbove j)
  · exact fun j => quaternionicComparisonPentad_mem (k.succAbove j)

theorem no_determination_by_deleted_fourPointInvariants :
    ¬ ∃ D : (Fin 5 → ℝ) → Prop, ∀ p : Fin 5 → Albert, Function.Injective p → (∀ i, IsAtom (p i)) →
      (D (fun k => fourPointInvariant (fun j : Fin 4 => p (k.succAbove j))) ↔ GeneratesAlbert p) := by
  rintro ⟨D,hD⟩
  obtain ⟨heq,hgen,hproper⟩ := pentad_quaternionic_same_deleted_invariants
  have h := (hD pentadF pentadF_distinct pentadF_isAtom).mpr hgen
  have hfun : (fun k : Fin 5 => fourPointInvariant (fun j : Fin 4 => pentadF (k.succAbove j))) =
      (fun k : Fin 5 => fourPointInvariant (fun j : Fin 4 => quaternionicComparisonPentad (k.succAbove j))) :=
    funext heq
  rw [hfun] at h
  exact hproper ((hD quaternionicComparisonPentad quaternionicComparisonPentad_distinct
    quaternionicComparisonPentad_isAtom).mp h)

end AlbertSequential
