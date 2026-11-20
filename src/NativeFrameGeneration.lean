/- SPDX-License-Identifier: Apache-2.0 -/
module
public import ComplexWindowDeterminantAndMax
public import PentadArityAndHelly

/-! Single frames generate their diagonal algebra. Four completed frames can generate the Albert algebra. -/
@[expose] public section
noncomputable section
namespace AlbertSequential

theorem atom_extends_to_labelled_frame (p : Albert) (hp : IsAtom p) :
    ∃ F : NativeJordanFrame, F.atom 0 = p := by
  obtain ⟨g,hg⟩ := atom_to_diagAtom0 p hp
  let F : NativeJordanFrame := {
    atom := fun i => g.symm.linearEquiv (diagAtom i)
    atoms := fun i => g.symm.map_isAtom (diagAtom_isAtom i)
    orthogonal := fun i j hij => by
      rw [← g.symm.preserves_product,diagAtom_orthogonal hij,map_zero]
    sum_unit := by rw [← map_sum,diagAtom_sum_eq_unit,g.symm.preserves_unit] }
  refine ⟨F,?_⟩
  change g.linearEquiv.symm (diagAtom 0) = p
  exact g.linearEquiv.symm_apply_eq.mpr hg.symm

theorem exists_four_generating_frames :
    ∃ F : Fin 4 → NativeJordanFrame, GeneratesAlbert (fun ij : Fin 4 × Fin 3 => (F ij.1).atom ij.2) := by
  choose F hF using fun i => atom_extends_to_labelled_frame _ (maximizerConfig_isAtom i)
  have hgen := (fourPointInvariant_pos_iff maximizerConfig maximizerConfig_isAtom).mp
    (by rw [fourPointInvariant_maximizerConfig]; norm_num)
  exact ⟨F, fun x B hB => hgen x B (fun i => hF i ▸ hB (i,0))⟩

theorem generated_frame_is_diagonal_span (F : NativeJordanFrame) :
    (generatedSubalgebra (Set.range F.atom)).carrier = Submodule.span ℝ (Set.range F.atom) := by
  let V := Submodule.span ℝ (Set.range F.atom)
  have mem (i : Fin 3) : F.atom i ∈ V := Submodule.subset_span ⟨i,rfl⟩
  let B : NativeJordanSubalgebra := {
    carrier := V
    unit_mem := F.sum_unit ▸ V.sum_mem (fun i _ => mem i)
    product_mem := by
      intro x hx y hy
      refine Submodule.span_induction₂ (p := fun a b _ _ => jordanMul a b ∈ V)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
      · rintro _ _ ⟨i,rfl⟩ ⟨j,rfl⟩
        by_cases h : i = j
        · subst j; rw [(F.atoms i).1]; exact mem i
        · rw [F.orthogonal i j h]; exact V.zero_mem
      · intros; rw [jordanMul_zero_left]; exact V.zero_mem
      · intros; rw [jordanMul_zero_right]; exact V.zero_mem
      · intro a b c _ _ _ h k; rw [jordanMul_add_left]; exact V.add_mem h k
      · intro a b c _ _ _ h k; rw [jordanMul_add_right]; exact V.add_mem h k
      · intro r a b _ _ h; rw [jordanMul_smul_left]; exact V.smul_mem r h
      · intro r a b _ _ h; rw [jordanMul_smul_right]; exact V.smul_mem r h }
  apply le_antisymm
  · exact generatedSubalgebra_le (B := B) (fun _ ⟨i,hi⟩ => hi ▸ mem i)
  · exact Submodule.span_le.mpr (subset_generatedSubalgebra _)

end AlbertSequential
