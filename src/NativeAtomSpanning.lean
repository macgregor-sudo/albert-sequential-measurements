/- SPDX-License-Identifier: Apache-2.0 -/
module
public import NativeDiagonalProduct
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! Spectral decomposition and finite basis extraction provide actual finite
generating atom menus. This does not identify the paper's specific four tests. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.NativeAnalysis

local instance : FiniteDimensional ℝ Albert :=
  recoveredCoordinateEquiv.symm.finiteDimensional

theorem diagonalElement_eq_sum_atoms (d : Fin 3 → ℝ) :
    diagonalElement d = ∑ i : Fin 3, d i • diagAtom i := by
  rw [Fin.sum_univ_three]
  apply Prod.ext
  · funext j
    change d j = d 0 * (if j = 0 then 1 else 0) +
      d 1 * (if j = 1 then 1 else 0) + d 2 * (if j = 2 then 1 else 0)
    fin_cases j <;> simp
  · funext j
    change (0 : Octonion) = d 0 • 0 + d 1 • 0 + d 2 • 0
    simp

theorem native_span_atoms_eq_top :
    Submodule.span ℝ {x : Albert | IsAtom x} = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨g,d,hg⟩ := nativeDiagonalization x
  have hx : x = ∑ i : Fin 3, d i • g.linearEquiv.symm (diagAtom i) := by
    apply g.linearEquiv.injective
    rw [hg, map_sum]
    simp only [map_smul, LinearEquiv.apply_symm_apply]
    exact diagonalElement_eq_sum_atoms d
  rw [hx]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact nativeAutomorphism_isAtom (nativeAutomorphismInverse g) (diagAtom i)
    (diagAtom_isAtom i)

theorem native_finrank : Module.finrank ℝ Albert = 27 := by
  rw [recoveredCoordinateEquiv.finrank_eq]
  exact Glennie.albert_finrank

/-- Twenty-seven actual atoms form a vector-space basis, hence generate the
entire literal native Jordan algebra. No coordinates or rank search are used. -/
theorem exists_spanning_atom_menu :
    ∃ p : Fin 27 → Albert, (∀ i, IsAtom (p i)) ∧
      Submodule.span ℝ (Set.range p) = ⊤ ∧ LinearIndependent ℝ p := by
  have hd : Module.finrank ℝ (Submodule.span ℝ {x : Albert | IsAtom x}) = 27 := by
    rw [native_span_atoms_eq_top, finrank_top]
    exact native_finrank
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℝ {x : Albert | IsAtom x}
  rw [hd] at hex
  obtain ⟨p,hp,hspan,hind⟩ := hex
  exact ⟨p,hp,hspan.trans native_span_atoms_eq_top,hind⟩

theorem generatesAlbert_of_span_eq_top {ι : Type*} (p : ι → Albert)
    (hp : Submodule.span ℝ (Set.range p) = ⊤) : GeneratesAlbert p := by
  intro x B hB
  have hle : Submodule.span ℝ (Set.range p) ≤ B.carrier := by
    apply Submodule.span_le.mpr
    rintro y ⟨i,rfl⟩
    exact hB i
  rw [hp] at hle
  exact hle (Submodule.mem_top : x ∈ (⊤ : Submodule ℝ Albert))

theorem exists_generating_atom_menu :
    ∃ p : Fin 27 → Albert, (∀ i, IsAtom (p i)) ∧ GeneratesAlbert p := by
  obtain ⟨p,hp,hspan,_⟩ := exists_spanning_atom_menu
  exact ⟨p,hp,generatesAlbert_of_span_eq_top p hspan⟩

#print axioms native_span_atoms_eq_top
#print axioms exists_spanning_atom_menu
#print axioms exists_generating_atom_menu

end AlbertSequential.NativeAnalysis
