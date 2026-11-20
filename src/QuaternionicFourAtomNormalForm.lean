/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ThreeAtomAndFourPoint
public import SubalgebraCoordsAndLine

/-! Core A.7(a) as a trace-preserving Jordan automorphism of the whole standard
quaternionic window, with normalized columns. -/
@[expose] public section
noncomputable section

namespace AlbertSequential

namespace NativeAlbertAutomorphism

/-- An ambient automorphism preserving the standard window restricts to an
automorphism of that finite dimensional Jordan algebra. -/
def onStandardQuaternionicWindow (g : NativeAlbertAutomorphism)
    (hg : ∀ x ∈ standardQuaternionicWindow.subalgebra.carrier,
      g.linearEquiv x ∈ standardQuaternionicWindow.subalgebra.carrier) :
    JordanSubalgebraIso standardQuaternionicWindow.subalgebra
      standardQuaternionicWindow.subalgebra := by
  let B := standardQuaternionicWindow.subalgebra
  have : FiniteDimensional ℝ Albert :=
    NativeAnalysis.recoveredCoordinateEquiv.symm.finiteDimensional
  let L : B.carrier →ₗ[ℝ] B.carrier :=
    (g.linearEquiv.toLinearMap.comp B.carrier.subtype).codRestrict B.carrier (fun x => hg x.1 x.2)
  have hi : Function.Injective L := fun x y h =>
    Subtype.ext (g.linearEquiv.injective (congrArg Subtype.val h))
  exact {
    toLinearEquiv := LinearEquiv.ofBijective L ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩
    map_unit := Subtype.ext g.preserves_unit
    map_jordan := fun x y => Subtype.ext (g.preserves_product x.1 y.1) }

theorem onStandardQuaternionicWindow_apply (g : NativeAlbertAutomorphism)
    (hg : ∀ x ∈ standardQuaternionicWindow.subalgebra.carrier,
      g.linearEquiv x ∈ standardQuaternionicWindow.subalgebra.carrier)
    (x : standardQuaternionicWindow.subalgebra.carrier) :
    ((g.onStandardQuaternionicWindow hg).toLinearEquiv x).1 = g.linearEquiv x.1 := rfl

end NativeAlbertAutomorphism

/-- Every four atoms in the standard quaternionic window admit the four columns
of Eq. `eq:fp:normal` using a trace-preserving automorphism of that window. -/
theorem lemma_A_zero_quaternionic_normal_form (p : Fin 4 → Albert)
    (hp : ∀ i, IsAtom (p i)) (hmem : ∀ i, p i ∈ standardQuaternionicWindow.subalgebra.carrier) :
    ∃ (ψ : JordanSubalgebraIso standardQuaternionicWindow.subalgebra
          standardQuaternionicWindow.subalgebra)
      (B₀ B₁ C₀ C₁ C₂ C₃ D₀ : ℝ) (X Y : Quaternion ℝ),
      (∀ x, albertTrace (ψ.toLinearEquiv x).1 = albertTrace x.1) ∧
      0 ≤ B₀ ∧ 0 ≤ B₁ ∧ 0 ≤ C₀ ∧ 0 ≤ C₃ ∧ 0 ≤ D₀ ∧
      B₀ ^ 2 + B₁ ^ 2 = 1 ∧
      C₀ ^ 2 + octNormSq (octonionScalar C₁ + C₂ • octI) + C₃ ^ 2 = 1 ∧
      D₀ ^ 2 + octNormSq (quatEmbed1 X) + octNormSq (quatEmbed1 Y) = 1 ∧
      (fun i => (ψ.toLinearEquiv ⟨p i, hmem i⟩).1) =
        sparseFourConfigOct B₀ B₁ C₀ C₁ C₂ C₃ D₀ (quatEmbed1 X) (quatEmbed1 Y) := by
  obtain ⟨g, B₀, B₁, C₀, C₁, C₂, C₃, D₀, X, Y, hg, hB₀, hB₁, hC₀, hC₃, hD₀, hform⟩ :=
    exists_quatAuto_to_sparseFourConfigOct p hp hmem
  let ψ := g.onStandardQuaternionicWindow hg
  have hnorm (i : Fin 4) :
      albertTrace (sparseFourConfigOct B₀ B₁ C₀ C₁ C₂ C₃ D₀ (quatEmbed1 X) (quatEmbed1 Y) i) = 1 :=
    (congrArg albertTrace (congrFun hform i).symm).trans ((g.preserves_trace (p i)).trans (hp i).2)
  have hscalar (r : ℝ) : octNormSq (octonionScalar r) = r ^ 2 := by
    rw [octNormSq_eq_coords]
    simp [octonionScalar]
  have hzero : octNormSq 0 = 0 := (octNormSq_eq_zero 0).mpr rfl
  refine ⟨ψ, B₀, B₁, C₀, C₁, C₂, C₃, D₀, X, Y, fun x => g.preserves_trace x.1,
    hB₀, hB₁, hC₀, hC₃, hD₀, ?_, ?_, ?_, hform⟩
  · simpa [sparseFourConfigOct, octDyad, albertTrace, Fin.sum_univ_three,
      hscalar, hzero] using hnorm 1
  · simpa [sparseFourConfigOct, octDyad, albertTrace, Fin.sum_univ_three,
      hscalar] using hnorm 2
  · simpa [sparseFourConfigOct, octDyad, albertTrace, Fin.sum_univ_three,
      hscalar] using hnorm 3

end AlbertSequential
