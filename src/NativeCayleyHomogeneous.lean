/- SPDX-License-Identifier: Apache-2.0 -/
module
public import NativeCayleyChart
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace AlbertSequential.NativeCayley

open WindowProbability NativeAnalysis Set Function

theorem continuous_atomAction :
    Continuous (fun q : AlbertAutomorphismGroup × AlbertAtomSpace => q.1 • q.2) := by
  have h := recoveredCoordinateEquiv.toLinearMap.continuous_of_finiteDimensional
  have hi := recoveredCoordinateEquiv.symm.toLinearMap.continuous_of_finiteDimensional
  have hVal : Continuous (fun q : AlbertAutomorphismGroup × AlbertAtomSpace => q.2.val) :=
    continuous_subtype_val.comp continuous_snd
  have he : Continuous (fun q : AlbertAutomorphismGroup × AlbertAtomSpace =>
      albertAutAction q.1 q.2.val) :=
    hi.comp (AlbertAutomorphismGroup.continuous_evaluation.comp (continuous_fst.prodMk (h.comp hVal)))
  exact he.subtype_mk _

theorem continuous_atomOrbit (p : AlbertAtomSpace) :
    Continuous (fun g : AlbertAutomorphismGroup => g • p) :=
  continuous_atomAction.comp (continuous_id.prodMk continuous_const)

theorem isClosed_atomStabilizer (p : AlbertAtomSpace) :
    IsClosed (MulAction.stabilizer AlbertAutomorphismGroup p : Set AlbertAutomorphismGroup) :=
  isClosed_singleton.preimage (continuous_atomOrbit p)

theorem atomAction_transitive (p q : AlbertAtomSpace) :
    ∃ g : AlbertAutomorphismGroup, g • p = q := by
  obtain ⟨g, hg⟩ := albertAtomAction_transitive p
  obtain ⟨h, hh⟩ := albertAtomAction_transitive q
  exact ⟨h * g⁻¹, by rw [mul_smul, ← hg, inv_smul_smul, hh]⟩

/-- The compact native automorphism group modulo the actual stabilizer of any atom. -/
def atomStabilizerQuotientHomeomorph (p : AlbertAtomSpace) :
    (AlbertAutomorphismGroup ⧸ MulAction.stabilizer AlbertAutomorphismGroup p) ≃ₜ AlbertAtomSpace := by
  let f := MulAction.ofQuotientStabilizer AlbertAutomorphismGroup p
  have hf : Continuous f :=
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr (continuous_atomOrbit p)
  have hInj : Injective f := MulAction.injective_ofQuotientStabilizer AlbertAutomorphismGroup p
  have hSurj : Surjective f := by
    intro q
    obtain ⟨g, hg⟩ := atomAction_transitive p q
    exact ⟨QuotientGroup.mk g, hg⟩
  exact (Equiv.ofBijective f ⟨hInj, hSurj⟩).toHomeomorphOfContinuousClosed hf
    (fun _ hs => (hs.isCompact.image hf).isClosed)

theorem atomStabilizerQuotientHomeomorph_apply (p : AlbertAtomSpace) (g : AlbertAutomorphismGroup) :
    atomStabilizerQuotientHomeomorph p (QuotientGroup.mk g) = g • p := rfl

end AlbertSequential.NativeCayley
