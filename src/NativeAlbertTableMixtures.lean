/- SPDX-License-Identifier: Apache-2.0 -/
module
public import JordanTableMixtures
public import ProjectiveTableMixtures
public import GeneratedPrimitiveTests
public import NativeIdempotentClassification

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace AlbertSequential
open NativeAnalysis UnitalJordanProduct
open scoped BigOperators

theorem nativeAlbertModuleFinite : FiniteDimensional ℝ Albert := recoveredCoordinateEquiv.symm.finiteDimensional
local instance : FiniteDimensional ℝ Albert := nativeAlbertModuleFinite

abbrev nativeAlbertProduct := HorizonFive.albertJordanProduct

theorem nativeAlbertProduct_formallyReal : nativeAlbertProduct.FormallyReal := by
  intro n x hx i
  have h := congrArg (tracePairingFunctional albertUnit) hx
  rw [map_sum,map_zero] at h
  have he : ∑ k, tracePairing (x k) (x k) = 0 := by
    have htrace (y : Albert) : tracePairing albertUnit (jordanMul y y) = tracePairing y y := by
      rw [tracePairing_comm albertUnit,tracePairing_unit_right]
      rfl
    simpa only [tracePairingFunctional_apply,show ∀ x y, nativeAlbertProduct.product x y =
      jordanMul x y from fun _ _ => rfl,htrace] using h
  exact (tracePairing_self_eq_zero _).mp
    ((Finset.sum_eq_zero_iff_of_nonneg (fun k _ => tracePairing_self_nonneg (x k))).mp he i (Finset.mem_univ i))

theorem nativeAlbertProduct_wordEffect {I : Type*} (p : I → Albert) (w : Word I) :
    nativeAlbertProduct.sequentialWordEffect p w = nativeWordEffect p w := by
  induction w with
  | nil => rfl
  | cons a v ih =>
    have eqOutcome : nativeAlbertProduct.sequentialOutcome p a = nativeOutcome p a := rfl
    rw [UnitalJordanProduct.sequentialWordEffect,ih,eqOutcome]
    simp only [UnitalJordanProduct.quadraticRepresentation_apply,nativeWordEffect,quadraticMap,two_smul]
    rfl

theorem nativeAlbertTables_subset_finiteJordan (n : ℕ) :
    nativeAlbertTables n ⊆ finiteJordanTables.{0} n := by
  rintro f ⟨p,ρ,hp,hρ,hw⟩
  let J := nativeAlbertProduct
  refine ⟨Albert,inferInstance,inferInstance,inferInstance,J,nativeAlbertProduct_formallyReal,?_⟩
  apply (J.mem_canonicalProjectiveTables_iff_functional _).mpr
  refine ⟨p,tracePairingFunctional ρ,hp,(isPositive_iff_dual_squares ρ).mp hρ.1,
    (tracePairing_unit_right ρ).trans hρ.2,?_⟩
  intro w
  rw [tracePairingFunctional_apply,nativeAlbertProduct_wordEffect,← nativeWordProbability_eq_pairing,hw]

/-- The actual canonical-density table set for the Albert product coincides
with the native table set using its fixed trace and square cone. -/
theorem nativeAlbert_canonicalProjectiveTables_eq (n : ℕ) :
    nativeAlbertProduct.canonicalProjectiveTables nativeAlbertProduct_formallyReal n = nativeAlbertTables n := by
  ext f
  rw [nativeAlbertProduct.mem_canonicalProjectiveTables_iff_functional]
  constructor
  · rintro ⟨p,ω,hp,hpos,hnorm,hw⟩
    let ρ := traceRepresentative ω
    refine ⟨p,ρ,hp,normalized_positiveFunctional_density ω hpos hnorm,?_⟩
    intro w
    rw [nativeWordProbability_eq_pairing,traceRepresentative_pairing,← nativeAlbertProduct_wordEffect,hw]
  · rintro ⟨p,ρ,hp,hρ,hw⟩
    refine ⟨p,tracePairingFunctional ρ,hp,(isPositive_iff_dual_squares ρ).mp hρ.1,
      (tracePairing_unit_right ρ).trans hρ.2,?_⟩
    intro w
    rw [tracePairingFunctional_apply,nativeAlbertProduct_wordEffect,← nativeWordProbability_eq_pairing,hw]

universe u

theorem generated_nativeAlbert_table_not_complex {n : ℕ}
    (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i)) (hg : GeneratesAlbert p) (ρ : Albert) :
    nativeWordProbability p ρ ∉ hilbertProjectiveTables.{u} ℂ n := by
  rintro ⟨H,hN,hI,hC,M,hM⟩
  let := hN
  let := hI
  let := hC
  exact algebraicProjective_not_matches_generating_atoms M.toAlgebraic p hp hg ρ hM

end AlbertSequential
