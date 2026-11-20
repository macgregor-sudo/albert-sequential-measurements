/- SPDX-License-Identifier: Apache-2.0 -/
module
public import HilbertTraceNorm
public import HilbertTraceQuaternionicInstrument

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.HilbertTrace

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (b : HilbertBasis ι ℝ H) (S : RightQuaternionicHilbertStructure H)

local notation "Carrier" => quaternionicSignedFiniteTrace b S
local notation "qTrace" => quaternionicSignedTrace b S
local notation "incl" => quaternionicCarrierInclusion b S

/-- The spectral positive and negative parts are right-linear, and the
quaternionic trace measures their exact signed mass. -/
theorem quaternionic_signedTrace_orthogonal_decomposition (X : Carrier)
    (D : H →L[ℝ] H) (hD : D.IsPositive) (hDsq : D * D = X.val * X.val) :
    ∃ U V : Carrier, U.val.IsPositive ∧ V.val.IsPositive ∧ V.val * U.val = 0 ∧
      X = U - V ∧ qTrace U + qTrace V = (1 / 4 : ℝ) * (positiveTrace b D).toReal := by
  obtain ⟨U, V, hU, hV, hVU, hX, hDsum, hMass⟩ :=
    real_signedTrace_orthogonal_decomposition b (incl X) D hD hDsq
  let A := S.toOperatorStructure.operatorAlgebra
  have hDa : D ∈ A := quaternionic_modulus_mem_operatorAlgebra S ⟨X.val, X.property.2⟩ D hD hDsq
  have hXval : X.val = U.val - V.val := congrArg Subtype.val hX
  have hU2 : D + X.val = (2 : ℝ) • U.val := by
    rw [hDsum, hXval, two_smul]
    abel
  have hV2 : D - X.val = (2 : ℝ) • V.val := by
    rw [hDsum, hXval, two_smul]
    abel
  have hUa : U.val ∈ A := by
    have h := A.smul_mem (A.add_mem hDa X.property.2) (1 / 2 : ℝ)
    rw [hU2, smul_smul] at h
    norm_num at h
    exact h
  have hVa : V.val ∈ A := by
    have h := A.smul_mem (A.sub_mem hDa X.property.2) (1 / 2 : ℝ)
    rw [hV2, smul_smul] at h
    norm_num at h
    exact h
  let u : Carrier := ⟨U.val, U.property, hUa⟩
  let v : Carrier := ⟨V.val, V.property, hVa⟩
  refine ⟨u, v, hU, hV, hVU, Subtype.ext hXval, ?_⟩
  change (1 / 4 : ℝ) * signedTrace b U + (1 / 4 : ℝ) * signedTrace b V = _
  rw [← mul_add, hMass]

theorem quaternionic_signedTrace_orthogonal_parts_minimal {T U V X Y : Carrier}
    (hU : U.val.IsPositive) (hV : V.val.IsPositive) (hVU : V.val * U.val = 0)
    (hT : T = U - V) (hX : X.val.IsPositive) (hY : Y.val.IsPositive) (hXY : T = X - Y) :
    qTrace U + qTrace V ≤ qTrace X + qTrace Y := by
  have h := signedTrace_orthogonal_parts_minimal b (realSandwich b) (fun _ _ => rfl)
    (fun _ hP => real_projection_trace_split b hP)
    (T := incl T) (U := incl U) (V := incl V) (X := incl X) (Y := incl Y)
    hU hV hVU (by rw [hT, map_sub]) hX hY (by rw [hXY, map_sub])
  change (1 / 4 : ℝ) * signedTrace b (incl U) + (1 / 4 : ℝ) * signedTrace b (incl V) ≤
    (1 / 4 : ℝ) * signedTrace b (incl X) + (1 / 4 : ℝ) * signedTrace b (incl Y)
  rw [← mul_add, ← mul_add]
  exact mul_le_mul_of_nonneg_left h (by norm_num)

def quaternionicSignedTraceMass : SignedTraceMassData Carrier where
  positive := {X | X.val.IsPositive}
  trace := qTrace
  zero_positive := ContinuousLinearMap.isPositive_zero
  add_positive := fun _ hx _ hy => hx.add hy
  smul_positive := fun _ hr _ hX => hX.smul_of_nonneg hr
  positive_trace := fun X hX hx =>
    (quaternionic_signedTrace_pos_iff b S hX).mpr (fun h => hx (Subtype.ext h))
  exists_minimum := by
    intro X
    have hs := signedFiniteTrace_isSelfAdjoint b (incl X)
    have hP : (X.val * X.val).IsPositive := by
      have h := ContinuousLinearMap.isPositive_adjoint_comp_self X.val
      change (star X.val * X.val).IsPositive at h
      have hv : star X.val = X.val := hs.star_eq
      rwa [hv] at h
    obtain ⟨U, V, hU, hV, hVU, hX, _⟩ := quaternionic_signedTrace_orthogonal_decomposition b S X
      (realPositiveSquareRoot _ hP) (realPositiveSquareRoot_positive_and_square _ hP).1
      (realPositiveSquareRoot_positive_and_square _ hP).2
    exact ⟨U, V, hU, hV, hX, fun p hp n hn hx =>
      quaternionic_signedTrace_orthogonal_parts_minimal b S hU hV hVU hX hp hn hx⟩

theorem quaternionic_traceNorm_eq_trace_modulus (X : (quaternionicSignedTraceMass b S).WithNorm)
    (D : H →L[ℝ] H) (hD : D.IsPositive)
    (hDsq : D * D = (show Carrier from X).val * (show Carrier from X).val) :
    ‖X‖ = (1 / 4 : ℝ) * (positiveTrace b D).toReal := by
  change (quaternionicSignedTraceMass b S).mass X = _
  obtain ⟨U, V, hU, hV, hVU, hX, hmass⟩ := quaternionic_signedTrace_orthogonal_decomposition b S X D hD hDsq
  rw [← hmass]
  apply le_antisymm ((quaternionicSignedTraceMass b S).mass_le hU hV hX)
  obtain ⟨p, n, hp, hn, hx, hm⟩ := (quaternionicSignedTraceMass b S).minimum X
  rw [hm]
  exact quaternionic_signedTrace_orthogonal_parts_minimal b S hU hV hVU hX hp hn hx

end AlbertSequential.HilbertTrace
