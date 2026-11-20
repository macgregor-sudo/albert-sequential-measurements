/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GeneralEJAWordTransport
public import JordanIdealProjections
public import Bridge.Atoms
public import NativeDiagonalProduct
public import NativeSupport
public import NativeTraceRiesz
public import AlgebraicProjectiveNoGo
public import WordRelabelling

/-! An actual Albert ideal of a general Euclidean Jordan algebra. Its
orthogonal projection is a unital Jordan map into the native Albert model;
its inclusion is generally nonunital. -/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

open scoped InnerProductSpace
open NativeAnalysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The indicated family generates the whole carrier as a unital Jordan algebra. -/
def GeneratesMenu {ι : Type*} (P : UnitalJordanProduct E) (p : ι → E) : Prop :=
  ∀ S : Submodule ℝ E, P.unit ∈ S →
    (∀ x ∈ S, ∀ y ∈ S, P.product x y ∈ S) → (∀ i, p i ∈ S) → ∀ x, x ∈ S

/-- A specific Jordan ideal identified with the compact native Albert algebra. -/
structure AlbertIdeal (P : UnitalJordanProduct E) where
  carrier : Submodule ℝ E
  isIdeal : P.IsJordanIdeal carrier
  identify : carrier ≃ₗ[ℝ] Albert
  product : ∀ x y : carrier,
    identify ⟨P.product x.val y.val, isIdeal _ y.property x.val⟩ =
      jordanMul (identify x) (identify y)
  unit : identify ⟨P.idealUnit carrier, P.idealUnit_mem carrier⟩ = albertUnit

namespace AlbertIdeal

variable {P : UnitalJordanProduct E} (I : P.AlbertIdeal)

def inclusion : Albert →ₗ[ℝ] E := I.carrier.subtype.comp I.identify.symm.toLinearMap

def projection : E →ₗ[ℝ] Albert :=
  I.identify.toLinearMap.comp (I.carrier.orthogonalProjectionOnto.toLinearMap)

theorem projection_unit : I.projection P.unit = albertUnit := I.unit

theorem inclusion_unit : I.inclusion albertUnit = P.idealUnit I.carrier := by
  rw [← I.unit]
  change (I.identify.symm (I.identify _)).val = _
  rw [LinearEquiv.symm_apply_apply]

theorem inclusion_mem (x : Albert) : I.inclusion x ∈ I.carrier :=
  (I.identify.symm x).property

theorem inclusion_projection_of_mem {x : E} (hx : x ∈ I.carrier) :
    I.inclusion (I.projection x) = x := by
  change (I.identify.symm (I.identify (I.carrier.orthogonalProjectionOnto x))).val = x
  rw [LinearEquiv.symm_apply_apply]
  exact I.carrier.starProjection_eq_self_iff.mpr hx

theorem projection_inclusion (x : Albert) : I.projection (I.inclusion x) = x := by
  have h : I.carrier.orthogonalProjectionOnto (I.inclusion x) = I.identify.symm x := by
    apply Subtype.ext
    exact I.carrier.starProjection_eq_self_iff.mpr (I.inclusion_mem x)
  change I.identify (I.carrier.orthogonalProjectionOnto (I.inclusion x)) = x
  rw [h, LinearEquiv.apply_symm_apply]

theorem projection_product
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z)) (x y : E) :
    I.projection (P.product x y) = jordanMul (I.projection x) (I.projection y) := by
  change I.identify (I.carrier.orthogonalProjectionOnto (P.product x y)) = _
  rw [P.idealProjection_product_subtype hinner I.carrier I.isIdeal]
  exact I.product _ _

theorem product_inclusion_left
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (x : Albert) (y : E) :
    P.product (I.inclusion x) y = I.inclusion (jordanMul x (I.projection y)) := by
  have hmem : P.product (I.inclusion x) y ∈ I.carrier := by
    rw [P.commutative]
    exact I.isIdeal _ (I.inclusion_mem x) y
  conv_lhs => rw [← I.inclusion_projection_of_mem hmem]
  rw [I.projection_product hinner, I.projection_inclusion]

theorem inclusion_product
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (x y : Albert) :
    P.product (I.inclusion x) (I.inclusion y) = I.inclusion (jordanMul x y) := by
  rw [I.product_inclusion_left hinner, I.projection_inclusion]

/-- A test supported in this ideal sends the entire state effect into the
same ideal, by precisely the native quadratic update of its local effect. -/
theorem quadraticRepresentation_inclusion
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (p : Albert) (x : E) :
    P.quadraticRepresentation (I.inclusion p) x = I.inclusion (quadraticMap p (I.projection x)) := by
  simp only [quadraticRepresentation_apply, quadraticMap, I.product_inclusion_left hinner,
    I.projection_inclusion, map_sub, two_smul, map_add]

/-- A primitive of the whole algebra either projects to zero or lies entirely
in the Albert ideal. This uses its orthogonal complement in the full algebra. -/
theorem primitive_projection_split
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    {p : E} (hp : P.IsPrimitive p) :
    I.projection p = 0 ∨ p = I.inclusion (I.projection p) := by
  let u := I.inclusion (I.projection p)
  have he : jordanMul (I.projection p) (I.projection p) = I.projection p := by
    rw [← I.projection_product hinner, hp.1]
  have hu : P.product u u = u := by
    dsimp [u]
    rw [I.inclusion_product hinner, he]
  have hup : P.product u p = u := by
    dsimp [u]
    rw [I.product_inclusion_left hinner, he]
  have hpu : P.product p u = u := by
    rw [P.commutative, hup]
  have hv : P.product (p - u) (p - u) = p - u := by
    simp only [map_sub, LinearMap.sub_apply, hp.1, hup, hpu, hu]
    abel
  have huv : P.product u (p - u) = 0 := by
    rw [map_sub, hup, hu, sub_self]
  rcases hp.2.2 u (p-u) hu hv huv (by abel) with hzero | hdiff
  · left
    have h := congrArg I.projection hzero
    simpa only [u, I.projection_inclusion, map_zero] using h
  · exact Or.inr (sub_eq_zero.mp hdiff)

/-- A nonzero component of a primitive is an atom of the native Albert
algebra. A decomposition into local orthogonal idempotents would lift. -/
theorem isAtom_projection_of_primitive
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    {p : E} (hp : P.IsPrimitive p) (hproj : I.projection p ≠ 0) :
    IsAtom (I.projection p) := by
  have hin : p = I.inclusion (I.projection p) :=
    (I.primitive_projection_split hinner hp).resolve_left hproj
  apply (NativeAnalysis.isAtom_iff_primitive _).mpr
  refine ⟨?_, hproj, ?_⟩
  · rw [← I.projection_product hinner, hp.1]
  · rintro ⟨x, y, hx, hy, hxn, hyn, hxy, hs⟩
    have hid₁ : P.product (I.inclusion x) (I.inclusion x) = I.inclusion x := by
      rw [I.inclusion_product hinner, hx]
    have hid₂ : P.product (I.inclusion y) (I.inclusion y) = I.inclusion y := by
      rw [I.inclusion_product hinner, hy]
    have horth : P.product (I.inclusion x) (I.inclusion y) = 0 := by
      rw [I.inclusion_product hinner, hxy, map_zero]
    have hsum : I.inclusion x + I.inclusion y = p := by
      rw [← map_add, ← hs, ← hin]
    rcases hp.2.2 _ _ hid₁ hid₂ horth hsum with h | h
    · exact hxn (by simpa only [I.projection_inclusion, map_zero] using congrArg I.projection h)
    · exact hyn (by simpa only [I.projection_inclusion, map_zero] using congrArg I.projection h)

theorem generatesAlbert_projected_nonzero {ι : Type*}
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (p : ι → E) (hgen : P.GeneratesMenu p) :
    GeneratesAlbert (fun i : {i // I.projection (p i) ≠ 0} => I.projection (p i.val)) := by
  intro a B hB
  have hmem : I.inclusion a ∈ B.carrier.comap I.projection := by
    apply hgen (B.carrier.comap I.projection)
    · change I.projection P.unit ∈ B.carrier
      rw [I.projection_unit]
      exact B.unit_mem
    · intro x hx y hy
      change I.projection (P.product x y) ∈ B.carrier
      rw [I.projection_product hinner]
      exact B.product_mem _ hx _ hy
    · intro i
      change I.projection (p i) ∈ B.carrier
      by_cases hz : I.projection (p i) = 0
      · rw [hz]
        exact B.carrier.zero_mem
      · exact hB ⟨i, hz⟩
  change I.projection (I.inclusion a) ∈ B.carrier at hmem
  rwa [I.projection_inclusion] at hmem

private theorem exists_albert_test_positive {ι : Type*} (p : ι → Albert)
    (hp : ∀ i, IsAtom (p i)) (hgen : GeneratesAlbert p) (ρ : Albert) (hρ : IsDensity ρ) :
    ∃ i, 0 < tracePairing ρ (p i) := by
  by_contra hnone
  have hzero (i : ι) : tracePairing ρ (p i) = 0 :=
    le_antisymm (le_of_not_gt fun h => hnone ⟨i, h⟩)
      (tracePairing_positive_nonnegative ρ _ hρ.1 (isPositive_idempotent _ (hp i).1))
  obtain ⟨g, d, hg⟩ := nativeDiagonalization ρ
  have hsum : ∑ k : Fin 3, d k = 1 := by
    rw [← diagonal_trace, ← hg, g.preserves_trace, hρ.2]
  obtain ⟨k, hk⟩ : ∃ k, d k ≠ 0 := by
    by_contra hz
    have hd (k : Fin 3) : d k = 0 := not_not.mp (fun h => hz ⟨k, h⟩)
    simp [hd] at hsum
  let r := g.linearEquiv.symm (diagAtom k)
  have hr : IsAtom r := nativeAutomorphism_isAtom (nativeAutomorphismInverse g)
    (diagAtom k) (diagAtom_isAtom k)
  have hgr : g.linearEquiv r = diagAtom k := g.linearEquiv.apply_symm_apply _
  have hz (i : ι) : tracePairing (p i) r = 0 := by
    have hm := (native_positive_zero_pairing_support (p i) ρ (hp i).1 hρ.1 (hzero i)).1
    rw [jordanMul_comm] at hm
    have hdiag := congrArg g.linearEquiv hm
    rw [g.preserves_product, hg, map_zero, jordanMul_diagonal] at hdiag
    have hcoord : (g.linearEquiv (p i)).1 k = 0 :=
      (mul_eq_zero.mp (congrArg (fun z : Albert => z.1 k) hdiag)).resolve_left hk
    have hquad := quadraticMap_diagAtom k (g.linearEquiv (p i))
    rw [quadraticMap_atom _ _ (diagAtom_isAtom k), hcoord, zero_smul] at hquad
    have hq0 : tracePairing (diagAtom k) (g.linearEquiv (p i)) = 0 :=
      (smul_eq_zero.mp hquad).resolve_right (by
        intro h
        have ht := (diagAtom_isAtom k).2
        rw [h, albertTrace_zero] at ht
        exact zero_ne_one ht)
    rw [tracePairing_comm, ← g.map_tracePairing, hgr]
    exact hq0
  have hline (i : ι) : p i ∈ (lineSubalgebra r hr).carrier := by
    rw [mem_lineSubalgebra_iff]
    have horth := (native_positive_zero_pairing_support r (p i) hr.1
      (isPositive_idempotent _ (hp i).1) (hz i)).1
    rw [horth, tracePairing_comm, hz i, zero_smul]
  obtain ⟨a, ha⟩ := atom_to_diagAtom0 r hr
  let x := a.linearEquiv.symm realConnector01
  have hx := (mem_lineSubalgebra_iff_idem r hr x).mp (hgen x (lineSubalgebra r hr) hline)
  have hcontr := congrArg a.linearEquiv hx
  simp only [a.preserves_product, ha, x, LinearEquiv.apply_symm_apply,
    jordanMul_diagAtom0_realConnector01, jordanMul_smul_right, smul_smul] at hcontr
  have hne : realConnector01 ≠ 0 := by
    intro h
    have h' := congrArg (fun z : Albert => (z.2 0).1.re) h
    change (realConnector01.2 0).1.re = 0 at h'
    simp [realConnector01, upperSlot, octonionScalar] at h'
  have heq : ((1 / 2 * (1 / 2) - 1 / 2 : ℝ) • realConnector01) = 0 := by
    rw [sub_smul, hcontr, sub_self]
  rcases smul_eq_zero.mp heq with h | h
  · norm_num at h
  · exact hne h

private theorem projection_wordEffect {ι : Type*}
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (p : ι → E) (w : Word ι) :
    I.projection (P.sequentialWordEffect p w) = nativeWordEffect (I.projection ∘ p) w := by
  induction w with
  | nil => exact I.projection_unit
  | cons a w ih =>
    have hout : I.projection (P.sequentialOutcome p a) = nativeOutcome (I.projection ∘ p) a := by
      rcases a with ⟨i, b⟩
      cases b <;> simp [sequentialOutcome, nativeOutcome, I.projection_unit]
    rw [sequentialWordEffect, nativeWordEffect]
    simp only [quadraticRepresentation_apply, map_sub, map_add, I.projection_product hinner,
      hout, ih, quadraticMap, two_smul]

private theorem exists_conditionedModel {ι A : Type*}
    [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
    [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData ι A) (j : ι) (hj : 0 < M.probability [(j, true)]) :
    ∃ N : AlgebraicProjectiveData ι A,
      ∀ w, N.probability w = M.probability ((j, true) :: w) / M.probability [(j, true)] := by
  let q := M.projection j
  let mass := M.probability [(j, true)]
  have hq : star q = q := M.selfAdjoint j
  have hqq : q * q = q := M.idempotent j
  have hm : mass = M.state q := by
    change M.state (wordOperator M.projection [(j, true)]) = M.state q
    rw [wordOperator_singleton M.projection M.idempotent M.selfAdjoint]
    rfl
  let compressed : A →ₗ[ℝ] ℝ :=
    { toFun := fun x => M.state (q * x * q)
      map_add' := fun x y => by rw [mul_add, add_mul, map_add]
      map_smul' := fun r x => by rw [mul_smul_comm, smul_mul_assoc, map_smul]; rfl }
  let N : AlgebraicProjectiveData ι A :=
    { M with
      state := mass⁻¹ • compressed
      state_unit := by
        change mass⁻¹ * M.state (q * 1 * q) = 1
        rw [mul_one, hqq, ← hm]
        exact inv_mul_cancel₀ hj.ne'
      state_star := fun x => by
        change mass⁻¹ * M.state (q * star x * q) = mass⁻¹ * M.state (q * x * q)
        rw [← M.state_star (q * x * q), star_mul, star_mul, hq, mul_assoc]
      state_positive := fun x => by
        change 0 ≤ mass⁻¹ * M.state (q * (star x * x) * q)
        have h : q * (star x * x) * q = star (x * q) * (x * q) := by
          simp only [star_mul, hq, mul_assoc]
        rw [h]
        exact mul_nonneg (inv_nonneg.mpr hj.le) (M.state_positive _) }
  refine ⟨N, fun w => ?_⟩
  rw [AlgebraicProjectiveData.probability, AlgebraicProjectiveData.probability,
    wordOperator_cons M.projection M.selfAdjoint]
  change mass⁻¹ * M.state (q * wordOperator M.projection w * q) =
    M.state (q * wordOperator M.projection w * q) / mass
  rw [div_eq_inv_mul]

/-- Positive weight of an actual Albert ideal excludes matching for a
generating family of primitive tests, with harmless zero tests allowed. -/
theorem no_algebraicModel_of_positive_weight {ι A : Type*}
    [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
    [SMulCommClass ℝ A A] [StarModule ℝ A]
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (p : ι → E) (hp : ∀ i, p i = 0 ∨ P.IsPrimitive (p i))
    (hgen : P.GeneratesMenu p)
    (f : E →ₗ[ℝ] ℝ) (hpos : ∀ x, 0 ≤ f (P.product x x))
    (hweight : 0 < f (P.idealUnit I.carrier))
    (M : AlgebraicProjectiveData ι A) :
    ¬ ∀ w, M.probability w = f (P.sequentialWordEffect p w) := by
  intro hmatch
  let J := {i : ι // I.projection (p i) ≠ 0}
  let pI : J → E := p ∘ Subtype.val
  let q : J → Albert := I.projection ∘ pI
  have hprimitive (i : J) : P.IsPrimitive (pI i) := by
    apply (hp i.val).resolve_left
    intro hz
    exact i.property (by rw [hz, map_zero])
  have hq (i : J) : IsAtom (q i) :=
    I.isAtom_projection_of_primitive hinner (hprimitive i) i.property
  have hin (i : J) : pI i = I.inclusion (q i) :=
    (I.primitive_projection_split hinner (hprimitive i)).resolve_left i.property
  have hqgen : GeneratesAlbert q := I.generatesAlbert_projected_nonzero hinner p hgen
  let weight := f (P.idealUnit I.carrier)
  let fI := weight⁻¹ • f.comp I.inclusion
  have hfpos (x : Albert) : 0 ≤ fI (jordanMul x x) := by
    change 0 ≤ weight⁻¹ * f (I.inclusion (jordanMul x x))
    rw [← I.inclusion_product hinner]
    exact mul_nonneg (inv_nonneg.mpr hweight.le) (hpos _)
  have hfnorm : fI albertUnit = 1 := by
    change weight⁻¹ * f (I.inclusion albertUnit) = 1
    rw [I.inclusion_unit]
    exact inv_mul_cancel₀ hweight.ne'
  let ρ := traceRepresentative fI
  have hρ : IsDensity ρ := NativeAnalysis.normalized_positiveFunctional_density fI hfpos hfnorm
  obtain ⟨j, hj⟩ := exists_albert_test_positive q hq hqgen ρ hρ
  rw [traceRepresentative_pairing] at hj
  change 0 < weight⁻¹ * f (I.inclusion (q j)) at hj
  have hjpos : 0 < f (I.inclusion (q j)) :=
    pos_of_mul_pos_right hj (inv_nonneg.mpr hweight.le)
  let M' := M.comap (Subtype.val : J → ι)
  have hrestricted (w : Word J) : M'.probability w = f (P.sequentialWordEffect pI w) := by
    have heff (u : Word J) :
        P.sequentialWordEffect p (relabelWord Subtype.val u) = P.sequentialWordEffect pI u := by
      induction u with
      | nil => rfl
      | cons a u ih =>
        rw [relabelWord_cons, sequentialWordEffect, sequentialWordEffect, ih]
        rfl
    rw [AlgebraicProjectiveData.comap_probability, hmatch, heff]
  have hprefix (w : Word J) :
      M'.probability ((j, true) :: w) = f (I.inclusion (q j)) * nativeWordProbability q (q j) w := by
    rw [hrestricted, sequentialWordEffect]
    change f (P.quadraticRepresentation (pI j) (P.sequentialWordEffect pI w)) = _
    rw [hin j, I.quadraticRepresentation_inclusion hinner, I.projection_wordEffect hinner,
      quadraticMap_atom _ _ (hq j), ← nativeWordProbability_eq_pairing, map_smul, map_smul]
    change nativeWordProbability q (q j) w * f (I.inclusion (q j)) = _
    exact mul_comm _ _
  have hsingle : M'.probability [(j, true)] = f (I.inclusion (q j)) := by
    rw [hprefix]
    change _ * albertTrace (q j) = _
    rw [(hq j).2, mul_one]
  have hMpos : 0 < M'.probability [(j, true)] := by rwa [hsingle]
  obtain ⟨conditioned, hconditioned⟩ := exists_conditionedModel M' j hMpos
  apply algebraicProjective_not_matches_generating_atoms conditioned q hq hqgen (q j)
  intro w
  rw [hconditioned, hprefix, hsingle]
  exact mul_div_cancel_left₀ _ hjpos.ne'

/-- Core Theorem 4.11(b) on the generated carrier. Trivial tests and tests
with a primitive complement are retained as labels after changing polarity. -/
theorem no_algebraicModel_of_positive_weight_of_primitiveTests {ι A : Type*}
    [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
    [SMulCommClass ℝ A A] [StarModule ℝ A]
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (p : ι → E)
    (hp : ∀ i, p i = 0 ∨ p i = P.unit ∨ P.IsPrimitive (p i) ∨ P.IsPrimitive (P.unit - p i))
    (hgen : P.GeneratesMenu p)
    (f : E →ₗ[ℝ] ℝ) (hpos : ∀ x, 0 ≤ f (P.product x x))
    (hweight : 0 < f (P.idealUnit I.carrier))
    (M : AlgebraicProjectiveData ι A) :
    ¬ ∀ w, M.probability w = f (P.sequentialWordEffect p w) := by
  classical
  intro hmatch
  let flip (i : ι) : Bool := if p i = 0 ∨ P.IsPrimitive (p i) then false else true
  let p' (i : ι) : E := if flip i then P.unit - p i else p i
  have hp' (i : ι) : p' i = 0 ∨ P.IsPrimitive (p' i) := by
    by_cases h : p i = 0 ∨ P.IsPrimitive (p i)
    · have hflip : flip i = false := ite_eq_left h
      simpa only [p', hflip, Bool.false_eq_true, ite_false] using h
    · have hc : p i = P.unit ∨ P.IsPrimitive (P.unit - p i) := by
        rcases hp i with hzero | hunit | hprimitive | hcomplement
        · exact (h (Or.inl hzero)).elim
        · exact Or.inl hunit
        · exact (h (Or.inr hprimitive)).elim
        · exact Or.inr hcomplement
      have hflip : flip i = true := ite_eq_right h
      have hp'eq : p' i = P.unit - p i := by simp [p', hflip]
      rcases hc with hunit | hcomplement
      · left
        rw [hp'eq, hunit, sub_self]
      · right
        rw [hp'eq]
        exact hcomplement
  have hgen' : P.GeneratesMenu p' := by
    intro S hunit hclosed hmem x
    refine hgen S hunit hclosed (fun i => ?_) x
    cases hflip : flip i with
    | false => simpa [p', hflip] using hmem i
    | true =>
      have hi : P.unit - p i ∈ S := by simpa [p', hflip] using hmem i
      simpa only [sub_sub_cancel] using S.sub_mem hunit hi
  let changeOutcome (a : Outcome ι) : Outcome ι :=
    (a.1, if flip a.1 then !a.2 else a.2)
  let q' (i : ι) : A := algebraicOutcome M.projection (changeOutcome (i, true))
  have hqid (i : ι) : q' i * q' i = q' i :=
    algebraicOutcome_idempotent M.projection M.idempotent _
  have hqstar (i : ι) : star (q' i) = q' i :=
    algebraicOutcome_star M.projection M.selfAdjoint _
  have houtcome (a : Outcome ι) :
      P.sequentialOutcome p' a = P.sequentialOutcome p (changeOutcome a) := by
    rcases a with ⟨i, b⟩
    cases hflip : flip i <;> cases b <;>
      simp [sequentialOutcome, changeOutcome, p', hflip, sub_sub_cancel]
  have halgebraic (a : Outcome ι) :
      algebraicOutcome q' a = algebraicOutcome M.projection (changeOutcome a) := by
    rcases a with ⟨i, b⟩
    cases hflip : flip i <;> cases b <;>
      simp [algebraicOutcome, q', changeOutcome, hflip, sub_sub_cancel]
  have heff (w : Word ι) :
      P.sequentialWordEffect p' w = P.sequentialWordEffect p (w.map changeOutcome) := by
    induction w with
    | nil => rfl
    | cons a w ih =>
      rw [List.map_cons, sequentialWordEffect, sequentialWordEffect, houtcome, ih]
  have hop (w : Word ι) : wordOperator q' w = wordOperator M.projection (w.map changeOutcome) := by
    induction w with
    | nil => rfl
    | cons a w ih =>
      rw [List.map_cons, wordOperator_cons q' hqstar,
        wordOperator_cons M.projection M.selfAdjoint, ih, halgebraic]
  let M' : AlgebraicProjectiveData ι A :=
    { M with projection := q', idempotent := hqid, selfAdjoint := hqstar }
  apply I.no_algebraicModel_of_positive_weight hinner p' hp' hgen' f hpos hweight M'
  intro w
  change M.state (wordOperator q' w) = f (P.sequentialWordEffect p' w)
  rw [hop, heff]
  exact hmatch _

include I in
/-- An actual Albert ideal of the ambient EJA supplies four idempotent tests
and one canonical state whose table has no algebraic projective model. -/
theorem exists_four_test_obstruction_of_albertIdeal
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z)) :
    ∃ (p : Fin 4 → E) (ρ : E),
      (∀ i, P.product (p i) (p i) = p i) ∧
      P.IsCanonicalDensity (P.formallyReal_of_associative_inner hinner) ρ ∧
      ∀ (A : Type*) [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
        [SMulCommClass ℝ A A] [StarModule ℝ A] (M : AlgebraicProjectiveData (Fin 4) A),
        ¬ ∀ w, M.probability w =
          P.canonicalTraceOfFormallyReal (P.formallyReal_of_associative_inner hinner)
            (P.sequentialBranchState p ρ w) := by
  let hfr := P.formallyReal_of_associative_inner hinner
  let p : Fin 4 → E := I.inclusion ∘ fixedS
  let ρJ : Albert := (1 / 3 : ℝ) • albertUnit
  let f := (tracePairingFunctional ρJ).comp I.projection
  have hposJ : IsPositive ρJ := isPositive_smul _ _ (by norm_num)
    (isPositive_idempotent _ (jordanMul_albertUnit_left _))
  have hp (i : Fin 4) : P.product (p i) (p i) = p i := by
    change P.product (I.inclusion (fixedS i)) (I.inclusion (fixedS i)) = I.inclusion (fixedS i)
    rw [I.inclusion_product hinner, (fixedS_isAtom i).1]
  have hf (x : E) : 0 ≤ f (P.product x x) := by
    change 0 ≤ tracePairing ρJ (I.projection (P.product x x))
    rw [I.projection_product hinner]
    exact tracePairing_positive_nonnegative _ _ hposJ (isPositive_square _)
  have hunit : f P.unit = 1 := by
    change tracePairing ρJ (I.projection P.unit) = 1
    rw [I.projection_unit, tracePairing_unit_right]
    change albertTrace ((1 / 3 : ℝ) • albertUnit) = 1
    rw [albertTrace_smul]
    norm_num [albertTrace, albertUnit]
  have hgen : GeneratesAlbert fixedS := by
    apply (fourPointInvariant_pos_iff fixedS fixedS_isAtom).mp
    rw [fourPointInvariant_fixedS]
    norm_num
  have htests : I.projection ∘ p = fixedS := funext fun i => I.projection_inclusion (fixedS i)
  let ρ := P.canonicalTraceRepresentative hfr f
  refine ⟨p, ρ, hp, P.normalized_positiveFunctional_density hfr f hf hunit, ?_⟩
  intro A _ _ _ _ _ _ M hmatch
  apply algebraicProjective_not_matches_generating_atoms M fixedS fixedS_isAtom hgen ρJ
  intro w
  have h := hmatch w
  rw [P.canonicalTrace_sequentialBranchState] at h
  change M.probability w =
    P.canonicalTraceFormOfFormallyReal hfr (P.canonicalTraceRepresentative hfr f)
      (P.sequentialWordEffect p w) at h
  rw [P.canonicalTraceRepresentative_pairing] at h
  change M.probability w = tracePairing ρJ (I.projection (P.sequentialWordEffect p w)) at h
  rwa [I.projection_wordEffect hinner, htests, ← nativeWordProbability_eq_pairing] at h

end AlbertIdeal
end AlbertSequential.UnitalJordanProduct
