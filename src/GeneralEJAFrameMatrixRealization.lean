/- SPDX-License-Identifier: Apache-2.0 -/
module
public import GeneralEJAFrameSparseProducts

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : UnitalJordanProduct E) (hfr : P.FormallyReal) {n : ℕ} (c : Fin n → E)
    {r s t : Fin n} (C : P.PeirceTriangleCoordinates hfr c r s t)

local notation "W" => P.frameOffDiagonalSpace c
local notation "Mat" => Matrix (Fin n) (Fin n) (W r t)
local notation "MJ" => P.peirceCoefficientMatrixJordan hfr c C
local notation "edge" => P.peirceCoefficientMatrixEdge hfr c C

structure FaithfulPeirceHermitianMatrixMap where
  map : E →ₗ[ℝ] Mat
  injective : Function.Injective map
  hermitian : ∀ x, P.PeirceCoefficientHermitian hfr c C (map x)
  unit : map P.unit = Matrix.diagonal (fun _ : Fin n => C.unit)
  jordan : ∀ x y, map (P.product x y) = MJ (map x) (map y)

section Product

variable (hc : ∀ j, P.IsPrimitive (c j)) (hor : ∀ i j, i ≠ j → P.product (c i) (c j) = 0)
    (hunit : ∑ j, c j = P.unit)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (hrs : r < s) (hst : s < t)
    (D : P.PeirceIncreasingFrameChart hfr c C hc hunit hrs hst)

local notation "F" => P.peirceFrameMatrix hfr c C hc hor hunit hinner hrs hst D
local notation "onDiag" => P.peirceFrameMatrix_on_primitive hfr c C hc hor hunit hinner hrs hst D
local notation "onEdge" => P.peirceFrameMatrix_on_edge hfr c C hc hor hunit hinner hrs hst D

private theorem frameMatrix_diag_pair (i j : Fin n) :
    F (P.product (c i) (c j)) = MJ (F (c i)) (F (c j)) := by
  rw [onDiag i, onDiag j, P.peirceCoefficientMatrixJordan_diagonal_pair]
  by_cases h : i = j
  · subst j
    rw [ite_eq_left rfl, (hc i).1, onDiag i]
  · rw [ite_eq_right h, hor i j h, map_zero]

private theorem frameMatrix_diag_edge {i j : Fin n} (hij : i < j) (k : Fin n) (x : W i j) :
    F (P.product (c k) x.val) = MJ (F (c k)) (F x.val) := by
  rw [onDiag k, onEdge hij x, P.peirceCoefficientMatrixJordan_diagonal_edge hfr c C hij]
  have h := (P.mem_frameJointSpace c _).mp x.property k
  by_cases hk : k = i ∨ k = j
  · rw [frameOffDiagonalPattern, ite_eq_left hk] at h
    rw [h, map_smul, onEdge hij x, ite_eq_left hk]
  · rw [frameOffDiagonalPattern, ite_eq_right hk, zero_smul] at h
    rw [h, map_zero, ite_eq_right hk]

variable (hform : P.peirceIncreasingChartPreservesTraceForm hfr c C hc hunit hrs hst D)

include hform in
private theorem frameMatrix_same_edge {i j : Fin n} (hij : i < j) (x y : W i j) :
    F (P.product x.val y.val) = MJ (F x.val) (F y.val) := by
  rw [P.peirceIncreasingChart_same_edge hfr c C hc hor hunit hrs hst D hform hij,
    map_smul, map_add, onDiag i, onDiag j, onEdge hij x, onEdge hij y, P.peirceCoefficientMatrixJordan_same_edge hfr c C hij]

private theorem frameMatrix_chain {i j k : Fin n} (hij : i < j) (hjk : j < k) (x : W i j) (y : W j k) :
    F (P.product x.val y.val) = MJ (F x.val) (F y.val) := by
  let xy := P.frameOffDiagonal_scaledProduct c (fun a => (hc a).1) hunit
    (ne_of_lt hij) (ne_of_lt (lt_trans hij hjk)) (ne_of_lt hjk) x y
  have hxy : P.product x.val y.val = (1 / 2 : ℝ) • xy.val := by
    change P.product x.val y.val = (1 / 2 : ℝ) • ((2 : ℝ) • P.product x.val y.val)
    module
  rw [hxy, map_smul, onEdge (lt_trans hij hjk) xy, onEdge hij x, onEdge hjk y,
    P.peirceCoefficientMatrixJordan_edge_chain hfr c C hij hjk]
  exact congrArg (fun a => (1 / 2 : ℝ) • edge i k a) (D.product hij hjk x y)

include hform in
private theorem frameMatrix_shared_first {i j k : Fin n}
    (hij : i < j) (hjk : j < k) (x : W i j) (z : W i k) :
    F (P.product x.val z.val) = MJ (F x.val) (F z.val) := by
  let xz := P.frameOffDiagonal_scaledLeftReverse c (fun a => (hc a).1) hunit hij hjk x z
  have hxz : P.product x.val z.val = (1 / 2 : ℝ) • xz.val := by
    change P.product x.val z.val = (1 / 2 : ℝ) • ((2 : ℝ) • P.product x.val z.val)
    module
  rw [hxz, map_smul, onEdge hjk xz, onEdge hij x, onEdge (lt_trans hij hjk) z,
    P.peirceCoefficientMatrixJordan_edges_same_first hfr c C hij hjk]
  exact congrArg (fun a => (1 / 2 : ℝ) • edge j k a)
    (P.peirceIncreasingChart_left_reverse hfr c C hc hunit hrs hst D hform hij hjk x z)

include hform in
private theorem frameMatrix_shared_last {i j k : Fin n}
    (hij : i < j) (hjk : j < k) (z : W i k) (y : W j k) :
    F (P.product z.val y.val) = MJ (F z.val) (F y.val) := by
  let zy := P.frameOffDiagonal_scaledRightReverse c (fun a => (hc a).1) hunit hij hjk z y
  have hzy : P.product z.val y.val = (1 / 2 : ℝ) • zy.val := by
    change P.product z.val y.val = (1 / 2 : ℝ) • ((2 : ℝ) • P.product z.val y.val)
    module
  rw [hzy, map_smul, onEdge hij zy, onEdge (lt_trans hij hjk) z, onEdge hjk y,
    P.peirceCoefficientMatrixJordan_edges_same_last hfr c C hij hjk]
  exact congrArg (fun a => (1 / 2 : ℝ) • edge i j a)
    (P.peirceIncreasingChart_right_reverse hfr c C hc hunit hrs hst D hform hij hjk z y)

private theorem frameMatrix_swap {x y : E} (h : F (P.product y x) = MJ (F y) (F x)) :
    F (P.product x y) = MJ (F x) (F y) := by
  rw [P.commutative x y, P.peirceCoefficientMatrixJordan_comm hfr c C (F x) (F y)]
  exact h

include hform in
private theorem frameMatrix_edges {i j k l : Fin n} (hij : i < j) (hkl : k < l)
    (x : W i j) (y : W k l) :
    F (P.product x.val y.val) = MJ (F x.val) (F y.val) := by
  by_cases hik : i = k
  · subst k
    rcases lt_trichotomy j l with hjl | rfl | hlj
    · exact P.frameMatrix_shared_first hfr c C hc hor hunit hinner hrs hst D hform hij hjl x y
    · exact P.frameMatrix_same_edge hfr c C hc hor hunit hinner hrs hst D hform hij x y
    · exact P.frameMatrix_swap hfr c C hc hor hunit hinner hrs hst D
        (P.frameMatrix_shared_first hfr c C hc hor hunit hinner hrs hst D hform hkl hlj y x)
  by_cases hjl : j = l
  · subst l
    rcases lt_or_gt_of_ne hik with hik' | hki
    · exact P.frameMatrix_shared_last hfr c C hc hor hunit hinner hrs hst D hform hik' hkl x y
    · exact P.frameMatrix_swap hfr c C hc hor hunit hinner hrs hst D
        (P.frameMatrix_shared_last hfr c C hc hor hunit hinner hrs hst D hform hki hij y x)
  by_cases hjk : j = k
  · subst k
    exact P.frameMatrix_chain hfr c C hc hor hunit hinner hrs hst D hij hkl x y
  by_cases hil : i = l
  · subst l
    exact P.frameMatrix_swap hfr c C hc hor hunit hinner hrs hst D
      (P.frameMatrix_chain hfr c C hc hor hunit hinner hrs hst D hkl hij y x)
  have hz : P.product x.val y.val = 0 := by
    apply P.frameOffDiagonal_product_eq_zero_of_disjoint c (fun a => (hc a).1) hunit
      (ne_of_lt hij) (ne_of_lt hkl) _ x.property y.property
    rintro q ⟨ha, hb⟩
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact hik (ha.symm.trans hb)
    · exact hil (ha.symm.trans hb)
    · exact hjk (ha.symm.trans hb)
    · exact hjl (ha.symm.trans hb)
  rw [hz, map_zero, onEdge hij x, onEdge hkl y, P.peirceCoefficientMatrixJordan_edges_disjoint hfr c C hik hil hjk hjl]

include hform in
theorem peirceFrameMatrix_product (x y : E) : F (P.product x y) = MJ (F x) (F y) := by
  let L := P.product.compr₂ₛₗ F
  let R := (MJ).compl₁₂ F F
  have hLR : L = R := by
    apply P.framePeirce_linear_ext c hc hor hunit hinner
    · intro i
      apply P.framePeirce_linear_ext c hc hor hunit hinner
      · exact P.frameMatrix_diag_pair hfr c C hc hor hunit hinner hrs hst D i
      · intro j k hjk z hz
        exact P.frameMatrix_diag_edge hfr c C hc hor hunit hinner hrs hst D hjk i ⟨z, hz⟩
    · intro i j hij z hz
      apply P.framePeirce_linear_ext c hc hor hunit hinner
      · intro k
        exact P.frameMatrix_swap hfr c C hc hor hunit hinner hrs hst D
          (P.frameMatrix_diag_edge hfr c C hc hor hunit hinner hrs hst D hij k ⟨z, hz⟩)
      · intro k l hkl u hu
        exact P.frameMatrix_edges hfr c C hc hor hunit hinner hrs hst D hform hij hkl ⟨z, hz⟩ ⟨u, hu⟩
  exact LinearMap.congr_fun (LinearMap.congr_fun hLR x) y

include hor hinner hform in
theorem exists_faithfulPeirceHermitianMatrixMap :
    Nonempty (P.FaithfulPeirceHermitianMatrixMap hfr c C) :=
  ⟨{
    map := F
    injective := P.peirceFrameMatrix_injective hfr c C hc hor hunit hinner hrs hst D
    hermitian := P.peirceFrameMatrix_hermitian hfr c C hc hor hunit hinner hrs hst D
    unit := P.peirceFrameMatrix_unit hfr c C hc hor hunit hinner hrs hst D
    jordan := P.peirceFrameMatrix_product hfr c C hc hor hunit hinner hrs hst D hform }⟩

end Product

theorem exists_faithfulPeirceHermitianMatrixMap_of_simple
    (hc : ∀ j, P.IsPrimitive (c j)) (hor : ∀ i j, i ≠ j → P.product (c i) (c j) = 0)
    (hunit : ∑ j, c j = P.unit)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (hsimple : P.IsSimpleJordan) (hrs : r < s) (hst : s < t)
    (hfirst : ∀ j, j ≠ r → j ≠ s → j ≠ t → t < j) :
    ∃ C₀ : P.PeirceTriangleCoordinates (P.formallyReal_of_associative_inner hinner) c r s t,
      Nonempty (P.FaithfulPeirceHermitianMatrixMap (P.formallyReal_of_associative_inner hinner) c C₀) := by
  let hfr₀ := P.formallyReal_of_associative_inner hinner
  obtain ⟨C₀⟩ := P.exists_peirceTriangleCoordinates_of_simple c hc hor hunit hinner hsimple
    (ne_of_lt hrs) (ne_of_lt (lt_trans hrs hst)) (ne_of_lt hst)
  have hconn (i j : Fin n) (hij : i < j) : W i j ≠ ⊥ :=
    P.frameOffDiagonal_ne_bot_of_simple c hc hor hunit hinner hsimple i j (ne_of_lt hij)
  obtain ⟨C₁, _, _, D, hform⟩ := P.exists_peirceIncreasingFrameChart_normalized hfr₀ c C₀
    hc hor hunit hrs hst hfirst hconn
  exact ⟨C₁, P.exists_faithfulPeirceHermitianMatrixMap hfr₀ c C₁ hc hor hunit hinner hrs hst D hform⟩

end AlbertSequential.UnitalJordanProduct
