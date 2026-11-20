/- SPDX-License-Identifier: Apache-2.0 -/
module
public import NativeAlbertTableMixtures
public import JordanPrimitiveTransport

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace AlbertSequential.TwoAlbert
open NativeAnalysis UnitalJordanProduct

local instance : FiniteDimensional ℝ Albert := nativeAlbertModuleFinite

abbrev Raw := Fin 2 → Albert

def rawProduct : UnitalJordanProduct Raw := factorProduct fun _ => nativeAlbertProduct

theorem raw_formallyReal : rawProduct.FormallyReal :=
  factorProduct_formallyReal _ fun _ => nativeAlbertProduct_formallyReal

abbrev Space := PositiveFormModel.Model Raw

def coordinates : Space ≃ₗ[ℝ] Raw := PositiveFormModel.linearEquiv Raw

@[instance_reducible] def innerCore : InnerProductSpace.Core ℝ Space :=
  PositiveFormModel.innerCore Raw (rawProduct.canonicalTraceFormOfFormallyReal raw_formallyReal)
    (rawProduct.canonicalTraceFormOfFormallyReal_symmetric raw_formallyReal)
    (rawProduct.canonicalTraceFormOfFormallyReal_positive raw_formallyReal)

local instance : InnerProductSpace.Core ℝ Space := innerCore
scoped instance : NormedAddCommGroup Space := innerCore.toNormedAddCommGroup
scoped instance : InnerProductSpace ℝ Space := InnerProductSpace.ofCore innerCore.toCore

scoped instance : FiniteDimensional ℝ Space :=
  Module.Finite.equiv (PositiveFormModel.linearEquiv Raw).symm

def product : UnitalJordanProduct Space := rawProduct.transportProduct coordinates

theorem formallyReal : product.FormallyReal := rawProduct.transportProduct_formallyReal raw_formallyReal coordinates

def pair {I : Type*} (p q : I → Albert) (i : I) : Space := coordinates.symm ![p i,q i]

def left (x : Albert) : Space := coordinates.symm ![x,0]
def right (y : Albert) : Space := coordinates.symm ![0,y]

@[simp] theorem coordinates_pair {I : Type*} (p q : I → Albert) (i : I) :
    coordinates (pair p q i) = ![p i,q i] := by simp [pair]

theorem pair_eq_left_add_right {I : Type*} (p q : I → Albert) (i : I) :
    pair p q i = left (p i) + right (q i) := by
  apply coordinates.injective
  rw [map_add,coordinates_pair]
  simp only [left,right,LinearEquiv.apply_symm_apply]
  funext j
  fin_cases j <;> simp

theorem product_coordinates (x y : Space) (j : Fin 2) :
    coordinates (product.product x y) j = jordanMul (coordinates x j) (coordinates y j) := by
  rw [product,rawProduct.transportProduct_apply]
  rfl

@[simp] theorem unit_coordinates (j : Fin 2) : coordinates product.unit j = albertUnit := by
  rw [product,rawProduct.transportProduct_unit]
  rfl

theorem left_coordinates (x : Albert) : coordinates (left x) = ![x,0] :=
  coordinates.apply_symm_apply _

theorem right_coordinates (x : Albert) : coordinates (right x) = ![0,x] :=
  coordinates.apply_symm_apply _

theorem left_idempotent (x : Albert) (h : jordanMul x x = x) :
    product.product (left x) (left x) = left x := by
  apply coordinates.injective
  funext j
  rw [product_coordinates,left_coordinates]
  fin_cases j <;> simp [h,jordanMul_zero_left]

theorem right_idempotent (x : Albert) (h : jordanMul x x = x) :
    product.product (right x) (right x) = right x := by
  apply coordinates.injective
  funext j
  rw [product_coordinates,right_coordinates]
  fin_cases j <;> simp [h,jordanMul_zero_left]

theorem left_right_orthogonal (x y : Albert) : product.product (left x) (right y) = 0 := by
  apply coordinates.injective
  funext j
  rw [product_coordinates,left_coordinates,right_coordinates,map_zero]
  fin_cases j <;> simp [jordanMul_zero_left,jordanMul_zero_right]

private theorem left_ne_zero {x : Albert} (h : x ≠ 0) : left x ≠ 0 := by
  intro hz
  exact h (by simpa [left_coordinates] using congrArg (fun y => coordinates y (0 : Fin 2)) hz)

private theorem right_ne_zero {x : Albert} (h : x ≠ 0) : right x ≠ 0 := by
  intro hz
  exact h (by simpa [right_coordinates] using congrArg (fun y => coordinates y (1 : Fin 2)) hz)

private theorem primitive_of_single_coordinate (c : Space) (k : Fin 2)
    (hatom : IsAtom (coordinates c k)) (hother : ∀ j, j ≠ k → coordinates c j = 0) :
    product.IsPrimitive c := by
  have hp := (NativeAnalysis.isAtom_iff_primitive _).mp hatom
  refine ⟨?_,fun hc => hp.2.1 (by simp [hc]),?_⟩
  · apply coordinates.injective
    funext j
    rw [product_coordinates]
    by_cases h : j = k
    · subst j
      exact hp.1
    · simp [hother j h,jordanMul_zero_left]
  · intro a b ha hb hab hs
    have hida (j : Fin 2) : jordanMul (coordinates a j) (coordinates a j) = coordinates a j := by
      rw [← product_coordinates,ha]
    have hidb (j : Fin 2) : jordanMul (coordinates b j) (coordinates b j) = coordinates b j := by
      rw [← product_coordinates,hb]
    have horth (j : Fin 2) : jordanMul (coordinates a j) (coordinates b j) = 0 := by
      rw [← product_coordinates,hab,map_zero,Pi.zero_apply]
    have hadd (j : Fin 2) : coordinates a j + coordinates b j = coordinates c j := by
      simpa only [map_add,Pi.add_apply] using congrArg (fun v : TwoAlbert.Space => coordinates v j) hs
    have hlocal : coordinates a k = 0 ∨ coordinates b k = 0 := by
      by_cases h0 : coordinates a k = 0
      · exact Or.inl h0
      · by_cases h1 : coordinates b k = 0
        · exact Or.inr h1
        · exact (hp.2.2 ⟨_,_,hida k,hidb k,h0,h1,horth k,(hadd k).symm⟩).elim
    have hz (j : Fin 2) (hj : j ≠ k) : coordinates a j = 0 ∧ coordinates b j = 0 := by
      have hx : coordinates a j = 0 := calc
        coordinates a j = jordanMul (coordinates a j) (coordinates a j) := (hida j).symm
        _ = jordanMul (coordinates a j) (coordinates a j) +
            jordanMul (coordinates a j) (coordinates b j) := by rw [horth,add_zero]
        _ = jordanMul (coordinates a j) (coordinates a j + coordinates b j) :=
          (jordanMul_add_right _ _ _).symm
        _ = 0 := by rw [hadd,hother j hj,jordanMul_zero_right]
      refine ⟨hx,?_⟩
      simpa [hx,hother j hj] using hadd j
    rcases hlocal with h0 | h0
    · left
      apply coordinates.injective
      funext j
      by_cases hj : j = k
      · subst j
        simpa only [map_zero,Pi.zero_apply] using h0
      · simpa only [map_zero,Pi.zero_apply] using (hz j hj).1
    · right
      apply coordinates.injective
      funext j
      by_cases hj : j = k
      · subst j
        simpa only [map_zero,Pi.zero_apply] using h0
      · simpa only [map_zero,Pi.zero_apply] using (hz j hj).2

theorem paired_test_rank_two {I : Type*} (p q : I → Albert)
    (hp : ∀ i, IsAtom (p i)) (hq : ∀ i, IsAtom (q i)) (i : I) :
    product.canonicalTraceOfFormallyReal formallyReal (pair p q i) = 2 := by
  have ha : product.IsPrimitive (left (p i)) := by
    apply primitive_of_single_coordinate _ 0
    · simpa [left_coordinates] using hp i
    · intro j hj
      fin_cases j
      · exact (hj rfl).elim
      · simp [left_coordinates]
  have hb : product.IsPrimitive (right (q i)) := by
    apply primitive_of_single_coordinate _ 1
    · simpa [right_coordinates] using hq i
    · intro j hj
      fin_cases j
      · simp [right_coordinates]
      · exact (hj rfl).elim
  rw [pair_eq_left_add_right,map_add,product.canonicalTraceOfFormallyReal_primitive formallyReal _ ha,
    product.canonicalTraceOfFormallyReal_primitive formallyReal _ hb]
  norm_num

theorem pair_complement_split {I : Type*} (p q : I → Albert) (i : I) :
    product.unit - pair p q i = left (albertUnit-p i) + right (albertUnit-q i) := by
  apply coordinates.injective
  rw [map_sub,map_add,coordinates_pair,left_coordinates,right_coordinates]
  funext j
  change coordinates product.unit j - ![p i,q i] j =
    ![albertUnit-p i,0] j + ![0,albertUnit-q i] j
  rw [unit_coordinates]
  fin_cases j <;> simp

private theorem generated_not_primitive_of_split {I : Type*} (m : I → Space) (hg : product.GeneratesMenu m)
    (x : product.generatedMenuCarrier m) (a b : Space)
    (ha : product.product a a = a) (hb : product.product b b = b) (hab : product.product a b = 0)
    (hs : a + b = x.val) (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    ¬ (product.generatedMenuProduct m).IsPrimitive x := by
  intro h
  have hall (z : Space) : z ∈ product.generatedMenuCarrier m :=
    hg _ (product.unit_mem_generatedMenuCarrier m)
      (fun _ h₁ _ h₂ => product.product_mem_generatedMenuCarrier m h₁ h₂)
      (product.test_mem_generatedMenuCarrier m) z
  obtain hzero | hzero := h.2.2 ⟨a,hall a⟩ ⟨b,hall b⟩
    (Subtype.ext ha) (Subtype.ext hb) (Subtype.ext hab) (Subtype.ext hs)
  · exact ha0 (congrArg Subtype.val hzero)
  · exact hb0 (congrArg Subtype.val hzero)

/-- The two signs of every paired atom test are nonprimitive in the actual
generated carrier if the menu generates both full factors. -/
theorem paired_test_not_BPrimitive {I : Type*} (p q : I → Albert)
    (hp : ∀ i, IsAtom (p i)) (hq : ∀ i, IsAtom (q i))
    (hg : product.GeneratesMenu (pair p q)) (i : I) :
    ¬ product.IsBPrimitiveTest (pair p q) i := by
  have hp0 := ((NativeAnalysis.isAtom_iff_primitive _).mp (hp i)).2.1
  have hq0 := ((NativeAnalysis.isAtom_iff_primitive _).mp (hq i)).2.1
  have hp1 : albertUnit-p i ≠ 0 := by
    intro hz
    have h := congrArg albertTrace (sub_eq_zero.mp hz)
    rw [albertTrace_unit,(hp i).2] at h
    norm_num at h
  have hq1 : albertUnit-q i ≠ 0 := by
    intro hz
    have h := congrArg albertTrace (sub_eq_zero.mp hz)
    rw [albertTrace_unit,(hq i).2] at h
    norm_num at h
  rintro ⟨_,_,h | h⟩
  · exact generated_not_primitive_of_split _ hg _ _ _
      (left_idempotent _ (hp i).1) (right_idempotent _ (hq i).1) (left_right_orthogonal _ _)
      (pair_eq_left_add_right p q i).symm (left_ne_zero hp0) (right_ne_zero hq0) h
  · exact generated_not_primitive_of_split _ hg _ _ _
      (left_idempotent _ (native_idempotent_complement _ (hp i).1))
      (right_idempotent _ (native_idempotent_complement _ (hq i).1)) (left_right_orthogonal _ _)
      (pair_complement_split p q i).symm (left_ne_zero hp1) (right_ne_zero hq1) h

def mixedFunctional (weight : ℝ) (ρ σ : Albert) : Space →ₗ[ℝ] ℝ :=
  weight • ((tracePairingFunctional ρ).comp ((LinearMap.proj (0 : Fin 2)).comp coordinates.toLinearMap)) +
    (1-weight) • ((tracePairingFunctional σ).comp ((LinearMap.proj (1 : Fin 2)).comp coordinates.toLinearMap))

theorem mixedFunctional_positive (weight : ℝ) (weight_pos : 0 ≤ weight) (weight_le : weight ≤ 1) {ρ σ : Albert}
    (hρ : IsDensity ρ) (hσ : IsDensity σ) (x : Space) :
    0 ≤ mixedFunctional weight ρ σ (product.product x x) := by
  change 0 ≤ weight * tracePairing ρ (coordinates (product.product x x) 0) +
    (1-weight) * tracePairing σ (coordinates (product.product x x) 1)
  rw [product_coordinates,product_coordinates]
  exact add_nonneg (mul_nonneg weight_pos ((isPositive_iff_dual_squares _).mp hρ.1 (coordinates x 0)))
    (mul_nonneg (sub_nonneg.mpr weight_le) ((isPositive_iff_dual_squares _).mp hσ.1 (coordinates x 1)))

theorem mixedFunctional_unit (weight : ℝ) {ρ σ : Albert} (hρ : IsDensity ρ) (hσ : IsDensity σ) :
    mixedFunctional weight ρ σ product.unit = 1 := by
  change weight * tracePairing ρ (coordinates product.unit 0) +
    (1-weight) * tracePairing σ (coordinates product.unit 1) = 1
  rw [unit_coordinates,unit_coordinates,tracePairing_unit_right,tracePairing_unit_right,hρ.2,hσ.2]
  ring

theorem mix_all_words {I : Type*} (p q : I → Albert) (weight : ℝ) (ρ σ : Albert) (w : Word I) :
    mixedFunctional weight ρ σ (product.sequentialWordEffect (pair p q) w) =
      weight * nativeWordProbability p ρ w + (1-weight) * nativeWordProbability q σ w := by
  have hcoords := product.map_sequentialWordEffect rawProduct coordinates.toLinearMap
    (rawProduct.transportProduct_unit coordinates) (rawProduct.transportProduct_apply coordinates) (pair p q) w
  change weight * tracePairing ρ (coordinates (product.sequentialWordEffect (pair p q) w) 0) +
    (1-weight) * tracePairing σ (coordinates (product.sequentialWordEffect (pair p q) w) 1) = _
  change coordinates (product.sequentialWordEffect (pair p q) w) =
    rawProduct.sequentialWordEffect (coordinates ∘ pair p q) w at hcoords
  rw [hcoords]
  simp only [rawProduct,factorProduct_sequentialWordEffect,Function.comp_apply,coordinates_pair]
  change weight * tracePairing ρ (nativeAlbertProduct.sequentialWordEffect p w) +
    (1-weight) * tracePairing σ (nativeAlbertProduct.sequentialWordEffect q w) = _
  rw [nativeAlbertProduct_wordEffect,nativeAlbertProduct_wordEffect,
    ← nativeWordProbability_eq_pairing,← nativeWordProbability_eq_pairing]

universe u

/-- The paired Albert table is an actual direct-sum density table. Each original
generating table is outside class (I). No membership conclusion for the mixture
follows from these statements. -/
theorem paired_albert_mixture {n : ℕ} (p q : Fin n → Albert)
    (hp : ∀ i, IsAtom (p i)) (hq : ∀ i, IsAtom (q i))
    (hgp : GeneratesAlbert p) (hgq : GeneratesAlbert q)
    (hg : product.GeneratesMenu (pair p q)) (weight : ℝ) (weight_pos : 0 < weight) (weight_pos' : weight < 1)
    (ρ σ : Albert) (hρ : IsDensity ρ) (hσ : IsDensity σ) :
    (∀ i, ¬ product.IsBPrimitiveTest (pair p q) i) ∧
    (∃ initial : Space, product.IsCanonicalDensity formallyReal initial ∧ ∀ w,
      product.canonicalTraceOfFormallyReal formallyReal (product.sequentialBranchState (pair p q) initial w) =
        weight * nativeWordProbability p ρ w + (1-weight) * nativeWordProbability q σ w) ∧
    nativeWordProbability p ρ ∉ hilbertProjectiveTables.{u} ℂ n ∧
    nativeWordProbability q σ ∉ hilbertProjectiveTables.{u} ℂ n := by
  let ω := mixedFunctional weight ρ σ
  refine ⟨paired_test_not_BPrimitive p q hp hq hg,?_,
    generated_nativeAlbert_table_not_complex p hp hgp ρ,generated_nativeAlbert_table_not_complex q hq hgq σ⟩
  refine ⟨product.canonicalTraceRepresentative formallyReal ω,
    product.normalized_positiveFunctional_density formallyReal ω
      (mixedFunctional_positive weight weight_pos.le weight_pos'.le hρ hσ) (mixedFunctional_unit weight hρ hσ),?_⟩
  intro w
  rw [product.canonicalTrace_sequentialBranchState,canonicalPairingFunctional,
    product.canonicalTraceRepresentative_pairing]
  exact mix_all_words p q weight ρ σ w

end AlbertSequential.TwoAlbert
