/- SPDX-License-Identifier: Apache-2.0 -/
module
public import SpinFactorClifford
public import JordanIdealOrthogonal

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

open scoped Matrix

section LowerRank

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  (P : UnitalJordanProduct E) (hfr : P.FormallyReal)

local notation "τ" => P.canonicalTraceOfFormallyReal hfr

theorem canonicalTrace_unit_eq_primitive_frame_length {n : ℕ} (c : Fin n → E)
    (hc : ∀ i, P.IsPrimitive (c i)) (hsum : ∑ i, c i = P.unit) : τ P.unit = n := by
  calc
    τ P.unit = ∑ i, τ (c i) := by rw [← map_sum, hsum]
    _ = ∑ _ : Fin n, (1 : ℝ) := Finset.sum_congr rfl
      (fun i _ => P.canonicalTraceOfFormallyReal_primitive hfr (c i) (hc i))
    _ = n := by simp

private theorem rankOne_scalar (hrank : τ P.unit = 1) (x : E) : x = τ x • P.unit := by
  obtain ⟨n, lam, c, hc, _, hsum, hx⟩ := P.primitive_spectral_resolution_of_formallyReal hfr x
  have hn : n = 1 := by
    exact_mod_cast (P.canonicalTrace_unit_eq_primitive_frame_length hfr c hc hsum).symm.trans hrank
  subst n
  have hc0 : c 0 = P.unit := by simpa only [Fin.sum_univ_one] using hsum
  have hx' : x = lam 0 • P.unit := by simpa only [Fin.sum_univ_one, hc0] using hx
  have hτx : τ x = lam 0 := by rw [hx', map_smul, smul_eq_mul, hrank, mul_one]
  rwa [hτx]

theorem faithfulHermitianEmbedding_of_rank_one (hrank : τ P.unit = 1) :
    Nonempty (FaithfulHermitianJordanEmbedding P 1) := by
  let g : E →ₗ[ℝ] Matrix (Fin 1) (Fin 1) ℂ :=
    { toFun x := τ x • (1 : Matrix (Fin 1) (Fin 1) ℂ)
      map_add' x y := by rw [map_add, add_smul]
      map_smul' r x := by rw [map_smul, RingHom.id_apply, smul_smul, smul_eq_mul] }
  refine ⟨{map := g, injective := ?_, hermitian := fun x => ?_, unit := ?_, jordan := fun x y => ?_}⟩
  · intro x y h
    have hxy := congrArg (fun A : Matrix (Fin 1) (Fin 1) ℂ => (A 0 0).re) h
    change ((τ x • (1 : Matrix (Fin 1) (Fin 1) ℂ)) 0 0).re =
      ((τ y • (1 : Matrix (Fin 1) (Fin 1) ℂ)) 0 0).re at hxy
    have ht : τ x = τ y := by
      simpa only [Matrix.smul_apply, Matrix.one_apply_eq, Complex.real_smul, mul_one,
        Complex.ofReal_re] using hxy
    calc
      x = τ x • P.unit := P.rankOne_scalar hfr hrank x
      _ = τ y • P.unit := congrArg (fun a : ℝ => a • P.unit) ht
      _ = y := (P.rankOne_scalar hfr hrank y).symm
  · change (τ x • (1 : Matrix (Fin 1) (Fin 1) ℂ))ᴴ = τ x • (1 : Matrix (Fin 1) (Fin 1) ℂ)
    simp only [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_one]
  · change τ P.unit • (1 : Matrix (Fin 1) (Fin 1) ℂ) = 1
    rw [hrank, one_smul]
  · have hxy : P.product x y = τ x • y := by
      conv_lhs => rw [P.rankOne_scalar hfr hrank x]
      simp only [map_smul, LinearMap.smul_apply, P.unit_left]
    change τ (P.product x y) • (1 : Matrix (Fin 1) (Fin 1) ℂ) =
      (1 / 2 : ℝ) • ((τ x • 1) * (τ y • 1) + (τ y • 1) * (τ x • 1))
    rw [hxy, map_smul, smul_eq_mul]
    simp only [Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul]
    module

private theorem rankTwo_traceZero_square (hrank : τ P.unit = 2) (x : E) (ht : τ x = 0) :
    P.product x x = (τ (P.product x x) / 2) • P.unit := by
  obtain ⟨n, lam, c, hc, ho, hsum, hx⟩ := P.primitive_spectral_resolution_of_formallyReal hfr x
  have hn : n = 2 := by
    exact_mod_cast (P.canonicalTrace_unit_eq_primitive_frame_length hfr c hc hsum).symm.trans hrank
  subst n
  have hsum' : c 0 + c 1 = P.unit := by simpa only [Fin.sum_univ_two] using hsum
  have hlam : lam 0 + lam 1 = 0 := by
    simpa only [hx, map_sum, map_add, map_smul, smul_eq_mul, Fin.sum_univ_two,
      P.canonicalTraceOfFormallyReal_primitive hfr _ (hc 0),
      P.canonicalTraceOfFormallyReal_primitive hfr _ (hc 1), mul_one] using ht
  have hneg : lam 1 = -(lam 0) := by linarith
  have hsquare : P.product x x = (lam 0)^2 • P.unit := by
    rw [hx, P.square_of_orthogonal_expansion c lam (fun i => (hc i).1) ho,
      Fin.sum_univ_two, hneg, neg_sq, ← smul_add, hsum']
  rw [hsquare, map_smul, smul_eq_mul, hrank]
  congr 1
  ring

private theorem rankTwo_traceZero_product (hrank : τ P.unit = 2) (x y : E)
    (hx : τ x = 0) (hy : τ y = 0) : P.product x y = (τ (P.product x y) / 2) • P.unit := by
  let excess (z : E) := z - (τ z / 2) • P.unit
  have hxself : excess (P.product x x) = 0 := sub_eq_zero.mpr (P.rankTwo_traceZero_square hfr hrank x hx)
  have hyself : excess (P.product y y) = 0 := sub_eq_zero.mpr (P.rankTwo_traceZero_square hfr hrank y hy)
  have ht : τ (x + y) = 0 := by rw [map_add, hx, hy, zero_add]
  have hsum : excess (P.product (x+y) (x+y)) = 0 :=
    sub_eq_zero.mpr (P.rankTwo_traceZero_square hfr hrank (x+y) ht)
  have hzero : (2 : ℝ) • excess (P.product x y) = 0 := by
    calc
      _ = excess (P.product (x+y) (x+y)) - excess (P.product x x) - excess (P.product y y) := by
        dsimp only [excess]
        simp only [map_add, LinearMap.add_apply, P.commutative y x]
        module
      _ = 0 := by rw [hsum, hxself, hyself, sub_zero, sub_zero]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_left (by norm_num))

end LowerRank

section Coordinates

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

private def centeredCoordinates (t : E →ₗ[ℝ] ℝ) (e : E) (hunit : t e = 1) :
    E ≃ₗ[ℝ] ℝ × LinearMap.ker t where
  toFun x := (t x, ⟨x - t x • e, by
    change t (x - t x • e) = 0
    rw [map_sub, map_smul, smul_eq_mul, hunit, mul_one, sub_self]⟩)
  invFun x := x.1 • e + x.2.val
  left_inv x := by
    change t x • e + (x - t x • e) = x
    rw [← add_sub_assoc, add_sub_cancel_left]
  right_inv x := by
    have ht : t (x.1 • e + x.2.val) = x.1 := by
      have hx : t x.2.val = 0 := x.2.property
      rw [map_add, map_smul, smul_eq_mul, hunit, mul_one, hx, add_zero]
    apply Prod.ext
    · exact ht
    · apply Subtype.ext
      change (x.1 • e + x.2.val) - t (x.1 • e + x.2.val) • e = x.2.val
      rw [ht]
      abel
  map_add' x y := by
    apply Prod.ext
    · exact map_add t x y
    · apply Subtype.ext
      change x + y - t (x+y) • e = (x - t x • e) + (y - t y • e)
      rw [map_add, add_smul]
      abel
  map_smul' r x := by
    apply Prod.ext
    · exact map_smul t r x
    · apply Subtype.ext
      change r • x - t (r • x) • e = r • (x - t x • e)
      rw [map_smul, smul_sub, smul_smul, smul_eq_mul]

end Coordinates

section SpinRealization

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  (P : UnitalJordanProduct E) (hfr : P.FormallyReal)

local notation "τ" => P.canonicalTraceOfFormallyReal hfr

/-- The trace-free part of a rank-two EJA realizes its actual spin-factor product. -/
theorem faithfulHermitianEmbedding_of_rank_two (hrank : τ P.unit = 2) :
    ∃ d, Nonempty (FaithfulHermitianJordanEmbedding P d) := by
  let t : E →ₗ[ℝ] ℝ := (1 / 2 : ℝ) • τ
  have ht : t P.unit = 1 := by
    change (1 / 2 : ℝ) * τ P.unit = 1
    norm_num [hrank]
  let K := LinearMap.ker t
  let B : K →ₗ[ℝ] K →ₗ[ℝ] ℝ :=
    (1 / 2 : ℝ) • (P.canonicalTraceFormOfFormallyReal hfr).compl₁₂ K.subtype K.subtype
  have hsym (x y : K) : B x y = B y x := by
    change (1 / 2 : ℝ) * P.canonicalTraceFormOfFormallyReal hfr x.val y.val =
      (1 / 2 : ℝ) * P.canonicalTraceFormOfFormallyReal hfr y.val x.val
    rw [P.canonicalTraceFormOfFormallyReal_symmetric]
  have hpos (x : K) (hx : x ≠ 0) : 0 < B x x := by
    have hx' : x.val ≠ 0 := fun h => hx (Subtype.ext h)
    change 0 < (1 / 2 : ℝ) * P.canonicalTraceFormOfFormallyReal hfr x.val x.val
    exact mul_pos (by norm_num) (P.canonicalTraceFormOfFormallyReal_positive hfr x.val hx')
  let W := AlbertSequential.PositiveFormModel.Model K
  let core : InnerProductSpace.Core ℝ W := AlbertSequential.PositiveFormModel.innerCore K B hsym hpos
  let _ : InnerProductSpace.Core ℝ W := core
  let _ : NormedAddCommGroup W := core.toNormedAddCommGroup
  let _ : InnerProductSpace ℝ W :=
    InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ W)
  let e : W ≃ₗ[ℝ] K := AlbertSequential.PositiveFormModel.linearEquiv K
  let c : E ≃ₗ[ℝ] ℝ × W :=
    (centeredCoordinates t P.unit ht).trans ((LinearEquiv.refl ℝ ℝ).prodCongr e.symm)
  have hinv (r : ℝ) (w : W) : c.symm (r,w) = r • P.unit + (e w).val := rfl
  have htrace (w : W) : τ (e w).val = 0 := by
    have hw : t (e w).val = 0 := (e w).property
    change (1 / 2 : ℝ) * τ (e w).val = 0 at hw
    linarith
  have hinner (u v : W) : inner ℝ u v = τ (P.product (e u).val (e v).val) / 2 := by
    change (1 / 2 : ℝ) * P.canonicalTraceFormOfFormallyReal hfr (e u).val (e v).val = _
    rw [P.canonicalTraceFormOfFormallyReal_apply]
    ring
  have hright (x : E) : P.product x P.unit = x := (P.commutative x P.unit).trans (P.unit_left x)
  let S : AlbertSequential.SpinFactorCoordinates P W :=
    { coordinates := c
      unit := by
        apply c.symm.injective
        rw [c.symm_apply_apply, hinv, one_smul, map_zero]
        simp
      product := fun x y => by
        let a := (c x).1
        let b := (c y).1
        let u := (c x).2
        let v := (c y).2
        have hx : x = a • P.unit + (e u).val := (c.symm_apply_apply x).symm
        have hy : y = b • P.unit + (e v).val := (c.symm_apply_apply y).symm
        have huv := P.rankTwo_traceZero_product hfr hrank (e u).val (e v).val (htrace u) (htrace v)
        rw [← hinner u v] at huv
        have hscale_left (r : ℝ) (z w : E) : P.product (r • z) w = r • P.product z w :=
          LinearMap.congr_fun (P.product.map_smul r z) w
        have hadd_left (z w q : E) : P.product (z + w) q = P.product z q + P.product w q :=
          LinearMap.congr_fun (P.product.map_add z w) q
        have hvec : (e (a • v + b • u)).val = a • (e v).val + b • (e u).val := by
          rw [map_add, map_smul, map_smul]
          rfl
        apply c.symm.injective
        rw [c.symm_apply_apply, hinv]
        change P.product x y = (a * b + inner ℝ u v) • P.unit + (e (a • v + b • u)).val
        calc
          _ = P.product (a • P.unit + (e u).val) (b • P.unit + (e v).val) :=
            congrArg₂ (fun s t => P.product s t) hx hy
          _ = _ := by
            rw [hadd_left, hscale_left, P.unit_left, map_add, map_smul, hright, huv, hvec,
              smul_add, smul_smul, add_smul]
            abel }
  exact S.exists_faithfulHermitianJordanEmbedding

end SpinRealization

section LowRankFactors

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (P : UnitalJordanProduct E)

/-- The Hermitian branch of the simple-factor dichotomy for ranks one and two. -/
theorem simple_factor_has_hermitian_embedding_of_rank_one_or_two
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (I : Submodule ℝ E) (hI : P.IsSimpleJordanIdeal I)
    (hrank : let Q := P.orthogonalIdealProduct hinner I hI.1
      let hfr := Q.formallyReal_of_associative_inner (P.orthogonalIdealProduct_inner hinner I hI.1)
      Q.canonicalTraceOfFormallyReal hfr Q.unit = 1 ∨ Q.canonicalTraceOfFormallyReal hfr Q.unit = 2) :
    ∃ d, Nonempty (FaithfulHermitianJordanEmbedding (P.orthogonalIdealProduct hinner I hI.1) d) := by
  let Q := P.orthogonalIdealProduct hinner I hI.1
  let hfr := Q.formallyReal_of_associative_inner (P.orthogonalIdealProduct_inner hinner I hI.1)
  rcases hrank with h1 | h2
  · exact ⟨1, Q.faithfulHermitianEmbedding_of_rank_one hfr h1⟩
  · exact Q.faithfulHermitianEmbedding_of_rank_two hfr h2

end LowRankFactors

end AlbertSequential.UnitalJordanProduct
