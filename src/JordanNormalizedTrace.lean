/- SPDX-License-Identifier: Apache-2.0 -/
module
public import JordanPrimitivePairing
public import EuclideanJordanSquareCone
public import JordanPrimitiveSpectralResolution

/-! Primitive-normalized trace, constructed from one actual frame. Association
is checked on primitive outer variables; no classification/ideal decomposition
or primitive normalization of the supplied form is assumed. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.UnitalJordanProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (P : UnitalJordanProduct E)

def frameNormalizingElement (_P : UnitalJordanProduct E) {ι : Type*} [Fintype ι] (c : ι → E) : E :=
  ∑ i,(inner ℝ (c i) (c i))⁻¹ • c i

def frameNormalizedTrace {ι : Type*} [Fintype ι] (c : ι → E) : E →ₗ[ℝ] ℝ :=
  (innerSL ℝ (P.frameNormalizingElement c)).toLinearMap

theorem frameNormalizingElement_product_primitive
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    {ι : Type*} [Fintype ι] (c : ι → E) (hc : ∀ i,P.IsPrimitive (c i))
    (hs : (∑ i,c i)=P.unit) (q : E) (hq : P.IsPrimitive q) :
    P.product (P.frameNormalizingElement c) q=(inner ℝ q q)⁻¹ • q := by
  have heach (i : ι) :
      (inner ℝ (c i) (c i))⁻¹ • P.product (c i) q=
        (inner ℝ q q)⁻¹ • P.product (c i) q := by
    by_cases hlen : inner ℝ (c i) (c i)=inner ℝ q q
    · rw [hlen]
    · rw [P.primitive_product_zero_of_length_ne hinner (c i) q (hc i) hq hlen,smul_zero,smul_zero]
  calc
    P.product (P.frameNormalizingElement c) q=
        ∑ i,(inner ℝ (c i) (c i))⁻¹ • P.product (c i) q := by
      simp only [frameNormalizingElement,map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply]
    _=∑ i,(inner ℝ q q)⁻¹ • P.product (c i) q := Finset.sum_congr rfl (fun i _ => heach i)
    _=(inner ℝ q q)⁻¹ • P.product (∑ i,c i) q := by
      simp only [map_sum,LinearMap.sum_apply,Finset.smul_sum]
    _=(inner ℝ q q)⁻¹ • q := by rw [hs,P.unit_left]

theorem frameNormalizedTrace_product_primitive
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    {ι : Type*} [Fintype ι] (c : ι → E) (hc : ∀ i,P.IsPrimitive (c i))
    (hs : (∑ i,c i)=P.unit) (q x : E) (hq : P.IsPrimitive q) :
    P.frameNormalizedTrace c (P.product q x)=inner ℝ q x/inner ℝ q q := by
  change inner ℝ (P.frameNormalizingElement c) (P.product q x)=_
  rw [← hinner,P.frameNormalizingElement_product_primitive hinner c hc hs q hq,
    real_inner_smul_left,div_eq_inv_mul]

theorem frameNormalizedTrace_primitive
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    {ι : Type*} [Fintype ι] (c : ι → E) (hc : ∀ i,P.IsPrimitive (c i))
    (hs : (∑ i,c i)=P.unit) (q : E) (hq : P.IsPrimitive q) :
    P.frameNormalizedTrace c q=1 := by
  have hpair : inner ℝ q P.unit=inner ℝ q q := by
    simpa only [hq.1] using P.square_inner_unit hinner q
  have hq0 : inner ℝ q q≠0 := (real_inner_self_pos.mpr hq.2.1).ne'
  have he := P.frameNormalizedTrace_product_primitive hinner c hc hs q P.unit hq
  simpa only [P.commutative q P.unit,P.unit_left,hpair,div_self hq0] using he

theorem frameNormalizedTrace_associative_primitive_outer
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    {ι : Type*} [Fintype ι] (c : ι → E) (hc : ∀ i,P.IsPrimitive (c i))
    (hs : (∑ i,c i)=P.unit) (q y r : E) (hq : P.IsPrimitive q) (hr : P.IsPrimitive r) :
    P.frameNormalizedTrace c (P.product (P.product q y) r)=
      P.frameNormalizedTrace c (P.product q (P.product y r)) := by
  rw [P.commutative (P.product q y) r,
    P.frameNormalizedTrace_product_primitive hinner c hc hs r (P.product q y) hr,
    P.frameNormalizedTrace_product_primitive hinner c hc hs q (P.product y r) hq]
  have hleft : inner ℝ r (P.product q y)=inner ℝ (P.product q r) y := by
    rw [← hinner,P.commutative r q]
  have hright : inner ℝ q (P.product y r)=inner ℝ (P.product q r) y := by
    rw [P.commutative y r,← hinner]
  rw [hleft,hright]
  by_cases hlen : inner ℝ q q=inner ℝ r r
  · rw [hlen]
  · rw [P.primitive_product_zero_of_length_ne hinner q r hq hr hlen,inner_zero_left,zero_div,zero_div]

theorem frameNormalizedTrace_associative
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    {ι : Type*} [Fintype ι] (c : ι → E) (hc : ∀ i,P.IsPrimitive (c i))
    (hs : (∑ i,c i)=P.unit) (x y z : E) :
    P.frameNormalizedTrace c (P.product (P.product x y) z)=
      P.frameNormalizedTrace c (P.product x (P.product y z)) := by
  obtain ⟨n,lam,q,hq,_,_,hx⟩ := P.primitive_spectral_resolution hinner x
  obtain ⟨m,mu,r,hr,_,_,hz⟩ := P.primitive_spectral_resolution hinner z
  rw [hx,hz]
  simp only [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,
    Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [P.frameNormalizedTrace_associative_primitive_outer hinner c hc hs _ y _ (hq j) (hr i)]

theorem normalized_trace_unique
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (tau sigma : E →ₗ[ℝ] ℝ) (htau : ∀ q,P.IsPrimitive q → tau q=1)
    (hsigma : ∀ q,P.IsPrimitive q → sigma q=1) : tau=sigma := by
  ext x
  obtain ⟨n,lam,c,hc,_,_,hx⟩ := P.primitive_spectral_resolution hinner x
  rw [hx,map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul,map_smul,htau _ (hc i),hsigma _ (hc i)]

theorem normalized_trace_square_positive
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (tau : E →ₗ[ℝ] ℝ) (htau : ∀ q,P.IsPrimitive q → tau q=1)
    (x : E) (hx : x≠0) : 0<tau (P.product x x) := by
  classical
  obtain ⟨n,lam,c,hc,ho,_,hxspec⟩ := P.primitive_spectral_resolution hinner x
  have hex : ∃ i,lam i≠0 := by
    by_contra h
    push Not at h
    apply hx
    rw [hxspec]
    simp only [h,zero_smul,Finset.sum_const_zero]
  obtain ⟨i,hi⟩ := hex
  rw [hxspec,P.square_of_orthogonal_expansion c lam (fun j => (hc j).1) ho,map_sum]
  simp only [map_smul,htau _ (hc _),smul_eq_mul,mul_one]
  exact Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨i,Finset.mem_univ _,sq_pos_of_ne_zero hi⟩

theorem exists_normalized_trace_with_laws
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z)) :
    ∃ tau : E →ₗ[ℝ] ℝ,
      (∀ q,P.IsPrimitive q → tau q=1) ∧
      (∀ x y z,tau (P.product (P.product x y) z)=tau (P.product x (P.product y z))) ∧
      (∀ x,x≠0 → 0<tau (P.product x x)) ∧
      (∀ q x,P.IsPrimitive q → P.quadraticRepresentation q x=tau (P.product q x) • q) := by
  obtain ⟨n,lam,c,hc,_,hs,_⟩ := P.primitive_spectral_resolution hinner P.unit
  refine ⟨P.frameNormalizedTrace c,P.frameNormalizedTrace_primitive hinner c hc hs,
    P.frameNormalizedTrace_associative hinner c hc hs,
    P.normalized_trace_square_positive hinner _ (P.frameNormalizedTrace_primitive hinner c hc hs),?_⟩
  intro q x hq
  rw [P.primitive_quadraticRepresentation_coefficient hinner q x hq,
    P.frameNormalizedTrace_product_primitive hinner c hc hs q x hq]

theorem existsUnique_primitiveNormalizedTrace
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z)) :
    ∃! tau : E →ₗ[ℝ] ℝ, ∀ q,P.IsPrimitive q → tau q=1 := by
  obtain ⟨tau,htau,_⟩ := P.exists_normalized_trace_with_laws hinner
  exact ⟨tau,htau,fun sigma hsigma => P.normalized_trace_unique hinner sigma tau hsigma htau⟩

/-- The unique primitive-normalized trace; distinct from regular operator trace. -/
def canonicalTrace
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z)) : E →ₗ[ℝ] ℝ :=
  Classical.choose (P.exists_normalized_trace_with_laws hinner)

theorem canonicalTrace_primitive
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (q : E) (hq : P.IsPrimitive q) : P.canonicalTrace hinner q=1 :=
  (Classical.choose_spec (P.exists_normalized_trace_with_laws hinner)).1 q hq

theorem canonicalTrace_associative
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (x y z : E) : P.canonicalTrace hinner (P.product (P.product x y) z)=
      P.canonicalTrace hinner (P.product x (P.product y z)) :=
  (Classical.choose_spec (P.exists_normalized_trace_with_laws hinner)).2.1 x y z

theorem canonicalTrace_square_positive
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (x : E) (hx : x≠0) : 0<P.canonicalTrace hinner (P.product x x) :=
  (Classical.choose_spec (P.exists_normalized_trace_with_laws hinner)).2.2.1 x hx

theorem canonicalTrace_primitive_compression
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (q x : E) (hq : P.IsPrimitive q) :
    P.quadraticRepresentation q x=P.canonicalTrace hinner (P.product q x) • q :=
  (Classical.choose_spec (P.exists_normalized_trace_with_laws hinner)).2.2.2 q x hq

end AlbertSequential.UnitalJordanProduct
