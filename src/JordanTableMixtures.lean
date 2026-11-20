/- SPDX-License-Identifier: Apache-2.0 -/
module
public import GeneralEJASpecialFactors
public import GeneralEJATableSpeciality
public import HorizonFive.Symbols
public import NativeWordDuality
public import Mathlib.Analysis.Convex.Combination

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace AlbertSequential
open NativeAnalysis
open scoped BigOperators

universe u

/-- Fixed-arity tables over finite formally real unital Jordan algebras. Their
canonical positive trace form gives an associative Euclidean inner product. -/
def finiteJordanTables (n : ℕ) : Set (Word (Fin n) → ℝ) :=
  {f | ∃ (E : Type u) (hE : AddCommGroup E), letI := hE
      ∃ (hR : Module ℝ E), letI := hR
      ∃ (_ : FiniteDimensional ℝ E) (P : UnitalJordanProduct E) (hfr : P.FormallyReal),
        f ∈ P.canonicalProjectiveTables hfr n}

/-- The native Albert factor, with the actual native density and arbitrary idempotents. -/
def nativeAlbertTables (n : ℕ) : Set (Word (Fin n) → ℝ) :=
  {f | ∃ (p : Fin n → Albert) (ρ : Albert), (∀ i, jordanMul (p i) (p i) = p i) ∧
    IsDensity ρ ∧ ∀ w, nativeWordProbability p ρ w = f w}

namespace UnitalJordanProduct
variable {E : Type u} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (P : UnitalJordanProduct E)

theorem mem_canonicalProjectiveTables_iff_functional (hfr : P.FormallyReal)
    {n : ℕ} {f : Word (Fin n) → ℝ} :
    f ∈ P.canonicalProjectiveTables hfr n ↔
      ∃ (p : Fin n → E) (ω : E →ₗ[ℝ] ℝ), (∀ i, P.product (p i) (p i) = p i) ∧
        (∀ x, 0 ≤ ω (P.product x x)) ∧ ω P.unit = 1 ∧
        (∀ w, ω (P.sequentialWordEffect p w) = f w) := by
  constructor
  · rintro ⟨p,ρ,hp,hρ,h⟩
    let ω := P.canonicalPairingFunctional hfr ρ
    refine ⟨p,ω,hp,?_,(P.canonicalTraceFormOfFormallyReal_unit hfr ρ).trans hρ.2,h⟩
    apply (P.canonicalTraceRepresentative_positive_iff hfr ω).mp
    rw [P.canonicalTraceRepresentative_pairingFunctional]
    exact hρ.1
  · rintro ⟨p,ω,hp,hpos,hunit,h⟩
    refine ⟨p,P.canonicalTraceRepresentative hfr ω,hp,
      P.normalized_positiveFunctional_density hfr ω hpos hunit,?_⟩
    intro w
    exact (P.canonicalTraceRepresentative_pairing hfr ω _).trans (h w)

theorem factorProduct_formallyReal {K : Type*} {V : K → Type*}
    [∀ k, AddCommGroup (V k)] [∀ k, Module ℝ (V k)]
    (Q : ∀ k, UnitalJordanProduct (V k)) (hQ : ∀ k, (Q k).FormallyReal) :
    (factorProduct Q).FormallyReal := by
  intro n x hx j
  funext k
  apply hQ k n (fun i => x i k)
  · simpa only [Finset.sum_apply,factorProduct_apply,Pi.zero_apply] using congrFun hx k

theorem factorProduct_sequentialWordEffect {K I : Type*} {V : K → Type*}
    [∀ k, AddCommGroup (V k)] [∀ k, Module ℝ (V k)]
    (Q : ∀ k, UnitalJordanProduct (V k)) (p : I → ∀ k, V k) (w : Word I) (k : K) :
    (factorProduct Q).sequentialWordEffect p w k = (Q k).sequentialWordEffect (fun i => p i k) w :=
  (factorProduct Q).map_sequentialWordEffect (Q k) (LinearMap.proj k) rfl (fun _ _ => rfl) p w

end UnitalJordanProduct

open UnitalJordanProduct in
/-- Closure under every genuine finite convex combination, realized in the
pointwise Jordan product of the actual carriers. -/
theorem finiteJordanTables_sum_mem {K : Type u} [Fintype K] {n : ℕ}
    (f : K → Word (Fin n) → ℝ) (a : K → ℝ)
    (hf : ∀ k, f k ∈ finiteJordanTables.{u} n) (ha : ∀ k, 0 ≤ a k) (hs : ∑ k, a k = 1) :
    (∑ k, a k • f k) ∈ finiteJordanTables.{u} n := by
  classical
  choose E hE hR hD Q hQ htab using hf
  let (k : K) : AddCommGroup (E k) := hE k
  let (k : K) : Module ℝ (E k) := hR k
  let (k : K) : FiniteDimensional ℝ (E k) := hD k
  choose p ω hp hpos hunit hwords using fun k => ((Q k).mem_canonicalProjectiveTables_iff_functional (hQ k)).mp (htab k)
  let V := factorProduct Q
  let ωV : (∀ k, E k) →ₗ[ℝ] ℝ := ∑ k, a k • ((ω k).comp (LinearMap.proj k))
  refine ⟨(∀ k, E k),inferInstance,inferInstance,inferInstance,V,factorProduct_formallyReal Q hQ,?_⟩
  apply (V.mem_canonicalProjectiveTables_iff_functional _).mpr
  refine ⟨fun i k => p k i,ωV,fun i => funext (fun k => hp k i),?_,?_,?_⟩
  · intro x
    simp only [ωV,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,LinearMap.comp_apply,
      LinearMap.proj_apply,V,factorProduct_apply]
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (ha k) (hpos k (x k)))
  · simpa only [ωV,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,LinearMap.comp_apply,
      LinearMap.proj_apply,V,factorProduct_unit,hunit,mul_one] using hs
  · intro w
    simp only [ωV,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,LinearMap.comp_apply,
      LinearMap.proj_apply,V,factorProduct_sequentialWordEffect,hwords,Finset.sum_apply,Pi.smul_apply]

end AlbertSequential
