/- SPDX-License-Identifier: Apache-2.0 -/
module
public import FrameSlotNormalizers
public import NativeRecoveredCoordinates
public import Glennie.Compactness
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Literal native trace polynomials in the generator list of Sydney Report 97-4,
Section 2, Proposition 1. The polynomial ring here has real coefficients. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.CompanionIltyakov

open MvPolynomial NativeAnalysis

/-- Bracketed monomials in the three generic arguments. -/
inductive TraceMonomial
  | var : Fin 3 → TraceMonomial
  | mul : TraceMonomial → TraceMonomial → TraceMonomial
  deriving DecidableEq

namespace TraceMonomial

def eval (x : Fin 3 → Albert) : TraceMonomial → Albert
  | .var i => x i
  | .mul t s => jordanMul (t.eval x) (s.eval x)

def degree : TraceMonomial → ℕ
  | .var _ => 1
  | .mul t s => t.degree + s.degree

def power (i : Fin 3) : ℕ → TraceMonomial
  | 0 => .var i
  | r + 1 => .mul (.var i) (power i r)

theorem eval_automorphism (g : NativeAlbertAutomorphism) (x : Fin 3 → Albert) (t : TraceMonomial) :
    t.eval (fun i => g.linearEquiv (x i)) = g.linearEquiv (t.eval x) := by
  induction t with
  | var _ => rfl
  | mul t s ht hs =>
    simp only [eval, ht, hs, g.preserves_product]

theorem trace_automorphism (g : NativeAlbertAutomorphism) (x : Fin 3 → Albert) (t : TraceMonomial) :
    albertTrace (t.eval (fun i => g.linearEquiv (x i))) = albertTrace (t.eval x) := by
  rw [eval_automorphism, g.preserves_trace]

end TraceMonomial

/-- The nine single-variable, twelve two-variable and eight three-variable traces. -/
abbrev GeneratorIndex := (Fin 3 × Fin 3) ⊕ (Fin 3 × Fin 2 × Fin 2) ⊕ (Fin 2 × Fin 2 × Fin 2)

theorem generatorIndex_card : Fintype.card GeneratorIndex = 29 := by decide

/-- The three cyclic pairs are `(x,y)`, `(y,z)`, `(z,x)`, with the printed bracketing. -/
def traceGenerator : GeneratorIndex → TraceMonomial
  | .inl (i, r) => .power i r.val
  | .inr (.inl (i, r, s)) => .mul (.power i r.val) (.power (i + 1) s.val)
  | .inr (.inr (r, s, t)) => .mul (.mul (.power 0 r.val) (.power 1 s.val)) (.power 2 t.val)

/-- The additional monomial `((z x) y)² ((z y) x)` whose trace is Iltyakov's ω. -/
def omegaMonomial : TraceMonomial :=
  let a := TraceMonomial.mul (.mul (.var 2) (.var 0)) (.var 1)
  let b := TraceMonomial.mul (.mul (.var 2) (.var 1)) (.var 0)
  .mul (.mul a a) b

def nativeBasis : Module.Basis (Fin 27) ℝ Albert :=
  Glennie.automorphismBasis.map recoveredCoordinateEquiv.symm

abbrev TracePolynomial := MvPolynomial (Fin 3 × Fin 27) ℝ

def coordinates (x : Fin 3 → Albert) (i : Fin 3 × Fin 27) : ℝ := nativeBasis.equivFun (x i.1) i.2

def structureConstant (i j k : Fin 27) : ℝ :=
  nativeBasis.equivFun (jordanMul (nativeBasis i) (nativeBasis j)) k

private def coordinateMap (k : Fin 27) : Albert →ₗ[ℝ] ℝ :=
  (LinearMap.proj k).comp nativeBasis.equivFun.toLinearMap

private def traceLinear : Albert →ₗ[ℝ] ℝ where
  toFun := albertTrace
  map_add' := albertTrace_add
  map_smul' := albertTrace_smul

private def nativeJordanBilinear : Albert →ₗ[ℝ] Albert →ₗ[ℝ] Albert where
  toFun a := {
    toFun := jordanMul a
    map_add' := jordanMul_add_right a
    map_smul' := fun r b => jordanMul_smul_right r a b }
  map_add' a b := LinearMap.ext fun x => jordanMul_add_left a b x
  map_smul' r a := LinearMap.ext fun x => jordanMul_smul_left r a x

private theorem structureConstant_expansion (x y : Albert) (k : Fin 27) :
    nativeBasis.equivFun (jordanMul x y) k =
      ∑ i, ∑ j, structureConstant i j k * (nativeBasis.equivFun x i * nativeBasis.equivFun y j) := by
  let a := nativeBasis.equivFun x
  let b := nativeBasis.equivFun y
  calc
    _ = coordinateMap k (nativeJordanBilinear (∑ i, a i • nativeBasis i) (∑ j, b j • nativeBasis j)) := by
      rw [nativeBasis.sum_equivFun x, nativeBasis.sum_equivFun y]
      rfl
    _ = _ := by
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum,
        smul_smul]
      conv_lhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change (b j * a i) * structureConstant i j k = _
      ring

private theorem trace_expansion (y : Albert) :
    albertTrace y = ∑ i, albertTrace (nativeBasis i) * nativeBasis.equivFun y i := by
  calc
    _ = traceLinear (∑ i, nativeBasis.equivFun y i • nativeBasis i) := by
      rw [nativeBasis.sum_equivFun]
      rfl
    _ = _ := by simp only [map_sum, map_smul, smul_eq_mul, traceLinear, LinearMap.coe_mk,
        AddHom.coe_mk, mul_comm]

/-- Coordinates of a bracketed monomial in actual polynomial variables. -/
def coordinatePolynomial : TraceMonomial → Fin 27 → TracePolynomial
  | .var i, k => X (i, k)
  | .mul t s, k => ∑ i, ∑ j, C (structureConstant i j k) *
      (coordinatePolynomial t i * coordinatePolynomial s j)

def tracePolynomial (t : TraceMonomial) : TracePolynomial :=
  ∑ k, C (albertTrace (nativeBasis k)) * coordinatePolynomial t k

theorem eval_coordinatePolynomial (x : Fin 3 → Albert) (t : TraceMonomial) (k : Fin 27) :
    MvPolynomial.eval (coordinates x) (coordinatePolynomial t k) = nativeBasis.equivFun (t.eval x) k := by
  induction t generalizing k with
  | var i => exact eval_X (i, k)
  | mul t s ht hs =>
    simp only [coordinatePolynomial, map_sum, map_mul, eval_C, ht, hs, TraceMonomial.eval]
    exact (structureConstant_expansion _ _ _).symm

theorem eval_tracePolynomial (t : TraceMonomial) (x : Fin 3 → Albert) :
    MvPolynomial.eval (coordinates x) (tracePolynomial t) = albertTrace (t.eval x) := by
  simp only [tracePolynomial, map_sum, map_mul, eval_C, eval_coordinatePolynomial]
  exact (trace_expansion _).symm

theorem coordinatePolynomial_homogeneous (t : TraceMonomial) (k : Fin 27) :
    (coordinatePolynomial t k).IsHomogeneous t.degree := by
  induction t generalizing k with
  | var i => exact isHomogeneous_X ℝ (i, k)
  | mul t s ht hs =>
    unfold coordinatePolynomial TraceMonomial.degree
    apply IsHomogeneous.sum
    intro i _
    apply IsHomogeneous.sum
    intro j _
    exact ((ht i).mul (hs j)).C_mul _

theorem tracePolynomial_homogeneous (t : TraceMonomial) : (tracePolynomial t).IsHomogeneous t.degree := by
  apply IsHomogeneous.sum
  intro k _
  exact (coordinatePolynomial_homogeneous t k).C_mul _

/-- The actual fixed polynomials for the compact-real diagonal action. -/
def nativeInvariantSubalgebra : Subalgebra ℝ TracePolynomial where
  carrier := {p | ∀ (g : NativeAlbertAutomorphism) (x : Fin 3 → Albert),
    MvPolynomial.eval (coordinates (fun i => g.linearEquiv (x i))) p = MvPolynomial.eval (coordinates x) p}
  algebraMap_mem' r g x := by simp [MvPolynomial.algebraMap_eq]
  add_mem' hp hq g x := by simp only [map_add, hp g x, hq g x]
  mul_mem' hp hq g x := by simp only [map_mul, hp g x, hq g x]
  zero_mem' g x := by simp
  one_mem' g x := by simp

theorem tracePolynomial_mem_nativeInvariantSubalgebra (t : TraceMonomial) :
    tracePolynomial t ∈ nativeInvariantSubalgebra := by
  intro g x
  simp only [eval_tracePolynomial, TraceMonomial.trace_automorphism]

def nativeIltyakovTraces : Set TracePolynomial :=
  Set.range (fun i : GeneratorIndex => tracePolynomial (traceGenerator i)) ∪ {tracePolynomial omegaMonomial}

theorem adjoin_nativeIltyakovTraces_le : Algebra.adjoin ℝ nativeIltyakovTraces ≤ nativeInvariantSubalgebra := by
  apply Algebra.adjoin_le
  rintro p (⟨i, rfl⟩ | hp)
  · exact tracePolynomial_mem_nativeInvariantSubalgebra _
  · obtain rfl : p = tracePolynomial omegaMonomial := hp
    exact tracePolynomial_mem_nativeInvariantSubalgebra _

theorem omegaPolynomial_totalDegree : (tracePolynomial omegaMonomial).totalDegree = 9 := by
  have h := tracePolynomial_homogeneous omegaMonomial
  apply h.totalDegree
  intro hz
  let p := diagAtom 0
  have hp := diagAtom_isAtom 0
  have hpIdem : jordanMul p p = p := hp.1
  have hEval : omegaMonomial.eval (fun _ => p) = p := by
    simp only [omegaMonomial, TraceMonomial.eval, hpIdem]
  have hOne := eval_tracePolynomial omegaMonomial (fun _ => p)
  rw [hz, map_zero, hEval, hp.2] at hOne
  exact zero_ne_one hOne

/-- Numeric multiscaling of the exact trace representative of ω. -/
theorem omega_multiscale (a b c : ℝ) (x y z : Albert) :
    albertTrace (omegaMonomial.eval ![a • x, b • y, c • z]) =
      a^3 * b^3 * c^3 * albertTrace (omegaMonomial.eval ![x,y,z]) := by
  simp [omegaMonomial, TraceMonomial.eval, jordanMul_smul_left, jordanMul_smul_right,
    smul_smul, albertTrace_smul]
  left
  ring

/-- The complex scalar extension of the native coordinates. -/
abbrev ComplexCoordinates := Fin 27 → ℂ

def extendRealCoordinates (a : Albert) : ComplexCoordinates := fun k => nativeBasis.equivFun a k

def complexJordanProduct (x y : ComplexCoordinates) : ComplexCoordinates :=
  fun k => ∑ i, ∑ j, (structureConstant i j k : ℂ) * (x i * y j)

def complexJordanTrace (x : ComplexCoordinates) : ℂ :=
  ∑ i, (albertTrace (nativeBasis i) : ℂ) * x i

theorem extendRealCoordinates_product (a b : Albert) :
    extendRealCoordinates (jordanMul a b) =
      complexJordanProduct (extendRealCoordinates a) (extendRealCoordinates b) := by
  funext k
  unfold extendRealCoordinates complexJordanProduct
  rw [structureConstant_expansion]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul]

theorem complexJordanTrace_extendRealCoordinates (a : Albert) :
    complexJordanTrace (extendRealCoordinates a) = (albertTrace a : ℂ) := by
  unfold complexJordanTrace extendRealCoordinates
  rw [trace_expansion a]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul]

def TraceMonomial.evalComplex (x : Fin 3 → ComplexCoordinates) : TraceMonomial → ComplexCoordinates
  | .var i => x i
  | .mul t s => complexJordanProduct (t.evalComplex x) (s.evalComplex x)

def complexTracePolynomial (t : TraceMonomial) : MvPolynomial (Fin 3 × Fin 27) ℂ :=
  MvPolynomial.map Complex.ofRealHom (tracePolynomial t)

theorem complexTracePolynomial_homogeneous (t : TraceMonomial) :
    (complexTracePolynomial t).IsHomogeneous t.degree :=
  (tracePolynomial_homogeneous t).map _

private theorem eval₂_coordinatePolynomial (x : Fin 3 → ComplexCoordinates) (t : TraceMonomial) (k : Fin 27) :
    MvPolynomial.eval₂ Complex.ofRealHom (fun i => x i.1 i.2) (coordinatePolynomial t k) = t.evalComplex x k := by
  induction t generalizing k with
  | var i => exact eval₂_X _ _ (i, k)
  | mul t s ht hs =>
    simp only [coordinatePolynomial, eval₂_sum, eval₂_mul, eval₂_C, ht, hs, TraceMonomial.evalComplex,
      complexJordanProduct]
    rfl

theorem eval_complexTracePolynomial (t : TraceMonomial) (x : Fin 3 → ComplexCoordinates) :
    MvPolynomial.eval (fun i => x i.1 i.2) (complexTracePolynomial t) = complexJordanTrace (t.evalComplex x) := by
  simp only [complexTracePolynomial, eval_map, tracePolynomial, eval₂_sum, eval₂_mul, eval₂_C,
    eval₂_coordinatePolynomial, complexJordanTrace]
  rfl

theorem complexTracePolynomial_invariant (t : TraceMonomial) (g : ComplexCoordinates ≃ₗ[ℂ] ComplexCoordinates)
    (hMul : ∀ x y, g (complexJordanProduct x y) = complexJordanProduct (g x) (g y))
    (hTrace : ∀ x, complexJordanTrace (g x) = complexJordanTrace x)
    (x : Fin 3 → ComplexCoordinates) :
    MvPolynomial.eval (fun i => g (x i.1) i.2) (complexTracePolynomial t) =
      MvPolynomial.eval (fun i => x i.1 i.2) (complexTracePolynomial t) := by
  have he : t.evalComplex (fun i => g (x i)) = g (t.evalComplex x) := by
    induction t with
    | var i => rfl
    | mul t s ht hs => simp only [TraceMonomial.evalComplex, ht, hs, hMul]
  calc
    _ = complexJordanTrace (t.evalComplex (fun i => g (x i))) :=
      eval_complexTracePolynomial t (fun i => g (x i))
    _ = _ := by rw [he, hTrace, eval_complexTracePolynomial]

end AlbertSequential.CompanionIltyakov
