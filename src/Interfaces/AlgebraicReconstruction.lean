module

public import Interfaces.WordsAndCertificates

/-! Statement types, not proofs of the paper. No statement of `Challenge`
is used here. The corner uses no ambient unit and no involution. -/
@[expose] public section
noncomputable section
namespace AlbertSequential

abbrev OverlapData := Fin 4 → Fin 4 → ℝ
abbrev TriangleData := Fin 4 → Fin 4 → Fin 4 → ℝ

/-- Exact R1--R3 subset, with base j=0 and other vertices k=1,l=2,m=3.
Arbitrary-base theorem is obtained only after a proved relabelling bridge. -/
structure CornerRelations {A : Type*} [NonUnitalRing A] [Module ℝ A]
    (X : Fin 4 → A) (o : OverlapData) (R : TriangleData) (Q : Fin 3 → ℝ) : Prop where
  idempotent : ∀ a, X a * X a = X a
  overlap_symmetric : ∀ a b, o a b = o b a
  triangle_swap : ∀ a b c, R a b c = R b a c ∧ R a b c = R a c b
  pair : ∀ a b, a ≠ b → X a * X b * X a = o a b • X a
  triangle_012 : X 0 * (X 1 * X 2 + X 2 * X 1) * X 0 = (2 * R 0 1 2) • X 0
  triangle_023 : X 0 * (X 2 * X 3 + X 3 * X 2) * X 0 = (2 * R 0 2 3) • X 0
  triangle_031 : X 0 * (X 3 * X 1 + X 1 * X 3) * X 0 = (2 * R 0 3 1) • X 0
  triangle_123 : X 1 * (X 2 * X 3 + X 3 * X 2) * X 1 = (2 * R 1 2 3) • X 1
  quadruple_123 : X 0 * (X 1 * X 2 * X 3 + X 3 * X 2 * X 1) * X 0 = (2 * Q 0) • X 0
  quadruple_231 : X 0 * (X 2 * X 3 * X 1 + X 1 * X 3 * X 2) * X 0 = (2 * Q 1) • X 0
  quadruple_312 : X 0 * (X 3 * X 1 * X 2 + X 2 * X 1 * X 3) * X 0 = (2 * Q 2) • X 0

/-- The denominator-free Delta of core appendix `sec:tet` at base0, with Q ordered123,231,312.
This is not the normalized statistic called Dtet. -/
def tetrahedronDiscriminant (o : OverlapData) (R : TriangleData) (Q : Fin 3 → ℝ) : ℝ :=
  let r₁ := R 0 1 2
  let r₂ := R 0 2 3
  let r₃ := R 0 3 1
  let b₁ := r₁ ^ 2 - o 0 1 * o 1 2 * o 2 0
  let b₂ := r₂ ^ 2 - o 0 2 * o 2 3 * o 3 0
  let b₃ := r₃ ^ 2 - o 0 3 * o 3 1 * o 1 0
  let b₁₂ := o 0 2 * Q 0 - r₁ * r₂
  let b₂₃ := o 0 3 * Q 1 - r₂ * r₃
  let b₁₃ := o 0 1 * Q 2 - r₃ * r₁
  let s := o 0 1 * o 0 2 * o 0 3 * R 1 2 3 - r₁ * r₂ * r₃ -
    r₁ * b₂₃ - r₂ * b₁₃ - r₃ * b₁₂
  show ℝ from -(b₁ * b₂ * b₃ + 2 * b₁₂ * b₂₃ * b₁₃ -
    b₁ * b₂₃ ^ 2 - b₂ * b₁₃ ^ 2 - b₃ * b₁₂ ^ 2) - s ^ 2

/-- The fixed-label algebraic engine, as a statement; it is proved in
`TetrahedronEngine`. No nonzero-corner assumption is allowed. -/
structure TetrahedronEngine (A : Type*) [NonUnitalRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] : Prop where
  annihilation : ∀ (X : Fin 4 → A) (o : OverlapData) (R : TriangleData)
    (Q : Fin 3 → ℝ), CornerRelations X o R Q →
    tetrahedronDiscriminant o R Q • X 0 = 0

/-- Native triple product, with every nonassociative bracket visible. -/
def jordanTriple (x y z : Albert) : Albert :=
  jordanMul (jordanMul x y) z + jordanMul (jordanMul z y) x -
    jordanMul (jordanMul x z) y

def nativeOverlaps (p : Fin 4 → Albert) : OverlapData :=
  fun i j => tracePairing (p i) (p j)
def nativeTriangles (p : Fin 4 → Albert) : TriangleData :=
  fun i j k => tracePairing (p i) (jordanMul (p j) (p k))
def nativeCornerQ (p : Fin 4 → Albert) : Fin 3 → ℝ :=
  ![tracePairing (p 0) (jordanTriple (p 1) (p 2) (p 3)),
    tracePairing (p 0) (jordanTriple (p 2) (p 3) (p 1)),
    tracePairing (p 0) (jordanTriple (p 3) (p 1) (p 2))]

/-- Unlabelled lemma immediately before thm:tetra:algebraic. This native
full-Albert version does not cover homomorphisms from a proper subalgebra. -/
structure NativeCornerBinding (A : Type*) [NonUnitalRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] : Prop where
  map_quadratic : ∀ (η : Albert →ₗ[ℝ] A), IsJordanHom η →
    ∀ x y, η (quadraticMap x y) = η x * η y * η x
  map_atoms : ∀ (η : Albert →ₗ[ℝ] A), IsJordanHom η →
    ∀ p : Fin 4 → Albert, (∀ i, IsAtom (p i)) →
      CornerRelations (fun i => η (p i)) (nativeOverlaps p) (nativeTriangles p) (nativeCornerQ p)

/-- Null set of a positive functional. It is not declared a two-sided ideal. -/
def NullFor {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (φ : A →ₗ[ℝ] ℝ) (x : A) : Prop := φ (star x * x) = 0

/-- Left action descends to the null quotient. It is proved from positive-functional
hypotheses (`nullFor_left_invariant`), not assumed inside the main no-go. -/
def NullLeftInvariant {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (φ : A →ₗ[ℝ] ℝ) : Prop :=
  ∀ a x, NullFor φ x → NullFor φ (a * x)

def WordVectorSpan {ι A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (P : ι → A) : Submodule ℝ A :=
  Submodule.span ℝ (Set.range (wordAmplitude P))

/-- Correct all-history conclusion is on the word-generated cyclic span.
It is not vanishing on an arbitrary larger ambient algebra. -/
structure AllHistoryNullContract {ι A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData ι A) : Prop where
  left_invariant : NullLeftInvariant M.state
  extend_to_span : ∀ Z,
    (∀ w, NullFor M.state (Z * wordAmplitude M.projection w)) →
    ∀ x ∈ WordVectorSpan M.projection, NullFor M.state (Z * x)

/-- Native purity c for an atom and an arbitrary suffix, including zero-mass
histories. A generic B-primitive version is not given here. -/
def purityElement {ι A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (P : ι → A) (i : ι) (v : Word ι) (c : ℝ) : A :=
  P i * wordOperator P v * P i - c • P i

structure NativePurityContract {ι A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData ι A) : Prop where
  null_every_history : ∀ p ρ, (∀ i, IsAtom (p i)) → IsDensity ρ → M.Matches p ρ →
    ∀ i v t, NullFor M.state
      (purityElement M.projection i v (nativeWordProbability p (p i) v) *
        wordAmplitude M.projection t)

/-- A deliberately small consumer: an assumed contract yields its own field.
This is interface elaboration only, not a proof of the engine. -/
example {A : Type*} [NonUnitalRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    (h : TetrahedronEngine A) (X : Fin 4 → A) (o : OverlapData)
    (R : TriangleData) (Q : Fin 3 → ℝ) (hR : CornerRelations X o R Q) :
    tetrahedronDiscriminant o R Q • X 0 = 0 := h.annihilation X o R Q hR

end AlbertSequential
