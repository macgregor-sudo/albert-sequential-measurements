module

public import RealJordanFundamental
public import Mathlib.LinearAlgebra.Span.Basic

/-! Algebraic Peirce-one projection and primitive-corner mechanism.
The EJA spectral input is an explicit idempotent-span hypothesis, not a field
of a purported Jordan algebra and not silently supplied by finite dimension. -/

@[expose] public section
noncomputable section
namespace AlbertSequential.RealJordan
variable {E : Type*} [NonUnitalNonAssocCommRing E]
  [Module ℝ E] [SMulCommClass ℝ E E] [IsCommJordan E]

/-- The Peirce-one space, defined by the actual multiplication operator. -/
def peirceOneSubmodule (q : E) : Submodule ℝ E :=
  (leftMultiplication q - LinearMap.id).ker

@[simp] theorem mem_peirceOneSubmodule (q x : E) :
    x ∈ peirceOneSubmodule q ↔ q*x=x := by
  change q*x-x=0 ↔ q*x=x
  exact sub_eq_zero

/-- An idempotent's multiplication operator has eigenvalues among 0, 1/2, 1.
This polynomial identity itself needs no spectral theorem. -/
theorem idempotent_multiplication_cubic (q x : E) (hq : q*q=q) :
    (2 : ℝ) • (q*(q*(q*x))) - (3 : ℝ) • (q*(q*x)) + q*x = 0 := by
  have h := cyclic_mulLeft_commutator q q x q
  simp only [hq, mul_comm x q, mul_comm (q*x) q] at h
  linear_combination (norm := module) h

/-- The image of U_q is fixed by multiplication by q. -/
theorem mul_quadraticRepresentation_idempotent (q x : E) (hq : q*q=q) :
    q*(quadraticRepresentation q x)=quadraticRepresentation q x := by
  rw [quadRep_apply]
  simp only [mul_sub, mul_smul_comm, hq]
  have h := idempotent_multiplication_cubic q x hq
  linear_combination (norm := module) h

/-- U_q acts as the identity on its Peirce-one space. -/
theorem quadraticRepresentation_of_mul_eq (q x : E) (hq : q*q=q)
    (hx : q*x=x) : quadraticRepresentation q x=x := by
  simp only [quadRep_apply, hq, hx, two_smul]
  abel

theorem quadraticRepresentation_idempotent_self (q : E) (hq : q*q=q) :
    quadraticRepresentation q q=q := quadraticRepresentation_of_mul_eq q q hq hq

/-- The exact algebraic range identity U_q E = E_1(q). -/
theorem quadraticRepresentation_idempotent_range (q : E) (hq : q*q=q) :
    Set.range (quadraticRepresentation q) = {x | q*x=x} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact mul_quadraticRepresentation_idempotent q y hq
  · intro hx
    exact ⟨x, quadraticRepresentation_of_mul_eq q x hq hx⟩

/-- An idempotent's quadratic representation is a linear projection. -/
theorem quadraticRepresentation_idempotent_comp (q : E) (hq : q*q=q) :
    (quadraticRepresentation q).comp (quadraticRepresentation q)=
      quadraticRepresentation q := by
  ext x
  exact quadraticRepresentation_of_mul_eq q _ hq
    (mul_quadraticRepresentation_idempotent q x hq)

/-- Bundled form of the range identity for use inside a generated subalgebra. -/
theorem quadraticRepresentation_range_eq_peirceOne (q : E) (hq : q*q=q) :
    LinearMap.range (quadraticRepresentation q)=peirceOneSubmodule q := by
  ext x
  rw [mem_peirceOneSubmodule]
  change x ∈ Set.range (quadraticRepresentation q) ↔ q*x=x
  rw [quadraticRepresentation_idempotent_range q hq]
  rfl

/-- Standard no-orthogonal-split primitivity, with nonzero idempotence explicit. -/
def IsPrimitiveIdempotent (q : E) : Prop :=
  q*q=q ∧ q≠0 ∧ ∀ r s : E, r*r=r → s*s=s → r*s=0 → r+s=q → r=0 ∨ s=0

/-- The precise spectral input needed below. In an EJA this follows from a
corner spectral decomposition. It is not proved here or inferred from a norm. -/
def CornerIdempotentsSpan (q : E) : Prop :=
  peirceOneSubmodule q ≤ Submodule.span ℝ {r : E | r*r=r ∧ q*r=r}

theorem primitive_corner_idempotent_eq_zero_or (q r : E)
    (hq : IsPrimitiveIdempotent q) (hr : r*r=r) (hqr : q*r=r) :
    r=0 ∨ r=q := by
  have hcomp : (q-r)*(q-r)=q-r := by
    simp only [sub_mul, mul_sub, hq.1, hr, hqr, mul_comm r q]
    abel
  have horth : r*(q-r)=0 := by
    rw [mul_sub, mul_comm r q, hqr, hr, sub_self]
  have hsum : r+(q-r)=q := by abel
  rcases hq.2.2 r (q-r) hr hcomp horth hsum with hzero | hzero
  · exact Or.inl hzero
  · exact Or.inr (sub_eq_zero.mp hzero).symm

/-- Primitive gives a one-dimensional corner only with the separately exposed
idempotent-span input. This is the general-EJA dependency boundary. -/
theorem primitive_peirceOne_eq_span (q : E) (hq : IsPrimitiveIdempotent q)
    (hspan : CornerIdempotentsSpan q) :
    peirceOneSubmodule q = Submodule.span ℝ {q} := by
  apply le_antisymm
  · apply le_trans hspan
    apply Submodule.span_le.mpr
    intro r hr
    rcases primitive_corner_idempotent_eq_zero_or q r hq hr.1 hr.2 with hzero | heq
    · rw [hzero]
      exact Submodule.zero_mem _
    · rw [heq]
      exact Submodule.subset_span (Set.mem_singleton q)
  · apply Submodule.span_le.mpr
    intro r hr
    have heq := Set.mem_singleton_iff.mp hr
    rw [heq]
    exact (mem_peirceOneSubmodule q q).mpr hq.1

/-- The paper's U_q x = λ q conclusion, with its spectral premise visible. -/
theorem primitive_quadraticRepresentation_eq_smul (q x : E)
    (hq : IsPrimitiveIdempotent q) (hspan : CornerIdempotentsSpan q) :
    ∃ r : ℝ, quadraticRepresentation q x=r • q := by
  have hx : quadraticRepresentation q x ∈ peirceOneSubmodule q :=
    (mem_peirceOneSubmodule _ _).mpr (mul_quadraticRepresentation_idempotent q x hq.1)
  rw [primitive_peirceOne_eq_span q hq hspan] at hx
  rcases Submodule.mem_span_singleton.mp hx with ⟨r, hr⟩
  exact ⟨r, hr.symm⟩

/-- Conversely a nonzero idempotent with a one-dimensional corner is primitive.
This direction needs no spectral premise. -/
theorem isPrimitiveIdempotent_of_peirceOne_eq_span (q : E) (hq : q*q=q)
    (hne : q≠0) (hcorner : peirceOneSubmodule q=Submodule.span ℝ {q}) :
    IsPrimitiveIdempotent q := by
  refine ⟨hq, hne, ?_⟩
  intro r s hr hs horth hsum
  have hqr : q*r=r := by
    rw [← hsum, add_mul, hr, mul_comm s r, horth, add_zero]
  have hqs : q*s=s := by
    rw [← hsum, add_mul, horth, hs, zero_add]
  have hmr : r ∈ Submodule.span ℝ {q} := by
    rw [← hcorner]
    exact (mem_peirceOneSubmodule q r).mpr hqr
  have hms : s ∈ Submodule.span ℝ {q} := by
    rw [← hcorner]
    exact (mem_peirceOneSubmodule q s).mpr hqs
  rcases Submodule.mem_span_singleton.mp hmr with ⟨a, ha⟩
  rcases Submodule.mem_span_singleton.mp hms with ⟨b, hb⟩
  have hab : (a*b) • q=0 := by
    calc
      _ = (a • q)*(b • q) := by
        rw [smul_mul_real, mul_smul_comm, smul_smul, hq]
      _ = 0 := by rw [ha, hb, horth]
  rcases smul_eq_zero.mp hab with hab | hzero
  · rcases mul_eq_zero.mp hab with ha0 | hb0
    · left
      rw [← ha, ha0, zero_smul]
    · right
      rw [← hb, hb0, zero_smul]
  · exact (hne hzero).elim

theorem primitive_iff_peirceOne_eq_span (q : E) (hq : q*q=q) (hne : q≠0)
    (hspan : CornerIdempotentsSpan q) :
    IsPrimitiveIdempotent q ↔ peirceOneSubmodule q=Submodule.span ℝ {q} := by
  exact ⟨fun hp => primitive_peirceOne_eq_span q hp hspan,
    isPrimitiveIdempotent_of_peirceOne_eq_span q hq hne⟩

/-- Exact bundled U_q E = ℝq, retaining the EJA spectral boundary. -/
theorem primitive_quadraticRepresentation_range (q : E)
    (hq : IsPrimitiveIdempotent q) (hspan : CornerIdempotentsSpan q) :
    LinearMap.range (quadraticRepresentation q)=Submodule.span ℝ {q} := by
  rw [quadraticRepresentation_range_eq_peirceOne q hq.1,
    primitive_peirceOne_eq_span q hq hspan]

end AlbertSequential.RealJordan
