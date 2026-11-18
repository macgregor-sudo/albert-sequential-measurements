module

public import RealJordanPeirce

/-! Coefficients in a primitive corner for an explicitly supplied positive
associative real bilinear form. No norm, cone or finite-dimensional premise is
silently introduced. -/

@[expose] public section
noncomputable section
namespace AlbertSequential.RealJordan
variable {E : Type*} [NonUnitalNonAssocCommRing E]
  [Module ℝ E] [SMulCommClass ℝ E E] [IsCommJordan E]

/-- Associativity of the pairing makes multiplication self-adjoint. -/
theorem mul_pairing (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hB : ∀ a b c : E, B (a*b) c=B a (b*c)) (a x y : E) :
    B (a*x) y=B x (a*y) := by
  rw [mul_comm a x, hB]

/-- The polynomial U_a=2 L_a²−L_(a²) is self-adjoint for an associative form. -/
theorem quadraticRepresentation_pairing (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hB : ∀ a b c : E, B (a*b) c=B a (b*c)) (a x y : E) :
    B (quadraticRepresentation a x) y=B x (quadraticRepresentation a y) := by
  simp only [quadRep_apply, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul]
  rw [mul_pairing B hB a (a*x) y, mul_pairing B hB a x (a*y),
    mul_pairing B hB (a*a) x y]

/-- Exact coefficient in the paper's primitive-corner compression formula.
Positive definiteness is used only to justify the nonzero denominator. -/
theorem primitive_quadraticRepresentation_coefficient
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hB : ∀ a b c : E, B (a*b) c=B a (b*c))
    (hpositive : ∀ x : E, x≠0 → 0<B x x)
    (q x : E) (hq : IsPrimitiveIdempotent q) (hspan : CornerIdempotentsSpan q) :
    quadraticRepresentation q x=(B q x / B q q) • q := by
  obtain ⟨r, hr⟩ := primitive_quadraticRepresentation_eq_smul q x hq hspan
  have hden : B q q≠0 := ne_of_gt (hpositive q hq.2.1)
  have hcoeff : r * B q q=B q x := by
    calc
      _ = B q (r • q) := by
        simp only [map_smul, RingHom.id_apply, smul_eq_mul]
      _ = B q (quadraticRepresentation q x) := by rw [hr]
      _ = B (quadraticRepresentation q q) x :=
        (quadraticRepresentation_pairing B hB q q x).symm
      _ = B q x := by rw [quadraticRepresentation_idempotent_self q hq.1]
  have hratio : r=B q x/B q q := (eq_div_iff hden).mpr hcoeff
  rw [hr, hratio]

/-- The fundamental formula transports primitive compression to U_a q.
This gives a rank-at-most-one quadratic map; positivity and a spectral argument
are also required to conclude that a nonzero positive image is primitive. -/
theorem quadraticImage_primitive_compression
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hB : ∀ a b c : E, B (a*b) c=B a (b*c))
    (hpositive : ∀ x : E, x≠0 → 0<B x x)
    (a q x : E) (hq : IsPrimitiveIdempotent q) (hspan : CornerIdempotentsSpan q) :
    quadraticRepresentation (quadraticRepresentation a q) x=
      (B q (quadraticRepresentation a x)/B q q) • quadraticRepresentation a q := by
  rw [quadraticRepresentation_fundamental_apply,
    primitive_quadraticRepresentation_coefficient B hB hpositive q
      (quadraticRepresentation a x) hq hspan]
  exact map_smul (quadraticRepresentation a) _ q

/-- Nonnegativity of the corner coefficient on squares is a separate cone-form
compatibility consequence, not an algebraic consequence of the Jordan axiom. -/
theorem primitive_square_coefficient_nonneg
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hpositive : ∀ x : E, x≠0 → 0<B x x)
    (hsquares : ∀ u v : E, 0≤B (u*u) (v*v))
    (q y : E) (hq : IsPrimitiveIdempotent q) :
    0≤B q (y*y)/B q q := by
  have h := hsquares q y
  rw [hq.1] at h
  exact div_nonneg h (le_of_lt (hpositive q hq.2.1))

end AlbertSequential.RealJordan
