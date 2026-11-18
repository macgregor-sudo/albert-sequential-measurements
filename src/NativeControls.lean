module

public import Defs
public import Mathlib.Tactic.NormNum

/-! Native model controls. They do not use the statements of `Challenge`. -/
@[expose] public section
namespace AlbertSequential

theorem unit_trace_control : albertTrace albertUnit = 3 := by
  norm_num [albertTrace, albertUnit, Fin.sum_univ_succ]

theorem unit_nonzero_control : albertUnit ≠ 0 := by
  intro h
  have h0 := congrArg (fun x : Albert => x.1 0) h
  change (1 : ℝ) = 0 at h0
  norm_num at h0

theorem zero_map_control (A : Type*) [NonUnitalRing A] [Module ℝ A] :
    IsJordanHom (0 : Albert →ₗ[ℝ] A) := by
  intro x y
  simp

/-- The zero-dimensional associative target is permitted, not excluded by
an accidental nontriviality or unit-preserving requirement. -/
theorem zero_ambient_control :
    IsJordanHom (0 : Albert →ₗ[ℝ] (Fin 0 → ℝ)) :=
  zero_map_control (Fin 0 → ℝ)

def octonionI : Octonion := (⟨0, 1, 0, 0⟩, 0)
def octonionJ : Octonion := (⟨0, 0, 1, 0⟩, 0)
def octonionL : Octonion := (0, 1)

/-- A nonassociative native product distinguishes it from pair multiplication. -/
theorem octonion_nonassociative_control :
    octonionMul (octonionMul octonionI octonionJ) octonionL ≠
      octonionMul octonionI (octonionMul octonionJ octonionL) := by
  intro h
  have hk := congrArg (fun x : Octonion => x.2.imK) h
  norm_num [octonionMul, octonionI, octonionJ, octonionL] at hk

/-- The coordinate projection API elaborates on sealed carriers. -/
theorem octonion_coordinate_control (x : Octonion) :
    (octonionConj x).2 = -x.2 := rfl

#print axioms unit_trace_control
#print axioms unit_nonzero_control
#print axioms zero_map_control
#print axioms zero_ambient_control
#print axioms octonion_nonassociative_control
#print axioms octonion_coordinate_control

end AlbertSequential
