module

public import Defs
public import Mathlib.Analysis.Quaternion

/-! Coordinate topology for the native carriers. This is the ordinary finite
product topology on real quaternion coordinates. No norm, multiplication, unit
or star instance is exported on either native carrier. Topological compatibility
of the explicitly defined native operations is not proved in this module. -/

@[expose] public section
noncomputable section
namespace AlbertSequential

instance : TopologicalSpace Octonion :=
  inferInstanceAs (TopologicalSpace (Quaternion ℝ × Quaternion ℝ))

instance : TopologicalSpace Albert :=
  inferInstanceAs (TopologicalSpace ((Fin 3 → ℝ) × (Fin 3 → Octonion)))

end AlbertSequential
