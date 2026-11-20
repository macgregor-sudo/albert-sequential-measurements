module

import AssociativeDyadOverlap
import NativeFrameGeneration
import NativeFrameCoarseGraining
import JordanConeUnitInterior

open AlbertSequential

example (F : NativeJordanFrame) :
    (generatedSubalgebra (Set.range F.atom)).carrier = Submodule.span ℝ (Set.range F.atom) :=
  generated_frame_is_diagonal_span F

example : ∃ F : Fin 4 → NativeJordanFrame,
    GeneratesAlbert (fun i : Fin 4 × Fin 3 => (F i.1).atom i.2) :=
  exists_four_generating_frames

example (F : OctSubalgebra)
    (ha : ∀ x ∈ F.carrier, ∀ y ∈ F.carrier, ∀ z ∈ F.carrier, octAssociator x y z = 0)
    (u v : Fin 3 → Octonion) (hu : ∀ i, u i ∈ F.carrier) (hv : ∀ i, v i ∈ F.carrier)
    (hn : octColumnNormSq u ≠ 0) (hm : octColumnNormSq v ≠ 0) :
    tracePairing (normalizedOctDyad u) (normalizedOctDyad v) =
      octNormSq (octColumnInner u v) / (octColumnNormSq u * octColumnNormSq v) :=
  (normalizedOctDyad_atom_and_overlap F ha u v hu hv hn hm).2.2

#print axioms AlbertSequential.normalizedOctDyad_atom_and_overlap
#print axioms AlbertSequential.UnitalJordanProduct.unit_mem_interior_squareCone
#print axioms AlbertSequential.atom_extends_to_labelled_frame
#print axioms AlbertSequential.exists_four_generating_frames
#print axioms AlbertSequential.generated_frame_is_diagonal_span
#print axioms AlbertSequential.frameCoarseNoUpdate_ne_binaryComplement
