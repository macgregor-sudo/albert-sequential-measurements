/- SPDX-License-Identifier: Apache-2.0 -/
module
public import LengthSeven.AlgebraicWalkSpace

@[expose] public section
noncomputable section
namespace AlbertSequential.LengthSeven
namespace AlgebraicWalkSpace
variable {V : Type*} [AddCommGroup V] [Module ℝ V] (W : AlgebraicWalkSpace V)

def headPath (x y z : Letter) := W.P z (W.P y (W.P x W.ξ))
def cornerPath (x y z : Letter) := W.P 0 (W.headPath x y z)
def returnPath (x y z : Letter) := W.P x (W.headPath x y z)

variable {τ : TraceData} (h : AlgebraicWalkHypotheses W τ)
include h

theorem printed_middle (x y z : Letter) (hs : IsOrderingBCD x y z) :
    W.L [x,y,z] = τ.om y := by
  have e := h.L_r3_base _ _ _ hs
  have r : W.L [z,y,x] = W.L [x,y,z] := W.L_reverse [x,y,z]
  linarith

theorem cornerPath_reverse_sum (x y z : Letter) (hs : IsOrderingBCD x y z) :
    W.cornerPath x y z + W.cornerPath z y x = (2*τ.om y) • W.ξ := by
  simpa only [cornerPath,headPath,W.fixA,add_comm] using h.r3 x y z hs

theorem returnPath_swap_sum (x y z : Letter) (hs : IsOrderingBCD x y z) :
    W.returnPath x y z + W.returnPath x z y = (2*τ.R x y z) • W.P x W.ξ := by
  obtain ⟨_,_,_,hxy,hyz,hxz⟩ := hs
  simpa only [returnPath,headPath,pathVec,List.reverse_nil,prodL_nil_apply,W.idem,add_comm]
    using h.r2 [] x y z hxy hyz hxz (by simp)

theorem cornerPath_pair_seed (x y z : Letter) (hs : IsOrderingBCD x y z) :
    W.form (W.cornerPath x y z) W.ξ = τ.om y := by
  rw [cornerPath,W.selfAdj,W.fixA,W.symm]
  exact (W.L_reverse [x,y,z]).trans (W.printed_middle h _ _ _ hs)

omit h in
theorem headPath_cornerPath (x y z u v w : Letter) :
    W.form (W.headPath x y z) (W.cornerPath u v w) =
      W.form (W.cornerPath x y z) (W.cornerPath u v w) := by
  simp only [cornerPath,W.selfAdj,W.idem]

theorem cornerPath_pair_reverse (x y z u v w : Letter)
    (hs : IsOrderingBCD x y z) (ht : IsOrderingBCD u v w) :
    W.form (W.cornerPath x y z) (W.cornerPath w v u) =
      2*τ.om y*τ.om v - W.form (W.cornerPath x y z) (W.cornerPath u v w) := by
  have e := congrArg (W.form (W.cornerPath x y z)) (W.cornerPath_reverse_sum h u v w ht)
  rw [map_add,map_smul,smul_eq_mul,W.cornerPath_pair_seed h _ _ _ hs] at e
  linarith

end AlgebraicWalkSpace
end AlbertSequential.LengthSeven
