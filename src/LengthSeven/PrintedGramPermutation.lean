/- SPDX-License-Identifier: Apache-2.0 -/
module
public import LengthSeven.PrintedGramTable

@[expose] public section
noncomputable section
namespace AlbertSequential.LengthSeven

def TraceData.reindex (τ : TraceData) (σ : Letter → Letter) : TraceData where
  o i j := τ.o (σ i) (σ j)
  R i j k := τ.R (σ i) (σ j) (σ k)
  om i := τ.om (σ i)
  o_symm _ _ := τ.o_symm _ _
  R_symm12 _ _ _ := τ.R_symm12 _ _ _
  R_symm23 _ _ _ := τ.R_symm23 _ _ _

theorem AlgebraicWalkRules.reindex {τ : TraceData} {L : List Letter → ℝ}
    (h : AlgebraicWalkRules τ L) (σ : Letter → Letter) (hi : Function.Injective σ) (hz : σ 0 = 0) :
    AlgebraicWalkRules (τ.reindex σ) (fun w => L (w.map σ)) := by
  have nz {x : Letter} (hx : x ≠ 0) : σ x ≠ 0 := hz ▸ hi.ne hx
  have ord {x y z} (hs : IsOrderingBCD x y z) : IsOrderingBCD (σ x) (σ y) (σ z) :=
    ⟨nz hs.1,nz hs.2.1,nz hs.2.2.1,hi.ne hs.2.2.2.1,hi.ne hs.2.2.2.2.1,hi.ne hs.2.2.2.2.2⟩
  constructor
  · exact h.empty
  · intro w; simpa only [List.map_reverse] using h.reverse (w.map σ)
  · intro w; simpa only [List.map_cons,hz] using h.dropLeftA (w.map σ)
  · intro w; simpa only [List.map_append,List.map_cons,List.map_nil,hz] using h.dropRightA (w.map σ)
  · intro u i v; simpa only [List.map_append,List.map_cons] using h.merge (u.map σ) (σ i) (v.map σ)
  · intro i hx; simpa only [TraceData.reindex,hz,List.map_cons,List.map_nil] using h.singleton (σ i) (nz hx)
  · intro i hx w; simpa only [TraceData.reindex,hz,List.map_cons] using h.secondA (σ i) (nz hx) (w.map σ)
  · intro i j hx hy hxy; simpa only [TraceData.reindex,hz,List.map_cons,List.map_nil] using
      h.pair _ _ (nz hx) (nz hy) (hi.ne hxy)
  · intro i j k hs; simpa only [TraceData.reindex,hz,List.map_cons,List.map_nil] using h.six _ _ _ (ord hs)
  · intro u v i j hij hv
    simpa only [TraceData.reindex,List.map_append,List.map_cons,List.map_nil] using
      h.r1 (u.map σ) (v.map σ) _ _ (hi.ne hij) (by simpa using hv)
  · intro u v i j k hij hjk hik hv
    simpa only [TraceData.reindex,List.map_append,List.map_cons,List.map_nil] using
      h.r2 (u.map σ) (v.map σ) _ _ _ (hi.ne hij) (hi.ne hjk) (hi.ne hik) (by simpa using hv)
  · intro i j k hs; exact h.r3Base _ _ _ (ord hs)
  · intro u i j k hs
    simpa only [TraceData.reindex,List.map_append,List.map_cons,List.map_nil,hz] using
      h.r3AfterA (u.map σ) _ _ _ (ord hs)

def printedTraces (τ : TraceData) (x y z : Letter) : Fin 13 → ℝ :=
  ![τ.o 0 x,τ.o 0 y,τ.o 0 z,τ.o x y,τ.o x z,τ.o y z,
    τ.R 0 x y,τ.R 0 x z,τ.R 0 y z,τ.R x y z,τ.om x,τ.om y,τ.om z]

theorem printedGramTable_ordered {τ : TraceData} {L : List Letter → ℝ}
    (h : AlgebraicWalkRules τ L) (x y z : Letter) (hs : IsOrderingBCD x y z)
    (i : Fin 9) (j : Fin 6) :
    let uv := printedHistories x y z i j
    L (uv.1 ++ uv.2.reverse) = printedGramTable (printedTraces τ x y z) i j := by
  let σ : Letter → Letter := ![0,x,y,z]
  have hi : Function.Injective σ := by
    obtain ⟨hx,hy,hz,hxy,hyz,hxz⟩ := hs
    intro a b
    fin_cases a <;> fin_cases b <;> simp_all [σ,ne_comm]
  have hm (k : PrintedPathKind) (a b c : Letter) :
      (k.history a b c).map σ = k.history (σ a) (σ b) (σ c) := by cases k <;> rfl
  have hh : let uv := printedHistories 1 2 3 i j
      (uv.1 ++ uv.2.reverse).map σ =
        (printedHistories x y z i j).1 ++ (printedHistories x y z i j).2.reverse := by
    simp only [printedHistories,List.map_append,List.map_reverse,hm]
    fin_cases j <;> rfl
  change L ((printedHistories x y z i j).1 ++ (printedHistories x y z i j).2.reverse) = _
  rw [← hh]
  exact printedGramTable_reference _ _ (h.reindex σ hi rfl) i j

end AlbertSequential.LengthSeven
