/- SPDX-License-Identifier: Apache-2.0 -/
module
public import LengthSeven.PrintedPaths
public import LengthSeven.WalkReductionGuide
import Mathlib.Tactic

@[expose] public section
noncomputable section
namespace AlbertSequential.LengthSeven

/-- Columns in the order xyz, xzy, yxz, yzx, zxy, zyx. Rows are HH, CC,
RR, RH, RC, JJ, JH, JC, JR. Inputs use the thirteen native trace coordinates. -/
def printedGramTable (v : Fin 13 → ℝ) : Fin 9 → Fin 6 → ℝ :=
  let ax := v 0; let ay := v 1; let az := v 2
  let xy := v 3; let xz := v 4; let yz := v 5
  let axy := v 6; let axz := v 7; let ayz := v 8; let xyz := v 9
  let ox := v 10; let oy := v 11; let oz := v 12
  let h1 := ax*xy*yz; let h2 := ax*yz*xyz; let h3 := 2*xyz*axy-xy*oz
  let h4 := xz*yz*axy; let h5 := xy*yz*axz; let h6 := 2*xyz*oy-h5
  let c1 := h1*az; let c2 := 2*ax*ayz*xyz-ax*yz*ox; let c3 := az*h3
  let r1 := h1*xz; let r2 := 2*ax*xyz^2-r1; let r4 := xy*h4
  let r3 := 2*xyz*h3-r4; let r5 := xz*h5; let r6 := 2*xz*xyz*oy-r5
  let rc1 := h1*axz; let rc4 := ax*h4
  let rc3 := 2*axz*h3-xz*(2*axy*oy-ax*xy*ayz)
  let jc1 := ax*xy*ayz; let jc2 := ax*ay*xyz; let jc5 := ay*xy*axz
  let jr1 := ax*xy*xyz; let jr5 := yz*xy*axz
  ![![h1,h2,h3,h4,h5,h6], ![c1,c2,c3,2*oy*oz-c2,2*ox*oy-c3,2*oy^2-c1],
    ![r1,r2,r3,r4,r5,r6], ![r1,r2,xz*h3,h4,xy*xz*oy,h6],
    ![rc1,2*ax*xyz*oz-rc4,rc3,rc4,2*ax*xyz*ox-rc3,2*ax*xyz*oy-rc1],
    ![ax*xy,ax*xyz,xy*axy,yz*axy,xy*axz,oy],
    ![h1,ax*xyz,h3,xy*oz,xy*axz,xy*oy],
    ![jc1,jc2,2*ox*axy-jc5,2*oz*axy-jc2,jc5,2*oy*axy-jc1],
    ![jr1,2*ax*xy*xyz-jr1,h3,2*xyz*axy-h3,jr5,2*xyz*oy-jr5]]

inductive PrintedPathKind | head | corner | ret | pair

def PrintedPathKind.history (k : PrintedPathKind) (x y z : Letter) : List Letter :=
  match k with
  | .head => [x,y,z]
  | .corner => [x,y,z,0]
  | .ret => [x,y,z,x]
  | .pair => [x,y]

def printedPathPairs : Fin 9 → PrintedPathKind × PrintedPathKind :=
  ![(.head,.head),(.corner,.corner),(.ret,.ret),(.ret,.head),(.ret,.corner),
    (.pair,.pair),(.pair,.head),(.pair,.corner),(.pair,.ret)]

def printedOrder (x y z : Letter) : Fin 6 → Letter × Letter × Letter :=
  ![(x,y,z),(x,z,y),(y,x,z),(y,z,x),(z,x,y),(z,y,x)]

def printedHistories (x y z : Letter) (i : Fin 9) (j : Fin 6) :
    List Letter × List Letter :=
  let q := printedOrder x y z j
  let k := printedPathPairs i
  (k.1.history x y z, k.2.history q.1 q.2.1 q.2.2)

private def reductionGuides : Fin 9 → Fin 6 → List ℕ :=
  ![![[0,0,0,0], [0,0,0], [0,0,0,1,0], [0,0,0], [0,0,0], [0,0,1,0,0]],
    ![[0,0,0,0,0], [0,1,0,2,0,0,0,0,1,0], [0,0,0,0,1,0], [0,2,0,0,0,0,1,0], [0,0,0,0,0,0,1,0], [0,0,0,0,0,0,0]],
    ![[0,0,0,0,0], [0,0,0,0,1,0,0,0], [0,0,0,1,0,1,0,0,0], [0,0,0,0], [3,0,0,0], [0,0,0,1,0,0]],
    ![[0,0,0,0], [0,0,0,1,0,0,0], [0,0,0,1,0], [0,0,0,0], [0,1,0], [0,0,0,1,0,0]],
    ![[0,0,0,0,0,0,1,0,0], [0,0,0,0,0,0,0], [0,0,0,1,0,1,0,0,0,1,0,0], [0,0,0,0], [0,0,0,0,0,1,0,2,0,0,2,0,0,1,1,0,0,1,0], [0,0,0,1,0,0]],
    ![[0,0,0], [0,0], [0,0], [0,0], [0,0], [0,0]],
    ![[0,0,0], [0,0,0], [0,0,1,0], [0,0], [0,0,0], [0,0]],
    ![[0], [0,0,0], [1,0,0,1,0], [0,0,0,0,0], [0,0,0], [1,0,0]],
    ![[0,0,0], [0,0,0], [0,0,0,1,0], [0,0,0], [0,0,0], [0,0,1,0,0]]]

private def reducedEntries : Fin 9 → Fin 6 → WalkPolynomial :=
  ![![(.mul (.integer 1) (.mul (.input 5) (.mul (.input 3) (.input 0)))), (.mul (.input 5) (.mul (.input 9) (.input 0))), (.mul (.integer 1) (.sub (.mul (.mul (.integer 2) (.input 9)) (.input 6)) (.mul (.input 3) (.input 12)))), (.mul (.input 4) (.mul (.input 5) (.input 6))), (.mul (.input 5) (.mul (.input 3) (.input 7))), (.sub (.mul (.mul (.integer 2) (.input 9)) (.input 11)) (.mul (.input 5) (.mul (.input 3) (.input 7))))],
    ![(.mul (.integer 1) (.mul (.input 2) (.mul (.input 5) (.mul (.input 3) (.input 0))))), (.mul (.integer 1) (.sub (.mul (.mul (.integer 2) (.input 12)) (.input 11)) (.sub (.mul (.mul (.integer 2) (.input 11)) (.input 12)) (.mul (.input 0) (.sub (.mul (.mul (.integer 2) (.input 9)) (.input 8)) (.mul (.input 5) (.input 10))))))), (.mul (.integer 1) (.mul (.input 2) (.sub (.mul (.mul (.integer 2) (.input 9)) (.input 6)) (.mul (.input 3) (.input 12))))), (.mul (.integer 1) (.sub (.mul (.mul (.integer 2) (.input 11)) (.input 12)) (.mul (.input 0) (.sub (.mul (.mul (.integer 2) (.input 9)) (.input 8)) (.mul (.input 5) (.input 10)))))), (.mul (.integer 1) (.sub (.mul (.mul (.integer 2) (.input 10)) (.input 11)) (.mul (.input 2) (.sub (.mul (.mul (.integer 2) (.input 9)) (.input 6)) (.mul (.input 3) (.input 12)))))), (.mul (.integer 1) (.sub (.mul (.mul (.integer 2) (.input 11)) (.input 11)) (.mul (.input 2) (.mul (.input 5) (.mul (.input 3) (.input 0))))))],
    ![(.mul (.integer 1) (.mul (.input 4) (.mul (.input 5) (.mul (.input 3) (.input 0))))), (.mul (.integer 1) (.sub (.mul (.mul (.integer 2) (.input 9)) (.mul (.input 9) (.input 0))) (.mul (.input 4) (.mul (.input 5) (.mul (.input 3) (.input 0)))))), (.sub (.mul (.mul (.integer 2) (.input 9)) (.sub (.mul (.mul (.integer 2) (.input 9)) (.input 6)) (.mul (.input 3) (.input 12)))) (.mul (.input 3) (.mul (.input 4) (.mul (.input 5) (.input 6))))), (.mul (.input 3) (.mul (.input 4) (.mul (.input 5) (.input 6)))), (.mul (.input 4) (.mul (.input 5) (.mul (.input 3) (.input 7)))), (.mul (.input 4) (.sub (.mul (.mul (.integer 2) (.input 9)) (.input 11)) (.mul (.input 5) (.mul (.input 3) (.input 7)))))],
    ![(.mul (.input 4) (.mul (.input 5) (.mul (.input 3) (.input 0)))), (.sub (.mul (.mul (.integer 2) (.input 9)) (.mul (.input 9) (.input 0))) (.mul (.input 4) (.mul (.input 5) (.mul (.input 3) (.input 0))))), (.mul (.input 4) (.sub (.mul (.mul (.integer 2) (.input 9)) (.input 6)) (.mul (.input 3) (.input 12)))), (.mul (.integer 1) (.mul (.input 4) (.mul (.input 5) (.input 6)))), (.mul (.input 3) (.mul (.input 4) (.input 11))), (.mul (.integer 1) (.sub (.mul (.mul (.integer 2) (.input 9)) (.input 11)) (.mul (.input 5) (.mul (.input 3) (.input 7)))))],
    ![(.sub (.mul (.mul (.integer 2) (.input 11)) (.mul (.input 9) (.input 0))) (.mul (.input 0) (.sub (.mul (.mul (.integer 2) (.input 9)) (.input 11)) (.mul (.input 5) (.mul (.input 3) (.input 7)))))), (.sub (.mul (.mul (.integer 2) (.input 12)) (.mul (.input 9) (.input 0))) (.mul (.input 0) (.mul (.input 4) (.mul (.input 5) (.input 6))))), (.sub (.mul (.mul (.integer 2) (.input 7)) (.sub (.mul (.mul (.integer 2) (.input 9)) (.input 6)) (.mul (.input 3) (.input 12)))) (.sub (.mul (.mul (.integer 2) (.input 6)) (.mul (.input 4) (.mul (.integer 1) (.input 11)))) (.mul (.integer 1) (.mul (.input 4) (.mul (.mul (.input 0) (.input 3)) (.input 8)))))), (.mul (.input 0) (.mul (.input 4) (.mul (.input 5) (.input 6)))), (.sub (.mul (.mul (.integer 2) (.input 6)) (.sub (.mul (.mul (.integer 2) (.input 9)) (.input 7)) (.sub (.mul (.mul (.integer 2) (.input 9)) (.input 7)) (.mul (.input 4) (.input 11))))) (.sub (.mul (.mul (.integer 2) (.input 9)) (.sub (.mul (.mul (.integer 2) (.input 6)) (.input 7)) (.mul (.input 0) (.mul (.integer 1) (.input 10))))) (.mul (.input 3) (.sub (.mul (.mul (.integer 2) (.input 7)) (.mul (.integer 1) (.input 12))) (.mul (.integer 1) (.mul (.mul (.input 0) (.input 4)) (.input 8))))))), (.mul (.input 0) (.sub (.mul (.mul (.integer 2) (.input 9)) (.input 11)) (.mul (.input 5) (.mul (.input 3) (.input 7)))))],
    ![(.mul (.integer 1) (.mul (.input 3) (.input 0))), (.mul (.input 9) (.input 0)), (.mul (.input 3) (.input 6)), (.mul (.input 5) (.input 6)), (.mul (.input 3) (.input 7)), (.mul (.integer 1) (.input 11))],
    ![(.mul (.input 5) (.mul (.input 3) (.input 0))), (.mul (.integer 1) (.mul (.input 9) (.input 0))), (.sub (.mul (.mul (.integer 2) (.input 9)) (.input 6)) (.mul (.input 3) (.input 12))), (.mul (.input 3) (.input 12)), (.mul (.integer 1) (.mul (.input 3) (.input 7))), (.mul (.input 3) (.input 11))],
    ![(.mul (.mul (.input 0) (.input 3)) (.input 8)), (.mul (.input 1) (.mul (.input 9) (.input 0))), (.sub (.mul (.mul (.integer 2) (.input 6)) (.mul (.integer 1) (.input 10))) (.mul (.integer 1) (.mul (.mul (.input 1) (.input 3)) (.input 7)))), (.sub (.mul (.mul (.integer 2) (.input 12)) (.input 6)) (.mul (.input 1) (.mul (.input 9) (.input 0)))), (.mul (.input 1) (.mul (.input 3) (.input 7))), (.sub (.mul (.mul (.integer 2) (.input 11)) (.input 6)) (.mul (.mul (.input 0) (.input 3)) (.input 8)))],
    ![(.mul (.input 9) (.mul (.input 3) (.input 0))), (.mul (.input 3) (.mul (.input 9) (.input 0))), (.mul (.integer 1) (.sub (.mul (.mul (.integer 2) (.input 9)) (.input 6)) (.mul (.input 3) (.input 12)))), (.mul (.integer 1) (.mul (.input 3) (.input 12))), (.mul (.input 5) (.mul (.input 3) (.input 7))), (.sub (.mul (.mul (.integer 2) (.input 9)) (.input 11)) (.mul (.input 5) (.mul (.input 3) (.input 7))))]]

deriving instance DecidableEq for WalkPolynomial

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem checkedGuides : ∀ i j,
    let uv := printedHistories 1 2 3 i j
    guidedWalk 13 (uv.1 ++ uv.2.reverse) (reductionGuides i j) = some (reducedEntries i j, []) := by
  decide +kernel

private theorem reducedEntries_eval (v : Fin 13 → ℝ) (i : Fin 9) (j : Fin 6) :
    (reducedEntries i j).eval v = printedGramTable v i j := by
  fin_cases i <;> fin_cases j <;>
    simp [reducedEntries,printedGramTable,WalkPolynomial.eval] <;> ring <;> simp

theorem printedGramTable_reference (τ : TraceData) (L : List Letter → ℝ)
    (h : AlgebraicWalkRules τ L) (i : Fin 9) (j : Fin 6) :
    let uv := printedHistories 1 2 3 i j
    L (uv.1 ++ uv.2.reverse) = printedGramTable (walkTraceCoordinates τ) i j :=
  (guidedWalk_sound τ L h _ _ _ (checkedGuides i j)).trans (reducedEntries_eval _ i j)

end AlbertSequential.LengthSeven
