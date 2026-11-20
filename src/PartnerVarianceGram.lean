/- SPDX-License-Identifier: Apache-2.0 -/
module

public import PartnerVariancePolynomial
public import LengthSeven.PrintedPhysicalGram

@[expose] public section
noncomputable section

namespace AlbertSequential.LengthSeven

open scoped BigOperators
open PartnerVariance (signedCCRow signedCCRow_split quadraticCCRow quadraticCC quadraticCC_eq)

/-- The sign of each ordering in the printed column convention. -/
def printedSign : Fin 6 → ℝ := ![1, -1, -1, 1, 1, -1]

private def relativeOrder (s : Fin 6) : Fin 6 → Fin 6 :=
  ![![0,1,2,3,4,5], ![1,0,4,5,2,3], ![2,3,0,1,5,4],
    ![3,2,5,4,0,1], ![4,5,1,0,3,2], ![5,4,3,2,1,0]] s

private theorem relativeOrder_bijective : ∀ s, Function.Bijective (relativeOrder s) := by decide

private def relativePerm (s : Fin 6) : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective (relativeOrder s) (relativeOrder_bijective s)

private theorem tripleOrdering : ∀ s : Fin 6,
    let t := printedOrder 1 2 3 s
    IsOrderingBCD t.1 t.2.1 t.2.2 := by decide

private theorem relativeOrder_identity : ∀ s j : Fin 6,
    let t := printedOrder 1 2 3 s
    printedOrder 1 2 3 (relativeOrder s j) = printedOrder t.1 t.2.1 t.2.2 j := by decide

private theorem relativeSign (s j : Fin 6) :
    printedSign s * printedSign (relativePerm s j) = printedSign j := by
  change printedSign s * printedSign (relativeOrder s j) = _
  fin_cases s <;> fin_cases j <;> norm_num [printedSign, relativeOrder]

def printedSignedRow (d : Fin 13 → ℝ) (row : Fin 9) : ℝ :=
  ∑ j : Fin 6, printedSign j * printedGramTable d row j

def rowTrace (τ : TraceData) (s : Fin 6) : Fin 13 → ℝ :=
  let t := printedOrder 1 2 3 s
  printedTraces τ t.1 t.2.1 t.2.2

def printedSignedGram (τ : TraceData) (row : Fin 9) : ℝ :=
  ∑ s : Fin 6, printedSignedRow (rowTrace τ s) row

section Form

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (W : WalkForm V)

def printedPath (k : PrintedPathKind) (s : Fin 6) : V :=
  let t := printedOrder 1 2 3 s
  W.pathVec (k.history t.1 t.2.1 t.2.2)

def printedKappa (k : PrintedPathKind) : V := ∑ s : Fin 6, printedSign s • printedPath W k s

def printedPhi : V := (4 : ℝ) • printedKappa W .corner + (10 : ℝ) • printedKappa W .ret -
  (9 : ℝ) • printedKappa W .head

theorem printedKappa_pairing {τ : TraceData} (h : HasPrintedGram W τ) (row : Fin 9) :
    W.form (printedKappa W (printedPathPairs row).1) (printedKappa W (printedPathPairs row).2) =
      printedSignedGram τ row := by
  unfold printedSignedGram
  rw [printedKappa, map_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro s _
  rw [map_smul, LinearMap.smul_apply, printedKappa, map_sum]
  simp only [map_smul, smul_eq_mul, Finset.mul_sum, printedSignedRow]
  rw [← Equiv.sum_comp (relativePerm s)]
  apply Finset.sum_congr rfl
  intro j _
  have he (k : PrintedPathKind) : printedPath W k (relativePerm s j) =
      let t := printedOrder 1 2 3 s
      let r := printedOrder t.1 t.2.1 t.2.2 j
      W.pathVec (k.history r.1 r.2.1 r.2.2) := by
    unfold printedPath
    rw [show relativePerm s j = relativeOrder s j from rfl, relativeOrder_identity s j]
  rw [he, ← mul_assoc, relativeSign]
  congr 1
  exact h _ _ _ (tripleOrdering s) row j

private theorem corner_eq_application (s : Fin 6) :
    printedPath W .corner s = W.P 0 (printedPath W .head s) := by
  unfold printedPath
  dsimp only [PrintedPathKind.history]
  rw [W.pathVec_eq, W.pathVec_eq]
  rfl

theorem printedKappa_HC (τ : TraceData) (h : HasPrintedGram W τ) :
    W.form (printedKappa W .head) (printedKappa W .corner) = printedSignedGram τ 1 := by
  have hc : printedKappa W .corner = W.P 0 (printedKappa W .head) := by
    simp only [printedKappa, corner_eq_application, map_sum, map_smul]
  have hcc := printedKappa_pairing W h 1
  change W.form (printedKappa W .corner) (printedKappa W .corner) = _ at hcc
  rw [← hcc, hc, W.selfAdj, W.idem]

end Form

def printedPhiValue (τ : TraceData) : ℝ :=
  81 * printedSignedGram τ 0 - 56 * printedSignedGram τ 1 + 100 * printedSignedGram τ 2 -
    180 * printedSignedGram τ 3 + 80 * printedSignedGram τ 4

theorem printedPhi_form {V : Type*} [AddCommGroup V] [Module ℝ V] (W : WalkForm V)
    {τ : TraceData} (h : HasPrintedGram W τ) : W.form (printedPhi W) (printedPhi W) = printedPhiValue τ := by
  have hh := printedKappa_pairing W h 0
  have cc := printedKappa_pairing W h 1
  have rr := printedKappa_pairing W h 2
  have rh := printedKappa_pairing W h 3
  have rc := printedKappa_pairing W h 4
  have hc := printedKappa_HC W τ h
  change W.form (printedKappa W .head) (printedKappa W .head) = _ at hh
  change W.form (printedKappa W .corner) (printedKappa W .corner) = _ at cc
  change W.form (printedKappa W .ret) (printedKappa W .ret) = _ at rr
  change W.form (printedKappa W .ret) (printedKappa W .head) = _ at rh
  change W.form (printedKappa W .ret) (printedKappa W .corner) = _ at rc
  simp only [printedPhi, map_sub, map_add, map_smul, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]
  rw [W.symm (printedKappa W .corner) (printedKappa W .head),
    W.symm (printedKappa W .corner) (printedKappa W .ret),
    W.symm (printedKappa W .head) (printedKappa W .ret), hh, cc, rr, rh, rc, hc]
  unfold printedPhiValue
  ring

def ccAffine (d : Fin 13 → ℝ) : ℝ :=
  2 * (printedGramTable d 1 0 - printedGramTable d 1 1 - printedGramTable d 1 2)

private theorem signedCC_split (d : Fin 13 → ℝ) :
    printedSignedRow d 1 = ccAffine d + quadraticCCRow (d 10) (d 11) (d 12) := by
  have h := signedCCRow_split (d 10) (d 11) (d 12)
    (printedGramTable d 1 0) (printedGramTable d 1 1) (printedGramTable d 1 2)
  rw [ccAffine, ← h]
  simp [printedSignedRow, Fin.sum_univ_succ, printedSign, printedGramTable, signedCCRow]
  ring

def printedCCAffine (τ : TraceData) : ℝ := ∑ s : Fin 6, ccAffine (rowTrace τ s)

theorem printedSignedGram_CC (τ : TraceData) :
    printedSignedGram τ 1 = printedCCAffine τ + quadraticCC (τ.om 1) (τ.om 2) (τ.om 3) := by
  simp only [printedSignedGram, signedCC_split, Finset.sum_add_distrib, printedCCAffine]
  congr 1
  simp [Fin.sum_univ_succ, rowTrace, printedOrder, printedTraces, quadraticCC, add_assoc]

def printedPhiAffine (τ : TraceData) : ℝ :=
  81 * printedSignedGram τ 0 - 56 * printedCCAffine τ + 100 * printedSignedGram τ 2 -
    180 * printedSignedGram τ 3 + 80 * printedSignedGram τ 4

theorem printedPhi_variance_decomposition (τ : TraceData) :
    printedPhiValue τ = printedPhiAffine τ - 56 *
      (4 * (τ.om 1 + τ.om 2 + τ.om 3)^2 - 8 * ((τ.om 1)^2 + (τ.om 2)^2 + (τ.om 3)^2)) := by
  rw [printedPhiValue, printedSignedGram_CC, quadraticCC_eq]
  unfold printedPhiAffine
  ring

private def phiAffineRow (d : Fin 13 → ℝ) : ℝ :=
  81 * printedSignedRow d 0 - 56 * ccAffine d + 100 * printedSignedRow d 2 -
    180 * printedSignedRow d 3 + 80 * printedSignedRow d 4

private theorem printedPhiAffine_sum (τ : TraceData) :
    printedPhiAffine τ = ∑ i : Fin 6, phiAffineRow (rowTrace τ i) := by
  simp only [printedPhiAffine, printedSignedGram, printedCCAffine, phiAffineRow,
    Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- Change the three middle-letter coordinates with the overlaps and triangles fixed. -/
def TraceData.withOmegas (τ : TraceData) (ω : Letter → ℝ) : TraceData := { τ with om := ω }

private def rowWithOmegas (d : Fin 13 → ℝ) (ξ : Fin 3 → ℝ) : Fin 13 → ℝ :=
  ![d 0,d 1,d 2,d 3,d 4,d 5,d 6,d 7,d 8,d 9,ξ 0,ξ 1,ξ 2]

set_option maxHeartbeats 1000000 in
private theorem phiAffineRow_omegas (d : Fin 13 → ℝ) (x y : Fin 3 → ℝ) (a : ℝ) :
    phiAffineRow (rowWithOmegas d (fun i => a * x i + (1 - a) * y i)) =
      a * phiAffineRow (rowWithOmegas d x) + (1 - a) * phiAffineRow (rowWithOmegas d y) := by
  simp [phiAffineRow, ccAffine, printedSignedRow, printedSign, printedGramTable, rowWithOmegas,
    Fin.sum_univ_succ]
  ring

private theorem rowTrace_withOmegas (τ : TraceData) (ω : Letter → ℝ) (s : Fin 6) :
    rowTrace (τ.withOmegas ω) s = rowWithOmegas (rowTrace τ s)
      (let t := printedOrder 1 2 3 s; ![ω t.1,ω t.2.1,ω t.2.2]) := by
  funext i
  fin_cases i <;> rfl

theorem printedPhiAffine_omegas (τ : TraceData) (x y : Letter → ℝ) (a : ℝ) :
    printedPhiAffine (τ.withOmegas (fun i => a * x i + (1 - a) * y i)) =
      a * printedPhiAffine (τ.withOmegas x) + (1 - a) * printedPhiAffine (τ.withOmegas y) := by
  simp only [printedPhiAffine_sum, Finset.mul_sum, ← Finset.sum_add_distrib, rowTrace_withOmegas]
  apply Finset.sum_congr rfl
  intro s _
  let t := printedOrder 1 2 3 s
  let u : Fin 3 → ℝ := ![x t.1,x t.2.1,x t.2.2]
  let v : Fin 3 → ℝ := ![y t.1,y t.2.1,y t.2.2]
  have he : (![a * x t.1 + (1 - a) * y t.1, a * x t.2.1 + (1 - a) * y t.2.1,
      a * x t.2.2 + (1 - a) * y t.2.2] : Fin 3 → ℝ) =
      fun i => a * u i + (1 - a) * v i := by
    funext i
    fin_cases i <;> rfl
  change phiAffineRow (rowWithOmegas (rowTrace τ s)
    ![a * x t.1 + (1 - a) * y t.1, a * x t.2.1 + (1 - a) * y t.2.1,
      a * x t.2.2 + (1 - a) * y t.2.2]) =
    a * phiAffineRow (rowWithOmegas (rowTrace τ s) u) + (1 - a) * phiAffineRow (rowWithOmegas (rowTrace τ s) v)
  rw [he]
  exact phiAffineRow_omegas (rowTrace τ s) u v a

end AlbertSequential.LengthSeven
