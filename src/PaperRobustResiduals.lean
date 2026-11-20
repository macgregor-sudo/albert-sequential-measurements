/- SPDX-License-Identifier: Apache-2.0 -/
module

public import BlockB.RobustNativeMS

@[expose] public section

noncomputable section

namespace AlbertSequential.LengthSeven.Robust

open AlbertSequential AlbertSequential.LengthSeven

private theorem sum_map_flatMap_eq {A B G : Type*} [AddMonoid G]
    (xs : List A) (f : A → List B) (g : B → G) :
    ((xs.flatMap f).map g).sum = (xs.map fun x => ((f x).map g).sum).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons, ih]

/-- The unmerged table terms of the actual Gram decomposition. -/
def gramTableTerms (pairs : List (ℚ × Entry)) : List (ℚ × Word Letter) :=
  pairs.flatMap fun p => p.2.tabs.map fun m => (p.1 * m.1, m.2.toWord)

/-- The signed coefficients and defects before combining occurrences. -/
def gramResidualOccurrences (pairs : List (ℚ × Entry)) : List (ℚ × Defect) :=
  pairs.flatMap fun p => p.2.defs.map fun d => (p.1 * d.y, d)

theorem gramResidualOccurrences_mem {pairs : List (ℚ × Entry)} {o : ℚ × Defect}
    (ho : o ∈ gramResidualOccurrences pairs) :
    ∃ p ∈ pairs, ∃ d ∈ p.2.defs, o = (p.1 * d.y, d) := by
  obtain ⟨p,hp,hm⟩ := List.mem_flatMap.mp ho
  obtain ⟨d,hd,he⟩ := List.mem_map.mp hm
  exact ⟨p,hp,d,hd,he.symm⟩

/-- The checked decomposition before the Young penalties, keeping the actual
signed scalar of each residual pairing. -/
theorem gram_norm_eq_table_add_residuals {V : Type*} [AddCommGroup V] [Module ℝ V]
    (W : WalkForm V) (vecs : List (ℚ × List Letter)) (pairs : List (ℚ × Entry))
    (hp : pairs.map (fun p => (p.1, p.2.u1, p.2.u2)) = pairSpec vecs)
    (hok : pairs.all (fun p => p.2.ok) = true) :
    W.normSq (phiVec W vecs) =
      evalF (fun w => W.normSq (W.vec w)) (gramTableTerms pairs) +
      ((gramResidualOccurrences pairs).map
        (fun o => (o.1 : ℝ) * W.form (W.pathVec o.2.α) (o.2.resid W))).sum := by
  rw [normSq_phiVec, ← hp, List.map_map]
  have hentry (p : ℚ × Entry) (hmem : p ∈ pairs) := Entry.sound W p.2 (List.all_eq_true.mp hok p hmem)
  unfold gramTableTerms gramResidualOccurrences
  rw [evalF_flatMap, sum_map_flatMap, ← List.sum_map_add]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hmem
  simp only [Function.comp_apply, hentry p hmem, Entry.rhs, evalF_tabs, mul_add, List.map_map]
  congr 1
  rw [mul_sum_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro d _
  simp only [Function.comp_apply]
  push_cast
  ring

/-- The raw table bound is exactly the sum of absolute values of table
occurrences. -/
theorem counterT_eq_tableOccurrences (pairs : List (ℚ × Entry)) :
    counterT pairs = l1 (gramTableTerms pairs) := by
  unfold counterT l1 gramTableTerms
  rw [sum_map_flatMap_eq]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  rw [List.map_map]
  change |p.1| * (p.2.tabs.map fun m => |m.1|).sum =
    (p.2.tabs.map fun m => |p.1 * m.1|).sum
  simp only [abs_mul, List.sum_map_mul_left]

/-- The sum in a bucket over the actual flattened residual occurrences. -/
theorem counterW_eq_residualOccurrences (T : TraceTable) (pairs : List (ℚ × Entry)) (π : ℚ) :
    counterW T pairs π = ((gramResidualOccurrences pairs).map fun o =>
      if piQ T o.2.α = π then |o.1| else 0).sum := by
  unfold counterW gramResidualOccurrences
  rw [sum_map_flatMap_eq]
  simp only [List.map_map]
  rfl

/-- The reported pure-state bucket is the same weight as three times the
unconditioned e/3 probability of the actual left word. -/
def nativeResidualBucket (p : Fin 4 → Albert) (d : Defect) : ℝ :=
  3 * nativeWordProbability p ((1/3 : ℝ) • albertUnit) ((0,true)::yesWord d.α)

private theorem nativeResidualBucket_eq (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (T : TraceTable) (hT : T.Holds (nativeTraceData p)) (d : Defect)
    (hd : (fvalQ T (.yes d.α)).isSome = true) :
    nativeResidualBucket p d = (piQ T d.α : ℝ) := by
  cases hf : fvalQ T (.yes d.α) with
  | none => simp [hf] at hd
  | some π =>
    have hv := fvalQ_sound hT (tableValues_native p hp) (.yes d.α) π hf
    change nativeWordProbability p (p 0) (yesWord d.α) = (π : ℝ) at hv
    rw [nativeResidualBucket, e3_conditioning p hp, hv, piQ, hf]
    simp

/-- Each calibrated purity contribution vanishes on the actual e/3 table,
with the leading yes inserted on all three emitted words. -/
theorem nativeResidualOccurrences_spec (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (T : TraceTable) (hT : T.Holds (nativeTraceData p)) (pairs : List (ℚ × Entry))
    (hok : octOk T pairs = true) (o : ℚ × Defect) (ho : o ∈ gramResidualOccurrences pairs) :
    let d := o.2
    let g := nativeWordProbability p ((1/3 : ℝ) • albertUnit)
    nativeResidualBucket p d = (piQ T d.α : ℝ) ∧
      g ((0,true)::d.long) - 2 * d.c * g ((0,true)::d.mid) +
        (d.c : ℝ)^2 * g ((0,true)::d.short) = 0 := by
  obtain ⟨e,he,d,hd,rfl⟩ := gramResidualOccurrences_mem ho
  have he' := List.all_eq_true.mp hok e he
  simp only [Bool.and_eq_true] at he'
  have hd' := List.all_eq_true.mp he'.2 d hd
  simp only [Bool.and_eq_true] at hd'
  refine ⟨nativeResidualBucket_eq p hp T hT d hd'.1,?_⟩
  have hv := xok_sound hT (tableValues_native p hp) d hd'.2
  dsimp only
  rw [e3_conditioning p hp, e3_conditioning p hp, e3_conditioning p hp]
  linear_combination (1/3 : ℝ) * hv

/-- Absolute coefficients grouped by actual native left-word probabilities. -/
def nativeBucketWeight (p : Fin 4 → Albert) (pairs : List (ℚ × Entry)) (π : ℚ) : ℝ :=
  ((gramResidualOccurrences pairs).map fun o =>
    if nativeResidualBucket p o.2 = (π : ℝ) then (|o.1| : ℝ) else 0).sum

theorem nativeBucketWeight_eq_counterW (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (T : TraceTable) (hT : T.Holds (nativeTraceData p)) (pairs : List (ℚ × Entry))
    (hok : octOk T pairs = true) (π : ℚ) :
    nativeBucketWeight p pairs π = (counterW T pairs π : ℝ) := by
  rw [nativeBucketWeight, counterW_eq_residualOccurrences]
  rw [cast_sum_map (gramResidualOccurrences pairs)
    (fun o => if piQ T o.2.α = π then |o.1| else 0)]
  apply congrArg List.sum
  apply List.map_congr_left
  intro o ho
  rw [(nativeResidualOccurrences_spec p hp T hT pairs hok o ho).1]
  by_cases h : piQ T o.2.α = π
  · simp [h]
  · have hn : (piQ T o.2.α : ℝ) ≠ (π : ℝ) := by exact_mod_cast h
    simp [h,hn]

theorem maximizerConfig_nativeBucketWeights :
    ([1,1/3,1/9,1/27,1/81] : List ℚ).map (nativeBucketWeight maximizerConfig pairsM) =
      ([231377/18,17863/3,45542/3,14008,32064] : List ℝ) := by
  have h := nativeBucketWeight_eq_counterW maximizerConfig maximizerConfig_isAtom tableM
    BlockB.tableM_holds_maximizerConfig pairsM octOk_M
  simp only [List.map_cons, List.map_nil, h, counterW_M_0, counterW_M_1, counterW_M_2,
    counterW_M_3, counterW_M_4]
  push_cast
  norm_num

theorem fixedS_nativeBucketWeights :
    ([1,1/2,1/3,1/6,1/9,1/18,1/27,1/54,1/81] : List ℚ).map (nativeBucketWeight fixedS pairsS) =
      ([3099331/108,4065,73880/9,28534/3,191914/9,9674,56086/3,25290,29772] : List ℝ) := by
  have h := nativeBucketWeight_eq_counterW fixedS fixedS_isAtom tableS
    BlockB.tableS_holds_fixedS pairsS octOk_S
  simp only [List.map_cons, List.map_nil, h, counterW_S_0, counterW_S_1, counterW_S_2,
    counterW_S_3, counterW_S_4, counterW_S_5, counterW_S_6, counterW_S_7, counterW_S_8]
  push_cast
  norm_num

theorem maximizerConfig_rawTableBound : l1 (gramTableTerms pairsM) = 1738400 / 243 :=
  (counterT_eq_tableOccurrences pairsM).symm.trans counterT_M

theorem fixedS_rawTableBound : l1 (gramTableTerms pairsS) = 21466321 / 1458 :=
  (counterT_eq_tableOccurrences pairsS).symm.trans counterT_S

def gramTableValueQ (T : TraceTable) (pairs : List (ℚ × Entry)) : ℚ :=
  (pairs.map fun e => (e.2.tabs.map fun m => e.1 * m.1 * (fvalQ T m.2).getD 0).sum).sum

theorem gramTableValue_e3 (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (T : TraceTable) (hT : T.Holds (nativeTraceData p)) (pairs : List (ℚ × Entry))
    (hok : octOk T pairs = true) :
    evalF (fun w => nativeWordProbability p ((1/3 : ℝ) • albertUnit) ((0,true)::w))
        (gramTableTerms pairs) = (1/3 : ℝ) * (gramTableValueQ T pairs : ℝ) := by
  rw [gramTableTerms, evalF_flatMap, gramTableValueQ, cast_sum_map, mul_sum_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro e he
  have hEntry := List.all_eq_true.mp hok e he
  simp only [Bool.and_eq_true] at hEntry
  rw [evalF, cast_sum_map, mul_sum_map, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro m hm
  have hTab := List.all_eq_true.mp hEntry.1 m hm
  cases heval : fvalQ T m.2 with
  | none => simp [heval] at hTab
  | some q =>
    have hval := fvalQ_sound hT (tableValues_native p hp) m.2 q heval
    simp only [Function.comp_apply, e3_conditioning p hp, hval, Option.getD_some]
    push_cast
    ring

set_option maxRecDepth 100000 in
theorem maximizerConfig_gramTableValue_e3 :
    evalF (fun w => nativeWordProbability maximizerConfig ((1/3 : ℝ) • albertUnit) ((0,true)::w))
      (gramTableTerms pairsM) = -4/81 := by
  have h : gramTableValueQ tableM pairsM = -4/27 := by decide +kernel
  rw [gramTableValue_e3 maximizerConfig maximizerConfig_isAtom tableM
    BlockB.tableM_holds_maximizerConfig pairsM octOk_M, h]
  norm_num

set_option maxRecDepth 100000 in
theorem fixedS_gramTableValue_e3 :
    evalF (fun w => nativeWordProbability fixedS ((1/3 : ℝ) • albertUnit) ((0,true)::w))
      (gramTableTerms pairsS) = -205/4374 := by
  have h : gramTableValueQ tableS pairsS = -205/1458 := by decide +kernel
  rw [gramTableValue_e3 fixedS fixedS_isAtom tableS
    BlockB.tableS_holds_fixedS pairsS octOk_S, h]
  norm_num

/-- A table word contributes an all-yes path or one of the polarizations in
clauses (i) and (ii), before the first yes on A is prepended. -/
def paperTableWordShape : TabWord → Bool
  | .yes [x,y,z,x',a] => decide (IsOrderingBCD x y z ∧ x' = x ∧ a = 0)
  | .yes w => decide (w.length ≤ 4)
  | .one [x,y] z a [] => decide (a = 0 ∧ IsOrderingBCD x y z)
  | .one [x,y,z] x' a [] => decide (a = 0 ∧ x' = x ∧ IsOrderingBCD x y z)
  | .one _ _ _ _ => false

/-- The printed chronological residual shapes in (iii) and left-length
bound (iv). Relating each occurrence to its original derivation step is
separate from this shape check. -/
def paperDefectShape (d : Defect) : Bool :=
  decide (d.α.length ≤ 4) && d.t.all (·.2) &&
  match d.v with
  | [v] => v.2 && decide (d.t.length ≤ 3 ∧ d.q ≠ v.1)
  | [v,w] => w.2 && decide (d.t.length ≤ 1 ∧ d.q ≠ v.1 ∧ v.1 ≠ w.1 ∧ d.q ≠ w.1)
  | [x,y,z] => z.2 && decide (d.t = [] ∧ d.q = 0 ∧ IsOrderingBCD x.1 y.1 z.1)
  | _ => false

def paperBucketPowersM : List (ℚ × ℚ) := [(1,1),(1/3,1),(1/9,2),(1/27,4),(1/81,8)]

def paperBucketPowersS : List (ℚ × ℚ) :=
  [(1,1),(1/2,1),(1/3,1),(1/6,2),(1/9,2),(1/18,4),(1/27,4),(1/54,4),(1/81,8)]

theorem maximizerConfig_weightedBucketTotal :
    (paperBucketPowersM.map fun (π,r) => counterW tableM pairsM π * r * π).sum = 422183 / 18 := by
  simp only [paperBucketPowersM, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    counterW_M_0, counterW_M_1, counterW_M_2, counterW_M_3, counterW_M_4]
  norm_num

theorem fixedS_weightedBucketTotal :
    (paperBucketPowersS.map fun (π,r) => counterW tableS pairsS π * r * π).sum = 16559187 / 324 := by
  simp only [paperBucketPowersS, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    counterW_S_0, counterW_S_1, counterW_S_2, counterW_S_3, counterW_S_4, counterW_S_5,
    counterW_S_6, counterW_S_7, counterW_S_8]
  norm_num

inductive GramVectorKind where
  | H | C | R

def gramVectorKind (w : List Letter) : GramVectorKind :=
  if w.length = 3 then .H else if w.getLastD 0 = 0 then .C else .R

inductive GramCounterRow where
  | HH | CC | RR | RH | RC
  deriving DecidableEq

/-- A CH entry uses its quoted CC row counter, as in Appendix A.2. -/
def gramCounterRow (e : Entry) : GramCounterRow :=
  match gramVectorKind e.u1, gramVectorKind e.u2 with
  | .H, .H => .HH
  | .R, .R => .RR
  | .H, .R | .R, .H => .RH
  | .C, .R | .R, .C => .RC
  | .H, .C | .C, .H | .C, .C => .CC

def counterW_byRow (T : TraceTable) (pairs : List (ℚ × Entry))
    (π : ℚ) (row : GramCounterRow) : ℚ :=
  counterW T (pairs.filter fun p => decide (gramCounterRow p.2 = row)) π

set_option maxRecDepth 100000 in
/-- The five row contributions in the printed M bucket at π = 1/27. -/
theorem maximizerConfig_gramRows_bucket_example :
    let bucket := counterW_byRow tableM pairsM (1/27)
    bucket .HH = 0 ∧ bucket .CC = 528*(8/3) ∧ bucket .RR = 600*4 ∧
      bucket .RH = 1080*5 ∧ bucket .RC = 480*10 := by decide +kernel

def paperEntryShape (T : TraceTable) (buckets : List (ℚ × ℚ)) (cmax : ℚ) (e : Entry) : Bool :=
  e.tabs.all (fun m => paperTableWordShape m.2) &&
    e.defs.all (fun d => paperDefectShape d && decide (1/27 ≤ d.c ∧ d.c ≤ cmax) &&
      let π := piQ T d.α
      decide ((π, rOf 64 1 π) ∈ buckets))

set_option maxRecDepth 100000 in
theorem pairsM_paperEntryShape :
    pairsM.all (fun p => paperEntryShape tableM paperBucketPowersM (1/3) p.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem pairsS_paperEntryShape :
    pairsS.all (fun p => paperEntryShape tableS paperBucketPowersS (1/2) p.2) = true := by decide +kernel

theorem gramResidualOccurrences_paperShape {T : TraceTable} {buckets : List (ℚ × ℚ)}
    {pairs : List (ℚ × Entry)} {cmax : ℚ}
    (h : pairs.all (fun p => paperEntryShape T buckets cmax p.2) = true)
    {o : ℚ × Defect} (ho : o ∈ gramResidualOccurrences pairs) :
    paperDefectShape o.2 = true ∧
      (1/27 ≤ o.2.c ∧ o.2.c ≤ cmax) ∧
      (piQ T o.2.α, rOf 64 1 (piQ T o.2.α)) ∈ buckets := by
  obtain ⟨p,hp,d,hd,rfl⟩ := gramResidualOccurrences_mem ho
  have he := List.all_eq_true.mp h p hp
  simp only [paperEntryShape, Bool.and_eq_true] at he
  have hh := List.all_eq_true.mp he.2 d hd
  simpa only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hh

end AlbertSequential.LengthSeven.Robust
