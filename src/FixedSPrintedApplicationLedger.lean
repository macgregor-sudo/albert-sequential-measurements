/- SPDX-License-Identifier: Apache-2.0 -/
module

public import FixedSPrintedWitness

@[expose] public section
noncomputable section

namespace AlbertSequential

open BlockB

private def applicationKey (s : Word (Fin 4)) (q : Outcome (Fin 4)) (v : Word (Fin 4)) : Word (Fin 4) :=
  List.replicate s.length (3, true) ++ ((3, false) :: q :: (s ++ v))

private theorem marker_length_eq (m n : ℕ) (u v : Word (Fin 4))
    (h : List.replicate m (3, true) ++ (3, false) :: u =
      List.replicate n (3, true) ++ (3, false) :: v) :
    m = n := by
  induction m generalizing n with
  | zero =>
    cases n with
    | zero => rfl
    | succ n => simp [List.replicate_succ] at h
  | succ m ih =>
    cases n with
    | zero => simp [List.replicate_succ] at h
    | succ n =>
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      exact congrArg Nat.succ (ih n h)

private theorem applicationKey_eq {s s' v v' : Word (Fin 4)} {q q' : Outcome (Fin 4)}
    (h : applicationKey s q v = applicationKey s' q' v') : s = s' ∧ q = q' ∧ v = v' := by
  unfold applicationKey at h
  have hlen := marker_length_eq _ _ _ _ h
  have ht := (List.append_inj h (by simpa using hlen)).2
  have hq := List.cons.inj (List.cons.inj ht).2
  have hwords := List.append_inj hq.2 hlen
  exact ⟨hwords.1, hq.1, hwords.2⟩

private def ledgerKeys : List (Word (Fin 4)) :=
  ledgerApplications.filterMap fun (t, q, v) => (reduceWord (t ++ [q])).map fun s => applicationKey s q v

private def occurrenceKeys (j : Fin 4) : List (Word (Fin 4)) :=
  (cornerResidualTelescopeOccurrences (atomCornerData (fixedSPrintedMenu j))
    (atomCornerScalar (fixedSPrintedMenu j))).map (fun o => applicationKey o.leaf.shortWord o.leaf.outcome o.leaf.suffix)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem occurrenceKeys_in_ledger (j : Fin 4) :
    (BinTrie.ofWordListBatched (occurrenceKeys j)).subBool
      (BinTrie.ofWordListBatched ledgerKeys) = true := by
  fin_cases j <;> decide +kernel

theorem fixedSPrinted_baseOccurrence_has_ledger_application (j : Fin 4)
    (o : ResidualTelescopeOccurrence 4)
    (ho : o ∈ cornerResidualTelescopeOccurrences (atomCornerData (fixedSPrintedMenu j))
      (atomCornerScalar (fixedSPrintedMenu j))) :
    ∃ t : Word (Fin 4), (t, o.leaf.outcome, o.leaf.suffix) ∈ ledgerApplications ∧
      reduceWord (t ++ [o.leaf.outcome]) = some o.leaf.shortWord := by
  let key := applicationKey o.leaf.shortWord o.leaf.outcome o.leaf.suffix
  have hkey : key ∈ occurrenceKeys j := List.mem_map.mpr ⟨o, ho, rfl⟩
  have hmem := BinTrie.mem_toFinset_of_subBool (BinTrie.mem_ofWordListBatched _)
    (BinTrie.mem_ofWordListBatched _) (occurrenceKeys_in_ledger j) hkey
  have hlist : key ∈ ledgerKeys := List.mem_toFinset.mp hmem
  obtain ⟨⟨t, q, v⟩, ha, he⟩ := List.mem_filterMap.mp hlist
  have he' : (reduceWord (t ++ [q])).map (fun s => applicationKey s q v) = some key := he
  cases hr : reduceWord (t ++ [q]) with
  | none => simp [hr] at he'
  | some s =>
    simp only [hr, Option.map_some, Option.some.injEq] at he'
    have hu := applicationKey_eq he'
    rcases hu with ⟨rfl, rfl, rfl⟩
    exact ⟨t, ha, hr⟩

theorem fixedSPrinted_occurrence_has_ledger_application (o : ResidualTelescopeOccurrence 4)
    (ho : o ∈ fixedSPrintedOccurrences) :
    ∃ (j : Fin 4) (t : Word (Fin 4)) (q : Outcome (Fin 4)) (v : Word (Fin 4)),
      (t, q, v) ∈ ledgerApplications ∧
      o.leaf.outcome = relabelOutcome (swapBase j) q ∧
      o.leaf.suffix = relabelWord (swapBase j) v ∧
      reduceWord (relabelWord (swapBase j) t ++ [o.leaf.outcome]) = some o.leaf.shortWord := by
  unfold fixedSPrintedOccurrences combinedCornerOccurrences ResidualOccurrenceExpression.combine
    ResidualOccurrenceExpression.scale ResidualOccurrenceExpression.relabel at ho
  rcases List.mem_flatten.mp ho with ⟨es, hes, ho⟩
  rcases List.mem_ofFn.mp hes with ⟨j, rfl⟩
  rcases List.mem_map.mp ho with ⟨u, hu, rfl⟩
  rcases List.mem_map.mp hu with ⟨o, horiginal, rfl⟩
  obtain ⟨t, ht, hr⟩ := fixedSPrinted_baseOccurrence_has_ledger_application j o horiginal
  refine ⟨j, t, o.leaf.outcome, o.leaf.suffix, ht, rfl, rfl, ?_⟩
  change reduceWord (relabelWord (swapBase j) t ++ [relabelOutcome (swapBase j) o.leaf.outcome]) =
    some (SupportedPurityLeaf.relabel (fun a => swapBase j a) o.leaf).shortWord
  have h := reduceWord_relabel (swapBase j).injective (t ++ [o.leaf.outcome])
  rw [hr] at h
  simpa only [relabelWord_append, relabelWord_cons, relabelWord_nil, Option.map_some,
    SupportedPurityLeaf.shortWord_relabel] using h

end AlbertSequential
