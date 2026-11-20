/- SPDX-License-Identifier: Apache-2.0 -/
module

public import MatchingModels.UniversalSixAffinity
public import MatchingModels.MatrixClassIBridge
public import MatchingModels.QuatPair
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace AlbertSequential.MatchingModels

open NativeAnalysis
open scoped List

private def continuation (f : PairFactor) : List (Fin 4) :=
  f.mid ++ [f.tail]

private def retainedLabels : EffectTerm → List (Fin 4)
  | .openTerm _ ops => ops
  | .splitTerm _ fs base ops => ops ++ base :: fs.flatMap continuation

private def linked (i : Fin 4) : List PairFactor → Prop
  | [] => True
  | f :: fs => f.head = i ∧ linked f.tail fs

private def ready : EffectTerm → Prop
  | .openTerm .. => True
  | .splitTerm _ fs base _ => linked base fs

private theorem retainedLabels_stepU (i : Fin 4) (t : EffectTerm) :
    retainedLabels (stepU i t) = i :: retainedLabels t := by
  cases t with
  | openTerm c ops =>
    simp only [stepU]
    cases hs : splitLast? ops with
    | none =>
      have h := (splitLast?_none_iff ops).mp hs
      subst ops
      rfl
    | some v =>
      obtain ⟨mid, tail⟩ := v
      rw [splitLast?_some hs]
      simp [retainedLabels, continuation]
  | splitTerm c fs base ops =>
    simp [stepU, retainedLabels, continuation, List.append_assoc]

private theorem ready_stepU (i : Fin 4) (t : EffectTerm) (ht : ready t) : ready (stepU i t) := by
  cases t with
  | openTerm c ops =>
    simp only [stepU]
    cases hs : splitLast? ops with
    | none => trivial
    | some v => exact ⟨rfl, trivial⟩
  | splitTerm c fs base ops =>
    exact ⟨rfl, ht⟩

private theorem retainedLabels_stepNeg2L (i : Fin 4) (t : EffectTerm) :
    retainedLabels (stepNeg2L i t) = i :: retainedLabels t := by
  cases t <;> rfl

private theorem ready_stepNeg2L (i : Fin 4) (t : EffectTerm) (ht : ready t) :
    ready (stepNeg2L i t) := by
  cases t <;> exact ht

private theorem retainedLabels_sublist (w : Word (Fin 4)) (t : EffectTerm)
    (ht : t ∈ expandWord w) : ready t ∧ retainedLabels t <+ w.map Prod.fst := by
  induction w generalizing t with
  | nil =>
    simp only [expandWord, List.mem_singleton] at ht
    subst t
    exact ⟨trivial, List.Sublist.slnil⟩
  | cons a w ih =>
    obtain ⟨s, hs, ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨hready, hsub⟩ := ih s hs
    rcases a with ⟨i, b⟩
    have hU : ready (stepU i s) ∧ retainedLabels (stepU i s) <+ i :: w.map Prod.fst := by
      rw [retainedLabels_stepU]
      exact ⟨ready_stepU i s hready, hsub.cons_cons i⟩
    cases b
    · simp only [stepTerm, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.mem_nil_iff,
        or_false] at ht
      rcases ht with rfl | rfl | rfl
      · exact ⟨hready, hsub.cons i⟩
      · rw [List.map_cons, retainedLabels_stepNeg2L]
        exact ⟨ready_stepNeg2L i s hready, hsub.cons_cons i⟩
      · exact hU
    · simp only [stepTerm, ↓reduceIte, List.mem_singleton] at ht
      subst t
      exact hU

private theorem retainedLabels_two (t : EffectTerm) (hready : ready t)
    (f g : PairFactor) (hf : (closeTerm t).2 = [f, g]) :
    g.head = f.tail ∧ retainedLabels t = f.atoms ++ continuation g := by
  cases t with
  | openTerm c ops =>
    rcases ops with _ | ⟨a, _ | ⟨b, ops⟩⟩
    · simp [closeTerm] at hf
    · simp [closeTerm] at hf
    · dsimp only [closeTerm] at hf
      split at hf <;> simp at hf
  | splitTerm c fs base ops =>
    cases ops with
    | nil =>
      change fs = [f, g] at hf
      subst fs
      have h : f.head = base ∧ g.head = f.tail ∧ True := hready
      exact ⟨h.2.1, by simp [retainedLabels, PairFactor.atoms, continuation, h.1]⟩
    | cons b ops =>
      change ⟨b, ops, base⟩ :: fs = [f, g] at hf
      obtain ⟨rfl, rfl⟩ := List.cons.inj hf
      exact ⟨hready.1, by simp [retainedLabels, PairFactor.atoms, continuation, List.append_assoc]⟩

private def fullFactor (f : PairFactor) : Bool :=
  (List.finRange 4).all (fun i => f.atoms.contains i)

private theorem fullFactor_iff (f : PairFactor) : fullFactor f = true ↔ ∀ i, i ∈ f.atoms := by
  simp [fullFactor, List.all_eq_true, List.mem_finRange]

private theorem fullFactor_weight {f : PairFactor} (hf : fullFactor f = true) : 3 ≤ f.weight := by
  have hsub : (Finset.univ : Finset (Fin 4)) ⊆ f.atoms.toFinset := by
    intro i _
    exact List.mem_toFinset.mpr (fullFactor_iff f |>.mp hf i)
  have hle : 4 ≤ f.atoms.length :=
    (by simpa using Finset.card_le_card hsub : 4 ≤ f.atoms.toFinset.card).trans
      (List.toFinset_card_le _)
  simp only [PairFactor.atoms, List.length_cons, List.length_append, List.length_nil] at hle
  simp only [PairFactor.weight]
  omega

private theorem factor_weight_lower_bound (fs : List PairFactor) :
    fs.length + 2 * (fs.filter fullFactor).length ≤ (fs.map PairFactor.weight).sum := by
  induction fs with
  | nil => simp
  | cons f fs ih =>
    cases h : fullFactor f
    · simp only [List.length_cons, List.filter_cons, h, Bool.false_eq_true, ↓reduceIte,
        List.map_cons, List.sum_cons]
      have : 1 ≤ f.weight := by simp [PairFactor.weight]
      omega
    · simp only [List.length_cons, List.filter_cons, h, ↓reduceIte, List.map_cons, List.sum_cons]
      have := fullFactor_weight h
      omega

private theorem weight_six_two_full_factors {fs : List PairFactor}
    (hwt : (fs.map PairFactor.weight).sum ≤ 6) (hfull : 2 ≤ (fs.filter fullFactor).length) :
    ∃ f g, fs = [f, g] ∧ fullFactor f = true ∧ fullFactor g = true ∧
      f.weight = 3 ∧ g.weight = 3 := by
  have hlen := List.length_filter_le (p := fullFactor) (l := fs)
  have hbudget := factor_weight_lower_bound fs
  have htwo : fs.length = 2 := by omega
  obtain ⟨f, g, rfl⟩ : ∃ f g, fs = [f, g] := by
    rcases fs with _ | ⟨f, _ | ⟨g, _ | ⟨h, fs⟩⟩⟩
    · simp at htwo
    · simp at htwo
    · exact ⟨f, g, rfl⟩
    · simp at htwo
  have hf : fullFactor f = true := by
    cases h : fullFactor f <;> cases h' : fullFactor g <;> simp_all
  have hg : fullFactor g = true := by
    cases h : fullFactor g <;> simp_all
  have hfwt := fullFactor_weight hf
  have hgwt := fullFactor_weight hg
  simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, add_zero] at hwt
  exact ⟨f, g, rfl, hf, hg, by omega, by omega⟩

def scheduleCoordinate (s : List (Fin 4)) : Fin 3 :=
  unorderedPairClass (s[0]?.getD 0) (s[1]?.getD 0)

private theorem factor_eval_four_labels (q : Fin 4 → Albert) (a b c d : Fin 4)
    (h : ∀ i : Fin 4, i ∈ ([a,b,c,d] : List (Fin 4))) :
    (⟨a, [b,c], d⟩ : PairFactor).eval q = tVec q (unorderedPairClass a b) := by
  unfold PairFactor.eval atomChainElem
  simp only [List.foldr_cons, List.foldr_nil]
  rw [← tracePairing_associative]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp_all [Fin.forall_fin_succ, unorderedPairClass, tVec, fpDoublePair1, fpDoublePair2,
      fpDoublePair3, jordanMul_comm, tracePairing_comm] <;> rw [jordanMul_comm (q 1) (q 0)]

private theorem fixed_first_full {w : Word (Fin 4)} (hw : w.length = 7) (t : EffectTerm)
    (ht : t ∈ expandWord w) (f g : PairFactor) (hfg : (closeTerm t).2 = [f, g])
    (hf : fullFactor f = true) (hfwt : f.weight = 3) (hgwt : g.weight = 3) :
    ∀ q, f.eval q = tVec q (scheduleCoordinate (w.map Prod.fst)) := by
  obtain ⟨hready, hsub⟩ := retainedLabels_sublist w t ht
  obtain ⟨_, hret⟩ := retainedLabels_two t hready f g hfg
  have hlen : (retainedLabels t).length = (w.map Prod.fst).length := by
    rw [hret, List.length_map, hw]
    simp only [PairFactor.weight] at hfwt hgwt
    simp only [PairFactor.atoms, continuation, List.length_append, List.length_cons, List.length_nil]
    omega
  have hword := (hsub.eq_of_length hlen).symm.trans hret
  rcases f with ⟨a, mid, d⟩
  rcases mid with _ | ⟨b, _ | ⟨c, _ | ⟨e, mid⟩⟩⟩
  · simp [PairFactor.weight] at hfwt
  · simp [PairFactor.weight] at hfwt
  · intro q
    rw [hword]
    simp only [scheduleCoordinate, PairFactor.atoms, List.cons_append, List.nil_append,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    exact factor_eval_four_labels q a b c d (fullFactor_iff _ |>.mp hf)
  · simp [PairFactor.weight] at hfwt

private theorem prod_affine_of_one_full (p qPlus qMinus : Fin 4 → Albert) (lam : ℝ)
    (affine : ∀ f : PairFactor, f.weight ≤ 6 →
      f.eval p = lam * f.eval qPlus + (1 - lam) * f.eval qMinus)
    (fixed : ∀ f : PairFactor, fullFactor f = false →
      f.eval qPlus = f.eval p ∧ f.eval qMinus = f.eval p)
    (fs : List PairFactor) (hwt : (fs.map PairFactor.weight).sum ≤ 6)
    (hfull : (fs.filter fullFactor).length ≤ 1) :
    (fs.map (fun f => f.eval p)).prod =
      lam * (fs.map (fun f => f.eval qPlus)).prod +
        (1 - lam) * (fs.map (fun f => f.eval qMinus)).prod := by
  induction fs with
  | nil => simp
  | cons f fs ih =>
    simp only [List.map_cons, List.sum_cons] at hwt
    cases hf : fullFactor f
    · have ht : (fs.filter fullFactor).length ≤ 1 := by simpa [List.filter_cons, hf] using hfull
      have hi := ih (by omega) ht
      simp only [List.map_cons, List.prod_cons, (fixed f hf).1, (fixed f hf).2, hi]
      ring
    · have hempty : fs.filter fullFactor = [] := by
        apply List.length_eq_zero_iff.mp
        simp only [List.filter_cons, hf, ↓reduceIte, List.length_cons] at hfull
        omega
      have hfixed : ∀ g ∈ fs, g.eval qPlus = g.eval p ∧ g.eval qMinus = g.eval p := by
        intro g hg
        apply fixed g
        cases hg' : fullFactor g
        · rfl
        · have hm : g ∈ fs.filter fullFactor := List.mem_filter.mpr ⟨hg, hg'⟩
          rw [hempty] at hm
          simp at hm
      have hp' : (fs.map (fun g => g.eval qPlus)).prod = (fs.map (fun g => g.eval p)).prod := by
        rw [List.map_congr_left (fun g hg => (hfixed g hg).1)]
      have hm' : (fs.map (fun g => g.eval qMinus)).prod = (fs.map (fun g => g.eval p)).prod := by
        rw [List.map_congr_left (fun g hg => (hfixed g hg).2)]
      simp only [List.map_cons, List.prod_cons, hp', hm', affine f (by omega)]
      ring

/-- Signed-word probabilities for a *fixed* seven-test schedule are affine when its first
pairing coordinate is held fixed. This includes schedules with repeated tests. -/
theorem nativeWordProbability_e3_affine_on_schedule
    {p qPlus qMinus : Fin 4 → Albert} {lam : ℝ} (s : List (Fin 4)) (hs : s.length = 7)
    (hp : ∀ i, IsAtom (p i)) (hpq : ∀ i, IsAtom (qPlus i)) (hmq : ∀ i, IsAtom (qMinus i))
    (hA : 0 < fourPointInvariant p)
    (ho : ∀ i j, fpOverlap p i j = fpOverlap qPlus i j ∧ fpOverlap p i j = fpOverlap qMinus i j)
    (hR : ∀ i j k, fpTriangle p i j k = fpTriangle qPlus i j k ∧
      fpTriangle p i j k = fpTriangle qMinus i j k)
    (ht1 : fpDoublePair1 p = lam * fpDoublePair1 qPlus + (1 - lam) * fpDoublePair1 qMinus)
    (ht2 : fpDoublePair2 p = lam * fpDoublePair2 qPlus + (1 - lam) * fpDoublePair2 qMinus)
    (ht3 : fpDoublePair3 p = lam * fpDoublePair3 qPlus + (1 - lam) * fpDoublePair3 qMinus)
    (hfixPlus : tVec qPlus (scheduleCoordinate s) = tVec p (scheduleCoordinate s))
    (hfixMinus : tVec qMinus (scheduleCoordinate s) = tVec p (scheduleCoordinate s))
    (w : Word (Fin 4)) (hw : w.map Prod.fst = s) :
    nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w =
      lam * nativeWordProbability qPlus ((1 / 3 : ℝ) • albertUnit) w +
        (1 - lam) * nativeWordProbability qMinus ((1 / 3 : ℝ) • albertUnit) w := by
  have hlen : w.length = 7 := by
    simpa only [List.length_map] using (congrArg List.length hw).trans hs
  have affine (f : PairFactor) (hf : f.weight ≤ 6) :
      f.eval p = lam * f.eval qPlus + (1 - lam) * f.eval qMinus := by
    apply pairFactor_eval_affine_of_count_le_one hp hpq hmq hA ho hR ht1 ht2 ht3
    apply exists_count_le_one_of_length_le_seven
    simp only [PairFactor.atoms, List.length_cons, List.length_append, List.length_nil]
    simp only [PairFactor.weight] at hf
    omega
  have fixed (f : PairFactor) (hf : fullFactor f = false) :
      f.eval qPlus = f.eval p ∧ f.eval qMinus = f.eval p := by
    have hmiss : ∃ i, i ∉ f.atoms := by
      by_contra h
      push Not at h
      have he := (fullFactor_iff f).mpr h
      rw [hf] at he
      contradiction
    exact ⟨pairFactor_eval_eq_of_missing hp hpq hA (fun i j => (ho i j).1)
      (fun i j k => (hR i j k).1) f hmiss,
      pairFactor_eval_eq_of_missing hp hmq hA (fun i j => (ho i j).2)
        (fun i j k => (hR i j k).2) f hmiss⟩
  have hprod (t : EffectTerm) (ht : t ∈ expandWord w) :
      ((closeTerm t).2.map (fun f => f.eval p)).prod =
        lam * ((closeTerm t).2.map (fun f => f.eval qPlus)).prod +
          (1 - lam) * ((closeTerm t).2.map (fun f => f.eval qMinus)).prod := by
    have hwt : ((closeTerm t).2.map PairFactor.weight).sum ≤ 6 := by
      have h := expandWord_weight w t ht
      rw [hlen] at h
      exact closeTerm_weight h
    by_cases hf : (((closeTerm t).2).filter fullFactor).length ≤ 1
    · exact prod_affine_of_one_full p qPlus qMinus lam affine fixed _ hwt hf
    · obtain ⟨f, g, hfg, hf, _, hfwt, hgwt⟩ := weight_six_two_full_factors hwt (by omega)
      have heval := fixed_first_full hlen t ht f g hfg hf hfwt hgwt
      rw [hw] at heval
      have hplus : f.eval qPlus = f.eval p := by rw [heval qPlus, heval p, hfixPlus]
      have hminus : f.eval qMinus = f.eval p := by rw [heval qMinus, heval p, hfixMinus]
      simp only [hfg, List.map_cons, List.prod_cons, List.map_nil, List.prod_nil,
        hplus, hminus, affine g (by omega)]
      ring
  rw [nativeWordProbability_e3_eq_sum hp, nativeWordProbability_e3_eq_sum hpq,
    nativeWordProbability_e3_eq_sum hmq]
  have hsum : ∀ ts : List EffectTerm, (∀ t ∈ ts, t ∈ expandWord w) →
      ((ts.map closeTerm).map (fun cf => cf.1 * (cf.2.map (fun f => f.eval p)).prod)).sum =
        lam * ((ts.map closeTerm).map (fun cf => cf.1 * (cf.2.map (fun f => f.eval qPlus)).prod)).sum +
          (1 - lam) * ((ts.map closeTerm).map (fun cf => cf.1 * (cf.2.map (fun f => f.eval qMinus)).prod)).sum := by
    intro ts hts
    induction ts with
    | nil => simp
    | cons t ts ih =>
      have hp' := hprod t (hts t (by simp))
      have hi := ih (fun t ht => hts t (by simp [ht]))
      simp only [List.map_cons, List.sum_cons, hp', hi]
      ring
  rw [hsum (expandWord w) (fun _ h => h)]
  ring

private def scheduleDirection (i : Fin 3) : Fin 3 → ℝ :=
  ![![0, 1, -1], ![1, 0, -1], ![1, -1, 0]] i

private theorem scheduleDirection_fixed (i : Fin 3) : scheduleDirection i i = 0 := by
  fin_cases i <;> rfl

private theorem scheduleDirection_sum (i : Fin 3) :
    scheduleDirection i 0 + scheduleDirection i 1 + scheduleDirection i 2 = 0 := by
  fin_cases i <;> norm_num [scheduleDirection]

private theorem scheduleDirection_nonzero (i : Fin 3) : scheduleDirection i ≠ 0 := by
  fin_cases i <;> intro h
  · have h1 := congrFun h 1
    norm_num [scheduleDirection] at h1
  · have h1 := congrFun h 0
    norm_num [scheduleDirection] at h1
  · have h1 := congrFun h 0
    norm_num [scheduleDirection] at h1

/-- Proposition 6.13(a): one C12 model for every word through length six and all outcomes
of a chosen schedule of length seven. -/
theorem prop_cer_schedule_a (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) (s : List (Fin 4)) (hs : s.length = 7) :
    ∃ M : HilbertProjectiveData (Fin 4) ℂ (EuclideanSpace ℂ (Fin 12)),
      ∀ w : Word (Fin 4), w.length ≤ 6 ∨ w.map Prod.fst = s →
        M.probability w = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w := by
  let k := scheduleCoordinate s
  let v := scheduleDirection k
  obtain ⟨xPlus, xMinus, lam, _, _, _, _, hlam0, hlam1,
    hπPlus, hπMinus, hMPlus, hMMinus, hDPlus, hDMinus, hconv, _⟩ :=
    prop_cer_quatpair_c_line p hp hA v (scheduleDirection_nonzero k) (scheduleDirection_sum k)
  obtain ⟨qPlus, hpq, hpqmem, hop, hrp, htp1, htp2, htp3⟩ :=
    prop_cer_quatpair_b p hp hA _ hπPlus hMPlus hDPlus
  obtain ⟨qMinus, hmq, hmqmem, hom, hrm, htm1, htm2, htm3⟩ :=
    prop_cer_quatpair_b p hp hA _ hπMinus hMMinus hDMinus
  have htPlus : tVec qPlus = tVec p + xPlus • v := by
    funext i
    fin_cases i
    · exact htp1
    · exact htp2
    · exact htp3
  have htMinus : tVec qMinus = tVec p + xMinus • v := by
    funext i
    fin_cases i
    · exact htm1
    · exact htm2
    · exact htm3
  have hfixPlus : tVec qPlus k = tVec p k := by
    rw [htPlus]
    simp [v, scheduleDirection_fixed]
  have hfixMinus : tVec qMinus k = tVec p k := by
    rw [htMinus]
    simp [v, scheduleDirection_fixed]
  have htvec : ∀ i : Fin 3, tVec p i = lam * tVec qPlus i + (1 - lam) * tVec qMinus i := by
    intro i
    rw [htPlus, htMinus]
    exact congrFun hconv i
  let Pplus := quatProj6 standardQuaternionicWindow qPlus hpqmem
  let Pminus := quatProj6 standardQuaternionicWindow qMinus hmqmem
  have hpHerm := quatProj6_hermitian standardQuaternionicWindow qPlus hpqmem
  have hpIdem := quatProj6_idempotent standardQuaternionicWindow qPlus hpqmem hpq
  have hmHerm := quatProj6_hermitian standardQuaternionicWindow qMinus hmqmem
  have hmIdem := quatProj6_idempotent standardQuaternionicWindow qMinus hmqmem hmq
  have hlam : lam ∈ Set.Icc (0 : ℝ) 1 := ⟨hlam0.le, hlam1.le⟩
  refine ⟨c12BlockMixtureModel Pplus Pminus hpHerm hpIdem hmHerm hmIdem lam hlam, ?_⟩
  intro w hw
  rw [c12BlockMixtureModel_probability, quatProj6_wordProb_e3 standardQuaternionicWindow qPlus hpqmem,
    quatProj6_wordProb_e3 standardQuaternionicWindow qMinus hmqmem]
  have ho' (i j : Fin 4) :
      fpOverlap p i j = fpOverlap qPlus i j ∧ fpOverlap p i j = fpOverlap qMinus i j :=
    ⟨(hop i j).symm, (hom i j).symm⟩
  have hR' (i j m : Fin 4) :
      fpTriangle p i j m = fpTriangle qPlus i j m ∧ fpTriangle p i j m = fpTriangle qMinus i j m :=
    ⟨(hrp i j m).symm, (hrm i j m).symm⟩
  symm
  rcases hw with hw | hw
  · exact nativeWordProbability_e3_affine_le_six hp hpq hmq hA ho' hR'
      (htvec 0) (htvec 1) (htvec 2) w hw
  · exact nativeWordProbability_e3_affine_on_schedule s hs hp hpq hmq hA ho' hR'
      (htvec 0) (htvec 1) (htvec 2) hfixPlus hfixMinus w hw

/-- Any list of words through length seven that no C12 model reproduces already
requires two distinct length-seven schedules. In particular this holds if no
class-I model reproduces the list. -/
theorem prop_cer_schedule_a_two_schedules (p : Fin 4 → Albert)
    (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p) (words : List (Word (Fin 4)))
    (hlen : ∀ w ∈ words, w.length ≤ 7)
    (hseparates : ¬ ∃ M : HilbertProjectiveData (Fin 4) ℂ (EuclideanSpace ℂ (Fin 12)),
      ∀ w ∈ words, M.probability w = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w) :
    ∃ u ∈ words, ∃ w ∈ words, u.length = 7 ∧ w.length = 7 ∧ u.map Prod.fst ≠ w.map Prod.fst := by
  by_contra h
  by_cases h7 : ∃ w ∈ words, w.length = 7
  · obtain ⟨u, hu, hu7⟩ := h7
    obtain ⟨M, hm⟩ := prop_cer_schedule_a p hp hA (u.map Prod.fst) (by simpa using hu7)
    apply hseparates
    refine ⟨M, fun w hw => hm w ?_⟩
    by_cases h6 : w.length ≤ 6
    · exact .inl h6
    · have hw7 : w.length = 7 := by have := hlen w hw; omega
      apply Or.inr
      by_contra hne
      exact h ⟨w, hw, u, hu, hw7, hu7, hne⟩
  · obtain ⟨M, hm⟩ := prop_cer_schedule_a p hp hA (List.replicate 7 0) (by simp)
    apply hseparates
    refine ⟨M, fun w hw => hm w (.inl ?_)⟩
    have hne : w.length ≠ 7 := fun he => h7 ⟨w, hw, he⟩
    have := hlen w hw
    omega

/-- The schedule lower bound for a list that excludes complex class-I models of
arbitrary dimension, rank, and state. -/
theorem prop_cer_schedule_a_classI (p : Fin 4 → Albert)
    (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p) (words : List (Word (Fin 4)))
    (hlen : ∀ w ∈ words, w.length ≤ 7)
    (hseparates : ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (M : HilbertProjectiveData (Fin 4) ℂ H), ¬ (∀ w ∈ words,
        M.probability w = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w)) :
    ∃ u ∈ words, ∃ w ∈ words, u.length = 7 ∧ w.length = 7 ∧ u.map Prod.fst ≠ w.map Prod.fst :=
  prop_cer_schedule_a_two_schedules p hp hA words hlen (by
    rintro ⟨M, hm⟩
    exact hseparates M hm)

end AlbertSequential.MatchingModels
