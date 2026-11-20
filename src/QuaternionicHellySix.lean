/- SPDX-License-Identifier: Apache-2.0 -/
module

public import PentadArityAndHelly
import NativeOrbitLifts
import NativePeirceIdentities
import NativeSquareCone
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

@[expose] public section

namespace AlbertSequential

noncomputable section

local instance : Module.Finite ℝ Octonion :=
  inferInstanceAs (Module.Finite ℝ (Quaternion ℝ × Quaternion ℝ))

local instance : Module.Finite ℝ Albert :=
  inferInstanceAs (Module.Finite ℝ ((Fin 3 → ℝ) × (Fin 3 → Octonion)))

/-- The quaternionic containment condition for a finite subfamily of a set of atoms. -/
def QuaternionicLocalContainment (n : ℕ) (S : Set Albert) : Prop :=
  ∀ T : Finset Albert, (T : Set Albert) ⊆ S → T.card ≤ n →
    ∃ Q : QuaternionicWindow, (T : Set Albert) ⊆ Q.subalgebra.carrier

/-- A geometric Helly property on arbitrary, possibly infinite, sets of atoms. -/
def QuaternionicHellyProperty (n : ℕ) : Prop :=
  ∀ S : Set Albert, (∀ x ∈ S, IsAtom x) → QuaternionicLocalContainment n S →
    ∃ Q : QuaternionicWindow, S ⊆ Q.subalgebra.carrier

private theorem QuaternionicWindow.proper (Q : QuaternionicWindow) : Q.subalgebra ≠ ⊤ := by
  intro h
  have hr := Q.finrank_eq
  rw [h, ← H3Subalgebra_O_eq_top, finrank_H3Subalgebra] at hr
  contradiction

private theorem lineSupport_mem_subalgebra (B : NativeJordanSubalgebra) {q a b : Albert}
    (hq : IsAtom q) (ha : IsAtom a) (hb : IsAtom b)
    (hqa : jordanMul q a = 0) (hqb : jordanMul q b = 0) (hab : a ≠ b)
    (haB : a ∈ B.carrier) (hbB : b ∈ B.carrier) :
    albertUnit - q ∈ B.carrier := by
  rw [(eq_fiv_support q a b hq ha hb hqa hqb hab).2]
  exact B.carrier.smul_mem _ (B.carrier.sub_mem (B.carrier.add_mem haB hbB)
    (B.carrier.smul_mem _ (B.product_mem _ haB _ hbB)))

private theorem trace_zero : albertTrace 0 = 0 := by
  change (∑ _ : Fin 3, (0 : ℝ)) = 0
  simp

private theorem trace_zero_on_span {S : Set Albert} (hS : ∀ z ∈ S, albertTrace z = 0) :
    ∀ z ∈ Submodule.span ℝ S, albertTrace z = 0 := by
  intro z hz
  induction hz using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => exact trace_zero
  | add x y _ _ hx hy => rw [albertTrace_add, hx, hy, add_zero]
  | smul r x _ hx => rw [albertTrace_smul, hx, mul_zero]

private theorem line_has_quaternionic_window (S : Set Albert) (hS : ∀ x ∈ S, IsAtom x)
    (hlocal : QuaternionicLocalContainment 6 S) {q : Albert} (hq : IsAtom q)
    (hline : S ⊆ (lineSubalgebra q hq).carrier) :
    ∃ Q : QuaternionicWindow, S ⊆ Q.subalgebra.carrier := by
  classical
  let L := S \ {q}
  have hLorth : ∀ z ∈ L, jordanMul q z = 0 := fun z hz =>
    (atom_of_mem_lineSubalgebra hq (hS z hz.1) (hline hz.1)).resolve_left hz.2
  let f := albertUnit - q
  have hftr : albertTrace f = 2 := by
    have he : albertTrace albertUnit = 3 := by simp [albertTrace, albertUnit]
    rw [show f = albertUnit - q from rfl, albertTrace_sub, he, hq.2]
    norm_num
  have hforth : jordanMul q f = 0 := by
    simp [f, jordanMul_sub_right, jordanMul_albertUnit_right, hq.1]
  let center : Albert → Albert := fun z => z - (1 / 2 : ℝ) • f
  let uncenter : Albert → Albert := fun z => z + (1 / 2 : ℝ) • f
  have h_uncenter : ∀ z, uncenter (center z) = z := fun z => sub_add_cancel z _
  have h_center : ∀ z, center (uncenter z) = z := fun z => add_sub_cancel_right z _
  have hunc_inj : Function.Injective uncenter := fun z w h => by
    simpa only [h_center] using congrArg center h
  let P := center '' L
  have hPtr : ∀ z ∈ P, albertTrace z = 0 := by
    rintro _ ⟨z, hz, rfl⟩
    simp [center, albertTrace_sub, albertTrace_smul, hS z hz.1 |>.2, hftr]
  have hPorth : ∀ z ∈ P, jordanMul q z = 0 := by
    rintro _ ⟨z, hz, rfl⟩
    simp [center, jordanMul_sub_right, jordanMul_smul_right, hLorth z hz, hforth]
  have hPu : ∀ z ∈ P, uncenter z ∈ L := by
    rintro _ ⟨z, hz, rfl⟩
    rwa [h_uncenter]
  have recover : ∀ (Q : QuaternionicWindow) {a b : Albert},
      a ∈ L → b ∈ L → a ≠ b → a ∈ Q.subalgebra.carrier → b ∈ Q.subalgebra.carrier →
      f ∈ Q.subalgebra.carrier ∧ q ∈ Q.subalgebra.carrier := by
    intro Q a b ha hb hab haQ hbQ
    have hf : f ∈ Q.subalgebra.carrier :=
      lineSupport_mem_subalgebra Q.subalgebra hq (hS a ha.1) (hS b hb.1) (hLorth a ha) (hLorth b hb)
        hab haQ hbQ
    refine ⟨hf, ?_⟩
    rw [show q = albertUnit - f by dsimp only [f]; abel]
    exact Q.subalgebra.carrier.sub_mem Q.subalgebra.unit_mem hf
  have center_mem : ∀ (Q : QuaternionicWindow) {z : Albert},
      uncenter z ∈ Q.subalgebra.carrier → f ∈ Q.subalgebra.carrier → z ∈ Q.subalgebra.carrier := by
    intro Q z hz hf
    rw [← h_center z]
    exact Q.subalgebra.carrier.sub_mem hz (Q.subalgebra.carrier.smul_mem _ hf)
  obtain ⟨T, hTP, _, hspan, hTind⟩ := Submodule.exists_finset_span_eq_linearIndepOn ℝ P
  have recover_from_two : ∀ (U : Finset Albert), (U : Set Albert) ⊆ P → 1 < U.card →
      ∀ (Q : QuaternionicWindow), (U.image uncenter : Set Albert) ⊆ Q.subalgebra.carrier →
      f ∈ Q.subalgebra.carrier ∧ q ∈ Q.subalgebra.carrier := by
    intro U hUP hcard Q hUQ
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
    exact recover Q (hPu a (hUP ha)) (hPu b (hUP hb)) (hunc_inj.ne hab)
      (hUQ (Finset.mem_image_of_mem uncenter ha)) (hUQ (Finset.mem_image_of_mem uncenter hb))
  have window_for_uncentered : ∀ U : Finset Albert, (U : Set Albert) ⊆ P → U.card ≤ 6 →
      ∃ Q : QuaternionicWindow, (U.image uncenter : Set Albert) ⊆ Q.subalgebra.carrier := by
    intro U hUP hc
    apply hlocal _ _ (Finset.card_image_le.trans hc)
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    exact (hPu w (hUP hw)).1
  have hTcard : T.card ≤ 5 := by
    by_contra! hlarge
    obtain ⟨U, hUT, hUc⟩ := Finset.exists_subset_card_eq (show 6 ≤ T.card by omega)
    have hUP : (U : Set Albert) ⊆ P := fun z hz => hTP (hUT hz)
    obtain ⟨Q, hUQ⟩ := window_for_uncentered U hUP hUc.le
    obtain ⟨hf, hqQ⟩ := recover_from_two U hUP (by omega) Q hUQ
    have hUind : LinearIndepOn ℝ id (U : Set Albert) := hTind.mono hUT
    have hf_not : f ∉ Submodule.span ℝ (U : Set Albert) := by
      intro h
      have h0 := trace_zero_on_span (fun z hz => hPtr z (hUP hz)) f h
      linarith
    have hUrange : Set.range (fun z : U => (z : Albert)) = (U : Set Albert) := by
      ext z; simp
    have hind : LinearIndependent ℝ (fun o : Option U => Option.casesOn' o f Subtype.val) :=
      hUind.option (by
        change f ∉ Submodule.span ℝ (Set.range (fun z : U => (z : Albert)))
        rwa [hUrange])
    have hmem : ∀ o : Option U, Option.casesOn' o f Subtype.val ∈ quatCornerSubmodule Q q := by
      intro o
      cases o with
      | none => exact ⟨hf, hforth⟩
      | some z =>
        exact ⟨center_mem Q (hUQ (Finset.mem_image_of_mem uncenter z.2)) hf,
          hPorth z (hUP z.2)⟩
    let v : Option U → quatCornerSubmodule Q q := fun o => ⟨_, hmem o⟩
    have hv : LinearIndependent ℝ v := hind.of_comp (quatCornerSubmodule Q q).subtype
    have hdim := hv.fintype_card_le_finrank
    simp only [Fintype.card_option, Fintype.card_coe, hUc] at hdim
    have hbound := quat_corner_finrank_le_six Q q hq hqQ
    omega
  by_cases hpair : ∃ a ∈ L, ∃ b ∈ L, a ≠ b
  · obtain ⟨a, ha, b, hb, hab⟩ := hpair
    have hex : ∃ Q : QuaternionicWindow, f ∈ Q.subalgebra.carrier ∧
        q ∈ Q.subalgebra.carrier ∧ (T : Set Albert) ⊆ Q.subalgebra.carrier := by
      by_cases hsmall : T.card ≤ 4
      · let U := insert (center a) (insert (center b) T)
        have hUP : (U : Set Albert) ⊆ P := by
          intro z hz
          simp only [U, Finset.mem_coe, Finset.mem_insert] at hz
          rcases hz with rfl | rfl | hz
          · exact ⟨a, ha, rfl⟩
          · exact ⟨b, hb, rfl⟩
          · exact hTP hz
        have hUc : U.card ≤ 6 := by
          have h1 := Finset.card_insert_le (a := center a) (s := insert (center b) T)
          have h2 := Finset.card_insert_le (a := center b) (s := T)
          dsimp only [U]
          omega
        obtain ⟨Q, hUQ⟩ := window_for_uncentered U hUP hUc
        have haQ : a ∈ Q.subalgebra.carrier := by
          rw [← h_uncenter a]
          exact hUQ (Finset.mem_image_of_mem uncenter (by simp [U]))
        have hbQ : b ∈ Q.subalgebra.carrier := by
          rw [← h_uncenter b]
          exact hUQ (Finset.mem_image_of_mem uncenter (by simp [U]))
        obtain ⟨hf, hqQ⟩ := recover Q ha hb hab haQ hbQ
        exact ⟨Q, hf, hqQ, fun z hz =>
          center_mem Q (hUQ (Finset.mem_image_of_mem uncenter
            (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz)))) hf⟩
      · obtain ⟨Q, hTQ⟩ := window_for_uncentered T hTP (by omega)
        obtain ⟨hf, hqQ⟩ := recover_from_two T hTP (by omega) Q hTQ
        exact ⟨Q, hf, hqQ, fun z hz => center_mem Q (hTQ (Finset.mem_image_of_mem uncenter hz)) hf⟩
    obtain ⟨Q, hf, hqQ, hTQ⟩ := hex
    refine ⟨Q, fun z hz => ?_⟩
    by_cases hqz : z = q
    · exact hqz ▸ hqQ
    have hu : center z ∈ Submodule.span ℝ P := Submodule.subset_span ⟨z, ⟨hz, hqz⟩, rfl⟩
    have hzQ : center z ∈ Q.subalgebra.carrier := (Submodule.span_le.mpr hTQ) (hspan ▸ hu)
    rw [← h_uncenter z]
    exact Q.subalgebra.carrier.add_mem hzQ (Q.subalgebra.carrier.smul_mem _ hf)
  · have hfin : ∃ U : Finset Albert, (U : Set Albert) = S ∧ U.card ≤ 2 := by
      by_cases hL : L.Nonempty
      · obtain ⟨a, ha⟩ := hL
        have heq : ∀ z ∈ L, z = a := fun z hz =>
          not_ne_iff.mp (fun h => hpair ⟨z, hz, a, ha, h⟩)
        let U : Finset Albert := {a, q}
        have hSU : S ⊆ U := by
          intro z hz
          by_cases hzq : z = q
          · simp [U, hzq]
          · simp [U, heq z ⟨hz, hzq⟩]
        exact ⟨U.filter (· ∈ S), by ext z; exact ⟨fun hz => (Finset.mem_filter.mp hz).2,
          fun hz => Finset.mem_filter.mpr ⟨hSU hz, hz⟩⟩,
          (Finset.card_filter_le _ _).trans (by
            dsimp only [U]
            exact (Finset.card_insert_le _ _).trans (by simp))⟩
      · let U : Finset Albert := {q}
        have hSU : S ⊆ U := by
          intro z hz
          by_contra hz'
          exact hL ⟨z, hz, by simpa [U] using hz'⟩
        exact ⟨U.filter (· ∈ S), by ext z; exact ⟨fun hz => (Finset.mem_filter.mp hz).2,
          fun hz => Finset.mem_filter.mpr ⟨hSU hz, hz⟩⟩,
          (Finset.card_filter_le _ _).trans (by simp [U])⟩
    obtain ⟨U, rfl, hcard⟩ := hfin
    exact hlocal U (by intro z hz; exact hz) (by omega)

/-- A set of Albert atoms is quaternionically contained if every at-most-six subset is. -/
theorem quaternionicHelly_six : QuaternionicHellyProperty 6 := by
  intro S hS hlocal
  obtain ⟨B, hB, hSB⟩ := (cor_helly_geometric S hS).mpr (by
    intro T hTS hc
    obtain ⟨Q, hTQ⟩ := hlocal T hTS (by omega)
    exact ⟨Q.subalgebra, Q.proper, hTQ⟩)
  have hlt : B.carrier < (H3Subalgebra .O).carrier := by
    rw [H3Subalgebra_O_eq_top]
    exact lt_of_le_of_ne le_top fun h => hB (nativeJordanSubalgebra_ext h)
  rcases lem_five_sub .O B hlt with ⟨q, hq, _, hline⟩ | ⟨Q, hQ⟩
  · exact line_has_quaternionic_window S hS hlocal hq (hSB.trans hline)
  · exact ⟨Q, hSB.trans hQ⟩

/-- The lower endpoint follows from the six-atom counterexample in the native corner. -/
theorem quaternionicHelly_iff (n : ℕ) : QuaternionicHellyProperty n ↔ 6 ≤ n := by
  constructor
  · intro h
    by_contra! hn
    obtain ⟨ha, hlocal, hno, _⟩ := lineHellyCounterexample6_controls
    obtain ⟨Q, hQ⟩ := h (Set.range lineHellyCounterexample6) (by rintro _ ⟨i, rfl⟩; exact ha i) (by
      intro T hT hc
      exact hlocal T hT (by omega))
    exact hno ⟨Q, fun i => hQ ⟨i, rfl⟩⟩
  · intro hn S hS h
    exact quaternionicHelly_six S hS fun T hTS hc => h T hTS (hc.trans hn)

theorem quaternionicHelly_isLeast : IsLeast {n | QuaternionicHellyProperty n} 6 :=
  ⟨quaternionicHelly_six, fun n hn => (quaternionicHelly_iff n).mp hn⟩

/-- Coordinates of the normalized dyad of `(1, u, 0)` when `u` is a unit octonion. -/
def dyadOnLine (u : Octonion) : Albert :=
  mkAlbert ![1 / 2, 1 / 2, 0] ![(1 / 2 : ℝ) • octonionConj u, 0, 0]

theorem dyadOnLine_matrix (u : Octonion) (hu : octNormSq u = 1) (a b : Fin 3) :
    albertMatrix (dyadOnLine u) a b =
      (1 / 2 : ℝ) • octonionMul (![octOne, u, 0] a) (octonionConj (![octOne, u, 0] b)) := by
  fin_cases a <;> fin_cases b <;>
    simp [albertMatrix, dyadOnLine, mkAlbert, octonionConj_one, octonionConj_zero, octonionConj_smul,
      octonionConj_conj, octonionMul_one_left, octonionMul_one_right,
      octonionMul_zero_left, octonionMul_zero_right, octonionScalar_zero,
      octMul_self_conj, hu, ← octOne_eq_scalar]
  all_goals exact octonionScalar_eq_smul _

/-- The normalized dyads of the six displayed columns in the published corner. -/
def paperLineHellySix : Fin 6 → Albert
  | 0 => diagAtom 0
  | 1 => dyadOnLine octOne
  | 2 => dyadOnLine octI
  | 3 => dyadOnLine octJ
  | 4 => dyadOnLine (octonionMul octI octJ)
  | 5 => dyadOnLine octL

private theorem unusedOctNorm : octNormSq octS = 1 := by
  rw [octNormSq_eq_coords]
  norm_num [octS]

private def paperLineHellyAuto : NativeAlbertAutomorphism :=
  (swap01AlbertAuto.comp swap02AlbertAuto).comp
    ((middleMoufangAlbertAuto octS unusedOctNorm).comp
      (familyCMoufangAlbertAuto octS unusedOctNorm))

private def hellyOctUnits : Fin 5 → Octonion := ![octOne, octI, octJ, octK, octL]

private theorem unusedOctConj (k : Fin 5) :
    octonionMul (octonionMul (octonionConj octS) (hellyOctUnits k)) octS =
      octonionConj (hellyOctUnits k) := by
  fin_cases k <;> apply Prod.ext <;> apply Quaternion.ext <;>
    norm_num [hellyOctUnits, octS, octOne, octI, octJ, octK, octL, octonionScalar, octonionMul,
      octonionConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem paperLineHellyAuto_spin (k : Fin 5) :
    paperLineHellyAuto.linearEquiv (spinAtom (hellyOctUnits k)) =
      dyadOnLine (hellyOctUnits k) := by
  change swap01AlbertAuto.linearEquiv (swap02AlbertAuto.linearEquiv
    ((middleMoufangAlbertAuto octS unusedOctNorm).linearEquiv
      ((familyCMoufangAlbertAuto octS unusedOctNorm).linearEquiv
        (spinAtom (hellyOctUnits k))))) = _
  have hf : (familyCMoufangAlbertAuto octS unusedOctNorm).linearEquiv (spinAtom (hellyOctUnits k)) =
      spinAtom (octonionMul (octonionConj octS) (hellyOctUnits k)) := by
    rw [familyCMoufangAlbertAuto_apply]
    apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;> simp [spinAtom, mkAlbert, octonionMul_zero_left, octonionMul_zero_right,
        octonionMul_smul_right]
  have hm : ∀ z, (middleMoufangAlbertAuto octS unusedOctNorm).linearEquiv (spinAtom z) =
      spinAtom (octonionMul z octS) := by
    intro z
    rw [middleMoufangAlbertAuto_apply]
    apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;> simp [spinAtom, mkAlbert, octonionMul_zero_left, octonionMul_zero_right,
        octonionMul_smul_left]
  have hs : ∀ z, swap02AlbertAuto.linearEquiv (spinAtom z) =
      mkAlbert ![1 / 2, 1 / 2, 0] ![octonionConj ((1 / 2 : ℝ) • z), 0, 0] := by
    intro z
    rw [swap02AlbertAuto_apply]
    apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;> simp [spinAtom, mkAlbert, octonionConj_zero]
  rw [hf, hm, unusedOctConj, hs, swap01AlbertAuto_apply]
  apply Prod.ext
  · rfl
  · funext i
    fin_cases i <;> simp [dyadOnLine, mkAlbert, octonionConj_conj]

private theorem paperLineHellyAuto_apply (i : Fin 6) :
    paperLineHellyAuto.linearEquiv (lineHellyCounterexample6 i) = paperLineHellySix i := by
  fin_cases i
  · change swap01AlbertAuto.linearEquiv (swap02AlbertAuto.linearEquiv
      ((middleMoufangAlbertAuto octS unusedOctNorm).linearEquiv
        ((familyCMoufangAlbertAuto octS unusedOctNorm).linearEquiv (diagAtom 1)))) = diagAtom 0
    rw [familyCMoufangAlbertAuto_diagAtom, middleMoufangAlbertAuto_diagAtom,
      swap02AlbertAuto_diagAtom, swap01AlbertAuto_diagAtom]
    rfl
  · exact paperLineHellyAuto_spin 0
  · exact paperLineHellyAuto_spin 1
  · exact paperLineHellyAuto_spin 2
  · change paperLineHellyAuto.linearEquiv (spinAtom octK) = dyadOnLine (octonionMul octI octJ)
    rw [octK_eq_mul]
    exact paperLineHellyAuto_spin 3
  · exact paperLineHellyAuto_spin 4

theorem paperLineHellySix_coordinates :
    ∃ g : NativeAlbertAutomorphism, ∀ i : Fin 6,
      g.linearEquiv (lineHellyCounterexample6 i) = paperLineHellySix i :=
  ⟨paperLineHellyAuto, paperLineHellyAuto_apply⟩

private theorem diagThree_orthogonal_of_coordinates {x : Albert}
    (h : x.1 2 = 0) (h1 : x.2 1 = 0) (h2 : x.2 2 = 0) :
    jordanMul (diagAtom 2) x = 0 := by
  rw [jordanMul_diagAtom2, h, h1, h2, smul_zero]
  apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

/-- The literal six dyads lie on the line opposite `E₃₃`. Every five share a
quaternionic window, while the six have no common window. -/
theorem paperLineHellySix_controls :
    (∀ i, IsAtom (paperLineHellySix i)) ∧
    (∀ i, jordanMul (diagAtom 2) (paperLineHellySix i) = 0) ∧
    QuaternionicLocalContainment 5 (Set.range paperLineHellySix) ∧
    ¬ (∃ Q : QuaternionicWindow, Set.range paperLineHellySix ⊆ Q.subalgebra.carrier) := by
  classical
  obtain ⟨hatoms, hlocal, hno, _⟩ := lineHellyCounterexample6_controls
  obtain ⟨g, hg⟩ := paperLineHellySix_coordinates
  refine ⟨fun i => hg i ▸ g.map_isAtom (hatoms i), ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> exact diagThree_orthogonal_of_coordinates rfl rfl rfl
  · intro T hTS hc
    let U := T.image g.linearEquiv.symm
    have hU : (U : Set Albert) ⊆ Set.range lineHellyCounterexample6 := by
      intro z hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨i, rfl⟩ := hTS hw
      exact ⟨i, by rw [← hg, LinearEquiv.symm_apply_apply]⟩
    obtain ⟨Q, hQ⟩ := hlocal U hU (Finset.card_image_le.trans hc)
    refine ⟨Q.transport g, fun z hz => ?_⟩
    exact ⟨g.linearEquiv.symm z, hQ _ (Finset.mem_image_of_mem _ hz),
      g.linearEquiv.apply_symm_apply z⟩
  · rintro ⟨Q, hQ⟩
    apply hno
    refine ⟨Q.transport g.symm, fun i => ?_⟩
    refine ⟨paperLineHellySix i, hQ ⟨i, rfl⟩, ?_⟩
    change g.linearEquiv.symm (paperLineHellySix i) = _
    rw [← hg, LinearEquiv.symm_apply_apply]

private theorem paperLineHellySix_overlap {i j : Fin 6} (h : i ≠ j) :
    tracePairing (paperLineHellySix i) (paperLineHellySix j) = 1 / 2 := by
  obtain ⟨g, hg⟩ := paperLineHellySix_coordinates
  rw [← hg i, ← hg j, g.map_tracePairing, tracePairing_eq_coords]
  fin_cases i <;> fin_cases j
  all_goals first
    | exact (h rfl).elim
    | simp [lineHellyCounterexample6, diagAtom, spinAtom, mkAlbert, octDot_zero_left,
        octDot_zero_right, octDot_smul_left, octDot_smul_right]
  all_goals rw [octDot_eq_coords]
  all_goals norm_num [octOne, octonionScalar, octI, octJ, octK, octL]

private theorem line_generated_structure {ι : Type*} [Fintype ι] (p : ι → Albert)
    (q : Albert) (hq : IsAtom q) (hp : ∀ i, IsAtom (p i))
    (horth : ∀ i, jordanMul q (p i) = 0)
    (hoverlap : ∀ i j, i ≠ j → tracePairing (p i) (p j) = 1 / 2)
    (hpair : ∃ i j : ι, i ≠ j) :
    let f := albertUnit - q
    let u : ι → Albert := fun i => p i - (1 / 2 : ℝ) • f
    (generatedSubalgebra (Set.range p)).carrier =
      Submodule.span ℝ (insert q (insert f (Set.range u))) ∧
    LinearIndependent ℝ u ∧ jordanMul q f = 0 ∧ jordanMul f f = f ∧
    (∀ i, jordanMul q (u i) = 0 ∧ jordanMul f (u i) = u i ∧
      jordanMul (u i) (u i) = (1 / 4 : ℝ) • f) ∧
    (∀ i j, i ≠ j → jordanMul (u i) (u j) = 0) ∧
    Module.finrank ℝ (generatedSubalgebra (Set.range p)).carrier = Fintype.card ι + 2 := by
  classical
  let f := albertUnit - q
  let u : ι → Albert := fun i => p i - (1 / 2 : ℝ) • f
  have hq0 : q ≠ 0 := by
    intro h
    exact zero_ne_one (by simpa only [h, trace_zero] using hq.2)
  have hftr : albertTrace f = 2 := by
    have he : albertTrace albertUnit = 3 := by simp [albertTrace, albertUnit]
    rw [show f = albertUnit - q from rfl, albertTrace_sub, he, hq.2]
    norm_num
  have hf0 : f ≠ 0 := by
    intro h
    have := hftr
    rw [h, trace_zero] at this
    norm_num at this
  have hqf : jordanMul q f = 0 := by
    simp [f, jordanMul_sub_right, jordanMul_albertUnit_right, hq.1]
  have hff : jordanMul f f = f := by
    change jordanMul (albertUnit - q) f = f
    rw [jordanMul_sub_left, jordanMul_albertUnit_left, hqf, sub_zero]
  have hfp (i : ι) : jordanMul f (p i) = p i := by
    simp [f, jordanMul_sub_left, jordanMul_albertUnit_left, horth]
  have hqu (i : ι) : jordanMul q (u i) = 0 := by
    simp [u, jordanMul_sub_right, jordanMul_smul_right, horth, hqf]
  have hfu (i : ι) : jordanMul f (u i) = u i := by
    simp [u, jordanMul_sub_right, jordanMul_smul_right, hfp, hff]
  have htr (i : ι) : albertTrace (u i) = 0 := by
    simp [u, albertTrace_sub, albertTrace_smul, (hp i).2, hftr]
  have hne (i j : ι) (h : i ≠ j) : p i ≠ p j := by
    intro hij
    have hov := hoverlap i j h
    rw [← hij, tracePairing, (hp i).1, (hp i).2] at hov
    norm_num at hov
  have hprod (i j : ι) : jordanMul (u i) (u j) = if i = j then (1 / 4 : ℝ) • f else 0 := by
    have hexp : jordanMul (u i) (u j) =
        jordanMul (p i) (p j) - (1 / 2 : ℝ) • p i - (1 / 2 : ℝ) • p j + (1 / 4 : ℝ) • f := by
      have hpf : jordanMul (p i) f = p i := (jordanMul_comm _ _).trans (hfp i)
      simp only [u, jordanMul_sub_left, jordanMul_sub_right, jordanMul_smul_left,
        jordanMul_smul_right, hfp, hpf, hff]
      module
    rw [hexp]
    by_cases h : i = j
    · subst j
      rw [ite_eq_left rfl, (hp i).1]
      module
    · rw [ite_eq_right h]
      have hsup := (eq_fiv_support q (p i) (p j) hq (hp i) (hp j)
        (horth i) (horth j) (hne i j h)).2
      change f = _ at hsup
      rw [hoverlap i j h] at hsup
      norm_num at hsup
      rw [hsup]
      module
  have hind : LinearIndependent ℝ u := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have h := congrArg (nativeJordanProductLinear (u j)) hc
    simp only [map_sum, map_smul, map_zero] at h
    change (∑ i, c i • jordanMul (u j) (u i)) = 0 at h
    simp only [hprod, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h
    rw [smul_smul] at h
    exact (mul_eq_zero.mp ((smul_eq_zero.mp h).resolve_right hf0)).resolve_right (by norm_num)
  let w : Option ι → Albert := fun i => Option.casesOn' i f u
  let v : Option (Option ι) → Albert := fun i => Option.casesOn' i q w
  have hw : LinearIndependent ℝ w := hind.option (by
    intro hf
    have hz := trace_zero_on_span (S := Set.range u) (by rintro _ ⟨i, rfl⟩; exact htr i) f hf
    linarith)
  have hw0 (i : Option ι) : jordanMul q (w i) = 0 := by
    cases i with
    | none => exact hqf
    | some i => exact hqu i
  have hv : LinearIndependent ℝ v := hw.option (by
    intro hz
    have hk : Submodule.span ℝ (Set.range w) ≤ (nativeJordanProductLinear q).ker :=
      Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact LinearMap.mem_ker.mpr (hw0 i))
    exact hq0 (hq.1.symm.trans (LinearMap.mem_ker.mp (hk hz))))
  let W := Submodule.span ℝ (Set.range v)
  have hqW : q ∈ W := Submodule.subset_span ⟨none, rfl⟩
  have hfW : f ∈ W := Submodule.subset_span ⟨some none, rfl⟩
  have huW (i : ι) : u i ∈ W := Submodule.subset_span ⟨some (some i), rfl⟩
  have hWprod : ∀ x ∈ Set.range v, ∀ y ∈ Set.range v, jordanMul x y ∈ W := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    cases i with
    | none =>
      cases j with
      | none => change jordanMul q q ∈ W; rwa [hq.1]
      | some j => change jordanMul q (w j) ∈ W; rw [hw0]; exact W.zero_mem
    | some i =>
      cases j with
      | none => change jordanMul (w i) q ∈ W; rw [jordanMul_comm, hw0]; exact W.zero_mem
      | some j =>
        cases i with
        | none =>
          cases j with
          | none => change jordanMul f f ∈ W; rwa [hff]
          | some j => change jordanMul f (u j) ∈ W; rw [hfu]; exact huW j
        | some i =>
          cases j with
          | none => change jordanMul (u i) f ∈ W; rw [jordanMul_comm, hfu]; exact huW i
          | some j =>
            change jordanMul (u i) (u j) ∈ W
            rw [hprod]
            split
            · exact W.smul_mem _ hfW
            · exact W.zero_mem
  let A : NativeJordanSubalgebra := {
    carrier := W
    unit_mem := by
      have he : albertUnit = q + f := by dsimp [f]; abel
      rw [he]
      exact W.add_mem hqW hfW
    product_mem := fun x hx y hy =>
      LinearMap.BilinMap.apply_apply_mem_of_mem_span W (Set.range v) (Set.range v)
        nativeJordanProductLinear hWprod x y hx hy }
  let B := generatedSubalgebra (Set.range p)
  have hBW : B.carrier ≤ W := generatedSubalgebra_le (B := A) (by
    rintro _ ⟨i, rfl⟩
    have he : p i = u i + (1 / 2 : ℝ) • f := by dsimp [u]; abel
    rw [he]
    exact W.add_mem (huW i) (W.smul_mem _ hfW))
  have hpB (i : ι) : p i ∈ B.carrier := subset_generatedSubalgebra _ ⟨i, rfl⟩
  obtain ⟨i, j, hij⟩ := hpair
  have hfB : f ∈ B.carrier := lineSupport_mem_subalgebra B hq (hp i) (hp j)
    (horth i) (horth j) (hne i j hij) (hpB i) (hpB j)
  have hqB : q ∈ B.carrier := by
    rw [show q = albertUnit - f by dsimp [f]; abel]
    exact B.carrier.sub_mem B.unit_mem hfB
  have hWB : W ≤ B.carrier := Submodule.span_le.mpr (by
    rintro _ ⟨i, rfl⟩
    cases i with
    | none => exact hqB
    | some i =>
      cases i with
      | none => exact hfB
      | some i => exact B.carrier.sub_mem (hpB i) (B.carrier.smul_mem _ hfB))
  have hB : B.carrier = W := le_antisymm hBW hWB
  have hv_range : Set.range v = insert q (insert f (Set.range u)) := by
    ext z
    rw [Set.mem_insert_iff, Set.mem_insert_iff]
    constructor
    · rintro ⟨i, rfl⟩
      cases i with
      | none => exact Or.inl rfl
      | some i =>
        cases i with
        | none => exact Or.inr (Or.inl rfl)
        | some i => exact Or.inr (Or.inr ⟨i, rfl⟩)
    · rintro (rfl | rfl | ⟨i, rfl⟩)
      · exact ⟨none, rfl⟩
      · exact ⟨some none, rfl⟩
      · exact ⟨some (some i), rfl⟩
  refine ⟨?_, hind, hqf, hff, ?_, ?_, ?_⟩
  · change B.carrier = _
    rw [hB, show W = Submodule.span ℝ (Set.range v) from rfl, hv_range]
  · intro i
    exact ⟨hqu i, hfu i, (hprod i i).trans (ite_eq_left rfl)⟩
  · intro i j hij
    exact (hprod i j).trans (ite_eq_right hij)
  · change Module.finrank ℝ B.carrier = _
    rw [hB, finrank_span_eq_card hv, Fintype.card_option, Fintype.card_option]

/-- Any five of the displayed dyads generate the direct sum of the reference
atom and their line spin factor. The displayed table also covers all six. -/
theorem paperLineHelly_generated_structure (I : Finset (Fin 6)) (hI : 2 ≤ I.card) :
    let p : I → Albert := fun i => paperLineHellySix i
    let q := diagAtom 2
    let f := albertUnit - q
    let u : I → Albert := fun i => p i - (1 / 2 : ℝ) • f
    (generatedSubalgebra (Set.range p)).carrier =
      Submodule.span ℝ (insert q (insert f (Set.range u))) ∧
    LinearIndependent ℝ u ∧ jordanMul q f = 0 ∧ jordanMul f f = f ∧
    (∀ i, jordanMul q (u i) = 0 ∧ jordanMul f (u i) = u i ∧
      jordanMul (u i) (u i) = (1 / 4 : ℝ) • f) ∧
    (∀ i j, i ≠ j → jordanMul (u i) (u j) = 0) ∧
    Module.finrank ℝ (generatedSubalgebra (Set.range p)).carrier = I.card + 2 := by
  classical
  obtain ⟨ha, ho, _, _⟩ := paperLineHellySix_controls
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hI
  have h := line_generated_structure (fun i : I => paperLineHellySix i) (diagAtom 2)
    (diagAtom_isAtom 2) (fun i => ha i) (fun i => ho i)
    (fun _ _ hne => paperLineHellySix_overlap (fun e => hne (Subtype.ext e)))
    ⟨⟨i, hi⟩, ⟨j, hj⟩, fun he => hij (congrArg Subtype.val he)⟩
  simpa only [Fintype.card_coe] using h

theorem paperLineHellySix_generated_finrank :
    Module.finrank ℝ (generatedSubalgebra (Set.range paperLineHellySix)).carrier = 8 := by
  obtain ⟨ha, ho, _, _⟩ := paperLineHellySix_controls
  obtain ⟨_, _, _, _, _, _, hdim⟩ :=
    line_generated_structure paperLineHellySix (diagAtom 2) (diagAtom_isAtom 2)
      ha ho (fun _ _ => paperLineHellySix_overlap) ⟨0, 1, by decide⟩
  simpa only [Fintype.card_fin] using hdim

theorem paperLineHellyFive_generated_finrank (I : Finset (Fin 6)) (hI : I.card = 5) :
    Module.finrank ℝ (generatedSubalgebra (Set.range fun i : I => paperLineHellySix i)).carrier = 7 := by
  classical
  obtain ⟨_, _, _, _, _, _, hdim⟩ := paperLineHelly_generated_structure I (by omega)
  simpa only [hI] using hdim

/-- A unital Jordan isomorphism from the standard quaternionic subalgebra
preserves the primitive normalization of the ambient trace. -/
theorem quaternionicIso_preserves_trace {B : NativeJordanSubalgebra}
    (ψ : JordanSubalgebraIso (H3Subalgebra .H) B) (x : (H3Subalgebra .H).carrier) :
    albertTrace (ψ.toLinearEquiv x).1 = albertTrace x.1 := by
  let d : Fin 3 → (H3Subalgebra .H).carrier := fun i =>
    ⟨diagAtom i, diagAtom_mem_H3Subalgebra .H i⟩
  let y := ψ.toLinearEquiv x
  have he : ∑ i, d i = ⟨albertUnit, (H3Subalgebra .H).unit_mem⟩ := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact diagAtom_sum_eq_unit
  have he' : ∑ i, (ψ.toLinearEquiv (d i)).1 = albertUnit := by
    have h := congrArg ψ.toLinearEquiv he
    rw [map_sum, ψ.map_unit] at h
    exact (Submodule.coe_sum _ _ _).symm.trans (congrArg Subtype.val h)
  have hcoeff : ∀ i, tracePairing (ψ.toLinearEquiv (d i)).1 y.1 = tracePairing (d i).1 x.1 := by
    intro i
    have ha : IsAtom (d i).1 := diagAtom_isAtom i
    have hb := iso_maps_atom ψ (d i) ha
    have hb0 : (ψ.toLinearEquiv (d i)).1 ≠ 0 := by
      intro hz
      have := hb.2
      rw [hz, trace_zero] at this
      exact zero_ne_one this
    have hm := ψ.map_quadraticMap (d i) x
    obtain ⟨z, hz, hmap⟩ : ∃ z : (H3Subalgebra .H).carrier,
        z.1 = quadraticMap (d i).1 x.1 ∧
          (ψ.toLinearEquiv z).1 = quadraticMap (ψ.toLinearEquiv (d i)).1 y.1 :=
      ⟨_, rfl, hm⟩
    have hz' : z = tracePairing (d i).1 x.1 • d i :=
      Subtype.ext (hz.trans (quadraticMap_atom _ _ ha))
    rw [hz', map_smul, Submodule.coe_smul, quadraticMap_atom _ _ hb] at hmap
    exact (smul_left_injective ℝ hb0 hmap).symm
  have hsum : ∀ (p : Fin 3 → Albert) (z : Albert),
      tracePairing (∑ i, p i) z = ∑ i, tracePairing (p i) z := by
    intro p z
    simp [Fin.sum_univ_three, tracePairing_add_left]
  have hunit (z : Albert) : tracePairing albertUnit z = albertTrace z := by
    unfold tracePairing
    rw [jordanMul_albertUnit_left]
  have hd : ∑ i, (d i).1 = albertUnit := diagAtom_sum_eq_unit
  calc
    albertTrace y.1 = ∑ i, tracePairing (ψ.toLinearEquiv (d i)).1 y.1 := by
      rw [← hsum, he', hunit]
    _ = ∑ i, tracePairing (d i).1 x.1 := Finset.sum_congr rfl fun i _ => hcoeff i
    _ = albertTrace x.1 := by rw [← hsum, hd, hunit]

private theorem quaternionicWindowIso (Q : QuaternionicWindow) :
    Nonempty (JordanSubalgebraIso (H3Subalgebra .H) Q.subalgebra) := by
  let e := assocHermEquiv assocCD_H
  let b := (quatWindowEquiv Q).symm
  have hb (M : QuatHermitian3) : (b M).1 = Q.embedding M := by
    rw [← quatWindowEquiv_apply_eq Q (b M)]
    change Q.embedding (quatWindowEquiv Q ((quatWindowEquiv Q).symm M)) = _
    rw [LinearEquiv.apply_symm_apply]
  have he1 : e 1 = ⟨albertUnit, (H3Subalgebra .H).unit_mem⟩ :=
    Subtype.ext (assocHermEquiv_one assocCD_H)
  refine ⟨⟨e.symm.trans b, ?_, ?_⟩⟩
  · apply Subtype.ext
    change (b (e.symm ⟨albertUnit, (H3Subalgebra .H).unit_mem⟩)).1 = albertUnit
    rw [← he1, LinearEquiv.symm_apply_apply, hb, Q.unit]
  · intro x y
    let M := e.symm x
    let N := e.symm y
    obtain ⟨P, hP⟩ := quatHermitian_product_closed M N
    have hp : (e P).1 = jordanMul x.1 y.1 := by
      rw [assocHermEquiv_apply, hP, jordanMul_assocMatToAlbert]
      have hx := congrArg Subtype.val (e.apply_symm_apply x)
      have hy := congrArg Subtype.val (e.apply_symm_apply y)
      change assocMatToAlbert assocCD_H M.1 = x.1 at hx
      change assocMatToAlbert assocCD_H N.1 = y.1 at hy
      rw [hx, hy]
    have hev : e.symm ⟨jordanMul x.1 y.1, (H3Subalgebra .H).product_mem _ x.2 _ y.2⟩ = P :=
      e.symm_apply_eq.mpr (Subtype.ext hp.symm)
    apply Subtype.ext
    change (b (e.symm ⟨jordanMul x.1 y.1, _⟩)).1 = jordanMul (b M).1 (b N).1
    rw [hev, hb, hb, hb]
    exact Q.preserves_product M N P hP

private theorem quaternionicIsoWindow (B : NativeJordanSubalgebra)
    (ψ : JordanSubalgebraIso (H3Subalgebra .H) B) :
    ∃ Q : QuaternionicWindow, Q.subalgebra = B := by
  let e : QuatHermitian3 ≃ₗ[ℝ] (H3Subalgebra .H).carrier := assocHermEquiv assocCD_H
  let c := e.trans ψ.toLinearEquiv
  let emb : QuatHermitian3 →ₗ[ℝ] Albert := B.carrier.subtype.comp c.toLinearMap
  have he1 : e 1 = ⟨albertUnit, (H3Subalgebra .H).unit_mem⟩ :=
    Subtype.ext (assocHermEquiv_one assocCD_H)
  refine ⟨{
    subalgebra := B
    embedding := emb
    injective := Subtype.val_injective.comp c.injective
    range_eq := ?_
    unit := ?_
    preserves_product := ?_
    preserves_trace := ?_ }, rfl⟩
  · ext x
    constructor
    · rintro ⟨M, rfl⟩
      exact (c M).2
    · intro hx
      exact ⟨c.symm ⟨x, hx⟩, congrArg Subtype.val (c.apply_symm_apply ⟨x, hx⟩)⟩
  · change (ψ.toLinearEquiv (e 1)).1 = albertUnit
    rw [he1, ψ.map_unit]
  · intro M N P hP
    have hp : e P = ⟨jordanMul (e M).1 (e N).1,
        (H3Subalgebra .H).product_mem _ (e M).2 _ (e N).2⟩ := by
      apply Subtype.ext
      change assocMatToAlbert assocCD_H P.1 =
        jordanMul (assocMatToAlbert assocCD_H M.1) (assocMatToAlbert assocCD_H N.1)
      rw [hP, jordanMul_assocMatToAlbert]
    change (ψ.toLinearEquiv (e P)).1 =
      jordanMul (ψ.toLinearEquiv (e M)).1 (ψ.toLinearEquiv (e N)).1
    rw [hp, ψ.map_jordanMul_eq]
  · intro M
    change albertTrace (ψ.toLinearEquiv (e M)).1 = _
    rw [quaternionicIso_preserves_trace]
    change (∑ i : Fin 3, (M.1 i i).re) = _
    rw [Fin.sum_univ_three]

/-- A window is exactly a unital Jordan subalgebra isomorphic to `H₃(ℍ)`. -/
theorem quaternionicContainment_iff_iso (S : Set Albert) :
    (∃ Q : QuaternionicWindow, S ⊆ Q.subalgebra.carrier) ↔
      (∃ B : NativeJordanSubalgebra, Nonempty (JordanSubalgebraIso (H3Subalgebra .H) B) ∧
        S ⊆ B.carrier) := by
  constructor
  · rintro ⟨Q, hQ⟩
    exact ⟨Q.subalgebra, quaternionicWindowIso Q, hQ⟩
  · rintro ⟨B, ⟨ψ⟩, hB⟩
    obtain ⟨Q, rfl⟩ := quaternionicIsoWindow B ψ
    exact ⟨Q, hB⟩

theorem paperLineHellySix_controls_iso :
    (∀ T : Finset Albert, (T : Set Albert) ⊆ Set.range paperLineHellySix → T.card ≤ 5 →
      ∃ B : NativeJordanSubalgebra, Nonempty (JordanSubalgebraIso (H3Subalgebra .H) B) ∧
        (T : Set Albert) ⊆ B.carrier) ∧
    ¬ (∃ B : NativeJordanSubalgebra, Nonempty (JordanSubalgebraIso (H3Subalgebra .H) B) ∧
      Set.range paperLineHellySix ⊆ B.carrier) := by
  obtain ⟨_, _, hlocal, hno⟩ := paperLineHellySix_controls
  exact ⟨fun T hTS hTc => (quaternionicContainment_iff_iso T).mp (hlocal T hTS hTc),
    fun h => hno ((quaternionicContainment_iff_iso _).mpr h)⟩

theorem quaternionicHelly_six_iso (S : Set Albert) (hS : ∀ x ∈ S, IsAtom x)
    (hlocal : ∀ T : Finset Albert, (T : Set Albert) ⊆ S → T.card ≤ 6 →
      ∃ B : NativeJordanSubalgebra, Nonempty (JordanSubalgebraIso (H3Subalgebra .H) B) ∧
        (T : Set Albert) ⊆ B.carrier) :
    ∃ B : NativeJordanSubalgebra, Nonempty (JordanSubalgebraIso (H3Subalgebra .H) B) ∧
      S ⊆ B.carrier :=
  (quaternionicContainment_iff_iso S).mp
    (quaternionicHelly_six S hS fun T hTS hTc =>
      (quaternionicContainment_iff_iso T).mpr (hlocal T hTS hTc))

/-- Six-wise containment gives a dimension-six model from every Albert density. -/
theorem quaternionicHelly_projective {n : ℕ} (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i))
    (hlocal : ∀ I : Finset (Fin n), I.card ≤ 6 →
      ∃ Q : QuaternionicWindow, ∀ i ∈ I, p i ∈ Q.subalgebra.carrier)
    (ρ : Albert) (hρ : IsDensity ρ) :
    ∃ (M : AlgebraicProjectiveData (Fin n) (HermitianEmbeddingMatrix 6))
      (σ : HermitianEmbeddingMatrix 6),
      AlgebraicMomentBinding M ∧ IsEmbeddingDensity 6 σ ∧
      (∀ X, M.state X = (Matrix.trace (σ * X)).re) ∧
      (∀ i, IsComplexRankTwoProjection6 (M.projection i)) ∧ M.Matches p ρ := by
  classical
  obtain ⟨Q, hQ⟩ := quaternionicHelly_six (Set.range p)
    (by rintro _ ⟨i, rfl⟩; exact hp i) (by
      intro T hT hTc
      have hchoose : ∀ t : T, ∃ i, p i = t := fun t => hT t.2
      choose idx hidx using hchoose
      let I := T.attach.image idx
      have hc : I.card ≤ 6 := by
        have h := Finset.card_image_le (f := idx) (s := T.attach)
        rw [Finset.card_attach] at h
        exact h.trans hTc
      obtain ⟨Q, hQ⟩ := hlocal I hc
      refine ⟨Q, fun z hz => ?_⟩
      have hi : idx ⟨z, hz⟩ ∈ I := Finset.mem_image_of_mem idx (Finset.mem_attach _ _)
      change z ∈ Q.subalgebra.carrier
      simpa only [hidx ⟨z, hz⟩] using hQ _ hi)
  exact quaternionic_c6_representation Q p hp (fun i => hQ ⟨i, rfl⟩) ρ hρ

private theorem nativeBranchState_zero {ι : Type*} (p : ι → Albert) (w : Word ι) :
    nativeBranchState p 0 w = 0 := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change nativeBranchState p (quadraticMap (nativeOutcome p a) 0) w = 0
    rw [quadraticMap_zero_right, ih]

/-- A word from an atom orthogonal to all the tests survives exactly when every outcome is no. -/
theorem orthogonalAtom_branchState {ι : Type*} (p : ι → Albert) (q : Albert)
    (hp : ∀ i, IsAtom (p i)) (horth : ∀ i, jordanMul q (p i) = 0)
    (w : Word ι) :
    nativeBranchState p q w = if w.any Prod.snd then 0 else q := by
  have hyes (i : ι) : quadraticMap (p i) q = 0 := by
    rw [quadraticMap_atom _ _ (hp i)]
    have hz : tracePairing (p i) q = 0 := by
      rw [tracePairing_comm, tracePairing, horth i]
      exact trace_zero
    rw [hz, zero_smul]
  have hno (i : ι) : quadraticMap (albertUnit - p i) q = q := by
    rw [NativeAnalysis.quadraticMap_complement, jordanMul_comm _ q, horth, hyes,
      smul_zero, sub_zero, add_zero]
  induction w with
  | nil => rfl
  | cons a w ih =>
    rcases a with ⟨i, b⟩
    change nativeBranchState p (quadraticMap (nativeOutcome p (i, b)) q) w =
      if (b || w.any Prod.snd) then 0 else q
    cases b
    · cases hw : w.any Prod.snd <;> simpa [nativeOutcome, hno, hw] using ih
    · simp [nativeOutcome, hyes, nativeBranchState_zero]

/-- The displayed six tests have a model on `ℂ⁶` from `E₃₃`,
although they have no common quaternionic subalgebra. -/
theorem paperLineHellySix_projective_nonconverse :
    (¬ (∃ Q : QuaternionicWindow, Set.range paperLineHellySix ⊆ Q.subalgebra.carrier)) ∧
    (∃ (M : AlgebraicProjectiveData (Fin 6) (HermitianEmbeddingMatrix 6))
      (σ : HermitianEmbeddingMatrix 6),
      AlgebraicMomentBinding M ∧ IsEmbeddingDensity 6 σ ∧
      (∀ X, M.state X = (Matrix.trace (σ * X)).re) ∧
      (∀ i, IsComplexRankTwoProjection6 (M.projection i)) ∧
      M.Matches paperLineHellySix (diagAtom 2)) := by
  obtain ⟨ha, hortho, _, hno⟩ := paperLineHellySix_controls
  refine ⟨hno, ?_⟩
  let p : Fin 6 → Albert := fun _ => diagAtom 0
  have hp : ∀ i, IsAtom (p i) := fun _ => diagAtom_isAtom 0
  have hq : IsAtom (diagAtom 2) := diagAtom_isAtom 2
  have hd : IsDensity (diagAtom 2) := ⟨NativeAnalysis.isPositive_idempotent _ hq.1, hq.2⟩
  have hpQ : ∀ i, p i ∈ standardQuaternionicWindow.subalgebra.carrier := fun _ =>
    (mem_standardQuaternionicWindow_iff _).mpr ⟨rfl, rfl, rfl⟩
  have hp0 : ∀ i, jordanMul (diagAtom 2) (p i) = 0 := fun _ =>
    diagThree_orthogonal_of_coordinates rfl rfl rfl
  obtain ⟨M, σ, hM, hσ, hstate, hrank, hmatch⟩ :=
    quaternionic_c6_representation standardQuaternionicWindow p hp hpQ (diagAtom 2) hd
  refine ⟨M, σ, hM, hσ, hstate, hrank, fun w => (hmatch w).trans ?_⟩
  unfold nativeWordProbability
  rw [orthogonalAtom_branchState p _ hp hp0, orthogonalAtom_branchState _ _ ha hortho]

#print axioms quaternionicHelly_six
#print axioms quaternionicHelly_iff
#print axioms quaternionicHelly_isLeast
#print axioms dyadOnLine_matrix
#print axioms paperLineHellySix_coordinates
#print axioms paperLineHellySix_controls
#print axioms paperLineHellySix_controls_iso
#print axioms paperLineHelly_generated_structure
#print axioms paperLineHellySix_generated_finrank
#print axioms paperLineHellyFive_generated_finrank
#print axioms quaternionicIso_preserves_trace
#print axioms quaternionicContainment_iff_iso
#print axioms quaternionicHelly_six_iso
#print axioms quaternionicHelly_projective
#print axioms orthogonalAtom_branchState
#print axioms paperLineHellySix_projective_nonconverse

end
end AlbertSequential
