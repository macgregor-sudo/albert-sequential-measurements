/- SPDX-License-Identifier: Apache-2.0
   Machine-generated file. -/
module

public import LengthSeven.LemmaA.Rules

/-! # Lemma A: the rule instances used, and the rule package `UsedRules`

`usedInsts` lists every pattern rule instance used by the walk lemmas (generated from the
derivations; (R3_0) is the separate field `r3`).  `UsedRules W τ` asks for these instances at
every assignment `(x, y, z)` (an ordering of `B, C, D`) and for (R3_0).

* `usedRules_of_gram28Rules`: the interface rule package `Gram28Rules` implies `UsedRules`
  (side conditions of each instance by `decide`, `usedInsts_ok`).
* `usedRules_of_table`: a table on a word set `S` gives `UsedRules` as soon as the forcing words
  of the used instances lie in `S` (for (R2) either sandwiched letter) and (P3) holds for the
  orderings `BCD`, `CDB`, `DCB`; this is the finite-route form `lemmaA_on`. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.LengthSeven.LemmaA

open AlbertSequential AlbertSequential.LengthSeven

/-- The pattern rule instances used by the walk lemmas (42 instances). -/
def usedInsts : List PatInst :=
  [.chain [.X],
  .delete [] .X .Y [],
  .chain [.X, .Y],
  .delete [.X] .Y .Z [],
  .chain [.X, .Y, .A],
  .chain [.X, .Y, .A, .Z],
  .delete [] .Z .X [.Y, .A],
  .delete [.X] .Z .Y [.A],
  .delete [.X, .Y] .A .Z [],
  .delete [] .Z .X [.Y, .A, .Z],
  .delete [.X] .Z .Y [.A, .Z],
  .delete [.X, .Y] .A .Z [.A],
  .r1 [] .A .X,
  .r1 [] .X .Y,
  .r2 [] .A .Y .X,
  .r2 [] .X .Y .A,
  .r2 [] .A .X .Z,
  .r2 [.Y] .X .Z .Y,
  .r1 [.Y, .X] .Z .A,
  .r1 [.Z] .Y .A,
  .r1 [] .Z .X,
  .r1 [] .Z .Y,
  .r1 [.X, .Y] .A .X,
  .r1 [.X] .Y .A,
  .r1 [.X, .Y] .A .Z,
  .r1 [.Y] .Z .X,
  .r1 [.X] .Z .Y,
  .r1 [.Y, .X] .Z .Y,
  .r2 [] .X .A .Y,
  .r2 [.X] .Y .Z .A,
  .r2 [] .Z .Y .X,
  .r2 [.Y] .Z .X .A,
  .delete [.X, .Y] .A .Z [.X],
  .r2 [] .X .Z .Y,
  .r1 [.X] .Y .Z,
  .r1 [.Z] .X .Y,
  .r1 [.Y] .X .Z,
  .r1 [.X, .Y] .Z .A,
  .r1 [.X, .Y] .Z .X,
  .r1 [.Y, .Z] .X .Y,
  .r2 [] .X .Y .Z,
  .r2 [.X] .Y .A .Z]

/-- The rule package consumed by the walk lemmas. -/
structure UsedRules {V : Type*} [AddCommGroup V] [Module ℝ V] (W : WalkForm V) (τ : TraceData) :
    Prop where
  inst : ∀ x y z : Letter, IsOrderingBCD x y z → ∀ π ∈ usedInsts, (π.toRule x y z).Holds W τ
  r3 : ∀ x y z : Letter, IsOrderingBCD x y z → W.R3Holds τ x y z

theorem usedInsts_ok : ∀ π ∈ usedInsts, π.ok = true := by decide

section
variable {V : Type*} [AddCommGroup V] [Module ℝ V] {W : WalkForm V} {τ : TraceData}

theorem PatInst.holds_of_ok (h : Gram28Rules W τ) {x y z : Letter} (hxyz : IsOrderingBCD x y z) :
    ∀ π : PatInst, π.ok = true → (π.toRule x y z).Holds W τ
  | .r1 t q v, hok => h.r1 _ _ _ (by simpa [PatInst.ok, yesWord] using hok)
  | .r2 [] q s m, _ => h.r2zero _ _ _
  | .r2 [c] q s m, hok => by
      simp only [PatInst.ok, Bool.and_eq_true, bne_iff_ne, ne_eq] at hok
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hok
      exact h.r2one _ _ _ _ (PL.ev_ne hxyz _ _ h1) (PL.ev_ne hxyz _ _ h2) (PL.ev_ne hxyz _ _ h3)
        (PL.ev_ne hxyz _ _ h4)
  | .r2 (_ :: _ :: _) _ _ _, hok => by simp [PatInst.ok] at hok
  | .delete u a n r, hok => h.delete _ _ _ _ (by simpa [PatInst.ok] using hok)
  | .chain u, hok => h.chain _ (by simpa [PatInst.ok] using hok)

/-- The interface rule package implies the one consumed by the walk lemmas. -/
theorem usedRules_of_gram28Rules (h : Gram28Rules W τ) : UsedRules W τ where
  inst x y z hxyz π hπ := PatInst.holds_of_ok h hxyz π (usedInsts_ok π hπ)
  r3 := h.r3

theorem PatInst.holds_of_covered {S : Set (Word Letter)} {f : Word Letter → ℝ}
    (hrep : W.Reproduces S f) (hT : TableValues τ f) {x y z : Letter} :
    ∀ π : PatInst, π.Covered S x y z → (π.toRule x y z).Holds W τ
  | .r1 _ _ _, hc => RuleInstance.holds_of_table hrep hT _ trivial hc
  | .r2 _ _ _ _, hc => hc.elim (fun hc => WalkForm.r2_of_table hrep hT _ _ _ _ hc)
      (fun hc => (WalkForm.r2_of_table hrep hT _ _ _ _ hc).comm)
  | .delete _ _ _ _, hc => RuleInstance.holds_of_table hrep hT _ trivial hc
  | .chain _, hc => RuleInstance.holds_of_table hrep hT _ trivial hc

/-- Finite-route form: the table on `S`, coverage of the used forcing words and (P3) for the
orderings `BCD`, `CDB`, `DCB` give the rule package. -/
theorem usedRules_of_table {S : Set (Word Letter)} {f : Word Letter → ℝ}
    (hrep : W.Reproduces S f) (hT : TableValues τ f)
    (hcov : ∀ x y z : Letter, IsOrderingBCD x y z → ∀ π ∈ usedInsts, π.Covered S x y z)
    (hB : Covers S (p3Words 1 2 3)) (hC : Covers S (p3Words 2 3 1)) (hD : Covers S (p3Words 3 2 1)) :
    UsedRules W τ where
  inst x y z hxyz π hπ := PatInst.holds_of_covered hrep hT π (hcov x y z hxyz π hπ)
  r3 := WalkForm.r3_of_table hrep hT 2 3 3 1 2 1 (by decide) (by decide) (by decide) hB hC hD

end

end AlbertSequential.LengthSeven.LemmaA
