/- SPDX-License-Identifier: Apache-2.0 -/
module

public import LengthSeven.WalkReduction

/-! A reduction guide selects branches of the already proved symbolic rules.
The checker computes in a single direction, and rejects an invalid rule index. -/

set_option autoImplicit false
@[expose] public section

namespace AlbertSequential.LengthSeven

/-- Preorder rule indices for a candidate derivation. Unused trailing indices
are returned along with the checked polynomial. -/
def guidedWalk : ℕ → List Letter → List ℕ → Option (WalkPolynomial × List ℕ)
  | 0, _, _ => none
  | _ + 1, _, [] => none
  | n + 1, w, i :: r => do
      let c ← (walkCandidates w)[i]?
      match c.step with
      | .value p => return (p, r)
      | .scaled p u =>
        let (q, tail) ← guidedWalk n u r
        return (.mul p q, tail)
      | .exchanged p u v =>
        let (q, tail) ← guidedWalk n u r
        let (s, rest) ← guidedWalk n v tail
        return (.sub (.mul (.mul (.integer 2) p) q) s, rest)

theorem guidedWalk_sound (τ : TraceData) (L : List Letter → ℝ) (h : AlgebraicWalkRules τ L)
    (n : ℕ) (w : List Letter) (r : List ℕ) {p : WalkPolynomial} {rest : List ℕ}
    (hp : guidedWalk n w r = some (p, rest)) : L w = p.eval (walkTraceCoordinates τ) := by
  induction n generalizing w r p rest with
  | zero => simp [guidedWalk] at hp
  | succ n ih =>
    cases r with
    | nil => simp [guidedWalk] at hp
    | cons i r =>
      cases hc : (walkCandidates w)[i]? with
      | none => simp [guidedWalk, hc] at hp
      | some c =>
        have hs := c.sound τ L h
        cases hstep : c.step with
        | value q =>
          simp [guidedWalk, hc, hstep] at hp
          rcases hp with ⟨rfl, _⟩
          simpa only [hstep, WalkReductionStep.eval] using hs
        | scaled q u =>
          cases hu : guidedWalk n u r with
          | none => simp [guidedWalk, hc, hstep, hu] at hp
          | some qr =>
            obtain ⟨q', tail⟩ := qr
            simp [guidedWalk, hc, hstep, hu] at hp
            rcases hp with ⟨rfl, _⟩
            simpa [hstep, WalkReductionStep.eval, WalkPolynomial.eval, ih u r hu] using hs
        | exchanged q u v =>
          cases hu : guidedWalk n u r with
          | none => simp [guidedWalk, hc, hstep, hu] at hp
          | some qr =>
            obtain ⟨q', tail⟩ := qr
            cases hv : guidedWalk n v tail with
            | none => simp [guidedWalk, hc, hstep, hu, hv] at hp
            | some sr =>
              obtain ⟨s, rest'⟩ := sr
              simp [guidedWalk, hc, hstep, hu, hv] at hp
              rcases hp with ⟨rfl, _⟩
              simpa [hstep, WalkReductionStep.eval, WalkPolynomial.eval, ih u r hu, ih v tail hv] using hs

/-- Numeric key for the finite certificate table. Soundness of a guide is
checked on the actual input, independent of how guides are retrieved. -/
def encodeWalk (w : List Letter) : ℕ := w.foldr (fun i z => 1 + i.val + 5 * z) 0

end AlbertSequential.LengthSeven
