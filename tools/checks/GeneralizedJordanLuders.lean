module

import GeneralizedJordanLuders

open AlbertSequential
open scoped BigOperators

section
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  (P : UnitalJordanProduct E) (hfr : P.FormallyReal)

example (a : E) (ha : a ∈ P.squareCone) :
    ∃! r : E, r ∈ P.squareCone ∧ P.product r r = a := by
  obtain ⟨r, hroot, hsq⟩ := P.exists_positiveSquareRoot hfr a ha
  exact ⟨r, ⟨hroot, hsq⟩, fun s hs => P.positiveSquareRoot_unique hfr hs.1 hroot (hs.2.trans hsq.symm)⟩

example {ι : Type*} [Fintype ι] (e : ι → E) (he : ∀ i, e i ∈ P.squareCone)
    (hn : ∑ i, e i = P.unit) (x : E) (hx : x ∈ P.squareCone) :
    let T (i : ι) : E →ₗ[ℝ] E := P.quadraticRepresentation (P.positiveSquareRoot hfr (e i) (he i))
    (∀ i, T i x ∈ P.squareCone) ∧
      (∀ i, CanonicalInstruments.measuredEffect P hfr (T i) = e i) ∧
      P.canonicalTraceOfFormallyReal hfr (∑ i, T i x) = P.canonicalTraceOfFormallyReal hfr x :=
  ⟨fun i => P.generalizedLudersUpdate_positive hfr (e i) (he i) x hx,
    fun i => P.generalizedLudersUpdate_measuredEffect hfr (e i) (he i),
    P.generalizedLudersInstrument_normalized hfr e he hn x⟩

example {ι : Type*} (e : Outcome ι → E) (he : ∀ i, e i ∈ P.squareCone)
    (hn : ∀ i, e (i, true) + e (i, false) = P.unit) :
    ∃ R : ClassicalBinaryRegister ι {x : E // P.IsCanonicalDensity hfr x},
      ∀ s w, R.wordProbability s w = P.canonicalTraceOfFormallyReal hfr
        (w.foldl (fun x b => P.quadraticRepresentation (P.positiveSquareRoot hfr (e b) (he b)) x) s.val) := by
  obtain ⟨R, _, _, h⟩ := P.exists_classical_register_for_generalizedLuders hfr e he hn
  exact ⟨R, h⟩
end

#print axioms UnitalJordanProduct.exists_positiveSquareRoot
#print axioms UnitalJordanProduct.positiveSquareRoot_unique
#print axioms UnitalJordanProduct.positiveSquareRoot_mem
#print axioms UnitalJordanProduct.positiveSquareRoot_square
#print axioms UnitalJordanProduct.generalizedLudersUpdate_of_idempotent
#print axioms UnitalJordanProduct.generalizedLudersUpdate_positive
#print axioms UnitalJordanProduct.generalizedLudersUpdate_trace
#print axioms UnitalJordanProduct.generalizedLudersUpdate_measuredEffect
#print axioms UnitalJordanProduct.generalizedLudersInstrument_normalized
#print axioms UnitalJordanProduct.exists_classical_register_for_generalizedLuders
