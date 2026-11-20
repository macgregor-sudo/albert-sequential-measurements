module

import NativeHalfBoost
import NativePrintedSpinorCoordinates

open AlbertSequential AlbertSequential.NativeAnalysis Matrix
open scoped Matrix

example (p q : Albert) (hp : IsAtom p) (hq : IsAtom q)
    (ho : 0 < tracePairing p q) (x y : nativePeirceZero p) :
    Function.Bijective (nativeCornerNoUpdate p q hq) ∧
    nativeCornerLorentzForm (nativeCornerNoUpdate p q hq x) (nativeCornerNoUpdate p q hq y) =
      tracePairing p q * nativeCornerLorentzForm (x : Albert) y :=
  ⟨nativeCornerNoUpdate_bijective_of_overlap p q hp hq ho,
   nativeCornerLorentzForm_no_similitude p q hp hq x y⟩

example (p q : Albert) (hp : IsAtom p) (hq : IsAtom q) (ho : 0 < tracePairing p q) :
    let A := nativePositiveOverlapKraus p hp q hq
    let c := nativeCornerBoostRoot p q hq
    let G := nativeCornerNoUpdate p q hq
    let k := nativeCornerBoostRest p q hq
    IsPositive (c : Albert) ∧ nativeCornerProduct q hq.1 c c = G (nativeCornerUnit p hp.1) ∧
    ∃ S : NativeSpinorMatrix, S.transpose * S = 1 ∧ S * S.transpose = 1 ∧
      A = nativeHalfMatrix q hq c * S ∧
      (∀ x, S * nativeHalfMatrix p hp x * S.transpose = nativeHalfMatrix q hq (k x)) ∧
      (∀ x, nativeCornerQuadraticMapLinear q hq c (k x) = G x) := by
  intro A c G k
  exact ⟨nativeCornerBoostRoot_positive p q hp hq, nativeHalfBoostRoot_square p q hp hq ho,
    nativePositiveOverlapKraus_boost_rest p q hp hq ho⟩

#print axioms albertSharp_nativeCorner
#print axioms albertSharp_atomComplementQuadratic
#print axioms nativeCornerLorentz_eq_Minkowski
#print axioms nativeCornerLorentz_no_similitude
#print axioms nativeCornerLorentzForm_no_similitude
#print axioms nativeCornerNoUpdate_bijective_of_overlap
#print axioms spinorOctonionConjugation_orthogonal
#print axioms nativeHalfMatrix_printedClifford_action
#print axioms printedSpinor_octonionLeft_adjoint
#print axioms nativeCornerBoostRoot_positive
#print axioms nativeHalfBoostRoot_square
#print axioms nativePositiveOverlapKraus_boost_factorization
#print axioms nativePositiveOverlapKraus_boost_rest
#print axioms nativeCornerBoostRest_unital_jordan

#print axioms nativeCornerBoostRest_trace_lorentz
