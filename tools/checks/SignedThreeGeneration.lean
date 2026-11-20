module

import CompanionSignedInvariantGeneration

open AlbertSequential AlbertSequential.NativeAnalysis

example {A : Type*} [Ring A] [Algebra ℝ A] (τ : A →ₗ[ℝ] ℝ)
    (hτ : ∀ a b, τ (a * b) = τ (b * a)) (X Y Z : A) :
    τ ((X * (Y * Z * Y) * X - Y * (X * Z * X) * Y) *
      (Z * ((1 / 2 : ℝ) • (X * Y + Y * X)) * Z)) = 0 :=
  cyclicTrace_signedThree_zero τ hτ X Y Z

example (Q : QuaternionicWindow) (x y z : Q.subalgebra.carrier) :
    signedThreeInvariant x.1 y.1 z.1 = 0 :=
  signedThreeInvariant_zero_of_scaledEmbedding (symplecticQuatEmbed Q) 2 (by norm_num)
    (symplecticQuatEmbed_tracePairing Q) x y z

example (q : Albert) (hq : IsAtom q) (x y z : (lineSubalgebra q hq).carrier) :
    signedThreeInvariant x.1 y.1 z.1 = 0 :=
  signedThreeInvariant_zero_of_scaledEmbedding (lineCliffordEmbed q hq) 8 (by norm_num)
    (lineCliffordEmbed_tracePairing q hq) x y z

example (B : NativeJordanSubalgebra) (hp : B ≠ ⊤) (x y z : B.carrier) :
    signedThreeInvariant x.1 y.1 z.1 = 0 :=
  signedThreeInvariant_zero_of_proper_subalgebra B hp x y z

example (x y z : Albert)
    (h : tracePairing (quadraticMap x (quadraticMap y z) - quadraticMap y (quadraticMap x z))
      (quadraticMap z (jordanMul x y)) ≠ 0) : GeneratesAlbert ![x, y, z] :=
  signedThreeInvariant_generates_of_ne_zero x y z h

#print axioms cyclicTrace_signedThree_zero
#print axioms signedThreeInvariant_zero_of_scaledEmbedding
#print axioms signedThreeInvariant_zero_of_proper_subalgebra
#print axioms signedThreeInvariant_generates_of_ne_zero
