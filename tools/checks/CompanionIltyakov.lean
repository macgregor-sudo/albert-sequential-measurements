module

import CompanionIltyakovAction

open AlbertSequential AlbertSequential.CompanionIltyakov
open MvPolynomial
open scoped Matrix

noncomputable section

example : Fintype.card GeneratorIndex = 29 := generatorIndex_card

example (x y z : Albert) :
    MvPolynomial.eval (coordinates ![x,y,z]) (tracePolynomial omegaMonomial) =
      let a := jordanMul (jordanMul z x) y
      let b := jordanMul (jordanMul z y) x
      albertTrace (jordanMul (jordanMul a a) b) :=
  eval_tracePolynomial omegaMonomial ![x,y,z]

example (x y z : ComplexCoordinates) :
    MvPolynomial.eval (fun i : Fin 3 × Fin 27 => (![x,y,z] : Fin 3 → ComplexCoordinates) i.1 i.2)
      (complexTracePolynomial omegaMonomial) =
      let a := complexJordanProduct (complexJordanProduct z x) y
      let b := complexJordanProduct (complexJordanProduct z y) x
      complexJordanTrace (complexJordanProduct (complexJordanProduct a a) b) :=
  eval_complexTracePolynomial omegaMonomial ![x,y,z]

example : Algebra.adjoin ℝ
    (Set.range (fun i : GeneratorIndex => tracePolynomial (traceGenerator i)) ∪ {tracePolynomial omegaMonomial}) ≤
      nativeInvariantSubalgebra := adjoin_nativeIltyakovTraces_le

example : (tracePolynomial omegaMonomial).totalDegree = 9 := omegaPolynomial_totalDegree

#print axioms generatorIndex_card
#print axioms eval_tracePolynomial
#print axioms tracePolynomial_homogeneous
#print axioms adjoin_nativeIltyakovTraces_le
#print axioms omegaPolynomial_totalDegree
#print axioms omega_multiscale
#print axioms extendRealCoordinates_product
#print axioms complexJordanTrace_extendRealCoordinates
#print axioms eval_complexTracePolynomial
#print axioms complexTracePolynomial_invariant

example (g : ComplexCoordinates ≃ₗ[ℂ] ComplexCoordinates)
    (hg : ∀ a b, g (complexJordanProduct a b) = complexJordanProduct (g a) (g b))
    (x : ComplexCoordinates) : complexJordanTrace (g x) = complexJordanTrace x :=
  complexTrace_preserved_of_product g hg x

example : Algebra.adjoin ℂ
    (Set.range (fun i : GeneratorIndex => complexTracePolynomial (traceGenerator i)) ∪
      {complexTracePolynomial omegaMonomial}) ≤ complexInvariantSubalgebra :=
  adjoin_complexIltyakovTraces_le

example : (complexTracePolynomial omegaMonomial).totalDegree = 9 := omegaComplexPolynomial_totalDegree

#print axioms omegaComplexPolynomial_totalDegree
#print axioms native_leftTrace_eq_nine
#print axioms complex_leftTrace_eq_nine
#print axioms complexTrace_preserved_of_product
#print axioms complexTracePolynomial_fixed
#print axioms adjoin_complexIltyakovTraces_le

example (x : Fin 3 → Albert) :
    (traceGenerator (.inl (2, 2))).eval x = jordanMul (x 2) (jordanMul (x 2) (x 2)) := rfl

example (x : Fin 3 → Albert) :
    (traceGenerator (.inr (.inl (2, 1, 0)))).eval x = jordanMul (jordanMul (x 2) (x 2)) (x 0) := rfl

example (x : Fin 3 → Albert) :
    (traceGenerator (.inr (.inr (1, 0, 1)))).eval x =
      jordanMul (jordanMul (jordanMul (x 0) (x 0)) (x 1)) (jordanMul (x 2) (x 2)) := rfl

example (g : ComplexCoordinates ≃ₗ[ℂ] ComplexCoordinates)
    (hg : ∀ u v, g (complexJordanProduct u v) = complexJordanProduct (g u) (g v))
    (x : Fin 3 → ComplexCoordinates) :
    MvPolynomial.eval (fun i => g (x i.1) i.2) (complexTracePolynomial omegaMonomial) =
      let a := complexJordanProduct (complexJordanProduct (x 2) (x 0)) (x 1)
      let b := complexJordanProduct (complexJordanProduct (x 2) (x 1)) (x 0)
      complexJordanTrace (complexJordanProduct (complexJordanProduct a a) b) := by
  rw [complexTracePolynomial_fixed _ g hg]
  exact eval_complexTracePolynomial omegaMonomial x

example (P : MvPolynomial (Fin 3 × Fin 27) ℂ)
    (hP : P ∈ Algebra.adjoin ℂ (Set.range (fun i : GeneratorIndex => complexTracePolynomial (traceGenerator i)) ∪
      {complexTracePolynomial omegaMonomial}))
    (g : ComplexCoordinates ≃ₗ[ℂ] ComplexCoordinates)
    (hg : ∀ u v, g (complexJordanProduct u v) = complexJordanProduct (g u) (g v))
    (x : Fin 3 → ComplexCoordinates) :
    MvPolynomial.eval (fun i => g (x i.1) i.2) P = MvPolynomial.eval (fun i => x i.1 i.2) P :=
  (show P ∈ complexInvariantSubalgebra from adjoin_complexIltyakovTraces_le hP) g hg x

#print axioms tracePolynomial_mem_nativeInvariantSubalgebra
#print axioms complexTracePolynomial_mem
