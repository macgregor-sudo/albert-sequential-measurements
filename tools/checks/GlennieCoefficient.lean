module

import AppF.GlennieCoefficient
import BlockA.GlennieGeneral

open AlbertSequential AlbertSequential.AppF

noncomputable section

example : glennieCoefficientExponent =
    Finsupp.single (0 : Fin 3) 2 + Finsupp.single 1 2 + Finsupp.single 2 2 := by
  ext j
  fin_cases j <;> simp [Finsupp.add_apply]

example (f : Albert →ₗ[ℝ] ℝ) (a b c d : Albert) (s t u : ℝ) :
    MvPolynomial.eval ![s,t,u] (nativePsiPolynomial f a b c d) =
      f (nativePsi (s • a + t • b) (s • a + u • c) d) := by
  simpa using eval_nativePsiPolynomial f a b c d ![s,t,u]

example (a b c d : Albert) (f : Albert →ₗ[ℝ] ℝ) (g : MvPolynomial (Fin 3) ℝ)
    (hg : ∀ s t u : ℝ, MvPolynomial.eval ![s,t,u] g =
      f (nativePsi (s • a + t • b) (s • a + u • c) d)) :
    g.coeff glennieCoefficientExponent = f (nativeGlennieF a b c d) := by
  apply coeff_eq_nativeGlennieF_of_eval
  intro values
  have h : ![values 0,values 1,values 2] = values := by
    funext i
    fin_cases i <;> rfl
  simpa only [h] using hg (values 0) (values 1) (values 2)

example (pA pB pC pD F : Albert) (hA : IsAtom pA) (hB : IsAtom pB) (hC : IsAtom pC) (hD : IsAtom pD)
    (hF : ∀ f : Albert →ₗ[ℝ] ℝ,
      (nativePsiPolynomial f (symmetryOf pA) (symmetryOf pB) (symmetryOf pC) (symmetryOf pD)).coeff
        glennieCoefficientExponent = f F) :
    tracePairing F F = 9 * 2 ^ 21 * albertCubicNorm (pA + pB + pC) * fourPointInvariant ![pA,pB,pC,pD] := by
  have h := existsUnique_nativePsiCoefficient (symmetryOf pA) (symmetryOf pB) (symmetryOf pC) (symmetryOf pD)
  have hEq : F = nativeGlennieF (symmetryOf pA) (symmetryOf pB) (symmetryOf pC) (symmetryOf pD) :=
    h.unique hF (fun f => coeff_nativePsiPolynomial f _ _ _ _)
  rw [hEq]
  exact thm_glennie_normSq pA pB pC pD hA hB hC hD

#print axioms glennieCoefficientExponent_apply
#print axioms eval_nativePsiPolynomial
#print axioms nativePsiPolynomial_unique
#print axioms coeff_nativePsiPolynomial
#print axioms coeff_eq_nativeGlennieF_of_eval
#print axioms existsUnique_nativePsiCoefficient
