/- SPDX-License-Identifier: Apache-2.0 -/
module
public import AppF.SecondOrderCoefficientIdeal
public import NativeMatrixTrace

/-! Real dimension of the coefficient ideal and the conjugate-transpose target of reduction. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.AppF

private def idealCoordinates : secondOrderCoefficientIdeal ≃ₗ[ℝ] ℝ × ℝ × Quaternion ℝ where
  toFun x := (x.val.2.2.1.imJ,x.val.2.2.1.imK,x.val.2.2.2)
  invFun z := ⟨(0,0,(⟨0,0,z.1,z.2.1⟩,z.2.2)), (mem_secondOrderCoefficientIdeal _).mpr ⟨rfl,rfl,rfl,rfl⟩⟩
  left_inv x := by
    obtain ⟨h0,h1,hre,him⟩ := (mem_secondOrderCoefficientIdeal _).mp x.property
    exact Subtype.ext (Prod.ext h0.symm (Prod.ext h1.symm
      (Prod.ext (Quaternion.ext _ _ hre.symm him.symm rfl rfl) rfl)))
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem secondOrderCoefficientIdeal_finrank : Module.finrank ℝ secondOrderCoefficientIdeal = 6 := by
  rw [idealCoordinates.finrank_eq]
  norm_num [Module.finrank_prod, Quaternion.finrank_eq_four]

private theorem oC_conj (x : Octonion) : oC (octonionConj x) = star (oC x) := by apply Complex.ext <;> simp [oC,octonionConj]
private theorem cO_conj (x : ℂ) : octonionConj (cO x) = cO (star x) := by
  apply Prod.ext
  · apply Quaternion.ext <;> simp [cO,octonionConj]
  · simp [cO,octonionConj]

instance : Star Dq := ⟨fun x => ⟨star x.c0,octonionConj x.o1,star x.c2⟩⟩

instance : StarRing Dq where
  star_involutive x := Dq.ext (star_star _) (octonionConj_conj _) (star_star _)
  star_add x y := Dq.ext (star_add _ _) (octonionConj_add _ _) (star_add _ _)
  star_mul x y := by
    refine Dq.ext (star_mul _ _) ?_ ?_
    · change octonionConj (_ + _) = octonionMul (cO (star y.c0)) (octonionConj x.o1) +
        octonionMul (octonionConj y.o1) (cO (star x.c0))
      simp only [octonionConj_add,octonionConj_mul,cO_conj,add_comm]
    · change star (x.c0*y.c2 + x.c2*y.c0 + _) = star y.c0 * star x.c2 + star y.c2 * star x.c0 + _
      simp only [star_add,star_mul, ← oC_conj,octonionConj_mul]
      abel

theorem redq_isHermitian (x : J3) : (redq x).IsHermitian := by
  apply Matrix.ext
  intro i j
  change star (redq x j i) = redq x i j
  exact Dq.ext (by change star (oC _) = _; rw [← oC_conj,NativeAnalysis.albertMatrix_conjugate]; rfl)
    (NativeAnalysis.albertMatrix_conjugate _ _ _) (by change star (oC _) = _; rw [← oC_conj,NativeAnalysis.albertMatrix_conjugate]; rfl)

end AlbertSequential.AppF
