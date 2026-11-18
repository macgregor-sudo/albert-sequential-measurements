/- SPDX-License-Identifier: Apache-2.0
   Machine-generated file. -/
module

public import HorizonFive.RecogBase

/-! # lem:cer:h5:lift, per-class lifts (length at most four)

Each theorem `lw_<word>` gives an explicit Jordan expression `K` with `deg K ≤ |w|`, of degree one
in every letter occurring once in `w`, and `σ̂(K) = [w] - ℓ(w) [r_0r_1r_2r_3]`; the special value
is checked by expanding both sides in `ℝ[G]` (`lift_spec`), the degree and letter conditions and
`ℓ(w)` by kernel `decide`. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.HorizonFive

theorem lw_0 : LiftP [0] :=
  liftP_of [0]
    (jX 0)
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_1 : LiftP [1] :=
  liftP_of [1]
    (jX 1)
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_2 : LiftP [2] :=
  liftP_of [2]
    (jX 2)
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_3 : LiftP [3] :=
  liftP_of [3]
    (jX 3)
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_01 : LiftP [0, 1] :=
  liftP_of [0, 1]
    (jM (jX 0) (jX 1))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_02 : LiftP [0, 2] :=
  liftP_of [0, 2]
    (jM (jX 0) (jX 2))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_03 : LiftP [0, 3] :=
  liftP_of [0, 3]
    (jM (jX 0) (jX 3))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_12 : LiftP [1, 2] :=
  liftP_of [1, 2]
    (jM (jX 1) (jX 2))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_13 : LiftP [1, 3] :=
  liftP_of [1, 3]
    (jM (jX 1) (jX 3))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_23 : LiftP [2, 3] :=
  liftP_of [2, 3]
    (jM (jX 2) (jX 3))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_010 : LiftP [0, 1, 0] :=
  liftP_of [0, 1, 0]
    (jU (jX 0) (jX 1))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_012 : LiftP [0, 1, 2] :=
  liftP_of [0, 1, 2]
    (jT (jX 0) (jX 1) (jX 2))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_013 : LiftP [0, 1, 3] :=
  liftP_of [0, 1, 3]
    (jT (jX 0) (jX 1) (jX 3))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_020 : LiftP [0, 2, 0] :=
  liftP_of [0, 2, 0]
    (jU (jX 0) (jX 2))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_021 : LiftP [0, 2, 1] :=
  liftP_of [0, 2, 1]
    (jT (jX 0) (jX 2) (jX 1))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_023 : LiftP [0, 2, 3] :=
  liftP_of [0, 2, 3]
    (jT (jX 0) (jX 2) (jX 3))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_030 : LiftP [0, 3, 0] :=
  liftP_of [0, 3, 0]
    (jU (jX 0) (jX 3))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_031 : LiftP [0, 3, 1] :=
  liftP_of [0, 3, 1]
    (jT (jX 0) (jX 3) (jX 1))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_032 : LiftP [0, 3, 2] :=
  liftP_of [0, 3, 2]
    (jT (jX 0) (jX 3) (jX 2))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_101 : LiftP [1, 0, 1] :=
  liftP_of [1, 0, 1]
    (jU (jX 1) (jX 0))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_102 : LiftP [1, 0, 2] :=
  liftP_of [1, 0, 2]
    (jT (jX 1) (jX 0) (jX 2))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_103 : LiftP [1, 0, 3] :=
  liftP_of [1, 0, 3]
    (jT (jX 1) (jX 0) (jX 3))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_121 : LiftP [1, 2, 1] :=
  liftP_of [1, 2, 1]
    (jU (jX 1) (jX 2))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_123 : LiftP [1, 2, 3] :=
  liftP_of [1, 2, 3]
    (jT (jX 1) (jX 2) (jX 3))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_131 : LiftP [1, 3, 1] :=
  liftP_of [1, 3, 1]
    (jU (jX 1) (jX 3))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_132 : LiftP [1, 3, 2] :=
  liftP_of [1, 3, 2]
    (jT (jX 1) (jX 3) (jX 2))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_202 : LiftP [2, 0, 2] :=
  liftP_of [2, 0, 2]
    (jU (jX 2) (jX 0))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_203 : LiftP [2, 0, 3] :=
  liftP_of [2, 0, 3]
    (jT (jX 2) (jX 0) (jX 3))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_212 : LiftP [2, 1, 2] :=
  liftP_of [2, 1, 2]
    (jU (jX 2) (jX 1))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_213 : LiftP [2, 1, 3] :=
  liftP_of [2, 1, 3]
    (jT (jX 2) (jX 1) (jX 3))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_232 : LiftP [2, 3, 2] :=
  liftP_of [2, 3, 2]
    (jU (jX 2) (jX 3))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_303 : LiftP [3, 0, 3] :=
  liftP_of [3, 0, 3]
    (jU (jX 3) (jX 0))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_313 : LiftP [3, 1, 3] :=
  liftP_of [3, 1, 3]
    (jU (jX 3) (jX 1))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_323 : LiftP [3, 2, 3] :=
  liftP_of [3, 2, 3]
    (jU (jX 3) (jX 2))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_0102 : LiftP [0, 1, 0, 2] :=
  liftP_of [0, 1, 0, 2]
    (jM (jX 2) (jU (jX 0) (jX 1)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_0103 : LiftP [0, 1, 0, 3] :=
  liftP_of [0, 1, 0, 3]
    (jM (jX 3) (jU (jX 0) (jX 1)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_0120 : LiftP [0, 1, 2, 0] :=
  liftP_of [0, 1, 2, 0]
    (jU (jX 0) (jM (jX 1) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_0121 : LiftP [0, 1, 2, 1] :=
  liftP_of [0, 1, 2, 1]
    (jM (jX 0) (jU (jX 1) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_0123 : LiftP [0, 1, 2, 3] :=
  liftP_of [0, 1, 2, 3]
    (.smul 0 (jM (jM (jX 0) (jX 1)) (jM (jX 2) (jX 3))))
    1 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_0130 : LiftP [0, 1, 3, 0] :=
  liftP_of [0, 1, 3, 0]
    (jU (jX 0) (jM (jX 1) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_0131 : LiftP [0, 1, 3, 1] :=
  liftP_of [0, 1, 3, 1]
    (jM (jX 0) (jU (jX 1) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_0132 : LiftP [0, 1, 3, 2] :=
  liftP_of [0, 1, 3, 2]
    (.smul (2 : ℝ) (jT (jX 0) (jX 1) (jM (jX 2) (jX 3))))
    (-1) (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_0201 : LiftP [0, 2, 0, 1] :=
  liftP_of [0, 2, 0, 1]
    (jM (jX 1) (jU (jX 0) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_0203 : LiftP [0, 2, 0, 3] :=
  liftP_of [0, 2, 0, 3]
    (jM (jX 3) (jU (jX 0) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_0212 : LiftP [0, 2, 1, 2] :=
  liftP_of [0, 2, 1, 2]
    (jM (jX 0) (jU (jX 2) (jX 1)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_0213 : LiftP [0, 2, 1, 3] :=
  liftP_of [0, 2, 1, 3]
    (.smul (2 : ℝ) (jT (jX 0) (jM (jX 1) (jX 2)) (jX 3)))
    (-1) (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_0230 : LiftP [0, 2, 3, 0] :=
  liftP_of [0, 2, 3, 0]
    (jU (jX 0) (jM (jX 2) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_0231 : LiftP [0, 2, 3, 1] :=
  liftP_of [0, 2, 3, 1]
    (.add (.smul (2 : ℝ) (jM (jX 0) (jT (jX 1) (jX 3) (jX 2)))) (.smul (-2 : ℝ) (jT (jX 0) (jX 1) (jM (jX 2) (jX 3)))))
    1 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_0232 : LiftP [0, 2, 3, 2] :=
  liftP_of [0, 2, 3, 2]
    (jM (jX 0) (jU (jX 2) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_0301 : LiftP [0, 3, 0, 1] :=
  liftP_of [0, 3, 0, 1]
    (jM (jX 1) (jU (jX 0) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_0302 : LiftP [0, 3, 0, 2] :=
  liftP_of [0, 3, 0, 2]
    (jM (jX 2) (jU (jX 0) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_0312 : LiftP [0, 3, 1, 2] :=
  liftP_of [0, 3, 1, 2]
    (.add (.smul (2 : ℝ) (jM (jX 0) (jT (jX 1) (jX 3) (jX 2)))) (.add (.smul (2 : ℝ) (jM (jX 0) (jT (jX 2) (jX 1) (jX 3)))) (.add (.smul (-2 : ℝ) (jT (jX 0) (jX 1) (jM (jX 2) (jX 3)))) (.smul (-2 : ℝ) (jT (jX 0) (jX 2) (jM (jX 1) (jX 3)))))))
    1 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_0313 : LiftP [0, 3, 1, 3] :=
  liftP_of [0, 3, 1, 3]
    (jM (jX 0) (jU (jX 3) (jX 1)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_0321 : LiftP [0, 3, 2, 1] :=
  liftP_of [0, 3, 2, 1]
    (.smul (2 : ℝ) (jM (jX 0) (jT (jX 1) (jX 2) (jX 3))))
    (-1) (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_0323 : LiftP [0, 3, 2, 3] :=
  liftP_of [0, 3, 2, 3]
    (jM (jX 0) (jU (jX 3) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_1012 : LiftP [1, 0, 1, 2] :=
  liftP_of [1, 0, 1, 2]
    (jM (jX 2) (jU (jX 1) (jX 0)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_1013 : LiftP [1, 0, 1, 3] :=
  liftP_of [1, 0, 1, 3]
    (jM (jX 3) (jU (jX 1) (jX 0)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_1021 : LiftP [1, 0, 2, 1] :=
  liftP_of [1, 0, 2, 1]
    (jU (jX 1) (jM (jX 0) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_1023 : LiftP [1, 0, 2, 3] :=
  liftP_of [1, 0, 2, 3]
    (.smul (2 : ℝ) (jT (jX 3) (jX 2) (jM (jX 0) (jX 1))))
    (-1) (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_1031 : LiftP [1, 0, 3, 1] :=
  liftP_of [1, 0, 3, 1]
    (jU (jX 1) (jM (jX 0) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_1032 : LiftP [1, 0, 3, 2] :=
  liftP_of [1, 0, 3, 2]
    (.add (.smul (-2 : ℝ) (jM (jX 0) (jT (jX 1) (jX 2) (jX 3)))) (.smul (2 : ℝ) (jM (jX 1) (jT (jX 0) (jX 3) (jX 2)))))
    1 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_1202 : LiftP [1, 2, 0, 2] :=
  liftP_of [1, 2, 0, 2]
    (jM (jX 1) (jU (jX 2) (jX 0)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_1203 : LiftP [1, 2, 0, 3] :=
  liftP_of [1, 2, 0, 3]
    (.add (.smul (2 : ℝ) (jM (jX 0) (jT (jX 1) (jX 3) (jX 2)))) (.add (.smul (2 : ℝ) (jM (jX 0) (jT (jX 2) (jX 1) (jX 3)))) (.add (.smul (2 : ℝ) (jM (jX 1) (jT (jX 2) (jX 0) (jX 3)))) (.add (.smul (-2 : ℝ) (jM (jX 2) (jT (jX 0) (jX 3) (jX 1)))) (.add (.smul (-2 : ℝ) (jT (jX 0) (jX 1) (jM (jX 2) (jX 3)))) (.smul (-2 : ℝ) (jT (jX 0) (jX 2) (jM (jX 1) (jX 3)))))))))
    1 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_1213 : LiftP [1, 2, 1, 3] :=
  liftP_of [1, 2, 1, 3]
    (jM (jX 3) (jU (jX 1) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_1231 : LiftP [1, 2, 3, 1] :=
  liftP_of [1, 2, 3, 1]
    (jU (jX 1) (jM (jX 2) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_1232 : LiftP [1, 2, 3, 2] :=
  liftP_of [1, 2, 3, 2]
    (jM (jX 1) (jU (jX 2) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_1302 : LiftP [1, 3, 0, 2] :=
  liftP_of [1, 3, 0, 2]
    (.add (.smul (-2 : ℝ) (jM (jX 0) (jT (jX 1) (jX 3) (jX 2)))) (.add (.smul (-2 : ℝ) (jM (jX 0) (jT (jX 2) (jX 1) (jX 3)))) (.add (.smul (2 : ℝ) (jM (jX 2) (jT (jX 0) (jX 3) (jX 1)))) (.add (.smul (2 : ℝ) (jT (jX 0) (jX 1) (jM (jX 2) (jX 3)))) (.smul (2 : ℝ) (jT (jX 0) (jX 2) (jM (jX 1) (jX 3))))))))
    (-1) (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_1303 : LiftP [1, 3, 0, 3] :=
  liftP_of [1, 3, 0, 3]
    (jM (jX 1) (jU (jX 3) (jX 0)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_1312 : LiftP [1, 3, 1, 2] :=
  liftP_of [1, 3, 1, 2]
    (jM (jX 2) (jU (jX 1) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_1323 : LiftP [1, 3, 2, 3] :=
  liftP_of [1, 3, 2, 3]
    (jM (jX 1) (jU (jX 3) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_2012 : LiftP [2, 0, 1, 2] :=
  liftP_of [2, 0, 1, 2]
    (jU (jX 2) (jM (jX 0) (jX 1)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_2013 : LiftP [2, 0, 1, 3] :=
  liftP_of [2, 0, 1, 3]
    (.add (.smul (2 : ℝ) (jM (jX 2) (jT (jX 0) (jX 1) (jX 3)))) (.smul (-2 : ℝ) (jT (jX 0) (jX 1) (jM (jX 2) (jX 3)))))
    1 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_2023 : LiftP [2, 0, 2, 3] :=
  liftP_of [2, 0, 2, 3]
    (jM (jX 3) (jU (jX 2) (jX 0)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_2032 : LiftP [2, 0, 3, 2] :=
  liftP_of [2, 0, 3, 2]
    (jU (jX 2) (jM (jX 0) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_2103 : LiftP [2, 1, 0, 3] :=
  liftP_of [2, 1, 0, 3]
    (.smul (2 : ℝ) (jM (jX 3) (jT (jX 0) (jX 1) (jX 2))))
    (-1) (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_2123 : LiftP [2, 1, 2, 3] :=
  liftP_of [2, 1, 2, 3]
    (jM (jX 3) (jU (jX 2) (jX 1)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_2132 : LiftP [2, 1, 3, 2] :=
  liftP_of [2, 1, 3, 2]
    (jU (jX 2) (jM (jX 1) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_2303 : LiftP [2, 3, 0, 3] :=
  liftP_of [2, 3, 0, 3]
    (jM (jX 2) (jU (jX 3) (jX 0)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_2313 : LiftP [2, 3, 1, 3] :=
  liftP_of [2, 3, 1, 3]
    (jM (jX 2) (jU (jX 3) (jX 1)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_3013 : LiftP [3, 0, 1, 3] :=
  liftP_of [3, 0, 1, 3]
    (jU (jX 3) (jM (jX 0) (jX 1)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_3023 : LiftP [3, 0, 2, 3] :=
  liftP_of [3, 0, 2, 3]
    (jU (jX 3) (jM (jX 0) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_3123 : LiftP [3, 1, 2, 3] :=
  liftP_of [3, 1, 2, 3]
    (jU (jX 3) (jM (jX 1) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

end AlbertSequential.HorizonFive
