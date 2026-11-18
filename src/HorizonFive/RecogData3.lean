/- SPDX-License-Identifier: Apache-2.0
   Machine-generated file. -/
module

public import HorizonFive.RecogBase

/-! # lem:cer:h5:lift, per-class lifts (length five, second half)

Each theorem `lw_<word>` gives an explicit Jordan expression `K` with `deg K ≤ |w|`, of degree one
in every letter occurring once in `w`, and `σ̂(K) = [w] - ℓ(w) [r_0r_1r_2r_3]`; the special value
is checked by expanding both sides in `ℝ[G]` (`lift_spec`), the degree and letter conditions and
`ℓ(w)` by kernel `decide`. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.HorizonFive

theorem lw_10232 : LiftP [1, 0, 2, 3, 2] :=
  liftP_of [1, 0, 2, 3, 2]
    (jT (jX 1) (jX 0) (jU (jX 2) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_10301 : LiftP [1, 0, 3, 0, 1] :=
  liftP_of [1, 0, 3, 0, 1]
    (jU (jX 1) (jU (jX 0) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_10302 : LiftP [1, 0, 3, 0, 2] :=
  liftP_of [1, 0, 3, 0, 2]
    (jT (jX 1) (jU (jX 0) (jX 3)) (jX 2))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_10303 : LiftP [1, 0, 3, 0, 3] :=
  liftP_of [1, 0, 3, 0, 3]
    (jT (jX 1) (jX 0) (jU (jX 3) (jX 0)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_10312 : LiftP [1, 0, 3, 1, 2] :=
  liftP_of [1, 0, 3, 1, 2]
    (.add (.smul (-1 : ℝ) (jT (jX 2) (jX 0) (jX 3))) (.smul (2 : ℝ) (jT (jX 2) (jX 1) (jT (jX 1) (jX 0) (jX 3)))))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_10313 : LiftP [1, 0, 3, 1, 3] :=
  liftP_of [1, 0, 3, 1, 3]
    (jT (jX 1) (jX 0) (jU (jX 3) (jX 1)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_10321 : LiftP [1, 0, 3, 2, 1] :=
  liftP_of [1, 0, 3, 2, 1]
    (jU (jX 1) (jT (jX 0) (jX 3) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_10323 : LiftP [1, 0, 3, 2, 3] :=
  liftP_of [1, 0, 3, 2, 3]
    (jT (jX 1) (jX 0) (jU (jX 3) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_12012 : LiftP [1, 2, 0, 1, 2] :=
  liftP_of [1, 2, 0, 1, 2]
    (.add (.smul (-1/2 : ℝ) (jU (jX 1) (jU (jX 2) (jX 0)))) (.add (.smul (-1/2 : ℝ) (jU (jX 2) (jU (jX 1) (jX 0)))) (.smul (2 : ℝ) (jU (jM (jX 1) (jX 2)) (jX 0)))))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_12013 : LiftP [1, 2, 0, 1, 3] :=
  liftP_of [1, 2, 0, 1, 3]
    (.add (jT (jX 0) (jX 2) (jX 3)) (.add (.smul (-2 : ℝ) (jT (jX 0) (jX 1) (jT (jX 1) (jX 2) (jX 3)))) (.smul (2 : ℝ) (jT (jX 1) (jX 2) (jT (jX 0) (jX 1) (jX 3))))))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_12021 : LiftP [1, 2, 0, 2, 1] :=
  liftP_of [1, 2, 0, 2, 1]
    (jU (jX 1) (jU (jX 2) (jX 0)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_12023 : LiftP [1, 2, 0, 2, 3] :=
  liftP_of [1, 2, 0, 2, 3]
    (jT (jX 1) (jU (jX 2) (jX 0)) (jX 3))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_12031 : LiftP [1, 2, 0, 3, 1] :=
  liftP_of [1, 2, 0, 3, 1]
    (jU (jX 1) (jT (jX 2) (jX 0) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_12032 : LiftP [1, 2, 0, 3, 2] :=
  liftP_of [1, 2, 0, 3, 2]
    (.add (.smul (-1 : ℝ) (jT (jX 0) (jX 3) (jX 1))) (.smul (2 : ℝ) (jT (jX 1) (jX 2) (jT (jX 0) (jX 3) (jX 2)))))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_12102 : LiftP [1, 2, 1, 0, 2] :=
  liftP_of [1, 2, 1, 0, 2]
    (jT (jX 2) (jX 0) (jU (jX 1) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_12103 : LiftP [1, 2, 1, 0, 3] :=
  liftP_of [1, 2, 1, 0, 3]
    (jT (jX 3) (jX 0) (jU (jX 1) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_12123 : LiftP [1, 2, 1, 2, 3] :=
  liftP_of [1, 2, 1, 2, 3]
    (jT (jX 3) (jX 2) (jU (jX 1) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_12131 : LiftP [1, 2, 1, 3, 1] :=
  liftP_of [1, 2, 1, 3, 1]
    (jU (jX 1) (jT (jX 2) (jX 1) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_12132 : LiftP [1, 2, 1, 3, 2] :=
  liftP_of [1, 2, 1, 3, 2]
    (jT (jX 2) (jX 3) (jU (jX 1) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_12302 : LiftP [1, 2, 3, 0, 2] :=
  liftP_of [1, 2, 3, 0, 2]
    (.add (.smul (-1 : ℝ) (jT (jX 1) (jX 0) (jX 3))) (.smul (2 : ℝ) (jT (jX 1) (jX 2) (jT (jX 2) (jX 0) (jX 3)))))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_12303 : LiftP [1, 2, 3, 0, 3] :=
  liftP_of [1, 2, 3, 0, 3]
    (jT (jX 1) (jX 2) (jU (jX 3) (jX 0)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_12312 : LiftP [1, 2, 3, 1, 2] :=
  liftP_of [1, 2, 3, 1, 2]
    (.add (.smul (-1/2 : ℝ) (jU (jX 1) (jU (jX 2) (jX 3)))) (.add (.smul (-1/2 : ℝ) (jU (jX 2) (jU (jX 1) (jX 3)))) (.smul (2 : ℝ) (jU (jM (jX 1) (jX 2)) (jX 3)))))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_12313 : LiftP [1, 2, 3, 1, 3] :=
  liftP_of [1, 2, 3, 1, 3]
    (jT (jX 1) (jX 2) (jU (jX 3) (jX 1)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_12321 : LiftP [1, 2, 3, 2, 1] :=
  liftP_of [1, 2, 3, 2, 1]
    (jU (jX 1) (jU (jX 2) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_12323 : LiftP [1, 2, 3, 2, 3] :=
  liftP_of [1, 2, 3, 2, 3]
    (jT (jX 1) (jX 2) (jU (jX 3) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_13012 : LiftP [1, 3, 0, 1, 2] :=
  liftP_of [1, 3, 0, 1, 2]
    (.add (jT (jX 0) (jX 3) (jX 2)) (.add (.smul (-2 : ℝ) (jT (jX 0) (jX 1) (jT (jX 1) (jX 3) (jX 2)))) (.smul (2 : ℝ) (jT (jX 1) (jX 3) (jT (jX 0) (jX 1) (jX 2))))))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_13013 : LiftP [1, 3, 0, 1, 3] :=
  liftP_of [1, 3, 0, 1, 3]
    (.add (.smul (-1/2 : ℝ) (jU (jX 1) (jU (jX 3) (jX 0)))) (.add (.smul (-1/2 : ℝ) (jU (jX 3) (jU (jX 1) (jX 0)))) (.smul (2 : ℝ) (jU (jM (jX 1) (jX 3)) (jX 0)))))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_13023 : LiftP [1, 3, 0, 2, 3] :=
  liftP_of [1, 3, 0, 2, 3]
    (.add (.smul (-1 : ℝ) (jT (jX 0) (jX 2) (jX 1))) (.smul (2 : ℝ) (jT (jX 1) (jX 3) (jT (jX 0) (jX 2) (jX 3)))))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_13031 : LiftP [1, 3, 0, 3, 1] :=
  liftP_of [1, 3, 0, 3, 1]
    (jU (jX 1) (jU (jX 3) (jX 0)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_13032 : LiftP [1, 3, 0, 3, 2] :=
  liftP_of [1, 3, 0, 3, 2]
    (jT (jX 1) (jU (jX 3) (jX 0)) (jX 2))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_13102 : LiftP [1, 3, 1, 0, 2] :=
  liftP_of [1, 3, 1, 0, 2]
    (jT (jX 2) (jX 0) (jU (jX 1) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_13103 : LiftP [1, 3, 1, 0, 3] :=
  liftP_of [1, 3, 1, 0, 3]
    (jT (jX 3) (jX 0) (jU (jX 1) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_13123 : LiftP [1, 3, 1, 2, 3] :=
  liftP_of [1, 3, 1, 2, 3]
    (jT (jX 3) (jX 2) (jU (jX 1) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_13132 : LiftP [1, 3, 1, 3, 2] :=
  liftP_of [1, 3, 1, 3, 2]
    (jT (jX 2) (jX 3) (jU (jX 1) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_13202 : LiftP [1, 3, 2, 0, 2] :=
  liftP_of [1, 3, 2, 0, 2]
    (jT (jX 1) (jX 3) (jU (jX 2) (jX 0)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_13203 : LiftP [1, 3, 2, 0, 3] :=
  liftP_of [1, 3, 2, 0, 3]
    (.add (.smul (-1 : ℝ) (jT (jX 1) (jX 0) (jX 2))) (.smul (2 : ℝ) (jT (jX 1) (jX 3) (jT (jX 2) (jX 0) (jX 3)))))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_13212 : LiftP [1, 3, 2, 1, 2] :=
  liftP_of [1, 3, 2, 1, 2]
    (jT (jX 1) (jX 3) (jU (jX 2) (jX 1)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_13213 : LiftP [1, 3, 2, 1, 3] :=
  liftP_of [1, 3, 2, 1, 3]
    (.add (.smul (-1/2 : ℝ) (jU (jX 1) (jU (jX 3) (jX 2)))) (.add (.smul (-1/2 : ℝ) (jU (jX 3) (jU (jX 1) (jX 2)))) (.smul (2 : ℝ) (jU (jM (jX 1) (jX 3)) (jX 2)))))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_13231 : LiftP [1, 3, 2, 3, 1] :=
  liftP_of [1, 3, 2, 3, 1]
    (jU (jX 1) (jU (jX 3) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_13232 : LiftP [1, 3, 2, 3, 2] :=
  liftP_of [1, 3, 2, 3, 2]
    (jT (jX 1) (jX 3) (jU (jX 2) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_20102 : LiftP [2, 0, 1, 0, 2] :=
  liftP_of [2, 0, 1, 0, 2]
    (jU (jX 2) (jU (jX 0) (jX 1)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_20103 : LiftP [2, 0, 1, 0, 3] :=
  liftP_of [2, 0, 1, 0, 3]
    (jT (jX 2) (jU (jX 0) (jX 1)) (jX 3))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_20123 : LiftP [2, 0, 1, 2, 3] :=
  liftP_of [2, 0, 1, 2, 3]
    (.add (jT (jX 1) (jX 0) (jX 3)) (.add (.smul (-2 : ℝ) (jT (jX 1) (jX 2) (jT (jX 2) (jX 0) (jX 3)))) (.smul (2 : ℝ) (jT (jX 2) (jX 0) (jT (jX 1) (jX 2) (jX 3))))))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_20132 : LiftP [2, 0, 1, 3, 2] :=
  liftP_of [2, 0, 1, 3, 2]
    (jU (jX 2) (jT (jX 0) (jX 1) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_20203 : LiftP [2, 0, 2, 0, 3] :=
  liftP_of [2, 0, 2, 0, 3]
    (jT (jX 3) (jX 0) (jU (jX 2) (jX 0)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_20212 : LiftP [2, 0, 2, 1, 2] :=
  liftP_of [2, 0, 2, 1, 2]
    (jU (jX 2) (jT (jX 0) (jX 2) (jX 1)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_20213 : LiftP [2, 0, 2, 1, 3] :=
  liftP_of [2, 0, 2, 1, 3]
    (jT (jX 3) (jX 1) (jU (jX 2) (jX 0)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_20232 : LiftP [2, 0, 2, 3, 2] :=
  liftP_of [2, 0, 2, 3, 2]
    (jU (jX 2) (jT (jX 0) (jX 2) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_20302 : LiftP [2, 0, 3, 0, 2] :=
  liftP_of [2, 0, 3, 0, 2]
    (jU (jX 2) (jU (jX 0) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_20303 : LiftP [2, 0, 3, 0, 3] :=
  liftP_of [2, 0, 3, 0, 3]
    (jT (jX 2) (jX 0) (jU (jX 3) (jX 0)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_20312 : LiftP [2, 0, 3, 1, 2] :=
  liftP_of [2, 0, 3, 1, 2]
    (jU (jX 2) (jT (jX 0) (jX 3) (jX 1)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_20313 : LiftP [2, 0, 3, 1, 3] :=
  liftP_of [2, 0, 3, 1, 3]
    (jT (jX 2) (jX 0) (jU (jX 3) (jX 1)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_20323 : LiftP [2, 0, 3, 2, 3] :=
  liftP_of [2, 0, 3, 2, 3]
    (jT (jX 2) (jX 0) (jU (jX 3) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_21012 : LiftP [2, 1, 0, 1, 2] :=
  liftP_of [2, 1, 0, 1, 2]
    (jU (jX 2) (jU (jX 1) (jX 0)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_21013 : LiftP [2, 1, 0, 1, 3] :=
  liftP_of [2, 1, 0, 1, 3]
    (jT (jX 2) (jU (jX 1) (jX 0)) (jX 3))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_21023 : LiftP [2, 1, 0, 2, 3] :=
  liftP_of [2, 1, 0, 2, 3]
    (.add (jT (jX 0) (jX 1) (jX 3)) (.add (.smul (-2 : ℝ) (jT (jX 0) (jX 2) (jT (jX 2) (jX 1) (jX 3)))) (.smul (2 : ℝ) (jT (jX 2) (jX 1) (jT (jX 0) (jX 2) (jX 3))))))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_21032 : LiftP [2, 1, 0, 3, 2] :=
  liftP_of [2, 1, 0, 3, 2]
    (jU (jX 2) (jT (jX 1) (jX 0) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_21203 : LiftP [2, 1, 2, 0, 3] :=
  liftP_of [2, 1, 2, 0, 3]
    (jT (jX 3) (jX 0) (jU (jX 2) (jX 1)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_21213 : LiftP [2, 1, 2, 1, 3] :=
  liftP_of [2, 1, 2, 1, 3]
    (jT (jX 3) (jX 1) (jU (jX 2) (jX 1)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_21232 : LiftP [2, 1, 2, 3, 2] :=
  liftP_of [2, 1, 2, 3, 2]
    (jU (jX 2) (jT (jX 1) (jX 2) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_21303 : LiftP [2, 1, 3, 0, 3] :=
  liftP_of [2, 1, 3, 0, 3]
    (jT (jX 2) (jX 1) (jU (jX 3) (jX 0)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_21312 : LiftP [2, 1, 3, 1, 2] :=
  liftP_of [2, 1, 3, 1, 2]
    (jU (jX 2) (jU (jX 1) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_21313 : LiftP [2, 1, 3, 1, 3] :=
  liftP_of [2, 1, 3, 1, 3]
    (jT (jX 2) (jX 1) (jU (jX 3) (jX 1)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_21323 : LiftP [2, 1, 3, 2, 3] :=
  liftP_of [2, 1, 3, 2, 3]
    (jT (jX 2) (jX 1) (jU (jX 3) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_23013 : LiftP [2, 3, 0, 1, 3] :=
  liftP_of [2, 3, 0, 1, 3]
    (.add (.smul (-1 : ℝ) (jT (jX 0) (jX 1) (jX 2))) (.smul (2 : ℝ) (jT (jX 2) (jX 3) (jT (jX 0) (jX 1) (jX 3)))))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_23023 : LiftP [2, 3, 0, 2, 3] :=
  liftP_of [2, 3, 0, 2, 3]
    (.add (.smul (-1/2 : ℝ) (jU (jX 2) (jU (jX 3) (jX 0)))) (.add (.smul (-1/2 : ℝ) (jU (jX 3) (jU (jX 2) (jX 0)))) (.smul (2 : ℝ) (jU (jM (jX 2) (jX 3)) (jX 0)))))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_23032 : LiftP [2, 3, 0, 3, 2] :=
  liftP_of [2, 3, 0, 3, 2]
    (jU (jX 2) (jU (jX 3) (jX 0)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_23103 : LiftP [2, 3, 1, 0, 3] :=
  liftP_of [2, 3, 1, 0, 3]
    (.add (.smul (-1 : ℝ) (jT (jX 1) (jX 0) (jX 2))) (.smul (2 : ℝ) (jT (jX 2) (jX 3) (jT (jX 1) (jX 0) (jX 3)))))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_23123 : LiftP [2, 3, 1, 2, 3] :=
  liftP_of [2, 3, 1, 2, 3]
    (.add (.smul (-1/2 : ℝ) (jU (jX 2) (jU (jX 3) (jX 1)))) (.add (.smul (-1/2 : ℝ) (jU (jX 3) (jU (jX 2) (jX 1)))) (.smul (2 : ℝ) (jU (jM (jX 2) (jX 3)) (jX 1)))))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_23132 : LiftP [2, 3, 1, 3, 2] :=
  liftP_of [2, 3, 1, 3, 2]
    (jU (jX 2) (jU (jX 3) (jX 1)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_23203 : LiftP [2, 3, 2, 0, 3] :=
  liftP_of [2, 3, 2, 0, 3]
    (jT (jX 3) (jX 0) (jU (jX 2) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_23213 : LiftP [2, 3, 2, 1, 3] :=
  liftP_of [2, 3, 2, 1, 3]
    (jT (jX 3) (jX 1) (jU (jX 2) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_30103 : LiftP [3, 0, 1, 0, 3] :=
  liftP_of [3, 0, 1, 0, 3]
    (jU (jX 3) (jU (jX 0) (jX 1)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_30123 : LiftP [3, 0, 1, 2, 3] :=
  liftP_of [3, 0, 1, 2, 3]
    (jU (jX 3) (jT (jX 0) (jX 1) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_30203 : LiftP [3, 0, 2, 0, 3] :=
  liftP_of [3, 0, 2, 0, 3]
    (jU (jX 3) (jU (jX 0) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_30213 : LiftP [3, 0, 2, 1, 3] :=
  liftP_of [3, 0, 2, 1, 3]
    (jU (jX 3) (jT (jX 0) (jX 2) (jX 1)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_30313 : LiftP [3, 0, 3, 1, 3] :=
  liftP_of [3, 0, 3, 1, 3]
    (jU (jX 3) (jT (jX 0) (jX 3) (jX 1)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_30323 : LiftP [3, 0, 3, 2, 3] :=
  liftP_of [3, 0, 3, 2, 3]
    (jU (jX 3) (jT (jX 0) (jX 3) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_31013 : LiftP [3, 1, 0, 1, 3] :=
  liftP_of [3, 1, 0, 1, 3]
    (jU (jX 3) (jU (jX 1) (jX 0)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_31023 : LiftP [3, 1, 0, 2, 3] :=
  liftP_of [3, 1, 0, 2, 3]
    (jU (jX 3) (jT (jX 1) (jX 0) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_31213 : LiftP [3, 1, 2, 1, 3] :=
  liftP_of [3, 1, 2, 1, 3]
    (jU (jX 3) (jU (jX 1) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_31323 : LiftP [3, 1, 3, 2, 3] :=
  liftP_of [3, 1, 3, 2, 3]
    (jU (jX 3) (jT (jX 1) (jX 3) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_32023 : LiftP [3, 2, 0, 2, 3] :=
  liftP_of [3, 2, 0, 2, 3]
    (jU (jX 3) (jU (jX 2) (jX 0)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_32123 : LiftP [3, 2, 1, 2, 3] :=
  liftP_of [3, 2, 1, 2, 3]
    (jU (jX 3) (jU (jX 2) (jX 1)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

end AlbertSequential.HorizonFive
