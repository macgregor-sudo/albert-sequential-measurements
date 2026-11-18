/- SPDX-License-Identifier: Apache-2.0
   Machine-generated file. -/
module

public import HorizonFive.RecogBase

/-! # lem:cer:h5:lift, per-class lifts (length five, first half)

Each theorem `lw_<word>` gives an explicit Jordan expression `K` with `deg K ≤ |w|`, of degree one
in every letter occurring once in `w`, and `σ̂(K) = [w] - ℓ(w) [r_0r_1r_2r_3]`; the special value
is checked by expanding both sides in `ℝ[G]` (`lift_spec`), the degree and letter conditions and
`ℓ(w)` by kernel `decide`. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.HorizonFive

theorem lw_01012 : LiftP [0, 1, 0, 1, 2] :=
  liftP_of [0, 1, 0, 1, 2]
    (jT (jX 2) (jX 1) (jU (jX 0) (jX 1)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_01013 : LiftP [0, 1, 0, 1, 3] :=
  liftP_of [0, 1, 0, 1, 3]
    (jT (jX 3) (jX 1) (jU (jX 0) (jX 1)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_01020 : LiftP [0, 1, 0, 2, 0] :=
  liftP_of [0, 1, 0, 2, 0]
    (jU (jX 0) (jT (jX 1) (jX 0) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_01021 : LiftP [0, 1, 0, 2, 1] :=
  liftP_of [0, 1, 0, 2, 1]
    (jT (jX 1) (jX 2) (jU (jX 0) (jX 1)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_01023 : LiftP [0, 1, 0, 2, 3] :=
  liftP_of [0, 1, 0, 2, 3]
    (jT (jX 3) (jX 2) (jU (jX 0) (jX 1)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_01030 : LiftP [0, 1, 0, 3, 0] :=
  liftP_of [0, 1, 0, 3, 0]
    (jU (jX 0) (jT (jX 1) (jX 0) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_01031 : LiftP [0, 1, 0, 3, 1] :=
  liftP_of [0, 1, 0, 3, 1]
    (jT (jX 1) (jX 3) (jU (jX 0) (jX 1)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_01032 : LiftP [0, 1, 0, 3, 2] :=
  liftP_of [0, 1, 0, 3, 2]
    (jT (jX 2) (jX 3) (jU (jX 0) (jX 1)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_01201 : LiftP [0, 1, 2, 0, 1] :=
  liftP_of [0, 1, 2, 0, 1]
    (.add (.smul (-1/2 : ℝ) (jU (jX 0) (jU (jX 1) (jX 2)))) (.add (.smul (-1/2 : ℝ) (jU (jX 1) (jU (jX 0) (jX 2)))) (.smul (2 : ℝ) (jU (jM (jX 0) (jX 1)) (jX 2)))))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_01202 : LiftP [0, 1, 2, 0, 2] :=
  liftP_of [0, 1, 2, 0, 2]
    (jT (jX 0) (jX 1) (jU (jX 2) (jX 0)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_01203 : LiftP [0, 1, 2, 0, 3] :=
  liftP_of [0, 1, 2, 0, 3]
    (.add (jT (jX 2) (jX 1) (jX 3)) (.add (.smul (2 : ℝ) (jT (jX 0) (jX 1) (jT (jX 2) (jX 0) (jX 3)))) (.smul (-2 : ℝ) (jT (jX 2) (jX 0) (jT (jX 0) (jX 1) (jX 3))))))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_01210 : LiftP [0, 1, 2, 1, 0] :=
  liftP_of [0, 1, 2, 1, 0]
    (jU (jX 0) (jU (jX 1) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_01212 : LiftP [0, 1, 2, 1, 2] :=
  liftP_of [0, 1, 2, 1, 2]
    (jT (jX 0) (jX 1) (jU (jX 2) (jX 1)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_01213 : LiftP [0, 1, 2, 1, 3] :=
  liftP_of [0, 1, 2, 1, 3]
    (jT (jX 0) (jU (jX 1) (jX 2)) (jX 3))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_01230 : LiftP [0, 1, 2, 3, 0] :=
  liftP_of [0, 1, 2, 3, 0]
    (jU (jX 0) (jT (jX 1) (jX 2) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_01231 : LiftP [0, 1, 2, 3, 1] :=
  liftP_of [0, 1, 2, 3, 1]
    (.add (.smul (-1 : ℝ) (jT (jX 0) (jX 3) (jX 2))) (.smul (2 : ℝ) (jT (jX 0) (jX 1) (jT (jX 1) (jX 3) (jX 2)))))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_01232 : LiftP [0, 1, 2, 3, 2] :=
  liftP_of [0, 1, 2, 3, 2]
    (jT (jX 0) (jX 1) (jU (jX 2) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_01301 : LiftP [0, 1, 3, 0, 1] :=
  liftP_of [0, 1, 3, 0, 1]
    (.add (.smul (-1/2 : ℝ) (jU (jX 0) (jU (jX 1) (jX 3)))) (.add (.smul (-1/2 : ℝ) (jU (jX 1) (jU (jX 0) (jX 3)))) (.smul (2 : ℝ) (jU (jM (jX 0) (jX 1)) (jX 3)))))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_01302 : LiftP [0, 1, 3, 0, 2] :=
  liftP_of [0, 1, 3, 0, 2]
    (.add (.smul (-1 : ℝ) (jT (jX 2) (jX 1) (jX 3))) (.smul (2 : ℝ) (jT (jX 2) (jX 0) (jT (jX 0) (jX 1) (jX 3)))))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_01303 : LiftP [0, 1, 3, 0, 3] :=
  liftP_of [0, 1, 3, 0, 3]
    (jT (jX 0) (jX 1) (jU (jX 3) (jX 0)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_01310 : LiftP [0, 1, 3, 1, 0] :=
  liftP_of [0, 1, 3, 1, 0]
    (jU (jX 0) (jU (jX 1) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_01312 : LiftP [0, 1, 3, 1, 2] :=
  liftP_of [0, 1, 3, 1, 2]
    (jT (jX 0) (jU (jX 1) (jX 3)) (jX 2))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_01313 : LiftP [0, 1, 3, 1, 3] :=
  liftP_of [0, 1, 3, 1, 3]
    (jT (jX 0) (jX 1) (jU (jX 3) (jX 1)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_01320 : LiftP [0, 1, 3, 2, 0] :=
  liftP_of [0, 1, 3, 2, 0]
    (jU (jX 0) (jT (jX 1) (jX 3) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_01321 : LiftP [0, 1, 3, 2, 1] :=
  liftP_of [0, 1, 3, 2, 1]
    (.add (.smul (-1 : ℝ) (jT (jX 0) (jX 2) (jX 3))) (.smul (2 : ℝ) (jT (jX 0) (jX 1) (jT (jX 1) (jX 2) (jX 3)))))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_01323 : LiftP [0, 1, 3, 2, 3] :=
  liftP_of [0, 1, 3, 2, 3]
    (jT (jX 0) (jX 1) (jU (jX 3) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_02012 : LiftP [0, 2, 0, 1, 2] :=
  liftP_of [0, 2, 0, 1, 2]
    (jT (jX 2) (jX 1) (jU (jX 0) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_02013 : LiftP [0, 2, 0, 1, 3] :=
  liftP_of [0, 2, 0, 1, 3]
    (jT (jX 3) (jX 1) (jU (jX 0) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_02021 : LiftP [0, 2, 0, 2, 1] :=
  liftP_of [0, 2, 0, 2, 1]
    (jT (jX 1) (jX 2) (jU (jX 0) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_02023 : LiftP [0, 2, 0, 2, 3] :=
  liftP_of [0, 2, 0, 2, 3]
    (jT (jX 3) (jX 2) (jU (jX 0) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_02030 : LiftP [0, 2, 0, 3, 0] :=
  liftP_of [0, 2, 0, 3, 0]
    (jU (jX 0) (jT (jX 2) (jX 0) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_02031 : LiftP [0, 2, 0, 3, 1] :=
  liftP_of [0, 2, 0, 3, 1]
    (jT (jX 1) (jX 3) (jU (jX 0) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_02032 : LiftP [0, 2, 0, 3, 2] :=
  liftP_of [0, 2, 0, 3, 2]
    (jT (jX 2) (jX 3) (jU (jX 0) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_02101 : LiftP [0, 2, 1, 0, 1] :=
  liftP_of [0, 2, 1, 0, 1]
    (jT (jX 0) (jX 2) (jU (jX 1) (jX 0)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_02102 : LiftP [0, 2, 1, 0, 2] :=
  liftP_of [0, 2, 1, 0, 2]
    (.add (.smul (-1/2 : ℝ) (jU (jX 0) (jU (jX 2) (jX 1)))) (.add (.smul (-1/2 : ℝ) (jU (jX 2) (jU (jX 0) (jX 1)))) (.smul (2 : ℝ) (jU (jM (jX 0) (jX 2)) (jX 1)))))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_02103 : LiftP [0, 2, 1, 0, 3] :=
  liftP_of [0, 2, 1, 0, 3]
    (.add (jT (jX 1) (jX 2) (jX 3)) (.add (.smul (2 : ℝ) (jT (jX 0) (jX 2) (jT (jX 1) (jX 0) (jX 3)))) (.smul (-2 : ℝ) (jT (jX 1) (jX 0) (jT (jX 0) (jX 2) (jX 3))))))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_02120 : LiftP [0, 2, 1, 2, 0] :=
  liftP_of [0, 2, 1, 2, 0]
    (jU (jX 0) (jU (jX 2) (jX 1)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_02121 : LiftP [0, 2, 1, 2, 1] :=
  liftP_of [0, 2, 1, 2, 1]
    (jT (jX 0) (jX 2) (jU (jX 1) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_02123 : LiftP [0, 2, 1, 2, 3] :=
  liftP_of [0, 2, 1, 2, 3]
    (jT (jX 0) (jU (jX 2) (jX 1)) (jX 3))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_02130 : LiftP [0, 2, 1, 3, 0] :=
  liftP_of [0, 2, 1, 3, 0]
    (jU (jX 0) (jT (jX 2) (jX 1) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_02131 : LiftP [0, 2, 1, 3, 1] :=
  liftP_of [0, 2, 1, 3, 1]
    (jT (jX 0) (jX 2) (jU (jX 1) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_02132 : LiftP [0, 2, 1, 3, 2] :=
  liftP_of [0, 2, 1, 3, 2]
    (.add (.smul (-1 : ℝ) (jT (jX 0) (jX 3) (jX 1))) (.smul (2 : ℝ) (jT (jX 0) (jX 2) (jT (jX 1) (jX 3) (jX 2)))))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_02301 : LiftP [0, 2, 3, 0, 1] :=
  liftP_of [0, 2, 3, 0, 1]
    (.add (.smul (-1 : ℝ) (jT (jX 1) (jX 2) (jX 3))) (.smul (2 : ℝ) (jT (jX 1) (jX 0) (jT (jX 0) (jX 2) (jX 3)))))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_02302 : LiftP [0, 2, 3, 0, 2] :=
  liftP_of [0, 2, 3, 0, 2]
    (.add (.smul (-1/2 : ℝ) (jU (jX 0) (jU (jX 2) (jX 3)))) (.add (.smul (-1/2 : ℝ) (jU (jX 2) (jU (jX 0) (jX 3)))) (.smul (2 : ℝ) (jU (jM (jX 0) (jX 2)) (jX 3)))))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_02303 : LiftP [0, 2, 3, 0, 3] :=
  liftP_of [0, 2, 3, 0, 3]
    (jT (jX 0) (jX 2) (jU (jX 3) (jX 0)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_02312 : LiftP [0, 2, 3, 1, 2] :=
  liftP_of [0, 2, 3, 1, 2]
    (.add (.smul (-1 : ℝ) (jT (jX 0) (jX 1) (jX 3))) (.smul (2 : ℝ) (jT (jX 0) (jX 2) (jT (jX 2) (jX 1) (jX 3)))))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_02313 : LiftP [0, 2, 3, 1, 3] :=
  liftP_of [0, 2, 3, 1, 3]
    (jT (jX 0) (jX 2) (jU (jX 3) (jX 1)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_02320 : LiftP [0, 2, 3, 2, 0] :=
  liftP_of [0, 2, 3, 2, 0]
    (jU (jX 0) (jU (jX 2) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_02321 : LiftP [0, 2, 3, 2, 1] :=
  liftP_of [0, 2, 3, 2, 1]
    (jT (jX 0) (jU (jX 2) (jX 3)) (jX 1))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_02323 : LiftP [0, 2, 3, 2, 3] :=
  liftP_of [0, 2, 3, 2, 3]
    (jT (jX 0) (jX 2) (jU (jX 3) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_03012 : LiftP [0, 3, 0, 1, 2] :=
  liftP_of [0, 3, 0, 1, 2]
    (jT (jX 2) (jX 1) (jU (jX 0) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_03013 : LiftP [0, 3, 0, 1, 3] :=
  liftP_of [0, 3, 0, 1, 3]
    (jT (jX 3) (jX 1) (jU (jX 0) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_03021 : LiftP [0, 3, 0, 2, 1] :=
  liftP_of [0, 3, 0, 2, 1]
    (jT (jX 1) (jX 2) (jU (jX 0) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_03023 : LiftP [0, 3, 0, 2, 3] :=
  liftP_of [0, 3, 0, 2, 3]
    (jT (jX 3) (jX 2) (jU (jX 0) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_03031 : LiftP [0, 3, 0, 3, 1] :=
  liftP_of [0, 3, 0, 3, 1]
    (jT (jX 1) (jX 3) (jU (jX 0) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_03032 : LiftP [0, 3, 0, 3, 2] :=
  liftP_of [0, 3, 0, 3, 2]
    (jT (jX 2) (jX 3) (jU (jX 0) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_03101 : LiftP [0, 3, 1, 0, 1] :=
  liftP_of [0, 3, 1, 0, 1]
    (jT (jX 0) (jX 3) (jU (jX 1) (jX 0)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_03102 : LiftP [0, 3, 1, 0, 2] :=
  liftP_of [0, 3, 1, 0, 2]
    (.add (jT (jX 1) (jX 3) (jX 2)) (.add (.smul (2 : ℝ) (jT (jX 0) (jX 3) (jT (jX 1) (jX 0) (jX 2)))) (.smul (-2 : ℝ) (jT (jX 1) (jX 0) (jT (jX 0) (jX 3) (jX 2))))))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_03103 : LiftP [0, 3, 1, 0, 3] :=
  liftP_of [0, 3, 1, 0, 3]
    (.add (.smul (-1/2 : ℝ) (jU (jX 0) (jU (jX 3) (jX 1)))) (.add (.smul (-1/2 : ℝ) (jU (jX 3) (jU (jX 0) (jX 1)))) (.smul (2 : ℝ) (jU (jM (jX 0) (jX 3)) (jX 1)))))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_03121 : LiftP [0, 3, 1, 2, 1] :=
  liftP_of [0, 3, 1, 2, 1]
    (jT (jX 0) (jX 3) (jU (jX 1) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_03123 : LiftP [0, 3, 1, 2, 3] :=
  liftP_of [0, 3, 1, 2, 3]
    (.add (.smul (-1 : ℝ) (jT (jX 0) (jX 2) (jX 1))) (.smul (2 : ℝ) (jT (jX 0) (jX 3) (jT (jX 1) (jX 2) (jX 3)))))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_03130 : LiftP [0, 3, 1, 3, 0] :=
  liftP_of [0, 3, 1, 3, 0]
    (jU (jX 0) (jU (jX 3) (jX 1)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_03131 : LiftP [0, 3, 1, 3, 1] :=
  liftP_of [0, 3, 1, 3, 1]
    (jT (jX 0) (jX 3) (jU (jX 1) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_03132 : LiftP [0, 3, 1, 3, 2] :=
  liftP_of [0, 3, 1, 3, 2]
    (jT (jX 0) (jU (jX 3) (jX 1)) (jX 2))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_03201 : LiftP [0, 3, 2, 0, 1] :=
  liftP_of [0, 3, 2, 0, 1]
    (.add (.smul (-1 : ℝ) (jT (jX 1) (jX 3) (jX 2))) (.smul (2 : ℝ) (jT (jX 1) (jX 0) (jT (jX 0) (jX 3) (jX 2)))))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_03202 : LiftP [0, 3, 2, 0, 2] :=
  liftP_of [0, 3, 2, 0, 2]
    (jT (jX 0) (jX 3) (jU (jX 2) (jX 0)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_03203 : LiftP [0, 3, 2, 0, 3] :=
  liftP_of [0, 3, 2, 0, 3]
    (.add (.smul (-1/2 : ℝ) (jU (jX 0) (jU (jX 3) (jX 2)))) (.add (.smul (-1/2 : ℝ) (jU (jX 3) (jU (jX 0) (jX 2)))) (.smul (2 : ℝ) (jU (jM (jX 0) (jX 3)) (jX 2)))))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_03212 : LiftP [0, 3, 2, 1, 2] :=
  liftP_of [0, 3, 2, 1, 2]
    (jT (jX 0) (jX 3) (jU (jX 2) (jX 1)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_03213 : LiftP [0, 3, 2, 1, 3] :=
  liftP_of [0, 3, 2, 1, 3]
    (.add (.smul (-1 : ℝ) (jT (jX 0) (jX 1) (jX 2))) (.smul (2 : ℝ) (jT (jX 0) (jX 3) (jT (jX 2) (jX 1) (jX 3)))))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_03230 : LiftP [0, 3, 2, 3, 0] :=
  liftP_of [0, 3, 2, 3, 0]
    (jU (jX 0) (jU (jX 3) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_03231 : LiftP [0, 3, 2, 3, 1] :=
  liftP_of [0, 3, 2, 3, 1]
    (jT (jX 0) (jU (jX 3) (jX 2)) (jX 1))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_03232 : LiftP [0, 3, 2, 3, 2] :=
  liftP_of [0, 3, 2, 3, 2]
    (jT (jX 0) (jX 3) (jU (jX 2) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_10102 : LiftP [1, 0, 1, 0, 2] :=
  liftP_of [1, 0, 1, 0, 2]
    (jT (jX 2) (jX 0) (jU (jX 1) (jX 0)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_10103 : LiftP [1, 0, 1, 0, 3] :=
  liftP_of [1, 0, 1, 0, 3]
    (jT (jX 3) (jX 0) (jU (jX 1) (jX 0)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_10121 : LiftP [1, 0, 1, 2, 1] :=
  liftP_of [1, 0, 1, 2, 1]
    (jU (jX 1) (jT (jX 0) (jX 1) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_10123 : LiftP [1, 0, 1, 2, 3] :=
  liftP_of [1, 0, 1, 2, 3]
    (jT (jX 3) (jX 2) (jU (jX 1) (jX 0)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_10131 : LiftP [1, 0, 1, 3, 1] :=
  liftP_of [1, 0, 1, 3, 1]
    (jU (jX 1) (jT (jX 0) (jX 1) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_10132 : LiftP [1, 0, 1, 3, 2] :=
  liftP_of [1, 0, 1, 3, 2]
    (jT (jX 2) (jX 3) (jU (jX 1) (jX 0)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_10201 : LiftP [1, 0, 2, 0, 1] :=
  liftP_of [1, 0, 2, 0, 1]
    (jU (jX 1) (jU (jX 0) (jX 2)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_10202 : LiftP [1, 0, 2, 0, 2] :=
  liftP_of [1, 0, 2, 0, 2]
    (jT (jX 1) (jX 0) (jU (jX 2) (jX 0)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_10203 : LiftP [1, 0, 2, 0, 3] :=
  liftP_of [1, 0, 2, 0, 3]
    (jT (jX 1) (jU (jX 0) (jX 2)) (jX 3))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_10212 : LiftP [1, 0, 2, 1, 2] :=
  liftP_of [1, 0, 2, 1, 2]
    (jT (jX 1) (jX 0) (jU (jX 2) (jX 1)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_10213 : LiftP [1, 0, 2, 1, 3] :=
  liftP_of [1, 0, 2, 1, 3]
    (.add (jT (jX 2) (jX 0) (jX 3)) (.add (.smul (2 : ℝ) (jT (jX 1) (jX 0) (jT (jX 2) (jX 1) (jX 3)))) (.smul (-2 : ℝ) (jT (jX 2) (jX 1) (jT (jX 1) (jX 0) (jX 3))))))
    0 (by decide) (by decide) (by decide) (by lift_spec)

theorem lw_10231 : LiftP [1, 0, 2, 3, 1] :=
  liftP_of [1, 0, 2, 3, 1]
    (jU (jX 1) (jT (jX 0) (jX 2) (jX 3)))
    0 (by decide) (by decide) (by decide) (by lift_spec)

end AlbertSequential.HorizonFive
