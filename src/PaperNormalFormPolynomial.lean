/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ThirteenTracesAndAform
import Mathlib.Algebra.MvPolynomial.Funext

@[expose] public section
noncomputable section

namespace AlbertSequential

namespace NormalFormPolynomial

/-- The Cayley–Dickson coordinates used in A.5, over a polynomial coefficient ring. -/
abbrev Oct (R : Type*) [CommRing R] := Quaternion R × Quaternion R

section Ring

variable {R S : Type*} [CommRing R] [CommRing S]

def mul (x y : Oct R) : Oct R :=
  (x.1 * y.1 - star y.2 * x.2, y.2 * x.1 + x.2 * star y.1)

def conj (x : Oct R) : Oct R :=
  (star x.1, -x.2)

def scalar (a : R) : Oct R :=
  (⟨a, 0, 0, 0⟩, 0)

def imI : Oct R :=
  (⟨0, 1, 0, 0⟩, 0)

def coordOct (u : Fin 8 → R) : Oct R :=
  (⟨u 0, u 1, u 2, u 3⟩, ⟨u 4, u 5, u 6, u 7⟩)

def normSq (x : Oct R) : R :=
  (mul x (conj x)).1.re

def associator (x y z : Oct R) : Oct R :=
  mul (mul x y) z - mul x (mul y z)

-- The thirteen-trace polynomial in the Ω variables, over an arbitrary commutative ring.
def omega (oAB oAC oAD oBC oBD oCD RABC RABD RACD RBCD w₁ w₂ w₃ : R) : R :=
  oAB * oAC * oAD * oBC * oBD * oCD
    - (RABC ^ 2 * oAD * oBD * oCD + RABD ^ 2 * oAC * oBC * oCD
        + RACD ^ 2 * oAB * oBC * oBD + RBCD ^ 2 * oAB * oAC * oAD)
    - 4 * RABC * RABD * RACD * RBCD
    - (oAB * oCD * w₁ ^ 2 + oAC * oBD * w₂ ^ 2 + oAD * oBC * w₃ ^ 2)
    + 2 * w₁ * (RABC * RABD * oCD + RACD * RBCD * oAB)
    + 2 * w₂ * (RABC * RACD * oBD + RABD * RBCD * oAC)
    + 2 * w₃ * (RABC * RBCD * oAD + RABD * RACD * oBC)
    - 2 * w₁ * w₂ * w₃

def traceSide (B₀ B₁ C₀ C₁ C₂ C₃ D₀ : R) (X Y : Oct R) : R :=
  let z := scalar C₁ + C₂ • imI
  let g₁ := scalar (B₀ * C₀) + B₁ • z
  let g₂ := scalar (B₀ * D₀) + B₁ • X
  let g₃ := scalar (C₀ * D₀) + mul (conj z) X + C₃ • Y
  omega (B₀ ^ 2) (C₀ ^ 2) (D₀ ^ 2) (normSq g₁) (normSq g₂) (normSq g₃)
    (B₀ * C₀ * g₁.1.re) (B₀ * D₀ * g₂.1.re) (C₀ * D₀ * g₃.1.re)
    (mul (mul g₁ g₃) (conj g₂)).1.re
    (C₀ * D₀ * (mul g₁ (conj g₂)).1.re) (B₀ * D₀ * (mul g₁ g₃).1.re)
    (B₀ * C₀ * (mul g₂ (conj g₃)).1.re)

def associatorSide (quarter B₀ B₁ C₀ C₂ C₃ D₀ : R) (X Y : Oct R) : R :=
  quarter * B₀ ^ 2 * B₁ ^ 4 * C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2 * D₀ ^ 2 *
    normSq (associator imI X Y)

private def quatMap (f : R →+* S) (x : Quaternion R) : Quaternion S :=
  ⟨f x.re, f x.imI, f x.imJ, f x.imK⟩

private theorem quatMap_add (f : R →+* S) (x y : Quaternion R) :
    quatMap f (x + y) = quatMap f x + quatMap f y := by
  ext <;> simp [quatMap]

private theorem quatMap_sub (f : R →+* S) (x y : Quaternion R) :
    quatMap f (x - y) = quatMap f x - quatMap f y := by
  ext <;> simp [quatMap]

private theorem quatMap_neg (f : R →+* S) (x : Quaternion R) :
    quatMap f (-x) = -quatMap f x := by
  ext <;> simp [quatMap]

private theorem quatMap_smul (f : R →+* S) (r : R) (x : Quaternion R) :
    quatMap f (r • x) = f r • quatMap f x := by
  ext <;> simp [quatMap, smul_eq_mul]

private theorem quatMap_star (f : R →+* S) (x : Quaternion R) :
    quatMap f (star x) = star (quatMap f x) := by
  ext <;> simp [quatMap]

private theorem quatMap_mul (f : R →+* S) (x y : Quaternion R) :
    quatMap f (x * y) = quatMap f x * quatMap f y := by
  ext <;> simp [quatMap, sub_eq_add_neg]

private def mapOct (f : R →+* S) (x : Oct R) : Oct S :=
  (quatMap f x.1, quatMap f x.2)

private theorem mapOct_add (f : R →+* S) (x y : Oct R) :
    mapOct f (x + y) = mapOct f x + mapOct f y := by
  exact Prod.ext (quatMap_add f x.1 y.1) (quatMap_add f x.2 y.2)

private theorem mapOct_sub (f : R →+* S) (x y : Oct R) :
    mapOct f (x - y) = mapOct f x - mapOct f y := by
  exact Prod.ext (quatMap_sub f x.1 y.1) (quatMap_sub f x.2 y.2)

private theorem mapOct_smul (f : R →+* S) (r : R) (x : Oct R) :
    mapOct f (r • x) = f r • mapOct f x := by
  exact Prod.ext (quatMap_smul f r x.1) (quatMap_smul f r x.2)

private theorem mapOct_mul (f : R →+* S) (x y : Oct R) :
    mapOct f (mul x y) = mul (mapOct f x) (mapOct f y) := by
  simp only [mapOct, mul, quatMap_add, quatMap_sub, quatMap_mul, quatMap_star]

private theorem mapOct_conj (f : R →+* S) (x : Oct R) :
    mapOct f (conj x) = conj (mapOct f x) := by
  simp only [mapOct, conj, quatMap_star, quatMap_neg]

private theorem mapOct_scalar (f : R →+* S) (a : R) :
    mapOct f (scalar a) = scalar (f a) := by
  apply Prod.ext <;> ext <;> simp [mapOct, scalar, quatMap]

private theorem mapOct_imI (f : R →+* S) :
    mapOct f (imI : Oct R) = imI := by
  apply Prod.ext <;> ext <;> simp [mapOct, imI, quatMap]

private theorem mapOct_coordOct (f : R →+* S) (u : Fin 8 → R) :
    mapOct f (coordOct u) = coordOct (fun i => f (u i)) :=
  rfl

private theorem map_re (f : R →+* S) (x : Oct R) :
    f x.1.re = (mapOct f x).1.re :=
  rfl

private theorem map_normSq (f : R →+* S) (x : Oct R) :
    f (normSq x) = normSq (mapOct f x) := by
  unfold normSq
  rw [map_re, mapOct_mul, mapOct_conj]

private theorem map_associator (f : R →+* S) (x y z : Oct R) :
    mapOct f (associator x y z) = associator (mapOct f x) (mapOct f y) (mapOct f z) := by
  simp only [associator, mapOct_sub, mapOct_mul]

private theorem map_traceSide (f : R →+* S) (B₀ B₁ C₀ C₁ C₂ C₃ D₀ : R) (X Y : Oct R) :
    f (traceSide B₀ B₁ C₀ C₁ C₂ C₃ D₀ X Y) =
      traceSide (f B₀) (f B₁) (f C₀) (f C₁) (f C₂) (f C₃) (f D₀) (mapOct f X) (mapOct f Y) := by
  simp only [traceSide, omega, map_add, map_sub, map_mul, map_pow, map_ofNat,
    map_re, map_normSq, mapOct_add, mapOct_mul, mapOct_smul, mapOct_conj, mapOct_scalar, mapOct_imI]

private theorem map_associatorSide (f : R →+* S) (quarter B₀ B₁ C₀ C₂ C₃ D₀ : R) (X Y : Oct R) :
    f (associatorSide quarter B₀ B₁ C₀ C₂ C₃ D₀ X Y) =
      associatorSide (f quarter) (f B₀) (f B₁) (f C₀) (f C₂) (f C₃) (f D₀) (mapOct f X) (mapOct f Y) := by
  simp only [associatorSide, map_mul, map_pow, map_normSq, map_associator, mapOct_imI]

end Ring

abbrev Coeffs := MvPolynomial (Fin 23) ℚ

/-- (X) and (Y) use index ranges 7–14 and 15–22, in Cayley–Dickson component order. -/
def coordX {R : Type*} [CommRing R] (v : Fin 23 → R) : Oct R :=
  coordOct (fun i => v ⟨7 + i.val, by omega⟩)

def coordY {R : Type*} [CommRing R] (v : Fin 23 → R) : Oct R :=
  coordOct (fun i => v ⟨15 + i.val, by omega⟩)

/-- The invariant of the sparse normal form as a rational polynomial in all 23 coordinates. -/
def tracePolynomial : Coeffs :=
  traceSide (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2) (MvPolynomial.X 3)
    (MvPolynomial.X 4) (MvPolynomial.X 5) (MvPolynomial.X 6)
    (coordX MvPolynomial.X) (coordY MvPolynomial.X)

/-- The associator-norm polynomial with the printed rational prefactor. -/
def associatorPolynomial : Coeffs :=
  associatorSide (MvPolynomial.C (1 / 4 : ℚ)) (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2)
    (MvPolynomial.X 4) (MvPolynomial.X 5) (MvPolynomial.X 6)
    (coordX MvPolynomial.X) (coordY MvPolynomial.X)

private theorem traceSide_real (B₀ B₁ C₀ C₁ C₂ C₃ D₀ : ℝ) (X Y : Octonion) :
    traceSide B₀ B₁ C₀ C₁ C₂ C₃ D₀ X Y =
      fourPointInvariant (sparseFourConfigOct B₀ B₁ C₀ C₁ C₂ C₃ D₀ X Y) := by
  obtain ⟨oAB, oAC, oAD, oBC, oBD, oCD, RABC, RABD, RACD, RBCD, w₁, w₂, w₃⟩ :=
    sparseFourConfigOct_traces B₀ B₁ C₀ C₁ C₂ C₃ D₀ X Y
  unfold fourPointInvariant
  rw [oAB, oAC, oAD, oBC, oBD, oCD, RABC, RABD, RACD, RBCD, w₁, w₂, w₃]
  rfl

private theorem associatorSide_real (B₀ B₁ C₀ C₂ C₃ D₀ : ℝ) (X Y : Octonion) :
    associatorSide (1 / 4 : ℝ) B₀ B₁ C₀ C₂ C₃ D₀ X Y =
      (1 / 4 : ℝ) * B₀ ^ 2 * B₁ ^ 4 * C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2 * D₀ ^ 2 *
        octNormSq (octAssociator octI X Y) :=
  rfl

theorem eval_tracePolynomial (v : Fin 23 → ℝ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) v tracePolynomial =
      fourPointInvariant (sparseFourConfigOct (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)
        (coordX v) (coordY v)) := by
  change MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) v tracePolynomial = _
  unfold tracePolynomial
  rw [map_traceSide]
  simp only [MvPolynomial.eval₂Hom_X', coordX, coordY, mapOct_coordOct]
  exact traceSide_real _ _ _ _ _ _ _ _ _

theorem eval_associatorPolynomial (v : Fin 23 → ℝ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) v associatorPolynomial =
      (1 / 4 : ℝ) * (v 0) ^ 2 * (v 1) ^ 4 * (v 2) ^ 2 * (v 4) ^ 2 * (v 5) ^ 2 * (v 6) ^ 2 *
        octNormSq (octAssociator octI (coordX v) (coordY v)) := by
  change MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) v associatorPolynomial = _
  unfold associatorPolynomial
  rw [map_associatorSide]
  simp only [MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C, coordX, coordY, mapOct_coordOct]
  have hquarter : algebraMap ℚ ℝ (1 / 4 : ℚ) = (1 / 4 : ℝ) := by norm_num
  rw [hquarter]
  exact associatorSide_real _ _ _ _ _ _ _ _

/-- Lemma A.5 as an identity in the rational polynomial ring, without hypotheses on the variables. -/
theorem normalFormPolynomial_eq : tracePolynomial = associatorPolynomial := by
  apply MvPolynomial.map_injective (algebraMap ℚ ℝ) (FaithfulSMul.algebraMap_injective ℚ ℝ)
  apply MvPolynomial.funext
  intro v
  rw [MvPolynomial.eval_map, MvPolynomial.eval_map, eval_tracePolynomial, eval_associatorPolynomial]
  exact sparseFourConfigOct_fourPointInvariant _ _ _ _ _ _ _ _ _

end NormalFormPolynomial

end AlbertSequential
