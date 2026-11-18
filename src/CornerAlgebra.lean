module

public import LocalVolume

/-! Elementary corner-word contractions and centering identities:
the explicit steps of the corner-word calculation. -/

@[expose] public section
noncomputable section
namespace AlbertSequential

variable {A : Type*} [NonUnitalRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]

omit [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem cornerWord_left (E a b : A) (hEE : E * E = E) :
    E * (E * a * b * E) = E * a * b * E := by
  simp only [← mul_assoc, hEE]

omit [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem cornerWord_right (E a b : A) (hEE : E * E = E) :
    (E * a * b * E) * E = E * a * b * E := by
  rw [mul_assoc (E * a * b), hEE]

theorem cornerWord_mul (E a b c : A) (t : ℝ)
    (hEE : E * E = E) (hbEb : b * E * b = t • b) :
    (E * a * b * E) * (E * b * c * E) = t • (E * a * b * c * E) := by
  calc
    (E * a * b * E) * (E * b * c * E) =
        (E * a * b) * (E * E) * (b * c * E) := by simp only [mul_assoc]
    _ = E * a * (b * E * b) * c * E := by
      rw [hEE]
      simp only [mul_assoc]
    _ = t • (E * a * b * c * E) := by
      rw [hbEb]
      simp only [mul_smul_comm, smul_mul_assoc]

theorem cornerWord_reverse_mul (E a b : A) (t u v : ℝ)
    (hEE : E * E = E)
    (hbEb : b * E * b = t • b)
    (haba : a * b * a = u • a)
    (hEaE : E * a * E = v • E) :
    (E * a * b * E) * (E * b * a * E) = (t * u * v) • E := by
  rw [cornerWord_mul E a b a t hEE hbEb]
  have hword : E * a * b * a * E = (u * v) • E := by
    calc
      E * a * b * a * E = E * (a * b * a) * E := by simp only [mul_assoc]
      _ = (u * v) • E := by
        rw [haba]
        simp only [mul_smul_comm, smul_mul_assoc, hEaE, smul_smul]
  rw [hword, smul_smul]
  congr 1
  ring

theorem cornerWord_mixed (E a b c : A) (t q : ℝ)
    (hEE : E * E = E) (hbEb : b * E * b = t • b)
    (hquad : E * (a * b * c + c * b * a) * E = (2 * q) • E) :
    (E * a * b * E) * (E * b * c * E) +
      (E * c * b * E) * (E * b * a * E) = (2 * t * q) • E := by
  rw [cornerWord_mul E a b c t hEE hbEb,
    cornerWord_mul E c b a t hEE hbEb, ← smul_add]
  have hword : E * a * b * c * E + E * c * b * a * E =
      E * (a * b * c + c * b * a) * E := by noncomm_ring
  rw [hword, hquad, smul_smul]
  congr 1
  ring

theorem cornerWord_chain_mul (E a b c d : A) (t : ℝ)
    (hEE : E * E = E) (hcEc : c * E * c = t • c) :
    (E * a * b * c * E) * (E * c * d * E) =
      t • (E * a * b * c * d * E) := by
  calc
    (E * a * b * c * E) * (E * c * d * E) =
        (E * a * b * c) * (E * E) * (c * d * E) := by simp only [mul_assoc]
    _ = E * a * b * (c * E * c) * d * E := by rw [hEE]; simp only [mul_assoc]
    _ = t • (E * a * b * c * d * E) := by
      rw [hcEc]
      simp only [mul_smul_comm, smul_mul_assoc]

theorem cornerWord_far (E a b c : A) (t u v r : ℝ)
    (hEE : E * E = E)
    (hbEb : b * E * b = t • b) (hcEc : c * E * c = u • c)
    (htriangle : a * (b * c + c * b) * a = (2 * r) • a)
    (hEaE : E * a * E = v • E) :
    (E * a * b * E) * (E * b * c * E) * (E * c * a * E) +
      (E * a * c * E) * (E * c * b * E) * (E * b * a * E) =
      (2 * t * u * v * r) • E := by
  rw [cornerWord_mul E a b c t hEE hbEb,
    cornerWord_mul E a c b u hEE hcEc]
  simp only [smul_mul_assoc]
  rw [cornerWord_chain_mul E a b c a u hEE hcEc,
    cornerWord_chain_mul E a c b a t hEE hbEb]
  simp only [smul_smul]
  have hword : E * a * b * c * a * E + E * a * c * b * a * E =
      E * (a * (b * c + c * b) * a) * E := by noncomm_ring
  calc
    (t * u) • (E * a * b * c * a * E) +
        (u * t) • (E * a * c * b * a * E) =
        (t * u) • (E * (a * (b * c + c * b) * a) * E) := by
      rw [← hword]
      module
    _ = (2 * t * u * v * r) • E := by
      rw [htriangle]
      simp only [mul_smul_comm, smul_mul_assoc, hEaE, smul_smul]
      congr 1
      ring

omit [IsScalarTower ℝ A A] in
theorem centeredCorner_left (E g : A) (r : ℝ)
    (hEE : E * E = E) (hEg : E * g = g) :
    E * (g - r • E) = g - r • E := by
  simp only [mul_sub, mul_smul_comm, hEg, hEE]

omit [SMulCommClass ℝ A A] in
theorem centeredCorner_right (E g : A) (r : ℝ)
    (hEE : E * E = E) (hgE : g * E = g) :
    (g - r • E) * E = g - r • E := by
  simp only [sub_mul, smul_mul_assoc, hgE, hEE]

theorem centeredCorner_square (E g g' : A) (r ν : ℝ)
    (hEE : E * E = E) (hEg : E * g = g) (hgE : g * E = g)
    (hreverse : g + g' = (2 * r) • E) (hlength : g * g' = ν • E) :
    (g - r • E) * (g - r • E) = (r ^ 2 - ν) • E := by
  have hg' : g' = (2 * r) • E - g := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using hreverse
  calc
    (g - r • E) * (g - r • E) = (r ^ 2) • E - g * g' := by
      rw [hg']
      simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
        hEE, hEg, hgE]
      module
    _ = (r ^ 2 - ν) • E := by rw [hlength]; module

theorem centeredCorner_anticommutator (E g g' h h' : A) (r s q : ℝ)
    (hEE : E * E = E)
    (hEg : E * g = g) (hgE : g * E = g)
    (hEh : E * h = h) (hhE : h * E = h)
    (hgreverse : g + g' = (2 * r) • E)
    (hhreverse : h + h' = (2 * s) • E)
    (hmixed : g * h + h' * g' = (2 * q) • E) :
    (g - r • E) * (h - s • E) + (h - s • E) * (g - r • E) =
      (2 * (q - r * s)) • E := by
  have hg' : g' = (2 * r) • E - g := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using hgreverse
  have hh' : h' = (2 * s) • E - h := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using hhreverse
  calc
    (g - r • E) * (h - s • E) + (h - s • E) * (g - r • E) =
        (g * h + h' * g') - (2 * r * s) • E := by
      rw [hg', hh']
      simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
        hEE, hEg, hgE, hEh, hhE, smul_smul, smul_sub]
      module
    _ = (2 * (q - r * s)) • E := by rw [hmixed]; module

theorem shiftedCorner_triple_expansion (E x y z : A) (r s t : ℝ)
    (hEE : E * E = E)
    (hEx : E * x = x) (hxE : x * E = x)
    (hEy : E * y = y) (hyE : y * E = y)
    (hEz : E * z = z) (hzE : z * E = z) :
    (r • E + x) * (s • E + y) * (t • E + z) +
      (t • E - z) * (s • E - y) * (r • E - x) =
      (2 * r * s * t) • E + r • (y * z + z * y) +
      s • (x * z + z * x) + t • (x * y + y * x) +
      (x * y * z - z * y * x) := by
  simp only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc,
    mul_smul_comm, hEE, hEx, hxE, hEy, hyE, hEz, hzE, smul_add,
    smul_sub, smul_smul, mul_assoc]
  module

end AlbertSequential
