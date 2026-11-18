module

public import LemmaB.Algebra
public import Mathlib.Tactic.Abel

/-!
# Lemma B, part 2: the form `𝒬` on four frames, the operators `P_x`, path vectors

Paper: core `sec:cer`, "The form on four frames". `𝒱 = 𝒞⁴` with letters
`A = 0, B = 1, C = 2, D = 3`;
`𝒬(F, F') = Σ_{x,y} ⟨F_x, T_xy F'_y⟩_𝒞` with `T_AA = T_Ax = T_xA = 1`, `T_xx = m_x`,
`T_BC = ĥ_1ς, T_CB = ςĥ_1^*, T_CD = ĥ_2ς, T_DC = ςĥ_2^*, T_DB = ĥ_3ς, T_BD = ςĥ_3^*`;
`(P_x F)_x = m_x⁻¹ Σ_y T_xy F_y`, other components zero; `ξ = (1;0;0;0)`;
`û(w) = P_{w_k} ⋯ P_{w_1} ξ` for a word `w = (w_1, …, w_k)` in chronological order.
Proved here: `T_yx = T_xy^*`, symmetry of `𝒬`, `P_x² = P_x`, `𝒬`-self-adjointness of `P_x`,
`P_A ξ = ξ`, and `û(w) = (∏ m_{w_i})⁻¹ • ũ(w)` where the unnormalised `ũ(w)` has the single
frame component `T_{w_k w_{k-1}} ⋯ T_{w_1 A} 1` at the last letter.
-/

@[expose] public section

namespace LemmaB

variable {K : Type*} [Field K] (p : Params K)

/-- The model space `𝒱 = 𝒞⁴`, components indexed by the letters `A, B, C, D = 0, 1, 2, 3`. -/
abbrev V (K : Type*) := Fin 4 → C8 K

/-- `m_A = 1, m_B, m_C, m_D`. -/
def mOf : Fin 4 → K := ![1, p.mB, p.mC, p.mD]

/-- The blocks `T_xy` (acting on `𝒞` by left multiplication and `ς`). -/
def T : Fin 4 → Fin 4 → C8 K → C8 K :=
  ![![fun v => v, fun v => v, fun v => v, fun v => v],
    ![fun v => v, fun v => p.mB • v, fun v => h1 p (sig v), fun v => sig (h3s p v)],
    ![fun v => v, fun v => sig (h1s p v), fun v => p.mC • v, fun v => h2 p (sig v)],
    ![fun v => v, fun v => h3 p (sig v), fun v => sig (h2s p v), fun v => p.mD • v]]

theorem T_add (x y : Fin 4) (v w : C8 K) : T p x y (v + w) = T p x y v + T p x y w := by
  fin_cases x <;> fin_cases y <;>
    simp [T, h1, h2, h3, h1s, h2s, h3s, sig_add, sig_sub, sig_smul, eps1_add, eps2_add,
      eps3_add, smul_add] <;> abel

theorem T_smul (x y : Fin 4) (c : K) (v : C8 K) : T p x y (c • v) = c • T p x y v := by
  fin_cases x <;> fin_cases y <;>
    simp [T, h1, h2, h3, h1s, h2s, h3s, sig_add, sig_sub, sig_smul, eps1_smul, eps2_smul,
      eps3_smul, smul_add, smul_sub, smul_smul, mul_comm]

theorem T_zero (x y : Fin 4) : T p x y 0 = 0 := by
  simpa using T_smul p x y 0 0

theorem T_diag (x : Fin 4) (v : C8 K) : T p x x v = mOf p x • v := by
  fin_cases x <;> simp [T, mOf]

/-- `T_xy` as a linear map. -/
def Tl (x y : Fin 4) : C8 K →ₗ[K] C8 K where
  toFun := T p x y
  map_add' := T_add p x y
  map_smul' := T_smul p x y

@[simp] theorem Tl_apply (x y : Fin 4) (v : C8 K) : Tl p x y v = T p x y v := rfl

/-- `T_yx = T_xy^*` with respect to `⟨·,·⟩_𝒞` (from skewness of `ε_a` and self-adjointness
of `ς`). -/
theorem T_adj (x y : Fin 4) (v w : C8 K) : W p v (T p x y w) = W p (T p y x v) w := by
  fin_cases x <;> fin_cases y <;>
    simp [T, h1, h2, h3, h1s, h2s, h3s, sig_add, sig_sub, sig_smul, W_add_left, W_add_right,
      W_sub_left, W_sub_right, W_smul_left, W_smul_right, W_sig, W_eps1, W_eps2, W_eps3] <;>
    ring

/-- The source map `(T F)_x = Σ_y T_xy F_y`. -/
def src (F : V K) (x : Fin 4) : C8 K := ∑ y, T p x y (F y)

/-- The form `𝒬(F, F') = Σ_{x,y} ⟨F_x, T_xy F'_y⟩_𝒞`. -/
def Q (F F' : V K) : K := ∑ x, ∑ y, W p (F x) (T p x y (F' y))

theorem W_sum_right {ι : Type*} (s : Finset ι) (v : C8 K) (f : ι → C8 K) :
    W p v (∑ i ∈ s, f i) = ∑ i ∈ s, W p v (f i) := by
  show Wl p v (∑ i ∈ s, f i) = ∑ i ∈ s, Wl p v (f i)
  exact map_sum _ _ _

theorem W_sum_left {ι : Type*} (s : Finset ι) (f : ι → C8 K) (w : C8 K) :
    W p (∑ i ∈ s, f i) w = ∑ i ∈ s, W p (f i) w := by
  rw [W_symm, W_sum_right]
  exact Finset.sum_congr rfl fun i _ => W_symm p _ _

/-- `𝒬(F', F) = Σ_x ⟨F'_x, (T F)_x⟩_𝒞`. -/
theorem Q_eq_src (F F' : V K) : Q p F F' = ∑ x, W p (F x) (src p F' x) := by
  simp only [Q, src, W_sum_right]

/-- `𝒬` is symmetric (because `T_yx = T_xy^*` and `⟨·,·⟩_𝒞` is symmetric). -/
theorem Q_symm (F F' : V K) : Q p F F' = Q p F' F := by
  simp only [Q]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  rw [T_adj, W_symm]

theorem Q_add_left (F G F' : V K) : Q p (F + G) F' = Q p F F' + Q p G F' := by
  simp only [Q, Pi.add_apply, W_add_left, Finset.sum_add_distrib]

theorem Q_smul_left (c : K) (F F' : V K) : Q p (c • F) F' = c * Q p F F' := by
  simp only [Q, Pi.smul_apply, W_smul_left, Finset.mul_sum]

theorem Q_add_right (F F' G' : V K) : Q p F (F' + G') = Q p F F' + Q p F G' := by
  rw [Q_symm, Q_add_left, Q_symm p F' F, Q_symm p G' F]

theorem Q_smul_right (c : K) (F F' : V K) : Q p F (c • F') = c * Q p F F' := by
  rw [Q_symm, Q_smul_left, Q_symm]

/-- `𝒬` as a bilinear map. -/
def Ql : V K →ₗ[K] V K →ₗ[K] K :=
  LinearMap.mk₂ K (Q p) (Q_add_left p) (Q_smul_left p) (Q_add_right p) (Q_smul_right p)

@[simp] theorem Ql_apply (F F' : V K) : Ql p F F' = Q p F F' := rfl

/-- The operators `P_x`. -/
def P (x : Fin 4) (F : V K) : V K := Pi.single x ((mOf p x)⁻¹ • src p F x)

/-- Unnormalised `P̃_x F = m_x P_x F`. -/
def Pt (x : Fin 4) (F : V K) : V K := Pi.single x (src p F x)

/-- `ξ = (1; 0; 0; 0)`. -/
def xi : V K := Pi.single 0 one8

theorem src_single (x y : Fin 4) (v : C8 K) : src p (Pi.single y v) x = T p x y v := by
  unfold src
  rw [Finset.sum_eq_single y]
  · simp
  · intro z _ hz; rw [Pi.single_eq_of_ne hz, T_zero]
  · intro h; exact absurd (Finset.mem_univ y) h

theorem src_add (F G : V K) (x : Fin 4) : src p (F + G) x = src p F x + src p G x := by
  simp only [src, Pi.add_apply, T_add, Finset.sum_add_distrib]

theorem src_smul (c : K) (F : V K) (x : Fin 4) : src p (c • F) x = c • src p F x := by
  simp only [src, Pi.smul_apply, T_smul, Finset.smul_sum]

/-- `P_A ξ = ξ`. -/
theorem P_A_xi : P p 0 (xi) = (xi : V K) := by
  unfold P xi
  rw [src_single]
  simp [T, mOf]

/-- `P_x² = P_x` (needs `m_x ≠ 0`). -/
theorem P_idem (x : Fin 4) (hm : mOf p x ≠ 0) (F : V K) : P p x (P p x F) = P p x F := by
  unfold P
  rw [src_single, T_diag, smul_smul, inv_mul_cancel₀ hm, one_smul]

/-- `P_x` is `𝒬`-self-adjoint (for every value of `m_x`, `0⁻¹ = 0` included). -/
theorem P_selfadj (x : Fin 4) (F F' : V K) : Q p (P p x F) F' = Q p F (P p x F') := by
  rw [Q_eq_src, Q_eq_src]
  unfold P
  simp only [src_single]
  rw [Finset.sum_eq_single x (fun z _ hz => by rw [Pi.single_eq_of_ne hz]; simp [W]) (by simp)]
  simp only [Pi.single_eq_same]
  set s := src p F' x
  clear_value s
  simp only [W_smul_left, T_smul, W_smul_right, src, W_sum_left, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [T_adj]

/-- Path vectors `û(w) = P_{w_k} ⋯ P_{w_1} ξ`, the word `w` in chronological order. -/
def uhat (w : List (Fin 4)) : V K := w.foldl (fun F x => P p x F) xi

/-- Unnormalised path vectors `ũ(w) = P̃_{w_k} ⋯ P̃_{w_1} ξ`. -/
def utilde (w : List (Fin 4)) : V K := w.foldl (fun F x => Pt p x F) xi

/-- Last letter and amplitude `T_{w_k w_{k-1}} ⋯ T_{w_1 A} 1` of a word. -/
def ampAux (s : Fin 4 × C8 K) (w : List (Fin 4)) : Fin 4 × C8 K :=
  w.foldl (fun s x => (x, T p x s.1 s.2)) s

def frameOf (w : List (Fin 4)) : Fin 4 := (ampAux p (0, one8) w).1
def amp (w : List (Fin 4)) : C8 K := (ampAux p (0, one8) w).2

theorem Pt_single (x y : Fin 4) (v : C8 K) : Pt p x (Pi.single y v) = Pi.single x (T p x y v) := by
  simp [Pt, src_single]

theorem foldl_Pt_single (w : List (Fin 4)) (y : Fin 4) (v : C8 K) :
    w.foldl (fun F x => Pt p x F) (Pi.single y v) =
      Pi.single (ampAux p (y, v) w).1 (ampAux p (y, v) w).2 := by
  induction w generalizing y v with
  | nil => rfl
  | cons x w ih => simp only [List.foldl, Pt_single, ampAux] at ih ⊢; exact ih x _

/-- `ũ(w)` has the single component `amp w` at the frame `frameOf w` (its last letter). -/
theorem utilde_eq (w : List (Fin 4)) : utilde p w = Pi.single (frameOf p w) (amp p w) :=
  foldl_Pt_single p w 0 one8

theorem Pt_smul (x : Fin 4) (c : K) (F : V K) : Pt p x (c • F) = c • Pt p x F := by
  simp [Pt, src_smul, Pi.single_smul]

theorem P_eq (x : Fin 4) (F : V K) : P p x F = (mOf p x)⁻¹ • Pt p x F := by
  simp [P, Pt, Pi.single_smul]

theorem foldl_P (w : List (Fin 4)) (c : K) (F : V K) :
    w.foldl (fun F x => P p x F) (c • F) =
      (c * ((w.map (mOf p)).prod)⁻¹) • w.foldl (fun F x => Pt p x F) F := by
  induction w generalizing c F with
  | nil => simp
  | cons x w ih =>
    simp only [List.foldl, List.map_cons, List.prod_cons]
    rw [P_eq, Pt_smul, smul_smul, ih, mul_inv]
    congr 1
    ring

/-- `û(w) = (∏_i m_{w_i})⁻¹ ũ(w)`. -/
theorem uhat_eq (w : List (Fin 4)) :
    uhat p w = ((w.map (mOf p)).prod)⁻¹ • utilde p w := by
  have := foldl_P p w 1 xi
  simpa [uhat, utilde] using this

end LemmaB
