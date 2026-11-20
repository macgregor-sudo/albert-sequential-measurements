/- SPDX-License-Identifier: Apache-2.0 -/
module

public import AlbertDerivationDimension

public section
noncomputable section

namespace AlbertSequential

open NativeAnalysis

/-- The actual linearized idempotent equation at an Albert atom. -/
def albertAtomTangent (p : Albert) : Submodule ℝ Albert where
  carrier := {x | x = (2 : ℝ) • jordanMul p x}
  zero_mem' := by simp [jordanMul_zero_right]
  add_mem' {x y} hx hy := by
    change x = (2 : ℝ) • jordanMul p x at hx
    change y = (2 : ℝ) • jordanMul p y at hy
    change x + y = (2 : ℝ) • jordanMul p (x+y)
    rw [jordanMul_add_right, smul_add, ← hx, ← hy]
  smul_mem' r x hx := by
    change x = (2 : ℝ) • jordanMul p x at hx
    change r • x = (2 : ℝ) • jordanMul p (r • x)
    rw [jordanMul_smul_right, smul_comm (2 : ℝ) r, ← hx]

private theorem tangentDiagonal_zero (x : albertAtomTangent (diagAtom 0)) (i : Fin 3) : x.val.1 i = 0 := by
  have hx : x.val = (2 : ℝ) • jordanMul (diagAtom 0) x.val := x.property
  have h := congrArg (fun y : Albert => y.1 i) hx
  change x.val.1 i = 2 * (jordanMul (diagAtom 0) x.val).1 i at h
  rw [jordanMul_diagAtom_diagonal] at h
  split at h <;> linarith

private theorem tangentThird_zero (x : albertAtomTangent (diagAtom 0)) : x.val.2 2 = 0 := by
  have hx : x.val = (2 : ℝ) • jordanMul (diagAtom 0) x.val := x.property
  have h := congrArg (fun y : Albert => y.2 2) hx
  change x.val.2 2 = (2 : ℝ) • (jordanMul (diagAtom 0) x.val).2 2 at h
  rw [jordanMul_diagAtom_offDiagonal] at h
  simpa [derivationSlotWeight,derivationFirst,derivationSecond] using h

private def tangentDiag0Equiv : albertAtomTangent (diagAtom 0) ≃ₗ[ℝ] Octonion × Octonion :=
  LinearEquiv.ofBijective
    { toFun := fun x => (x.val.2 0,x.val.2 1)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } (by
        constructor
        · intro x y h
          apply Subtype.ext
          apply Prod.ext
          · funext i; rw [tangentDiagonal_zero,tangentDiagonal_zero]
          · funext i
            fin_cases i
            · exact congrArg Prod.fst h
            · exact congrArg Prod.snd h
            · exact (tangentThird_zero x).trans (tangentThird_zero y).symm
        · rintro ⟨u,v⟩
          let x := derivationUpperSlot 0 u + derivationUpperSlot 1 v
          have hx : x = (2 : ℝ) • jordanMul (diagAtom 0) x := by
            dsimp only [x]
            rw [jordanMul_add_right,jordanMul_diagAtom_upperSlot,jordanMul_diagAtom_upperSlot]
            norm_num [derivationSlotWeight,derivationFirst,derivationSecond]
            module
          exact ⟨⟨x,hx⟩, by
            change (derivationSlotCoord 0 x,derivationSlotCoord 1 x) = (u,v)
            simp [x]⟩)

private def tangentAutoEquiv (g : NativeAlbertAutomorphism) (p : Albert) :
    albertAtomTangent p ≃ₗ[ℝ] albertAtomTangent (g.linearEquiv p) :=
  LinearEquiv.ofBijective
    { toFun := fun x => ⟨g.linearEquiv x.val, by
        have hx : x.val = (2 : ℝ) • jordanMul p x.val := x.property
        have h := congrArg g.linearEquiv hx
        rwa [map_smul,g.preserves_product] at h⟩
      map_add' x y := Subtype.ext (g.linearEquiv.map_add x.val y.val)
      map_smul' r x := Subtype.ext (g.linearEquiv.map_smul r x.val) } (by
        constructor
        · intro x y h
          exact Subtype.ext (g.linearEquiv.injective (congrArg Subtype.val h))
        · intro y
          let x := g.linearEquiv.symm y.val
          have hxg : g.linearEquiv x = y.val := g.linearEquiv.apply_symm_apply y.val
          have hx : x = (2 : ℝ) • jordanMul p x := by
            apply g.linearEquiv.injective
            rw [map_smul,g.preserves_product,hxg]
            exact y.property
          exact ⟨⟨x,hx⟩, Subtype.ext hxg⟩)

theorem finrank_albertAtomTangent (p : Albert) (hp : IsAtom p) : Module.finrank ℝ (albertAtomTangent p) = 16 := by
  obtain ⟨g,hg⟩ := atom_to_diagAtom0 p hp
  rw [(tangentAutoEquiv g p).finrank_eq,hg,tangentDiag0Equiv.finrank_eq,
    octonionPairCoordinates.finrank_eq,Module.finrank_fintype_fun_eq_card]
  exact spinorCoordinate_card

theorem albertAtomTangent_trace_zero (p : Albert) (hp : IsAtom p) (x : albertAtomTangent p) :
    albertTrace x.val = 0 := by
  obtain ⟨g,hg⟩ := atom_to_diagAtom0 p hp
  have hx : g.linearEquiv x.val ∈ albertAtomTangent (diagAtom 0) := by
    rw [← hg]
    exact ((tangentAutoEquiv g p) x).property
  have hd (i : Fin 3) : (g.linearEquiv x.val).1 i = 0 :=
    tangentDiagonal_zero ⟨_, hx⟩ i
  rw [← g.preserves_trace x.val]
  simp [albertTrace,hd]

def derivationMenuTangent {ι : Type*} (menu : ι → Albert) (hp : ∀ i, IsAtom (menu i)) :
    AlbertDerivation →ₗ[ℝ] ((i : ι) → albertAtomTangent (menu i)) where
  toFun D i := ⟨D.val (menu i), by
    change D.val (menu i) = (2 : ℝ) • jordanMul (menu i) (D.val (menu i))
    have h := albertDerivation_mul D (menu i) (menu i)
    rw [(hp i).1,jordanMul_comm (D.val (menu i)) (menu i)] at h
    simpa only [two_smul ℝ] using h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem derivationMenuTangent_injective {ι : Type*} (menu : ι → Albert) (hp : ∀ i, IsAtom (menu i))
    (hgen : GeneratesAlbert menu) : Function.Injective (derivationMenuTangent menu hp) := by
  intro D E he
  let F := D-E
  have hF : derivationMenuTangent menu hp F = 0 := by
    change derivationMenuTangent menu hp (D-E) = 0
    rw [map_sub (derivationMenuTangent menu hp) D E,he,sub_self]
  have hmenu (i : ι) : F.val (menu i) = 0 := congrArg Subtype.val (congrFun hF i)
  let B : NativeJordanSubalgebra :=
    { carrier := F.val.ker
      unit_mem := albertDerivation_unit F
      product_mem := by
        intro x hx y hy
        change F.val x = 0 at hx
        change F.val y = 0 at hy
        change F.val (jordanMul x y) = 0
        rw [albertDerivation_mul,hx,hy,jordanMul_zero_left,jordanMul_zero_right,zero_add] }
  apply sub_eq_zero.mp
  apply Subtype.ext
  ext x
  exact hgen x B hmenu

/-- The linearized quotient on the generating four-atom locus. -/
theorem finrank_albertGeneratingLinearizedQuotient (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hgen : GeneratesAlbert p) :
    Module.finrank ℝ (((i : Fin 4) → albertAtomTangent (p i)) ⧸ (derivationMenuTangent p hp).range) = 12 := by
  let : FiniteDimensional ℝ Albert := nativeAlbertModuleFinite
  let f := derivationMenuTangent p hp
  have hr : Module.finrank ℝ f.range = 52 :=
    (LinearEquiv.ofInjective _ (derivationMenuTangent_injective p hp hgen)).finrank_eq.symm.trans
      finrank_albertDerivation
  have hm : Module.finrank ℝ ((i : Fin 4) → albertAtomTangent (p i)) = 64 := by
    rw [Module.finrank_pi_fintype]
    simp [finrank_albertAtomTangent, hp]
  have h := f.range.finrank_quotient_add_finrank
  rw [hr,hm] at h
  exact Nat.add_right_cancel (h.trans (show 12 + 52 = 64 by decide).symm)

end AlbertSequential
