module

public import NativeSquareCone
public import Interfaces.Geometry

/-! Basic maps for the existing shared native automorphism structure. No new
automorphism interface, orbit assumption or Jordan law is introduced. -/

@[expose] public section
noncomputable section
namespace AlbertSequential.NativeAnalysis

def quadraticMapLinear (q : Albert) : Albert →ₗ[ℝ] Albert where
  toFun := quadraticMap q
  map_add' := quadraticMap_add_right q
  map_smul' r x := quadraticMap_smul_right r q x

@[simp] theorem quadraticMapLinear_apply (q x : Albert) :
    quadraticMapLinear q x = quadraticMap q x := rfl

def nativeAutomorphismIdentity : NativeAlbertAutomorphism where
  linearEquiv := LinearEquiv.refl ℝ Albert
  preserves_product _ _ := rfl
  preserves_unit := rfl
  preserves_trace _ := rfl

@[simp] theorem nativeAutomorphismIdentity_apply (x : Albert) :
    nativeAutomorphismIdentity.linearEquiv x = x := rfl

theorem nativeAutomorphism_pairing (g : NativeAlbertAutomorphism) (x y : Albert) :
    tracePairing (g.linearEquiv x) (g.linearEquiv y) = tracePairing x y := by
  unfold tracePairing
  rw [← g.preserves_product, g.preserves_trace]

theorem nativeAutomorphism_quadraticMap (g : NativeAlbertAutomorphism) (x y : Albert) :
    g.linearEquiv (quadraticMap x y) = quadraticMap (g.linearEquiv x) (g.linearEquiv y) := by
  simp only [quadraticMap, two_smul, map_sub, map_add, g.preserves_product]

theorem nativeAutomorphism_isAtom (g : NativeAlbertAutomorphism) (p : Albert)
    (hp : IsAtom p) : IsAtom (g.linearEquiv p) := by
  constructor
  · rw [← g.preserves_product, hp.1]
  · rw [g.preserves_trace, hp.2]

def nativeAutomorphismInverse (g : NativeAlbertAutomorphism) : NativeAlbertAutomorphism where
  linearEquiv := g.linearEquiv.symm
  preserves_product x y := by
    apply g.linearEquiv.injective
    rw [LinearEquiv.apply_symm_apply, g.preserves_product,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  preserves_unit := by
    apply g.linearEquiv.injective
    rw [LinearEquiv.apply_symm_apply, g.preserves_unit]
  preserves_trace x := by
    have h := g.preserves_trace (g.linearEquiv.symm x)
    simpa only [LinearEquiv.apply_symm_apply] using h.symm

/-- Composition applies h first, then g. -/
def nativeAutomorphismComposition (g h : NativeAlbertAutomorphism) : NativeAlbertAutomorphism where
  linearEquiv := h.linearEquiv.trans g.linearEquiv
  preserves_product x y := by
    simp only [LinearEquiv.trans_apply, g.preserves_product, h.preserves_product]
  preserves_unit := by
    simp only [LinearEquiv.trans_apply, h.preserves_unit, g.preserves_unit]
  preserves_trace x := by
    simp only [LinearEquiv.trans_apply, g.preserves_trace, h.preserves_trace]

@[simp] theorem nativeAutomorphismInverse_apply (g : NativeAlbertAutomorphism) (x : Albert) :
    (nativeAutomorphismInverse g).linearEquiv x = g.linearEquiv.symm x := rfl

@[simp] theorem nativeAutomorphismComposition_apply (g h : NativeAlbertAutomorphism) (x : Albert) :
    (nativeAutomorphismComposition g h).linearEquiv x = g.linearEquiv (h.linearEquiv x) := rfl

/-- Transport an actual recovered compact automorphism through the literal
coordinate equivalence, preserving the existing shared structure. -/
def recoveredNativeAutomorphism (g : Glennie.CompactAutomorphism) : NativeAlbertAutomorphism where
  linearEquiv := recoveredCoordinateEquiv.trans (g.equiv.trans recoveredCoordinateEquiv.symm)
  preserves_product x y := by
    apply recoveredCoordinateEquiv.injective
    change g.equiv (recoveredCoordinateEquiv (jordanMul x y)) =
      recoveredCoordinateEquiv (jordanMul
        (recoveredCoordinateEquiv.symm (g.equiv (recoveredCoordinateEquiv x)))
        (recoveredCoordinateEquiv.symm (g.equiv (recoveredCoordinateEquiv y))))
    rw [recoveredCoordinateEquiv_jordanMul, g.map_jordan,
      recoveredCoordinateEquiv_jordanMul, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
  preserves_unit := by
    apply recoveredCoordinateEquiv.injective
    change g.equiv (recoveredCoordinateEquiv albertUnit) = recoveredCoordinateEquiv albertUnit
    rw [recoveredCoordinateEquiv_unit, g.map_unit]
  preserves_trace x := by
    have h := recoveredCoordinateEquiv_trace
      (recoveredCoordinateEquiv.symm (g.equiv (recoveredCoordinateEquiv x)))
    rw [LinearEquiv.apply_symm_apply, g.map_trace, recoveredCoordinateEquiv_trace] at h
    exact h.symm

@[simp] theorem recoveredNativeAutomorphism_apply (g : Glennie.CompactAutomorphism) (x : Albert) :
    (recoveredNativeAutomorphism g).linearEquiv x =
      recoveredCoordinateEquiv.symm (g.equiv (recoveredCoordinateEquiv x)) := rfl

end AlbertSequential.NativeAnalysis
