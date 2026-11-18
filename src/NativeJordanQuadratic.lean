module

public import RealJordanPeirce
public import NativeJordanIdentity
public import Mathlib.Algebra.Module.TransferInstance

/-! A separate wrapper algebra binds the generic quadratic identities to the
literal compact native product. No Mul/One/Star instance is installed
on the sealed native Albert carrier. -/

@[expose] public section
noncomputable section
namespace AlbertSequential.NativeAnalysis

/-- This wrapper alone receives the Jordan ring operations. -/
structure NativeJordanElement where
  value : Albert

def nativeJordanEquiv : NativeJordanElement ≃ Albert where
  toFun := NativeJordanElement.value
  invFun := NativeJordanElement.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup NativeJordanElement := nativeJordanEquiv.addCommGroup

def nativeJordanAddEquiv : NativeJordanElement ≃+ Albert := nativeJordanEquiv.addEquiv

instance : Module ℝ NativeJordanElement := nativeJordanAddEquiv.module ℝ

instance : NonUnitalNonAssocCommRing NativeJordanElement :=
  { (inferInstance : AddCommGroup NativeJordanElement) with
  mul x y := ⟨jordanMul x.value y.value⟩
  left_distrib x y z := by
    apply nativeJordanEquiv.injective
    exact jordanMul_add_right x.value y.value z.value
  right_distrib x y z := by
    apply nativeJordanEquiv.injective
    exact jordanMul_add_left x.value y.value z.value
  zero_mul x := by
    apply nativeJordanEquiv.injective
    exact jordanMul_zero_left x.value
  mul_zero x := by
    apply nativeJordanEquiv.injective
    exact jordanMul_zero_right x.value
  mul_comm x y := by
    apply nativeJordanEquiv.injective
    exact jordanMul_comm x.value y.value }

instance : SMulCommClass ℝ NativeJordanElement NativeJordanElement where
  smul_comm r x y := by
    apply nativeJordanEquiv.injective
    exact (jordanMul_smul_right r x.value y.value).symm

instance : IsCommJordan NativeJordanElement where
  lmul_comm_rmul_rmul x y := by
    apply nativeJordanEquiv.injective
    exact jordan_identity x.value y.value

instance : One NativeJordanElement := ⟨⟨albertUnit⟩⟩

instance : MulOneClass NativeJordanElement where
  mul_one x := by
    apply nativeJordanEquiv.injective
    exact jordanMul_albertUnit_right x.value
  one_mul x := by
    apply nativeJordanEquiv.injective
    change jordanMul albertUnit x.value=x.value
    rw [jordanMul_comm]
    exact jordanMul_albertUnit_right x.value

@[simp] theorem nativeJordan_value_mul (x y : NativeJordanElement) :
    (x*y).value=jordanMul x.value y.value := rfl

@[simp] theorem nativeJordan_value_one : (1 : NativeJordanElement).value=albertUnit := rfl

/-- The scalar convention is bound explicitly: generic U uses real 2; native U
uses natural-number doubling. Both are the same actual additive operation. -/
theorem nativeJordan_quadraticRepresentation (a x : NativeJordanElement) :
    (RealJordan.quadraticRepresentation a x).value=quadraticMap a.value x.value := by
  change (2 : ℝ) • jordanMul a.value (jordanMul a.value x.value) -
      jordanMul (jordanMul a.value a.value) x.value = quadraticMap a.value x.value
  simp only [quadraticMap, two_smul]

/-- The fundamental formula on the actual native compact Albert algebra. -/
theorem quadraticMap_fundamental (a b x : Albert) :
    quadraticMap (quadraticMap a b) x=quadraticMap a (quadraticMap b (quadraticMap a x)) := by
  have h := congrArg NativeJordanElement.value
    (RealJordan.quadraticRepresentation_fundamental_apply
      (NativeJordanElement.mk a) (NativeJordanElement.mk b) (NativeJordanElement.mk x))
  simpa only [nativeJordan_quadraticRepresentation] using h

/-- Actual native idempotent projection, including q=0. -/
theorem quadraticMap_idempotent_comp (q x : Albert) (hq : jordanMul q q=q) :
    quadraticMap q (quadraticMap q x)=quadraticMap q x := by
  have hq' : (NativeJordanElement.mk q)*(NativeJordanElement.mk q)=NativeJordanElement.mk q := by
    apply nativeJordanEquiv.injective
    exact hq
  have h := congrArg NativeJordanElement.value
    (DFunLike.congr_fun
      (RealJordan.quadraticRepresentation_idempotent_comp (NativeJordanElement.mk q) hq')
      (NativeJordanElement.mk x))
  simpa only [LinearMap.comp_apply, nativeJordan_quadraticRepresentation] using h

/-- Actual native Peirce-one range, distinct from full geometric classification. -/
theorem quadraticMap_idempotent_range (q : Albert) (hq : jordanMul q q=q) :
    Set.range (quadraticMap q)={x | jordanMul q x=x} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change jordanMul q (quadraticMap q y)=quadraticMap q y
    have hq' : (NativeJordanElement.mk q)*(NativeJordanElement.mk q)=NativeJordanElement.mk q := by
      apply nativeJordanEquiv.injective
      exact hq
    have h := congrArg NativeJordanElement.value
      (RealJordan.mul_quadraticRepresentation_idempotent
        (NativeJordanElement.mk q) (NativeJordanElement.mk y) hq')
    simpa only [nativeJordan_value_mul, nativeJordan_quadraticRepresentation] using h
  · intro hx
    change jordanMul q x=x at hx
    refine ⟨x, ?_⟩
    simp only [quadraticMap, hq, hx, two_smul]
    abel

end AlbertSequential.NativeAnalysis
