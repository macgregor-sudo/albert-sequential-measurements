/- SPDX-License-Identifier: Apache-2.0 -/
module

public import RealMatrixComplexification
public import BinarySpectralSupport

/-! Choose support and complementary-root data over the ACTUAL real matrices,
then embed the complete data bundle. No complex eigenbasis is assumed real. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential
open scoped Matrix ComplexOrder
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem complexifyMatrix_conjTranspose (A : Matrix n n ℝ) :
    complexifyMatrix A.conjTranspose = (complexifyMatrix A).conjTranspose :=
  complexifyMatrix_transpose A

namespace FiniteSpectralSupport

/-- Destination equality is explicit, while each data matrix stays LITERALLY
entrywise ofReal; this avoids opaque casts of the support data itself. -/
def toComplex {A : Matrix n n ℝ} {B : Matrix n n ℂ}
    (s : FiniteSpectralSupport A) (hA : complexifyMatrix A = B) : FiniteSpectralSupport B where
  root := complexifyMatrix s.root
  inverseRoot := complexifyMatrix s.inverseRoot
  support := complexifyMatrix s.support
  root_positive := (complexifyMatrix_posSemidef_iff _).mpr s.root_positive
  root_hermitian := by
    simpa only [complexifyMatrix_conjTranspose] using congrArg complexifyMatrix s.root_hermitian
  inverse_hermitian := by
    simpa only [complexifyMatrix_conjTranspose] using congrArg complexifyMatrix s.inverse_hermitian
  support_hermitian := by
    simpa only [complexifyMatrix_conjTranspose] using congrArg complexifyMatrix s.support_hermitian
  root_sq := by
    simpa only [complexifyMatrix_mul, hA] using congrArg complexifyMatrix s.root_sq
  inverse_root := by
    simpa only [complexifyMatrix_mul] using congrArg complexifyMatrix s.inverse_root
  root_inverse := by
    simpa only [complexifyMatrix_mul] using congrArg complexifyMatrix s.root_inverse
  inverse_effect := by
    simpa only [complexifyMatrix_mul, hA] using congrArg complexifyMatrix s.inverse_effect
  support_sq := by
    simpa only [complexifyMatrix_mul] using congrArg complexifyMatrix s.support_sq
  effect_complement := by
    simpa only [complexifyMatrix_mul, complexifyMatrix_sub, complexifyMatrix_one,
      complexifyMatrix_zero, hA] using congrArg complexifyMatrix s.effect_complement
  root_complement := by
    simpa only [complexifyMatrix_mul, complexifyMatrix_sub, complexifyMatrix_one,
      complexifyMatrix_zero] using congrArg complexifyMatrix s.root_complement

theorem toComplex_entries_real {A : Matrix n n ℝ} {B : Matrix n n ℂ}
    (s : FiniteSpectralSupport A) (hA : complexifyMatrix A = B) :
    (∀ i j, ((s.toComplex hA).root i j).im=0) ∧
    (∀ i j, ((s.toComplex hA).inverseRoot i j).im=0) ∧
    (∀ i j, ((s.toComplex hA).support i j).im=0) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

end FiniteSpectralSupport

namespace BinarySpectralSupport

def toComplex {A : Matrix n n ℝ} {B : Matrix n n ℂ}
    (s : BinarySpectralSupport A) (hA : complexifyMatrix A = B) : BinarySpectralSupport B where
  yes := s.yes.toComplex hA
  no := s.no.toComplex (by rw [complexifyMatrix_sub, complexifyMatrix_one, hA])
  roots_commute := by
    change complexifyMatrix s.yes.root * complexifyMatrix s.no.root =
      complexifyMatrix s.no.root * complexifyMatrix s.yes.root
    simpa only [complexifyMatrix_mul] using congrArg complexifyMatrix s.roots_commute

theorem toComplex_entries_real {A : Matrix n n ℝ} {B : Matrix n n ℂ}
    (s : BinarySpectralSupport A) (hA : complexifyMatrix A = B) :
    (∀ i j, ((s.toComplex hA).yes.root i j).im=0) ∧
    (∀ i j, ((s.toComplex hA).no.root i j).im=0) ∧
    (∀ i j, ((s.toComplex hA).yes.inverseRoot i j).im=0) ∧
    (∀ i j, ((s.toComplex hA).no.inverseRoot i j).im=0) ∧
    (∀ i j, ((s.toComplex hA).yes.support i j).im=0) ∧
    (∀ i j, ((s.toComplex hA).no.support i j).im=0) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

end BinarySpectralSupport

def realFiniteSpectralSupport {d : ℕ} {A : ComplexMatrix d}
    (hA : A.PosSemidef) (hreal : HasRealEntries A) : FiniteSpectralSupport A :=
  (finiteSpectralSupport (realPartMatrix_positive_of_real hA hreal)).toComplex
    (complexify_realPart_of_hasRealEntries A hreal)

theorem realFiniteSpectralSupport_real {d : ℕ} {A : ComplexMatrix d}
    (hA : A.PosSemidef) (hreal : HasRealEntries A) :
    HasRealEntries (realFiniteSpectralSupport hA hreal).root ∧
    HasRealEntries (realFiniteSpectralSupport hA hreal).inverseRoot ∧
    HasRealEntries (realFiniteSpectralSupport hA hreal).support :=
  FiniteSpectralSupport.toComplex_entries_real _ _

def realBinarySpectralSupport {d : ℕ} {A : ComplexMatrix d}
    (hA : A.PosSemidef) (hAc : (1-A).PosSemidef) (hreal : HasRealEntries A) :
    BinarySpectralSupport A := by
  let R := realPartMatrix A
  have hR : R.PosSemidef := realPartMatrix_positive_of_real hA hreal
  have hRc : (1-R).PosSemidef := by
    apply (complexifyMatrix_posSemidef_iff _).mp
    change (complexifyMatrix (1-realPartMatrix A)).PosSemidef
    rw [complexifyMatrix_sub, complexifyMatrix_one,
      complexify_realPart_of_hasRealEntries A hreal]
    exact hAc
  exact (binarySpectralSupport hR hRc).toComplex (complexify_realPart_of_hasRealEntries A hreal)

theorem realBinarySpectralSupport_real {d : ℕ} {A : ComplexMatrix d}
    (hA : A.PosSemidef) (hAc : (1-A).PosSemidef) (hreal : HasRealEntries A) :
    HasRealEntries (realBinarySpectralSupport hA hAc hreal).yes.root ∧
    HasRealEntries (realBinarySpectralSupport hA hAc hreal).no.root ∧
    HasRealEntries (realBinarySpectralSupport hA hAc hreal).yes.inverseRoot ∧
    HasRealEntries (realBinarySpectralSupport hA hAc hreal).no.inverseRoot ∧
    HasRealEntries (realBinarySpectralSupport hA hAc hreal).yes.support ∧
    HasRealEntries (realBinarySpectralSupport hA hAc hreal).no.support :=
  BinarySpectralSupport.toComplex_entries_real _ _

end AlbertSequential
