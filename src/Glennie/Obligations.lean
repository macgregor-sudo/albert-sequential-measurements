/- SPDX-License-Identifier: Apache-2.0
Descends from the Glennie layer of the Palomar entry PALOMAR-2026-10-16-000013
(https://github.com/macgregor-sudo/compact-albert-recognition, commit
40d3b344180d9ddb78aaa2876873377c1e631515; same contributor) through a later version of the
same code; see THIRD_PARTY_NOTICES. -/
/- Statements used as hypotheses or targets (`Prop`-valued definitions); nothing here
is assumed as an axiom. -/
module
public import Glennie.Native

@[expose] public section
namespace Glennie
noncomputable section

/-- An actual invertible real-linear map preserving the native product and trace.
No orbit, spectral, pair-reduction, or endpoint conclusion is a structure field. -/
structure CompactAutomorphism where
  equiv : Albert ≃ₗ[ℝ] Albert
  map_jordan : ∀ x y, equiv (jordan x y) = jordan (equiv x) (equiv y)
  map_trace : ∀ x, trace (equiv x) = trace x

def IsDiagonal (x : Albert) : Prop := x.o01 = 0 ∧ x.o02 = 0 ∧ x.o12 = 0

/-- The fixed ordinary complex line is span(1,i) inside the first quaternion. -/
def OctInComplex (x : Octonion) : Prop := x.1.imJ = 0 ∧ x.1.imK = 0 ∧ x.2 = 0

def InComplexSector (x : Albert) : Prop :=
  OctInComplex x.o01 ∧ OctInComplex x.o02 ∧ OctInComplex x.o12

def CompactSpectralDecomposition : Prop := ∀ x : Albert,
  ∃ (p : Fin 3 → Albert) (a : Fin 3 → ℝ), Frame p ∧ x = ∑ i, a i • p i

/-- Includes every pair, with zero slots and repeated spectra. This statement is not proved here. -/
def UniversalPairReduction : Prop := ∀ x y : Albert,
  ∃ g : CompactAutomorphism, IsDiagonal (g.equiv x) ∧ InComplexSector (g.equiv y)

def transformTriple (x y z : Albert) (A : Matrix (Fin 3) (Fin 3) ℝ) : Fin 3 → Albert :=
  fun j => ∑ i, A i j • triple x y z i

def GeneratorCovariance : Prop := ∀ (x y z : Albert) (A : Matrix (Fin 3) (Fin 3) ℝ),
  phi (transformTriple x y z A 0) (transformTriple x y z A 1)
    (transformTriple x y z A 2) = A.det ^ 3 * phi x y z

def IndependentUnitShifts : Prop := ∀ (x y z : Albert) (a b c : ℝ),
  phi (x + a • (1 : Albert)) (y + b • (1 : Albert)) (z + c • (1 : Albert)) = phi x y z

end
end Glennie
