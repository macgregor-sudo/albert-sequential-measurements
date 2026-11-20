module

import NativeGenericGeneration

set_option warningAsError true

open AlbertSequential AlbertSequential.WindowProbability AlbertSequential.NativeAnalysis

example :
    IsOpen {p : Fin 4 → AlbertAtomSpace | GeneratesAlbert (fun i => (p i).val)} ∧
      Dense {p : Fin 4 → AlbertAtomSpace | GeneratesAlbert (fun i => (p i).val)} :=
  generating_fourAtoms_open_dense

#print axioms generating_fourAtoms_open_dense
