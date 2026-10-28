/-
  Axiom check for the headline theorems. Building this file prints
  the axioms the proofs depend on. The expected output is only
  the three standard Lean axioms: `propext`, `Classical.choice`,
  `Quot.sound`, or a subset of them. Any other name here breaks
  the verified bar.
-/

import Proofs.RoundTrip
import Proofs.Resolve

#print axioms print_split
#print axioms split_print
#print axioms Uri.Proofs.removeDotSegments_noDots
#print axioms Uri.Proofs.removeDotSegments_idempotent
#print axioms Uri.Proofs.resolve_scheme
