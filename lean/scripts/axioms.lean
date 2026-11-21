import Palprimes
/-! Run with `lake env lean scripts/axioms.lean`. Expected output: only `propext`,
`Classical.choice`, `Quot.sound` (no `sorryAx`, no `Lean.ofReduceBool`). -/
#print axioms Palprimes.infinite_palindromes_Omega_le_five
#print axioms Palprimes.almostPalprimesInfinite_five
