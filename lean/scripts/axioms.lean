import Palprimes
/-! Run with `lake env lean scripts/axioms.lean`. Expected output: only `propext`,
`Classical.choice`, `Quot.sound` (no `sorryAx`, no `Lean.ofReduceBool`). -/
#print axioms Palprimes.infinite_palindromes_Omega_le_five
#print axioms Palprimes.almostPalprimesInfinite_five
#print axioms Palprimes.many_palindromes_Omega_le_five
#print axioms Palprimes.infinite_palindromes_Omega_le_five_large_factors
#print axioms Palprimes.MT.infinite_palindromes_Omega_le_four
#print axioms Palprimes.MT.almostPalprimesInfinite_four
