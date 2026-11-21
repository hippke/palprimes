import Palprimes.Defs

/-! # Target statements of the project (definitions only, nothing is assumed)

`PalprimesInfinite b` is the goal of the project. The proved results establish instances of
`AlmostPalprimesInfinite k b`. -/

namespace Palprimes

/-- In base `b` there are infinitely many palindromic primes. -/
def PalprimesInfinite (b : ℕ) : Prop :=
  {p : ℕ | IsPalindrome b p ∧ p.Prime}.Infinite

/-- In base `b` there are infinitely many palindromes with at most `k` prime factors
(counted with multiplicity). -/
def AlmostPalprimesInfinite (k b : ℕ) : Prop :=
  {n : ℕ | IsPalindrome b n ∧ Nat.IsAtMostAlmostPrime k n}.Infinite

end Palprimes
