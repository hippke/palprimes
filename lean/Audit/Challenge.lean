import Mathlib

/-! Challenge for `lake comparator`: the target, written with Mathlib only. -/

/-- In every base `b ≥ 2` there are infinitely many `n` whose base-`b` digit list is a palindrome
and which have at most five prime factors counted with multiplicity (`n ≠ 0 ∧ Ω n ≤ 5`). -/
theorem palindromes_omega_le_five : ∀ b : ℕ, 2 ≤ b →
    {n : ℕ | (Nat.digits b n).reverse = Nat.digits b n ∧ Nat.IsAtMostAlmostPrime 5 n}.Infinite :=
  sorry
