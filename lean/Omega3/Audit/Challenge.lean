import Mathlib

/-! Challenge for `lake comparator` (Ω ≤ 3 audit): the targets, written with Mathlib only. -/

/-- In every base `b ≥ 5` there are infinitely many `n` whose base-`b` digit list is a palindrome
and which have at most three prime factors counted with multiplicity (`n ≠ 0 ∧ Ω n ≤ 3`). -/
theorem palindromes_omega_le_three : ∀ b : ℕ, 5 ≤ b →
    {n : ℕ | (Nat.digits b n).reverse = Nat.digits b n ∧ Nat.IsAtMostAlmostPrime 3 n}.Infinite :=
  sorry

/-- Infinitely many palindromes `n` with `Ω(n) ≤ 3` and every prime factor above `n^{1/250}`. -/
theorem palindromes_omega_le_three_large_factors : ∀ b : ℕ, 5 ≤ b →
    {n : ℕ | (Nat.digits b n).reverse = Nat.digits b n ∧ Nat.IsAtMostAlmostPrime 3 n ∧
      ∀ p ∈ n.primeFactors, (n : ℝ) ^ ((1 : ℝ) / 250) < (p : ℝ)}.Infinite :=
  sorry

/-- Among the palindromes with `2N + 1` digits coprime to `b³ − b`, at least `c 3^N / log x`,
`x = b^{2N+1}`, have `Ω ≤ 3` and all prime factors `> x^{1/250}`. -/
theorem palindromes_omega_le_three_count : ∀ b : ℕ, 5 ≤ b → ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    c * (3 : ℝ) ^ N / Real.log ((b : ℝ) ^ (2 * N + 1)) ≤
    (Finset.card (((Finset.Ico (b ^ (2 * N)) (b ^ (2 * N + 1))).filter
        (fun n => (Nat.digits b n).reverse = Nat.digits b n ∧ Nat.Coprime n (b ^ 3 - b))).filter
        (fun n => ArithmeticFunction.cardFactors n ≤ 3 ∧
          ∀ p ∈ n.primeFactors, ((b : ℝ) ^ (2 * N + 1)) ^ ((1 : ℝ) / 250) < (p : ℝ))) : ℝ) :=
  sorry
