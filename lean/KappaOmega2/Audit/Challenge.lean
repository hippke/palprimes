import Mathlib

/-! Challenge for `lake comparator` (Ω ≤ 2 for κ-palindromes, κ = 7/10, every base `b ≥ 3`): the targets, written
with Mathlib only. -/

/-- In every base `b ≥ 3` there are infinitely many `n` whose first `⌊7L/20⌋` base-`b` digits mirror the last ones
(`L` the number of digits) and with at most two prime factors counted with multiplicity. -/
theorem kappa_palindromes_omega_le_two (b : ℕ) (hb : 3 ≤ b) :
    {n : ℕ | (∀ i < 7 * (Nat.digits b n).length / 20,
        (Nat.digits b n).getD i 0 = (Nat.digits b n).getD ((Nat.digits b n).length - 1 - i) 0) ∧
      n ≠ 0 ∧ ArithmeticFunction.cardFactors n ≤ 2}.Infinite :=
  sorry

/-- Among the integers with `2N + 1` base-`b` digits, coprime to `b³ − b`, whose first `m = ⌊7(2N+1)/20⌋` digits
mirror the last ones, at least `c 2^m W / log x` (`W = b^{2N+1−2m}`, `x = b^{2N+1}`) have `Ω ≤ 2` and all prime
factors `> x^{1/100}`. -/
theorem kappa_palindromes_omega_le_two_count : ∀ b : ℕ, 3 ≤ b → ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    c * (2 : ℝ) ^ (7 * (2 * N + 1) / 20) * ((b ^ (2 * N + 1 - 2 * (7 * (2 * N + 1) / 20)) : ℕ) : ℝ) /
        Real.log ((b : ℝ) ^ (2 * N + 1)) ≤
    (Finset.card (((Finset.Ico (b ^ (2 * N)) (b ^ (2 * N + 1))).filter
        (fun n => (∀ i < 7 * (Nat.digits b n).length / 20,
            (Nat.digits b n).getD i 0 = (Nat.digits b n).getD ((Nat.digits b n).length - 1 - i) 0) ∧
          Nat.Coprime n (b ^ 3 - b))).filter
        (fun n => ArithmeticFunction.cardFactors n ≤ 2 ∧
          ∀ p ∈ n.primeFactors, ((b : ℝ) ^ (2 * N + 1)) ^ ((1 : ℝ) / 100) < (p : ℝ))) : ℝ) :=
  sorry
