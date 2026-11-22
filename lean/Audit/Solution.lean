import Mathlib
import Palprimes.AlmostPrime.OmegaLeFiveCount
import Palprimes.Omega4.Final

/-! Solution for `lake comparator`. -/

theorem palindromes_omega_le_five : ∀ b : ℕ, 2 ≤ b →
    {n : ℕ | (Nat.digits b n).reverse = Nat.digits b n ∧ Nat.IsAtMostAlmostPrime 5 n}.Infinite :=
  fun b hb => Palprimes.infinite_palindromes_Omega_le_five b hb

/-- Infinitely many palindromes `n` with `Ω(n) ≤ 5` and every prime factor at least `n^{1/20}`. -/
theorem palindromes_omega_le_five_large_factors : ∀ b : ℕ, 2 ≤ b →
    {n : ℕ | (Nat.digits b n).reverse = Nat.digits b n ∧ Nat.IsAtMostAlmostPrime 5 n ∧
      ∀ p ∈ n.primeFactors, (n : ℝ) ^ ((1 : ℝ) / 20) ≤ (p : ℝ)}.Infinite :=
  fun b hb => Palprimes.infinite_palindromes_Omega_le_five_large_factors b hb

open Classical in
/-- Among the palindromes with `2N + 1` digits coprime to `b³ − b`, at least a proportion
`1/(40 log x)`, `x = b^{2N+1}`, have `Ω ≤ 5` and all prime factors `≥ x^{1/20}`. -/
theorem palindromes_omega_le_five_count : ∀ b : ℕ, 2 ≤ b → ∃ N₀ : ℕ, ∀ N ≥ N₀,
    1 / 40 * ((Finset.card ((Finset.Ico (b ^ (2 * N)) (b ^ (2 * N + 1))).filter
        (fun n => (Nat.digits b n).reverse = Nat.digits b n ∧ Nat.Coprime n (b ^ 3 - b))) : ℝ) /
      Real.log ((b : ℝ) ^ (2 * N + 1))) ≤
    (Finset.card (((Finset.Ico (b ^ (2 * N)) (b ^ (2 * N + 1))).filter
        (fun n => (Nat.digits b n).reverse = Nat.digits b n ∧ Nat.Coprime n (b ^ 3 - b))).filter
        (fun n => Nat.IsAtMostAlmostPrime 5 n ∧
          ∀ p ∈ n.primeFactors, ((b : ℝ) ^ (2 * N + 1)) ^ ((1 : ℝ) / 20) ≤ (p : ℝ))) : ℝ) :=
  fun b hb => Palprimes.many_palindromes_Omega_le_five b hb

/-- In every base `b ≥ 2` there are infinitely many palindromes with `Ω ≤ 4`. -/
theorem palindromes_omega_le_four : ∀ b : ℕ, 2 ≤ b →
    {n : ℕ | (Nat.digits b n).reverse = Nat.digits b n ∧ Nat.IsAtMostAlmostPrime 4 n}.Infinite :=
  fun b hb => Palprimes.MT.infinite_palindromes_Omega_le_four b hb
