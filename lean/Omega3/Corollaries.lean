import Omega3.Skeleton

/-!
# Corollary of the counting form: large prime factors

`largeFactors_of_count : MainCount → MainLargeFactors`: in every base `b ≥ 5` there are infinitely many palindromes
`n` with `Ω(n) ≤ 3` all of whose prime factors exceed `n^{1/250}` (`n < x` and every prime factor is `> x^{1/250}`).
-/

set_option linter.style.longLine false

open Finset Real
open scoped ArithmeticFunction.Omega

namespace Omega3

open Palprimes

/-- Infinitely many palindromes with `Ω ≤ 3` and every prime factor `> n^{1/250}`. -/
def MainLargeFactors : Prop :=
  ∀ b : ℕ, 5 ≤ b → {n : ℕ | IsPalindrome b n ∧ Nat.IsAtMostAlmostPrime 3 n ∧
    ∀ p ∈ n.primeFactors, (n : ℝ) ^ ((1 : ℝ) / 250) < (p : ℝ)}.Infinite

theorem largeFactors_of_count (h : MainCount) : MainLargeFactors := by
  intro b hb
  classical
  obtain ⟨c, hc, N₀, hN⟩ := h b hb
  refine Set.infinite_of_not_bddAbove ?_
  rintro ⟨M, hM⟩
  set N := max N₀ (M + 1) with hNdef
  have hcount := hN N (le_max_left _ _)
  have hx1 : 1 < xx b N := one_lt_xx b N (by omega)
  have hL : 0 < Real.log (xx b N) := Real.log_pos hx1
  have hpos : (0 : ℝ) < (#((piStar b N).filter (fun n => Ω n ≤ 3 ∧ ∀ p ∈ n.primeFactors, xx b N ^ c0 < (p : ℝ))) : ℝ) :=
    lt_of_lt_of_le (by positivity) hcount
  obtain ⟨n, hn⟩ := Finset.card_pos.1 (by exact_mod_cast hpos)
  rw [Finset.mem_filter] at hn
  obtain ⟨hnP, hn3, hbig⟩ := hn
  obtain ⟨h1, h2, hpal, -⟩ := Palprimes.mem_piStar hnP
  have hn0 : n ≠ 0 := by
    have : 1 ≤ b ^ (2 * N) := Nat.one_le_pow _ _ (by omega)
    omega
  have hmem : n ∈ {n : ℕ | IsPalindrome b n ∧ Nat.IsAtMostAlmostPrime 3 n ∧
      ∀ p ∈ n.primeFactors, (n : ℝ) ^ ((1 : ℝ) / 250) < (p : ℝ)} := by
    refine ⟨hpal, ⟨hn0, hn3⟩, fun p hp => lt_of_le_of_lt ?_ (hbig p hp)⟩
    rw [show c0 = (1 : ℝ) / 250 by norm_num [c0]]
    apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ (by norm_num)
    unfold xx; exact_mod_cast h2.le
  have hle : n ≤ M := hM hmem
  have hlt : M < b ^ (2 * N) := by
    calc M < N := by omega
      _ < 2 ^ N := Nat.lt_two_pow_self
      _ ≤ b ^ N := Nat.pow_le_pow_left (by omega) _
      _ ≤ b ^ (2 * N) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- All items imply the large-prime-factor form. -/
theorem skeleton_largeFactors : AllItems → MainLargeFactors := fun H => largeFactors_of_count (mainCount_of H)

end Omega3
