import Palprimes.AlmostPrime.OmegaLeFive
import Palprimes.Sieve.WeightedCount

/-! # Many palindromes with `Ω ≤ 5` and large prime factors

`many_palindromes_Omega_le_five`: among the palindromes with `2N + 1` digits that are coprime to
`b³ − b`, at least a proportion `1/(40 log x)`, `x = b^{2N+1}`, have `Ω ≤ 5` and no prime factor
below `x^{1/20}`.
`infinite_palindromes_Omega_le_five_large_factors`: infinitely many palindromes `n` have `Ω(n) ≤ 5`
and every prime factor at least `n^{1/20}`. -/

open Finset Real

namespace Palprimes

open Classical in
/-- **Counting form.** For large `N`, at least `#Π*_b(2N) / (40 log x)` palindromes in `Π*_b(2N)`
have `Ω ≤ 5` and all prime factors `≥ x^{1/20}`, where `x = b^{2N+1}`. -/
theorem many_palindromes_Omega_le_five (b : ℕ) (hb : 2 ≤ b) :
    ∃ N₀, ∀ N ≥ N₀,
      1 / 40 * ((#(piStar b N) : ℝ) / Real.log ((b : ℝ) ^ (2 * N + 1))) ≤
        (#((piStar b N).filter (fun n => Nat.IsAtMostAlmostPrime 5 n ∧
          ∀ p ∈ n.primeFactors, ((b : ℝ) ^ (2 * N + 1)) ^ ((1 : ℝ) / 20) ≤ (p : ℝ))) : ℝ) := by
  obtain ⟨x₀, hsieve⟩ := sieve_count_large_factors (bigB b) (one_le_bigB hb)
  obtain ⟨N₁, hlev⟩ := level_piStar_weighted b hb
  obtain ⟨N₂, hsq⟩ := squares_piStar b hb
  obtain ⟨N₄, hN₄⟩ := pow_unbounded_of_one_lt x₀ (by norm_num : (1 : ℝ) < 2)
  have hx : ∀ N ≥ N₄, x₀ ≤ (b : ℝ) ^ (2 * N + 1) := fun N hN => by
    have h2b : (2 : ℝ) ≤ b := by exact_mod_cast hb
    calc x₀ ≤ (2 : ℝ) ^ N₄ := hN₄.le
      _ ≤ (2 : ℝ) ^ (2 * N + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ ≤ (b : ℝ) ^ (2 * N + 1) := pow_le_pow_left₀ (by norm_num) h2b _
  refine ⟨max (max N₁ N₂) N₄, fun N hN => ?_⟩
  refine hsieve (piStar b N) ((b : ℝ) ^ (2 * N + 1)) (hx N (by omega)) ?_
    (hlev N (by omega)) (hsq N (by omega))
  intro n hn
  obtain ⟨h1, h2, -, h4⟩ := mem_piStar hn
  refine ⟨le_trans (Nat.one_le_pow _ _ (by omega)) h1, ?_, h4⟩
  exact_mod_cast h2.le

/-- **Large prime factors.** In every base `b ≥ 2` there are infinitely many palindromes `n` with
`Ω(n) ≤ 5` all of whose prime factors are at least `n^{1/20}`. -/
theorem infinite_palindromes_Omega_le_five_large_factors (b : ℕ) (hb : 2 ≤ b) :
    {n : ℕ | IsPalindrome b n ∧ Nat.IsAtMostAlmostPrime 5 n ∧
      ∀ p ∈ n.primeFactors, (n : ℝ) ^ ((1 : ℝ) / 20) ≤ (p : ℝ)}.Infinite := by
  classical
  obtain ⟨N₀, h⟩ := many_palindromes_Omega_le_five b hb
  obtain ⟨N₃, hne⟩ := piStar_nonempty b hb
  refine Set.infinite_of_not_bddAbove ?_
  rintro ⟨m, hm⟩
  set N := max (max N₀ N₃) (m + 1)
  have hcount := h N (by omega)
  set x : ℝ := (b : ℝ) ^ (2 * N + 1)
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hx1 : 1 < x := one_lt_pow₀ hb1 (by omega)
  have hL : 0 < Real.log x := Real.log_pos hx1
  have hA : (0 : ℝ) < #(piStar b N) := by exact_mod_cast (hne N (by omega)).card_pos
  have hpos : (0 : ℝ) < (#((piStar b N).filter (fun n => Nat.IsAtMostAlmostPrime 5 n ∧
      ∀ p ∈ n.primeFactors, x ^ ((1 : ℝ) / 20) ≤ (p : ℝ))) : ℝ) :=
    lt_of_lt_of_le (by positivity) hcount
  obtain ⟨n, hn⟩ := Finset.card_pos.1 (by exact_mod_cast hpos)
  rw [mem_filter] at hn
  obtain ⟨hnP, hn5, hnp⟩ := hn
  obtain ⟨h1, h2, hpal, -⟩ := mem_piStar hnP
  have hmem : n ∈ {n : ℕ | IsPalindrome b n ∧ Nat.IsAtMostAlmostPrime 5 n ∧
      ∀ p ∈ n.primeFactors, (n : ℝ) ^ ((1 : ℝ) / 20) ≤ (p : ℝ)} := by
    refine ⟨hpal, hn5, fun p hp => le_trans ?_ (hnp p hp)⟩
    apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ (by norm_num)
    simp only [x]; exact_mod_cast h2.le
  have hle : n ≤ m := hm hmem
  have hlt : m < b ^ (2 * N) := by
    calc m < N := by omega
      _ < 2 ^ N := Nat.lt_two_pow_self
      _ ≤ b ^ N := Nat.pow_le_pow_left hb _
      _ ≤ b ^ (2 * N) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

end Palprimes
