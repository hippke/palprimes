import Palprimes.Omega4.Final

/-! # Corollaries of the Ω ≤ 4 proof

* `level_piStar_theta`: palindromes have level of distribution `θ = 0.2608` with weights `3^ω`
  (moduli coprime to `b³ − b`) in every base `b ≥ 2`.
* `many_palindromes_Omega_le_four`: among the palindromes with `2N + 1` digits coprime to `b³ − b`,
  at least a proportion `c / log x`, `x = b^{2N+1}`, have `Ω ≤ 4` and every prime factor above
  `x^{0.0326}` (`0.0326 = θ T₀`, `T₀ = 1/8`); the constant `c > 0` depends on `b` and is not
  explicit.
* `infinite_palindromes_Omega_le_four_large_factors`: infinitely many palindromes `n` with
  `Ω(n) ≤ 4` and every prime factor above `n^{0.0326}`. -/

set_option linter.style.longLine false

open Finset Real
open scoped ArithmeticFunction.Omega

namespace Palprimes.MT

open Palprimes.Greaves

/-- **Level of distribution `θ = 0.2608` in every base.** -/
theorem level_piStar_theta (b : ℕ) (hb : 2 ≤ b) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∑ q ∈ (Icc 1 ⌊((b : ℝ) ^ (2 * N + 1)) ^ (2608 / 10000 : ℝ)⌋₊).filter (fun q => Nat.Coprime q (bigB b)),
          (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors q) *
            |(countDvd (piStar b N) q : ℝ) - (#(piStar b N) : ℝ) / q|
        ≤ (#(piStar b N) : ℝ) / (Real.log ((b : ℝ) ^ (2 * N + 1))) ^ 3 := by
  obtain ⟨κ, hκ, hκ1, hTL⟩ := tl1_all b hb
  exact level_theta b hb (2608 / 10000) κ (by norm_num) (by norm_num) hκ hκ1 hTL

open Classical in
/-- **Counting form.** For large `N`, at least `c · #Π*_b(2N) / log x` palindromes in `Π*_b(2N)`
have `Ω ≤ 4` and all prime factors `> x^{0.0326}`, where `x = b^{2N+1}`. -/
theorem many_palindromes_Omega_le_four (b : ℕ) (hb : 2 ≤ b) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      c * ((#(piStar b N) : ℝ) / Real.log ((b : ℝ) ^ (2 * N + 1))) ≤
        (#((piStar b N).filter (fun n => Nat.IsAtMostAlmostPrime 4 n ∧
          ∀ p ∈ n.primeFactors, ((b : ℝ) ^ (2 * N + 1)) ^ ((163 : ℝ) / 5000) < (p : ℝ))) : ℝ) := by
  obtain ⟨κ, hκ, hκ1, hTL⟩ := tl1_all b hb
  have hθ : (0 : ℝ) < 2608 / 10000 := by norm_num
  have HL := level_theta b hb (2608 / 10000) κ (by norm_num) (by norm_num) hκ hκ1 hTL
  have HM := HM_of_E1 Pstar b hb (Palprimes.E1.rosserAsymp_of_two_le b hb) (by simp [Pstar])
    Mval_Pstar_pos (2608 / 10000) hθ
  obtain ⟨c, hc, N₀, hcount⟩ := omega4_skeleton b hb Pstar (2608 / 10000) (1 / 10000) hθ
    (by rw [Pstar_U]) (by rw [Pstar_V]) HL (HS_Pstar b hb) HM
  have hT : (2608 / 10000 : ℝ) * Pstar.T0 = 163 / 5000 := by rw [PT0]; norm_num
  refine ⟨c, hc, N₀, fun N hN => le_trans (hcount N hN) ?_⟩
  rw [hT]
  have hsub : (piStar b N).filter (fun n => Ω n ≤ 4 ∧
        ∀ p ∈ n.primeFactors, ((b : ℝ) ^ (2 * N + 1)) ^ ((163 : ℝ) / 5000) < (p : ℝ)) ⊆
      (piStar b N).filter (fun n => Nat.IsAtMostAlmostPrime 4 n ∧
        ∀ p ∈ n.primeFactors, ((b : ℝ) ^ (2 * N + 1)) ^ ((163 : ℝ) / 5000) < (p : ℝ)) := by
    intro n hn
    rw [mem_filter] at hn ⊢
    refine ⟨hn.1, ⟨?_, hn.2.1⟩, hn.2.2⟩
    obtain ⟨h1', -, -, -⟩ := Palprimes.mem_piStar hn.1
    have : 1 ≤ n := le_trans (Nat.one_le_pow _ _ (by omega)) h1'
    omega
  exact_mod_cast Finset.card_le_card hsub

/-- **Large prime factors.** In every base `b ≥ 2` there are infinitely many palindromes `n` with
`Ω(n) ≤ 4` all of whose prime factors exceed `n^{0.0326}`. -/
theorem infinite_palindromes_Omega_le_four_large_factors (b : ℕ) (hb : 2 ≤ b) :
    {n : ℕ | IsPalindrome b n ∧ Nat.IsAtMostAlmostPrime 4 n ∧
      ∀ p ∈ n.primeFactors, (n : ℝ) ^ ((163 : ℝ) / 5000) < (p : ℝ)}.Infinite := by
  classical
  obtain ⟨c, hc, N₀, h⟩ := many_palindromes_Omega_le_four b hb
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
  have hpos : (0 : ℝ) < (#((piStar b N).filter (fun n => Nat.IsAtMostAlmostPrime 4 n ∧
      ∀ p ∈ n.primeFactors, x ^ ((163 : ℝ) / 5000) < (p : ℝ))) : ℝ) :=
    lt_of_lt_of_le (by positivity) hcount
  obtain ⟨n, hn⟩ := Finset.card_pos.1 (by exact_mod_cast hpos)
  rw [mem_filter] at hn
  obtain ⟨hnP, hn4, hnp⟩ := hn
  obtain ⟨h1, h2, hpal, -⟩ := Palprimes.mem_piStar hnP
  have hmem : n ∈ {n : ℕ | IsPalindrome b n ∧ Nat.IsAtMostAlmostPrime 4 n ∧
      ∀ p ∈ n.primeFactors, (n : ℝ) ^ ((163 : ℝ) / 5000) < (p : ℝ)} := by
    refine ⟨hpal, hn4, fun p hp => lt_of_le_of_lt ?_ (hnp p hp)⟩
    apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ (by norm_num)
    simp only [x]; exact_mod_cast h2.le
  have hle : n ≤ m := hm hmem
  have hlt : m < b ^ (2 * N) := by
    calc m < N := by omega
      _ < 2 ^ N := Nat.lt_two_pow_self
      _ ≤ b ^ N := Nat.pow_le_pow_left hb _
      _ ≤ b ^ (2 * N) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

end Palprimes.MT
