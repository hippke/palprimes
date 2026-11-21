import Palprimes.Level.Level
import Palprimes.Squares.PropW
import Palprimes.Sieve.Weighted
import Palprimes.Statements

/-! # M15. Assembly: the main theorem from the interfaces

This file has no `sorry`. It derives the main theorem from `level_piStar_weighted` (M10),
`squares_piStar` (M11), `piStar_nonempty` (M1) and `sieve_omega_le_five` (M13). -/

open Finset Real

namespace Palprimes

theorem mem_piStar {b N n : ℕ} (h : n ∈ piStar b N) :
    b ^ (2 * N) ≤ n ∧ n < b ^ (2 * N + 1) ∧ IsPalindrome b n ∧ Nat.Coprime n (bigB b) := by
  simp only [piStar, mem_filter, mem_Ico] at h
  exact ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩

theorem one_le_bigB {b : ℕ} (hb : 2 ≤ b) : 1 ≤ bigB b := by
  unfold bigB
  have h4 : 4 ≤ b * b := Nat.mul_le_mul hb hb
  have h3 : b * 4 ≤ b ^ 3 := by
    calc b * 4 ≤ b * (b * b) := Nat.mul_le_mul_left _ h4
      _ = b ^ 3 := by ring
  omega

/-- For every large `N` some palindrome with `2N+1` digits has `Ω ≤ 5`. -/
theorem exists_piStar_omega_le_five (b : ℕ) (hb : 2 ≤ b) :
    ∃ N₀, ∀ N ≥ N₀, ∃ n ∈ piStar b N, Nat.IsAtMostAlmostPrime 5 n := by
  obtain ⟨x₀, hsieve⟩ := sieve_omega_le_five (bigB b) (one_le_bigB hb)
  obtain ⟨N₁, hlev⟩ := level_piStar_weighted b hb
  obtain ⟨N₂, hsq⟩ := squares_piStar b hb
  obtain ⟨N₃, hne⟩ := piStar_nonempty b hb
  obtain ⟨N₄, hN₄⟩ := pow_unbounded_of_one_lt x₀ (by norm_num : (1 : ℝ) < 2)
  have hx : ∀ N ≥ N₄, x₀ ≤ (b : ℝ) ^ (2 * N + 1) := fun N hN => by
    have h2b : (2 : ℝ) ≤ b := by exact_mod_cast hb
    calc x₀ ≤ (2 : ℝ) ^ N₄ := hN₄.le
      _ ≤ (2 : ℝ) ^ (2 * N + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ ≤ (b : ℝ) ^ (2 * N + 1) := pow_le_pow_left₀ (by norm_num) h2b _
  refine ⟨max (max N₁ N₂) (max N₃ N₄), fun N hN => ?_⟩
  refine hsieve (piStar b N) ((b : ℝ) ^ (2 * N + 1)) (hx N (by omega)) ?_
    (hlev N (by omega)) (hsq N (by omega)) (hne N (by omega))
  intro n hn
  obtain ⟨h1, h2, -, h4⟩ := mem_piStar hn
  refine ⟨le_trans (Nat.one_le_pow _ _ (by omega)) h1, ?_, h4⟩
  exact_mod_cast h2.le

/-- **Main theorem.** In every base `b ≥ 2` there are infinitely many palindromes with at most
five prime factors counted with multiplicity. -/
theorem infinite_palindromes_Omega_le_five (b : ℕ) (hb : 2 ≤ b) :
    {n : ℕ | IsPalindrome b n ∧ Nat.IsAtMostAlmostPrime 5 n}.Infinite := by
  obtain ⟨N₀, h⟩ := exists_piStar_omega_le_five b hb
  refine Set.infinite_of_not_bddAbove ?_
  rintro ⟨m, hm⟩
  obtain ⟨n, hn, hn5⟩ := h (max N₀ m) (le_max_left _ _)
  obtain ⟨h1, -, hpal, -⟩ := mem_piStar hn
  have hle : n ≤ m := hm ⟨hpal, hn5⟩
  have hlt : m < b ^ (2 * max N₀ m) := by
    calc m ≤ max N₀ m := le_max_right _ _
      _ < 2 ^ max N₀ m := Nat.lt_two_pow_self
      _ ≤ b ^ max N₀ m := Nat.pow_le_pow_left hb _
      _ ≤ b ^ (2 * max N₀ m) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- The main theorem in the form of `Statements.lean`. -/
theorem almostPalprimesInfinite_five (b : ℕ) (hb : 2 ≤ b) : AlmostPalprimesInfinite 5 b :=
  infinite_palindromes_Omega_le_five b hb

end Palprimes
