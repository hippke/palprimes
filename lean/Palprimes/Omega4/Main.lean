import Palprimes.MainTerm.HM
import Palprimes.Squares.PropW2
import Palprimes.TL1.LevelTheta
import Palprimes.Major.Fejer
import Palprimes.AlmostPrime.OmegaLeFive
import Palprimes.MainTerm.MvalPos

/-! # Ω ≤ 4: assembly

Parameters `θ = 0.2608`, `ε₀ = 10⁻⁴`, `T₀ = 1/8` (`Pstar`). From
* HL: `level_theta` with the TL¹ hypothesis `TLHyp b κ`,
* HS: `squares_piStar2` (primes in `[x^{1/40}, x^{0.2499}]` ⊇ `[x^{θT₀}, x^{1/4−ε₀}]`),
* HM: `HM_of_E1` (Greaves' Lemma 4.2 as the hypothesis `RosserAsymp b`, and `0 < Mval Pstar`),
`omega4_of` gives a palindrome with `Ω ≤ 4` among the `(2N+1)`-digit ones for all large `N`. -/

set_option linter.style.longLine false

open Finset Real
open scoped ArithmeticFunction.Omega

namespace Palprimes.MT

open Palprimes.Greaves

/-- The TL¹ hypothesis of `level_theta` at `θ = 0.2608`, `δ = 0.47`. -/
def TLHyp (b : ℕ) (κ : ℝ) : Prop :=
  ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ R0 : ℕ, ((b : ℝ) ^ N) ^ (47 / 100 : ℝ) ≤ R0 →
    (R0 : ℝ) ≤ ((b : ℝ) ^ (2 * N + 1)) ^ (2608 / 10000 : ℝ) →
    ∀ Qs : Finset ℕ, (∀ q ∈ Qs, R0 ≤ q ∧ q ≤ 2 * R0 ∧ Nat.Coprime q b) → ∀ β : ℝ,
      ∑ q ∈ Qs, ∑ h ∈ redRes q, Fprod b N ((h : ℝ) / q + β) ≤ R0 * ((b : ℝ) ^ N) ^ (-κ)

theorem HS_Pstar (b : ℕ) (hb : 2 ≤ b) :
    ∃ N₂ : ℕ, ∀ N ≥ N₂,
      ∑ p ∈ (Icc ⌈((b : ℝ) ^ (2 * N + 1)) ^ ((2608 / 10000 : ℝ) * Pstar.T0)⌉₊
          ⌊((b : ℝ) ^ (2 * N + 1)) ^ (1 / 4 - 1 / 10000 : ℝ)⌋₊).filter Nat.Prime,
          (countDvd (piStar b N) (p ^ 2) : ℝ)
        ≤ (#(piStar b N) : ℝ) / (Real.log ((b : ℝ) ^ (2 * N + 1))) ^ 3 := by
  obtain ⟨N₀, h⟩ := squares_piStar2 b hb
  refine ⟨N₀, fun N hN => le_trans ?_ (h N hN)⟩
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · apply Finset.filter_subset_filter
    have hx : (1 : ℝ) ≤ (b : ℝ) ^ (2 * N + 1) := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ b))
    apply Finset.Icc_subset_Icc
    · apply Nat.ceil_mono
      apply Real.rpow_le_rpow_of_exponent_le hx
      simp only [Pstar]; norm_num
    · apply le_of_eq; norm_num
  · intro p _ _; exact Nat.cast_nonneg _

/-- **Ω ≤ 4 from TL¹, E1 and `𝓜 > 0`.** -/
theorem omega4_of (b : ℕ) (hb : 2 ≤ b) (hE1 : RosserAsymp b) (hM : 0 < Mval Pstar)
    (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hTL : TLHyp b κ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∃ n ∈ piStar b N, Nat.IsAtMostAlmostPrime 4 n := by
  classical
  have hθ : (0 : ℝ) < 2608 / 10000 := by norm_num
  have HL := level_theta b hb (2608 / 10000) κ (by norm_num) (by norm_num) hκ hκ1 hTL
  have HM := HM_of_E1 Pstar b hb hE1 (by simp [Pstar]) hM (2608 / 10000) hθ
  obtain ⟨c, hc, N₀, hcount⟩ := omega4_skeleton b hb Pstar (2608 / 10000) (1 / 10000) hθ
    (by rw [Pstar_U]) (by rw [Pstar_V]) HL (HS_Pstar b hb) HM
  obtain ⟨c', hc', N₁, hcard⟩ := card_piStar_lower b hb
  refine ⟨max N₀ N₁, fun N hN => ?_⟩
  have h1 := hcount N (le_trans (le_max_left _ _) hN)
  have h2 := hcard N (le_trans (le_max_right _ _) hN)
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hlx : 0 < Real.log ((b : ℝ) ^ (2 * N + 1)) := Real.log_pos (one_lt_pow₀ hb1 (by omega))
  have hpos : 0 < (#(piStar b N) : ℝ) := lt_of_lt_of_le (by positivity) h2
  have hfil : 0 < (#((piStar b N).filter (fun n => Ω n ≤ 4 ∧
      ∀ p ∈ n.primeFactors, ((b : ℝ) ^ (2 * N + 1)) ^ ((2608 / 10000 : ℝ) * Pstar.T0) < (p : ℝ))) : ℝ) :=
    lt_of_lt_of_le (by positivity) h1
  obtain ⟨n, hn⟩ := Finset.card_pos.1 (by exact_mod_cast hfil)
  rw [Finset.mem_filter] at hn
  refine ⟨n, hn.1, ?_, hn.2.1⟩
  obtain ⟨h1', -, -, -⟩ := Palprimes.mem_piStar hn.1
  have : 1 ≤ n := le_trans (Nat.one_le_pow _ _ (by omega)) h1'
  omega

theorem infinite_of_exists (k b : ℕ) (hb : 2 ≤ b) (h : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∃ n ∈ piStar b N, Nat.IsAtMostAlmostPrime k n) :
    {n : ℕ | IsPalindrome b n ∧ Nat.IsAtMostAlmostPrime k n}.Infinite := by
  obtain ⟨N₀, h⟩ := h
  refine Set.infinite_of_not_bddAbove ?_
  rintro ⟨m, hm⟩
  obtain ⟨n, hn, hnk⟩ := h (max N₀ m) (le_max_left _ _)
  obtain ⟨h1, -, hpal, -⟩ := Palprimes.mem_piStar hn
  have hle : n ≤ m := hm ⟨hpal, hnk⟩
  have hlt : m < b ^ (2 * max N₀ m) := by
    calc m ≤ max N₀ m := le_max_right _ _
      _ < 2 ^ max N₀ m := Nat.lt_two_pow_self
      _ ≤ b ^ max N₀ m := Nat.pow_le_pow_left hb _
      _ ≤ b ^ (2 * max N₀ m) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- **Ω ≤ 4 for `b ≥ 10`, conditional on E1 and `𝓜 > 0`** (TL¹ by the Fejér family). -/
theorem infinite_Omega_le_four_ge_ten (b : ℕ) (hb : 10 ≤ b) (hE1 : RosserAsymp b) (hM : 0 < Mval Pstar) :
    {n : ℕ | IsPalindrome b n ∧ Nat.IsAtMostAlmostPrime 4 n}.Infinite := by
  obtain ⟨κ, hκ, hκ1, hTL⟩ := Palprimes.tl1_ge_ten b hb
  exact infinite_of_exists 4 b (by omega) (omega4_of b (by omega) hE1 hM κ hκ hκ1 hTL)

/-- **Ω ≤ 4 for `b ≥ 10`, conditional only on E1** (Greaves' Lemma 4.2). -/
theorem infinite_Omega_le_four_ge_ten' (b : ℕ) (hb : 10 ≤ b) (hE1 : RosserAsymp b) :
    {n : ℕ | IsPalindrome b n ∧ Nat.IsAtMostAlmostPrime 4 n}.Infinite :=
  infinite_Omega_le_four_ge_ten b hb hE1 Mval_Pstar_pos

end Palprimes.MT
