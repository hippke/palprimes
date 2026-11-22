import Palprimes.Omega4.Main
import Palprimes.MainTerm.MvalPos
import Palprimes.Major1D.TL1Small
import Palprimes.Major2D.Top
import Palprimes.E1.Main

/-! # Ω ≤ 4 palindromes in every base b ≥ 2

`infinite_palindromes_Omega_le_four`: for every `b ≥ 2` there are infinitely many base-`b` palindromes
with at most four prime factors counted with multiplicity. Ingredients: TL¹ (Fejér family for `b ≥ 10`,
kernel-checked majorants for `b = 2, …, 9`), the level `θ = 0.2608`, the prime squares, Greaves'
combinatorics, the main-term limit `2e^γ 𝓜` (Lemmas 5.1, 5.2), `𝓜 > 0`, and Greaves' Lemma 4.2
(Rosser–Iwaniec linear sieve asymptotic, `Palprimes/E1/`). -/

set_option linter.style.longLine false

namespace Palprimes.MT

theorem tl1_all (b : ℕ) (hb : 2 ≤ b) : ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 ∧ TLHyp b κ := by
  rcases (show b = 2 ∨ b = 3 ∨ (4 ≤ b ∧ b ≤ 9) ∨ 10 ≤ b by omega) with rfl | rfl | ⟨h4, h9⟩ | h10
  · exact Palprimes.tl1_two
  · exact Palprimes.tl1_three
  · exact Palprimes.tl1_small b h4 h9
  · exact Palprimes.tl1_ge_ten b h10

/-- **Main theorem.** -/
theorem infinite_palindromes_Omega_le_four (b : ℕ) (hb : 2 ≤ b) :
    {n : ℕ | IsPalindrome b n ∧ Nat.IsAtMostAlmostPrime 4 n}.Infinite := by
  obtain ⟨κ, hκ, hκ1, hTL⟩ := tl1_all b hb
  exact infinite_of_exists 4 b hb
    (omega4_of b hb (Palprimes.E1.rosserAsymp_of_two_le b hb) Mval_Pstar_pos κ hκ hκ1 hTL)

/-- In the form of `Statements.lean`. -/
theorem almostPalprimesInfinite_four (b : ℕ) (hb : 2 ≤ b) : AlmostPalprimesInfinite 4 b :=
  infinite_palindromes_Omega_le_four b hb

end Palprimes.MT
