import Omega3.Skeleton
import Omega3.Corollaries
import Omega3.Items.L01
import Omega3.Items.L02
import Omega3.Items.L03
import Omega3.Items.L04
import Omega3.Items.L05
import Omega3.Items.L06
import Omega3.Items.L07
import Omega3.Items.L08
import Omega3.Items.L09
import Omega3.Items.L10
import Omega3.Items.L11
import Omega3.Items.L12
import Omega3.Items.L13
import Omega3.Items.L14
import Omega3.Items.L15
import Omega3.Items.L16
import Omega3.Items.L17
import Omega3.Items.Q01
import Omega3.Items.Q02
import Omega3.Items.Q03
import Omega3.Items.Q04
import Omega3.Items.S01
import Omega3.Items.S02
import Omega3.Items.S03
import Omega3.Items.S04
import Omega3.Items.S05
import Omega3.Items.S06
import Omega3.Items.S07
import Omega3.Items.S08
import Omega3.Items.S09
import Omega3.Items.S10
import Omega3.Items.S11
import Omega3.Items.S12
import Omega3.Items.S13
import Omega3.Items.S14
import Omega3.Items.S15
import Omega3.Items.M01
import Omega3.Items.M02
import Omega3.Items.M03
import Omega3.Items.M04
import Omega3.Items.M05
import Omega3.Items.M06
import Omega3.Items.M07
import Omega3.Items.M08
import Omega3.Items.M09
import Omega3.Items.M10
import Omega3.Items.M11
import Omega3.Items.M12
import Omega3.Items.M13

/-! # Ω ≤ 3 in every base `b ≥ 5`: final theorems (all 49 items proved, 2026-11-24). -/

open Finset Real
open scoped ArithmeticFunction.omega ArithmeticFunction.Omega ArithmeticFunction.Moebius

namespace Omega3

theorem allItems : AllItems :=
  ⟨itemL01, itemL02, itemL03, itemL04, itemL05, itemL06, itemL07, itemL08, itemL09, itemL10, itemL11, itemL12,
    itemL13, itemL14, itemL15, itemL16, itemL17, itemQ01, itemQ02, itemQ03, itemQ04, itemS01, itemS02, itemS03,
    itemS04, itemS05, itemS06, itemS07, itemS08, itemS09, itemS10, itemS11, itemS12, itemS13, itemS14, itemS15,
    itemM01, itemM02, itemM03, itemM04, itemM05, itemM06, itemM07, itemM08, itemM09, itemM10, itemM11, itemM12,
    itemM13⟩

/-- **Main theorem.** For every base `b ≥ 5` there are infinitely many palindromes with at most three prime factors
counted with multiplicity. -/
theorem infinite_palindromes_Omega_le_three (b : ℕ) (hb : 5 ≤ b) :
    {n : ℕ | Palprimes.IsPalindrome b n ∧ Nat.IsAtMostAlmostPrime 3 n}.Infinite :=
  (skeleton allItems).1 b hb

/-- **Counting form.** At least `c 3^N / log x` palindromes with `2N + 1` digits, coprime to `b³ − b`, have `Ω ≤ 3` and
every prime factor `> x^{1/250}`, `x = b^{2N+1}`. -/
theorem many_palindromes_Omega_le_three (b : ℕ) (hb : 5 ≤ b) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      c * (3 : ℝ) ^ N / Real.log (xx b N) ≤
        (#((Palprimes.piStar b N).filter (fun n => ArithmeticFunction.cardFactors n ≤ 3 ∧
          ∀ p ∈ n.primeFactors, xx b N ^ c0 < (p : ℝ))) : ℝ) :=
  (skeleton allItems).2 b hb

/-- **Large prime factors.** Infinitely many palindromes with `Ω ≤ 3` and every prime factor `> n^{1/250}`. -/
theorem infinite_palindromes_Omega_le_three_large_factors (b : ℕ) (hb : 5 ≤ b) :
    {n : ℕ | Palprimes.IsPalindrome b n ∧ Nat.IsAtMostAlmostPrime 3 n ∧
      ∀ p ∈ n.primeFactors, (n : ℝ) ^ ((1 : ℝ) / 250) < (p : ℝ)}.Infinite :=
  skeleton_largeFactors allItems b hb

end Omega3
