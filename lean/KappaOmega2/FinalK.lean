import KappaOmega2.SkeletonK
import KappaOmega2.Items.S01
import KappaOmega2.Items.S02
import KappaOmega2.Items.S03
import KappaOmega2.Items.S04
import KappaOmega2.Items.S05
import KappaOmega2.Items.S06
import KappaOmega2.Items.S07
import KappaOmega2.Items.S08
import KappaOmega2.Items.S09
import KappaOmega2.Items.S10
import KappaOmega2.Items.S11
import KappaOmega2.Items.S12
import KappaOmega2.Items.S13
import KappaOmega2.Items.S14
import KappaOmega2.Items.S15
import KappaOmega2.Items.M01
import KappaOmega2.Items.M02
import KappaOmega2.Items.M03
import KappaOmega2.Items.M04
import KappaOmega2.Items.M05
import KappaOmega2.Items.M06
import KappaOmega2.Items.M07
import KappaOmega2.Items.M08
import KappaOmega2.Items.M09
import KappaOmega2.Items.M10
import KappaOmega2.Items.M11
import KappaOmega2.Items.M12
import KappaOmega2.Items.M13
import KappaOmega2.Items.L01
import KappaOmega2.Items.L02
import KappaOmega2.Items.L03
import KappaOmega2.Items.LK01
import KappaOmega2.Items.LK06
import KappaOmega2.Items.LK07
import KappaOmega2.Items.LK08
import KappaOmega2.Items.LK09
import KappaOmega2.Items.LKM
import KappaOmega2.Items.LK10
import KappaOmega2.Items.LK13
import KappaOmega2.Items.LK14
import KappaOmega2.Items.LK15
import KappaOmega2.Items.LK17
import KappaOmega2.Items.QK01
import KappaOmega2.Items.QK03
import KappaOmega2.Items.QK04

/-!
# Final: Ω ≤ 2 for κ-palindromes (κ = 7/10) in every base `b ≥ 3`

All items are proved (`KappaOmega2/Items`), `skeletonK` combines them. No `sorry`, standard axioms only.
-/

set_option linter.style.longLine false

open Finset Real
open scoped ArithmeticFunction.Omega

namespace KappaOmega2

open Palprimes

theorem allItemsK : AllItemsK :=
  ⟨⟨itemS01, itemS02, itemS03, itemS04, itemS05, itemS06, itemS07, itemS08, itemS09, itemS10, itemS11, itemS12, itemS13, itemS14, itemS15, itemM01, itemM02, itemM03, itemM04, itemM05, itemM06, itemM07, itemM08, itemM09, itemM10, itemM11, itemM12, itemM13⟩,
    ⟨itemL01, itemL02, itemL03, itemLK01, itemLK06, itemLK07, itemLK08, itemLK09, itemLKM, itemLK10, itemLK13, itemLK14, itemLK15, itemLK17, itemQK01, itemQK03, itemQK04⟩⟩

/-- **Ω ≤ 2 for κ-palindromes.** In every base `b ≥ 3` there are infinitely many integers whose first `⌊7L/20⌋` digits
mirror their last `⌊7L/20⌋` digits (`L` = number of digits) and which have at most two prime factors counted with
multiplicity. -/
theorem infinite_kappaPal_Omega_le_two (b : ℕ) (hb : 3 ≤ b) :
    {n : ℕ | IsKappaPal b n ∧ Nat.IsAtMostAlmostPrime 2 n}.Infinite :=
  (skeletonK allItemsK).1 b hb

/-- Counting form: at least `c 2^m W / log x` such κ-palindromes with `2N + 1` digits, coprime to `b³ − b`, with every
prime factor `> x^{1/100}`. -/
theorem many_kappaPal_Omega_le_two : MainCountK := (skeletonK allItemsK).2

/-! ## The main theorems stated with Mathlib definitions only -/

/-- In every base `b ≥ 3` there are infinitely many `n` whose first `⌊7L/20⌋` base-`b` digits mirror the last ones
(`L` the number of digits) and with at most two prime factors counted with multiplicity. -/
theorem _root_.kappa_palindromes_omega_le_two (b : ℕ) (hb : 3 ≤ b) :
    {n : ℕ | (∀ i < 7 * (Nat.digits b n).length / 20,
        (Nat.digits b n).getD i 0 = (Nat.digits b n).getD ((Nat.digits b n).length - 1 - i) 0) ∧
      n ≠ 0 ∧ ArithmeticFunction.cardFactors n ≤ 2}.Infinite := by
  have h := infinite_kappaPal_Omega_le_two b hb
  convert h using 1
  ext n
  simp only [Set.mem_setOf_eq, IsKappaPal, Nat.IsAtMostAlmostPrime]

/-- Among the integers with `2N + 1` base-`b` digits, coprime to `b³ − b`, whose first `m = ⌊7(2N+1)/20⌋` digits
mirror the last ones, at least `c 2^m W / log x` (`W = b^{2N+1−2m}`, `x = b^{2N+1}`) have `Ω ≤ 2` and all prime
factors `> x^{1/100}`. -/
theorem _root_.kappa_palindromes_omega_le_two_count : ∀ b : ℕ, 3 ≤ b → ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    c * (2 : ℝ) ^ (7 * (2 * N + 1) / 20) * ((b ^ (2 * N + 1 - 2 * (7 * (2 * N + 1) / 20)) : ℕ) : ℝ) /
        Real.log ((b : ℝ) ^ (2 * N + 1)) ≤
    (Finset.card (((Finset.Ico (b ^ (2 * N)) (b ^ (2 * N + 1))).filter
        (fun n => (∀ i < 7 * (Nat.digits b n).length / 20,
            (Nat.digits b n).getD i 0 = (Nat.digits b n).getD ((Nat.digits b n).length - 1 - i) 0) ∧
          Nat.Coprime n (b ^ 3 - b))).filter
        (fun n => ArithmeticFunction.cardFactors n ≤ 2 ∧
          ∀ p ∈ n.primeFactors, ((b : ℝ) ^ (2 * N + 1)) ^ ((1 : ℝ) / 100) < (p : ℝ))) : ℝ) :=
  fun b hb => many_kappaPal_Omega_le_two b hb

end KappaOmega2
