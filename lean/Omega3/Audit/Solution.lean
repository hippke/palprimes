import Mathlib
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

/-! Solution for `lake comparator` (Ω ≤ 3 audit).

`Omega3.Final` sits at import depth 21 (Palprimes/Omega3 modules only), and `lake build` of a module at
depth 22 aborts with "Stack overflow detected" (lake itself, toolchain v4.37.0-rc1; `lean` alone elaborates
`import Omega3.Final` fine). This file therefore imports exactly the modules `Omega3.Final` imports and
repeats its three one-line proofs (the same terms as in `Omega3/Final.lean`). -/

/-- The 49 items, assembled exactly as `Omega3.allItems` in `Omega3/Final.lean`. -/
theorem audit_allItems : Omega3.AllItems :=
  open Omega3 in
  ⟨itemL01, itemL02, itemL03, itemL04, itemL05, itemL06, itemL07, itemL08, itemL09, itemL10, itemL11, itemL12,
    itemL13, itemL14, itemL15, itemL16, itemL17, itemQ01, itemQ02, itemQ03, itemQ04, itemS01, itemS02, itemS03,
    itemS04, itemS05, itemS06, itemS07, itemS08, itemS09, itemS10, itemS11, itemS12, itemS13, itemS14, itemS15,
    itemM01, itemM02, itemM03, itemM04, itemM05, itemM06, itemM07, itemM08, itemM09, itemM10, itemM11, itemM12,
    itemM13⟩

/-- In every base `b ≥ 5` there are infinitely many palindromes with `Ω ≤ 3`. -/
theorem palindromes_omega_le_three : ∀ b : ℕ, 5 ≤ b →
    {n : ℕ | (Nat.digits b n).reverse = Nat.digits b n ∧ Nat.IsAtMostAlmostPrime 3 n}.Infinite :=
  fun b hb => (Omega3.skeleton audit_allItems).1 b hb

/-- Infinitely many palindromes `n` with `Ω(n) ≤ 3` and every prime factor above `n^{1/250}`. -/
theorem palindromes_omega_le_three_large_factors : ∀ b : ℕ, 5 ≤ b →
    {n : ℕ | (Nat.digits b n).reverse = Nat.digits b n ∧ Nat.IsAtMostAlmostPrime 3 n ∧
      ∀ p ∈ n.primeFactors, (n : ℝ) ^ ((1 : ℝ) / 250) < (p : ℝ)}.Infinite :=
  fun b hb => Omega3.skeleton_largeFactors audit_allItems b hb

/-- Among the palindromes with `2N + 1` digits coprime to `b³ − b`, at least `c 3^N / log x`,
`x = b^{2N+1}`, have `Ω ≤ 3` and all prime factors `> x^{1/250}`. -/
theorem palindromes_omega_le_three_count : ∀ b : ℕ, 5 ≤ b → ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    c * (3 : ℝ) ^ N / Real.log ((b : ℝ) ^ (2 * N + 1)) ≤
    (Finset.card (((Finset.Ico (b ^ (2 * N)) (b ^ (2 * N + 1))).filter
        (fun n => (Nat.digits b n).reverse = Nat.digits b n ∧ Nat.Coprime n (b ^ 3 - b))).filter
        (fun n => ArithmeticFunction.cardFactors n ≤ 3 ∧
          ∀ p ∈ n.primeFactors, ((b : ℝ) ^ (2 * N + 1)) ^ ((1 : ℝ) / 250) < (p : ℝ))) : ℝ) :=
  fun b hb => (Omega3.skeleton audit_allItems).2 b hb
