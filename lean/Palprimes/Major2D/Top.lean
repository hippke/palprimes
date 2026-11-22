import Palprimes.Major2D.B2

/-! # TL¹ for the bases 3 and 2 (inner-only cut, `θ = 0.2608`, `δ = 0.47`)

The conclusions are literally that of `tl1_ge_ten` (`Palprimes/Major/Fejer.lean`) with `b = 3` and `b = 2`.
Block majorants: `l = 3`, `p = 49/50` (73 terms) for `b = 3`; `l = 7`, `p = 999/1000` (551 terms) for `b = 2`;
`‖Γ_l‖^p ≤ T` is kernel-checked by an adaptive Taylor-model cell certificate (`Palprimes/Major2D`). -/

namespace Palprimes

/-- **TL¹ for base 3.** -/
theorem tl1_three : ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 ∧
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ R0 : ℕ, (((3 : ℕ) : ℝ) ^ N) ^ (47 / 100 : ℝ) ≤ R0 →
      (R0 : ℝ) ≤ (((3 : ℕ) : ℝ) ^ (2 * N + 1)) ^ (2608 / 10000 : ℝ) →
      ∀ Qs : Finset ℕ, (∀ q ∈ Qs, R0 ≤ q ∧ q ≤ 2 * R0 ∧ Nat.Coprime q 3) → ∀ β : ℝ,
        ∑ q ∈ Qs, ∑ h ∈ redRes q, Fprod 3 N ((h : ℝ) / q + β) ≤ R0 * ((((3 : ℕ) : ℝ)) ^ N) ^ (-κ) :=
  M2.tl1_three

/-- **TL¹ for base 2.** -/
theorem tl1_two : ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 ∧
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ R0 : ℕ, (((2 : ℕ) : ℝ) ^ N) ^ (47 / 100 : ℝ) ≤ R0 →
      (R0 : ℝ) ≤ (((2 : ℕ) : ℝ) ^ (2 * N + 1)) ^ (2608 / 10000 : ℝ) →
      ∀ Qs : Finset ℕ, (∀ q ∈ Qs, R0 ≤ q ∧ q ≤ 2 * R0 ∧ Nat.Coprime q 2) → ∀ β : ℝ,
        ∑ q ∈ Qs, ∑ h ∈ redRes q, Fprod 2 N ((h : ℝ) / q + β) ≤ R0 * ((((2 : ℕ) : ℝ)) ^ N) ^ (-κ) :=
  M2.tl1_two

end Palprimes
