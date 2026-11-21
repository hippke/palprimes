import Mathlib
import Palprimes.AlmostPrime.OmegaLeFive

/-! Solution for `lake comparator`. -/

theorem palindromes_omega_le_five : ∀ b : ℕ, 2 ≤ b →
    {n : ℕ | (Nat.digits b n).reverse = Nat.digits b n ∧ Nat.IsAtMostAlmostPrime 5 n}.Infinite :=
  fun b hb => Palprimes.infinite_palindromes_Omega_le_five b hb
