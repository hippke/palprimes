import Palprimes.Sieve.Vendor.Mertens

/-! # Prime sums over geometric-in-exponent grids (sieve route, M13)

`prime_grid_sum`: if `f p ≤ M_j / p` on `(T^{c_j}, T^{c_{j+1}}]`, then
`Σ f p ≤ Σ_j M_j (log(c_{j+1}/c_j) + C₂/(c_j log T))` by Mertens 2 on each piece. -/

open Finset Real

namespace Palprimes

theorem sum_Ioc_split (F : ℕ → ℝ) (g : ℕ → ℕ) (hg : Monotone g) (n : ℕ) :
    ∑ k ∈ Ioc (g 0) (g n), F k = ∑ j ∈ range n, ∑ k ∈ Ioc (g j) (g (j + 1)), F k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    exact (Finset.sum_Ioc_consecutive F (hg (Nat.zero_le n)) (hg (Nat.le_succ n))).symm

theorem prime_grid_sum (C₂ : ℝ)
    (hC₂ : ∀ a t : ℝ, 2 ≤ a → a ≤ t →
      |∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊t⌋₊).filter Nat.Prime, (1 : ℝ) / p -
        (Real.log (Real.log t) - Real.log (Real.log a))| ≤ C₂ / Real.log a)
    (T : ℝ) (hT : 1 < T) (c : ℕ → ℝ) (n : ℕ) (hc0 : 0 < c 0) (hmono : Monotone c)
    (h2 : 2 ≤ T ^ (c 0)) (f : ℕ → ℝ) (M : ℕ → ℝ) (hM0 : ∀ j < n, 0 ≤ M j)
    (hf : ∀ j < n, ∀ p : ℕ, p.Prime → T ^ (c j) < p → (p : ℝ) ≤ T ^ (c (j + 1)) → f p ≤ M j / p) :
    ∑ p ∈ (Ioc ⌊T ^ (c 0)⌋₊ ⌊T ^ (c n)⌋₊).filter Nat.Prime, f p ≤
      ∑ j ∈ range n, M j * (Real.log (c (j + 1) / c j) + C₂ / (c j * Real.log T)) := by
  have hlT : 0 < Real.log T := Real.log_pos hT
  have hgm : Monotone (fun j => ⌊T ^ (c j)⌋₊) := by
    intro i j hij
    exact Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le hT.le (hmono hij))
  rw [Finset.sum_filter, sum_Ioc_split _ (fun j => ⌊T ^ (c j)⌋₊) hgm n]
  apply Finset.sum_le_sum
  intro j hj
  rw [mem_range] at hj
  have hcj : 0 < c j := lt_of_lt_of_le hc0 (hmono (Nat.zero_le j))
  have hcj1 : c j ≤ c (j + 1) := hmono (Nat.le_succ j)
  have ha2 : 2 ≤ T ^ (c j) := le_trans h2 (Real.rpow_le_rpow_of_exponent_le hT.le (hmono (Nat.zero_le j)))
  have hat : T ^ (c j) ≤ T ^ (c (j + 1)) := Real.rpow_le_rpow_of_exponent_le hT.le hcj1
  rw [← Finset.sum_filter]
  calc ∑ p ∈ (Ioc ⌊T ^ (c j)⌋₊ ⌊T ^ (c (j + 1))⌋₊).filter Nat.Prime, f p
      ≤ ∑ p ∈ (Ioc ⌊T ^ (c j)⌋₊ ⌊T ^ (c (j + 1))⌋₊).filter Nat.Prime, M j / p := by
        apply Finset.sum_le_sum; intro p hp
        simp only [mem_filter, mem_Ioc] at hp
        refine hf j hj p hp.2 ?_ ?_
        · have := Nat.lt_floor_add_one (T ^ (c j))
          have h' : ((⌊T ^ (c j)⌋₊ + 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast hp.1.1
          push_cast at h'; linarith
        · exact le_trans (by exact_mod_cast hp.1.2) (Nat.floor_le (by linarith))
    _ = M j * ∑ p ∈ (Ioc ⌊T ^ (c j)⌋₊ ⌊T ^ (c (j + 1))⌋₊).filter Nat.Prime, (1 : ℝ) / p := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (hM0 j hj)
        have h := hC₂ _ _ ha2 hat
        have e1 : Real.log (T ^ (c j)) = c j * Real.log T := Real.log_rpow (by linarith) _
        have e2 : Real.log (T ^ (c (j + 1))) = c (j + 1) * Real.log T := Real.log_rpow (by linarith) _
        have e3 : Real.log (Real.log (T ^ (c (j + 1)))) - Real.log (Real.log (T ^ (c j))) =
            Real.log (c (j + 1) / c j) := by
          rw [e1, e2, Real.log_mul (by linarith) hlT.ne', Real.log_mul hcj.ne' hlT.ne',
            Real.log_div (by linarith) hcj.ne']
          ring
        rw [e3, e1] at h
        have := (abs_le.1 h).2
        linarith

end Palprimes
