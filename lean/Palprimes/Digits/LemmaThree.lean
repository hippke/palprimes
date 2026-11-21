import Palprimes.Defs

/-! # M3. Lemma 3 (injectivity of symmetric digit strings)

PROOF_buniform.md §1. Proved here by a shorter argument than the carry induction there.
Let `j0` be the lowest index with `t_{j0} ≠ 0`. Reducing `Σ t_j b^j = 0` modulo `b^{j0+1}`
gives `b ∣ t_{j0}`, so `|t_{j0}| ≥ b`. By symmetry the highest nonzero index is
`m = 2L − j0` with `t_m = t_{j0}`, and `|t_m| b^m ≥ 2b^m > (2b−2)(b^m−1)/(b−1) ≥ |Σ_{j<m} t_j b^j|`,
so the sum cannot vanish. -/

open Finset

namespace Palprimes

/-- **Lemma 3.** A symmetric string `t_0, …, t_{2L}` with `|t_j| ≤ 2b − 2` and
`Σ t_j b^j = 0` vanishes. -/
theorem symm_digits_eq_zero (b L : ℕ) (hb : 2 ≤ b) (t : ℕ → ℤ)
    (hbound : ∀ j ≤ 2 * L, |t j| ≤ 2 * (b : ℤ) - 2)
    (hsymm : ∀ j ≤ 2 * L, t j = t (2 * L - j))
    (hsum : ∑ j ∈ range (2 * L + 1), t j * (b : ℤ) ^ j = 0) :
    ∀ j ≤ 2 * L, t j = 0 := by
  classical
  by_contra hne
  push Not at hne
  have hex : ∃ j, j ≤ 2 * L ∧ t j ≠ 0 := hne
  obtain ⟨hj0le, hj0ne⟩ := Nat.find_spec hex
  set j0 := Nat.find hex with hj0def
  have hmin : ∀ j < j0, j ≤ 2 * L → t j = 0 := fun j hj hjle => by
    by_contra h
    exact Nat.find_min hex hj ⟨hjle, h⟩
  set m := 2 * L - j0 with hm
  have htm : t m = t j0 := (hsymm j0 hj0le).symm
  have hzero_above : ∀ j, m < j → j ≤ 2 * L → t j = 0 := fun j hj hjle => by
    rw [hsymm j hjle]
    exact hmin _ (by omega) (by omega)
  have hb0 : (0 : ℤ) < b := by exact_mod_cast (by omega : 0 < b)
  -- the lowest nonzero digit is divisible by `b`
  have hdvd : (b : ℤ) ∣ t j0 := by
    have hrest : (b : ℤ) ^ (j0 + 1) ∣ ∑ j ∈ (range (2 * L + 1)).erase j0, t j * (b : ℤ) ^ j := by
      apply Finset.dvd_sum
      intro j hj
      obtain ⟨hjne, hjr⟩ := Finset.mem_erase.1 hj
      rw [Finset.mem_range] at hjr
      rcases lt_or_gt_of_ne hjne with h | h
      · rw [hmin j h (by omega)]
        simp
      · exact Dvd.dvd.mul_left (pow_dvd_pow _ h) _
    have hsplit := Finset.add_sum_erase (range (2 * L + 1)) (fun j => t j * (b : ℤ) ^ j)
      (Finset.mem_range.2 (by omega : j0 < 2 * L + 1))
    beta_reduce at hsplit
    have h1 : (b : ℤ) ^ (j0 + 1) ∣ t j0 * (b : ℤ) ^ j0 := by
      have : t j0 * (b : ℤ) ^ j0 = -(∑ j ∈ (range (2 * L + 1)).erase j0, t j * (b : ℤ) ^ j) := by
        linarith
      rw [this]
      exact (dvd_neg).2 hrest
    rw [pow_succ, mul_comm (t j0)] at h1
    exact (mul_dvd_mul_iff_left (pow_ne_zero _ hb0.ne')).1 h1
  -- hence the top digit has size at least `b`
  have habs : (b : ℤ) ≤ |t m| := by
    rw [htm]
    obtain ⟨k, hk⟩ := hdvd
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hk
      exact hj0ne hk
    rw [hk, abs_mul, abs_of_pos hb0]
    exact le_mul_of_one_le_right hb0.le (Int.one_le_abs hk0)
  -- the top term dominates the rest
  have hsplit2 : ∑ j ∈ range (2 * L + 1), t j * (b : ℤ) ^ j =
      ∑ j ∈ range m, t j * (b : ℤ) ^ j + t m * (b : ℤ) ^ m := by
    rw [← Finset.sum_range_add_sum_Ico _ (by omega : m + 1 ≤ 2 * L + 1), Finset.sum_range_succ]
    have : ∑ j ∈ Ico (m + 1) (2 * L + 1), t j * (b : ℤ) ^ j = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [Finset.mem_Ico] at hj
      rw [hzero_above j (by omega) (by omega)]
      simp
    rw [this, add_zero]
  have hlow : |∑ j ∈ range m, t j * (b : ℤ) ^ j| ≤ 2 * (b : ℤ) ^ m - 2 := by
    calc |∑ j ∈ range m, t j * (b : ℤ) ^ j| ≤ ∑ j ∈ range m, |t j * (b : ℤ) ^ j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ range m, (2 * (b : ℤ) - 2) * (b : ℤ) ^ j := by
          apply Finset.sum_le_sum
          intro j hj
          rw [Finset.mem_range] at hj
          rw [abs_mul, abs_of_pos (pow_pos hb0 _)]
          exact mul_le_mul_of_nonneg_right (hbound j (by omega)) (pow_pos hb0 _).le
      _ = 2 * ((∑ j ∈ range m, (b : ℤ) ^ j) * ((b : ℤ) - 1)) := by
          rw [← Finset.mul_sum]
          ring
      _ = 2 * (b : ℤ) ^ m - 2 := by
          rw [geom_sum_mul]
          ring
  have htop : 2 * (b : ℤ) ^ m ≤ |t m * (b : ℤ) ^ m| := by
    rw [abs_mul, abs_of_pos (pow_pos hb0 _)]
    have h2b : (2 : ℤ) ≤ b := by exact_mod_cast hb
    exact mul_le_mul_of_nonneg_right (le_trans h2b habs) (pow_pos hb0 _).le
  rw [hsplit2] at hsum
  have : t m * (b : ℤ) ^ m = -(∑ j ∈ range m, t j * (b : ℤ) ^ j) := by linarith
  rw [this, abs_neg] at htop
  linarith


/-- Form used downstream: a combination `Σ_{k≤L} s_k c_k` with `|s_k| ≤ 2b − 2`
vanishes only if all `s_k` vanish (`c_k = b^k + b^{2L−k}`, `c_L = b^L`). -/
theorem sum_cK_eq_zero (b L : ℕ) (hb : 2 ≤ b) (s : ℕ → ℤ)
    (hbound : ∀ k ≤ L, |s k| ≤ 2 * (b : ℤ) - 2)
    (hsum : ∑ k ∈ range (L + 1), s k * (cK b L k : ℤ) = 0) :
    ∀ k ≤ L, s k = 0 := by
  set t : ℕ → ℤ := fun j => if j ≤ L then s j else s (2 * L - j) with ht
  have hre : ∑ j ∈ range (2 * L + 1), t j * (b : ℤ) ^ j =
      ∑ k ∈ range (L + 1), s k * (cK b L k : ℤ) := by
    rw [← Finset.sum_range_add_sum_Ico _ (by omega : L + 1 ≤ 2 * L + 1),
      Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ,
      Finset.sum_range_succ (fun k => s k * (cK b L k : ℤ))]
    have hc : ∀ k ∈ range L, s k * (cK b L k : ℤ) =
        s k * (b : ℤ) ^ k + s k * (b : ℤ) ^ (2 * L - k) := by
      intro k hk
      rw [Finset.mem_range] at hk
      simp [cK, hk]
      ring
    rw [Finset.sum_congr rfl hc, Finset.sum_add_distrib]
    have h1 : ∑ x ∈ range L, t x * (b : ℤ) ^ x = ∑ x ∈ range L, s x * (b : ℤ) ^ x :=
      Finset.sum_congr rfl (fun x hx => by
        rw [Finset.mem_range] at hx
        simp [ht, show x ≤ L by omega])
    have h2 : t L = s L := by simp [ht]
    have h3 : (cK b L L : ℤ) = (b : ℤ) ^ L := by simp [cK]
    have h4 : ∑ k ∈ range (2 * L + 1 - (L + 1)), t (L + 1 + k) * (b : ℤ) ^ (L + 1 + k) =
        ∑ k ∈ range L, s k * (b : ℤ) ^ (2 * L - k) := by
      rw [show 2 * L + 1 - (L + 1) = L by omega,
        ← Finset.sum_range_reflect (fun k => s k * (b : ℤ) ^ (2 * L - k)) L]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      simp only [ht, show ¬ (L + 1 + k ≤ L) by omega, ite_false]
      rw [show 2 * L - (L + 1 + k) = L - 1 - k by omega,
        show 2 * L - (L - 1 - k) = L + 1 + k by omega]
    rw [h1, h2, h3, h4]
    ring
  have key : ∀ j ≤ 2 * L, t j = 0 := by
    apply symm_digits_eq_zero b L hb t
    · intro j hj
      simp only [ht]
      split_ifs with h
      · exact hbound j h
      · exact hbound _ (by omega)
    · intro j hj
      simp only [ht]
      split_ifs with h1 h2 h2 <;> first | rfl | (congr 1; omega)
    · rw [hre, hsum]
  intro k hk
  have := key k (by omega)
  simpa [ht, hk] using this

end Palprimes
