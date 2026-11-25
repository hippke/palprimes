import KappaOmega2.Items.M02_G

/-! # M02 helpers (copied from S08, renamed), part A: `A_d = Σ_{k < z, d | k} g(k)` against `G(z/d)`. -/

namespace KappaOmega2

open Finset Palprimes

set_option linter.style.longLine false

/-- `A_d(z) = Σ_{k ∈ ltSet z, d | k} g(k)`. -/
noncomputable def m02A (b : ℕ) (z : ℝ) (d : ℕ) : ℝ := ∑ k ∈ (ltSet z).filter (fun k => d ∣ k), gS b k

/-- `S_d(w) = Σ_{k ∈ ltSet w, (k, d) = 1} g(k)`. -/
noncomputable def m02Sc (b : ℕ) (w : ℝ) (d : ℕ) : ℝ := ∑ k ∈ (ltSet w).filter (fun k => Nat.Coprime k d), gS b k

lemma m02_gS_mul (b d k : ℕ) (hd : Squarefree d) (hdB : Nat.Coprime d (bigB b)) :
    gS b (d * k) = if Nat.Coprime k d then gS b d * gS b k else 0 := by
  classical
  split_ifs with hc
  · have hc' : Nat.Coprime d k := hc.symm
    unfold gS
    by_cases hk : Squarefree k ∧ Nat.Coprime k (bigB b)
    · rw [if_pos ⟨Nat.squarefree_mul_iff.2 ⟨hc', hd, hk.1⟩, Nat.coprime_mul_iff_left.2 ⟨hdB, hk.2⟩⟩, if_pos ⟨hd, hdB⟩, if_pos hk,
        Nat.totient_mul hc']
      push_cast
      rw [one_div_mul_one_div]
    · rw [if_neg hk, mul_zero, if_neg]
      intro h
      apply hk
      exact ⟨(Nat.squarefree_mul_iff.1 h.1).2.2, Nat.Coprime.coprime_mul_left h.2⟩
  · unfold gS
    rw [if_neg]
    intro h
    exact hc (Nat.squarefree_mul_iff.1 h.1).1.symm

lemma m02_A_eq (b : ℕ) (z : ℝ) (d : ℕ) (hd : Squarefree d) (hdB : Nat.Coprime d (bigB b)) :
    m02A b z d = gS b d * m02Sc b (z / d) d := by
  classical
  have hd0 : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd0
  unfold m02A m02Sc
  have : ∑ k ∈ (ltSet z).filter (fun k => d ∣ k), gS b k = ∑ k' ∈ ltSet (z / d), gS b (d * k') := by
    symm
    apply Finset.sum_nbij' (fun j => d * j) (fun m => m / d)
    · intro j hj
      simp only [Finset.mem_coe, m02_mem_ltSet] at hj
      simp only [Finset.mem_coe, Finset.mem_filter, m02_mem_ltSet]
      refine ⟨⟨by nlinarith, ?_⟩, dvd_mul_right d j⟩
      push_cast
      rw [lt_div_iff₀ hdr] at hj
      linarith
    · intro m hm
      simp only [Finset.mem_coe, Finset.mem_filter, m02_mem_ltSet] at hm
      simp only [Finset.mem_coe, m02_mem_ltSet]
      obtain ⟨⟨h1, h2⟩, k, rfl⟩ := hm
      rw [Nat.mul_div_cancel_left k hd0]
      refine ⟨?_, ?_⟩
      · rcases Nat.eq_zero_or_pos k with h | h
        · subst h; simp at h1
        · exact h
      · rw [lt_div_iff₀ hdr]; push_cast at h2; linarith
    · intro j _; exact Nat.mul_div_cancel_left j hd0
    · intro m hm
      simp only [Finset.mem_coe, Finset.mem_filter] at hm
      exact Nat.mul_div_cancel' hm.2
    · intro j _; rfl
  rw [this, Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  rw [m02_gS_mul b d k hd hdB]

lemma m02_Sc_le (b : ℕ) (w : ℝ) (d : ℕ) : m02Sc b w d ≤ GS b w :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun n _ _ => m02_gS_nonneg b n)

lemma m02_Sc_nonneg (b : ℕ) (w : ℝ) (d : ℕ) : 0 ≤ m02Sc b w d :=
  Finset.sum_nonneg (fun n _ => m02_gS_nonneg b n)

lemma m02_A_nonneg (b : ℕ) (w : ℝ) (d : ℕ) : 0 ≤ m02A b w d :=
  Finset.sum_nonneg (fun n _ => m02_gS_nonneg b n)

lemma m02_A_prime_le (b : ℕ) (w : ℝ) (hw : 0 < w) (p : ℕ) (hp : p.Prime) : m02A b w p ≤ gS b p * GS b w := by
  classical
  by_cases hpB : Nat.Coprime p (bigB b)
  · rw [m02_A_eq b w p hp.squarefree hpB]
    apply mul_le_mul_of_nonneg_left _ (m02_gS_nonneg b p)
    refine le_trans (m02_Sc_le b _ p) (m02_GS_mono b ?_)
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    rw [div_le_iff₀ (by linarith)]; nlinarith
  · have : m02A b w p = 0 := by
      unfold m02A
      apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.mem_filter] at hk
      unfold gS
      rw [if_neg]
      intro h
      apply hpB
      exact Nat.Coprime.coprime_dvd_left hk.2 h.2
    rw [this]
    exact mul_nonneg (m02_gS_nonneg b p) (m02_GS_nonneg b w)

lemma m02_GS_le_Sc (b : ℕ) (w : ℝ) (d : ℕ) (hd : d ≠ 0) :
    GS b w ≤ m02Sc b w d + ∑ p ∈ d.primeFactors, m02A b w p := by
  classical
  unfold GS m02Sc m02A
  rw [Finset.sum_comm' (t' := ltSet w) (s' := fun k => d.primeFactors.filter (fun p => p ∣ k))
    (s := d.primeFactors) (t := fun p => (ltSet w).filter (fun k => p ∣ k))]
  swap
  · intro p k
    simp only [Finset.mem_filter]
    tauto
  rw [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _
  split_ifs with hc
  · have : 0 ≤ ∑ p ∈ d.primeFactors.filter (fun p => p ∣ k), gS b k :=
      Finset.sum_nonneg (fun _ _ => m02_gS_nonneg b k)
    linarith
  · simp only [zero_add]
    obtain ⟨p, hp, hpd⟩ := Nat.Prime.not_coprime_iff_dvd.1 hc
    have hpmem : p ∈ d.primeFactors.filter (fun p => p ∣ k) := by
      rw [Finset.mem_filter]; exact ⟨Nat.mem_primeFactors.2 ⟨hp, hpd.2, hd⟩, hpd.1⟩
    exact Finset.single_le_sum (f := fun _ => gS b k) (fun _ _ => m02_gS_nonneg b k) hpmem

/-- `d/φ(d)` and `σ_d = Σ_{p | d} g(p)`: `|d A_d − G(z/d)| ≤ ((c − 1) + cσ) G(z)`. -/
lemma m02_A_approx (b : ℕ) (z : ℝ) (hz : 0 < z) (d : ℕ) (hd : Squarefree d) (hdB : Nat.Coprime d (bigB b)) :
    |(d : ℝ) * m02A b z d - GS b (z / d)| ≤
      (((d : ℝ) * gS b d - 1) + (d : ℝ) * gS b d * ∑ p ∈ d.primeFactors, gS b p) * GS b z := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd0
  set c := (d : ℝ) * gS b d with hc
  have hc1 : 1 ≤ c := by
    rw [hc]; unfold gS; rw [if_pos ⟨hd, hdB⟩]
    have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.2 hd0
    rw [mul_one_div, le_div_iff₀ hφ, one_mul]; exact_mod_cast Nat.totient_le d
  have hzd : 0 < z / d := div_pos hz (by linarith)
  have hmono : GS b (z / d) ≤ GS b z := m02_GS_mono b (by rw [div_le_iff₀ (by linarith)]; nlinarith)
  have hA := m02_A_eq b z d hd hdB
  set S := m02Sc b (z / d) d
  have hS0 : 0 ≤ S := m02_Sc_nonneg b _ d
  have hSu : S ≤ GS b (z / d) := m02_Sc_le b _ d
  have hSl := m02_GS_le_Sc b (z / d) d hd.ne_zero
  have hsum : ∑ p ∈ d.primeFactors, m02A b (z / d) p ≤ (∑ p ∈ d.primeFactors, gS b p) * GS b z := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro p hp
    refine le_trans (m02_A_prime_le b _ hzd p (Nat.prime_of_mem_primeFactors hp)) ?_
    exact mul_le_mul_of_nonneg_left hmono (m02_gS_nonneg b p)
  have hσ0 : 0 ≤ ∑ p ∈ d.primeFactors, gS b p := Finset.sum_nonneg (fun p _ => m02_gS_nonneg b p)
  have hG0 := m02_GS_nonneg b z
  have hdA : (d : ℝ) * m02A b z d = c * S := by rw [hA, hc]; ring
  rw [hdA, abs_le]
  constructor
  · nlinarith
  · nlinarith

end KappaOmega2
