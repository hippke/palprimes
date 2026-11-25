import Omega3.Statements
import Palprimes.ExpSum.ColBound

/-!
# L12. Lemma K (weighted Col bound)

`Π_{1≤n≤M} ‖G_g(c_n α)‖ ≤ exp(−g(0)g(1)⌊(M − 1)/L_q⌋/(b⁴(b+1)²))`, `L_q = max(1, ⌊log_b q⌋)`, at
`α = h/q + k/(b³ − b)`. Proof in `L12_PLAN.md`: pointwise `‖G_g(t)‖ ≤ exp(−8g(0)g(1)‖t‖²)` (from the pair (0, 1)),
TP's pairing `b c_n − c_{n+1} = (b² − 1)b^{2N−n−1}`, Maynard's windows of length `L_q`. The pairing and the
window sum follow Palprimes `col_bound` (ExpSum/ColBound.lean); the window lemma is re-proved for the shorter window.
-/

set_option linter.style.longLine false

open Finset Real

namespace Omega3

open Palprimes

/-- Maynard's window argument with windows of length `max 1 ⌊log_b q⌋`. -/
theorem L12_window (b q a : ℕ) (hb : 2 ≤ b) (hq : 2 ≤ q) (haq : Nat.Coprime a q)
    (hbq : Nat.Coprime b q) (j0 : ℕ) :
    ∃ j ∈ Ico j0 (j0 + max 1 (Nat.log b q)),
      1 / (2 * (b : ℝ) ^ 2) ≤ distZ (((a * b ^ j : ℕ) : ℝ) / q) := by
  set L := max 1 (Nat.log b q) with hL
  have hL1 : 1 ≤ L := le_max_left _ _
  have hLlog : Nat.log b q ≤ L := le_max_right _ _
  by_contra hcon
  push Not at hcon
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hq0 : 0 < q := by omega
  set e : ℕ → ℝ := fun j => distZ (((a * b ^ j : ℕ) : ℝ) / q)
  have hstart : 1 / (q : ℝ) ≤ e j0 := by
    have := distZ_div_ge ((a * b ^ j0 : ℕ) : ℤ) q hq0 (by
      intro hd
      have hd' : q ∣ a * b ^ j0 := by exact_mod_cast hd
      have hcop : Nat.Coprime (a * b ^ j0) q := Nat.Coprime.mul_left haq (Nat.Coprime.pow_left _ hbq)
      have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm hcop) hd'
      omega)
    simpa [e] using this
  have hgrow : ∀ i, i < L → (b : ℝ) ^ i / q ≤ e (j0 + i) := by
    intro i
    induction i with
    | zero => intro _; simpa using hstart
    | succ i ih =>
      intro hi
      have hprev := ih (by omega)
      have hsmall := hcon (j0 + i) (by rw [mem_Ico]; omega)
      have hb2 : (b : ℝ) * e (j0 + i) ≤ 1 / 2 := by
        have : (b : ℝ) * e (j0 + i) < b * (1 / (2 * (b : ℝ) ^ 2)) :=
          mul_lt_mul_of_pos_left hsmall (by linarith)
        have h' : (b : ℝ) * (1 / (2 * (b : ℝ) ^ 2)) ≤ 1 / 2 := by
          rw [show (b : ℝ) * (1 / (2 * (b : ℝ) ^ 2)) = 1 / (2 * b) by field_simp]
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
        linarith
      have hm := distZ_mul_ge b _ hb2
      have he : ((a * b ^ (j0 + (i + 1)) : ℕ) : ℝ) / q = (b : ℝ) * (((a * b ^ (j0 + i) : ℕ) : ℝ) / q) := by
        push_cast; rw [show j0 + (i + 1) = (j0 + i) + 1 by ring, pow_succ]; ring
      have : e (j0 + (i + 1)) ≥ (b : ℝ) * e (j0 + i) := by
        simp only [e]; rw [he]; exact hm
      calc (b : ℝ) ^ (i + 1) / q = (b : ℝ) * ((b : ℝ) ^ i / q) := by ring
        _ ≤ (b : ℝ) * e (j0 + i) := mul_le_mul_of_nonneg_left hprev (by linarith)
        _ ≤ _ := this
  have hlast := hgrow (L - 1) (by omega)
  have hlt : (q : ℝ) < (b : ℝ) ^ (L + 1) := by
    have h1 : q < b ^ (Nat.log b q + 1) := Nat.lt_pow_succ_log_self (by omega : 1 < b) q
    have h2 : b ^ (Nat.log b q + 1) ≤ b ^ (L + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    exact_mod_cast lt_of_lt_of_le h1 h2
  have hge : 1 / (b : ℝ) ^ 2 < (b : ℝ) ^ (L - 1) / q := by
    rw [div_lt_div_iff₀ (by positivity) (by exact_mod_cast hq0)]
    have : (b : ℝ) ^ (L - 1) * (b : ℝ) ^ 2 = (b : ℝ) ^ (L + 1) := by
      rw [← pow_add]; congr 1; omega
    linarith
  have hsmall := hcon (j0 + (L - 1)) (by rw [mem_Ico]; omega)
  have : 1 / (2 * (b : ℝ) ^ 2) ≤ 1 / (b : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  linarith

/-- `‖G_g(t)‖² = Σ_{u,v} g(u)g(v) cos 2π(u − v)t`. -/
theorem L12_normSq (b : ℕ) (g : ℕ → ℝ) (t : ℝ) :
    ‖Gg b g t‖ ^ 2 = ∑ u ∈ range b, ∑ v ∈ range b, g u * g v * Real.cos (2 * π * (((u : ℝ) - v) * t)) := by
  set F := Gg b g t
  have h1 : ‖F‖ ^ 2 = (F * starRingEnd ℂ F).re := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [h1]
  simp only [F, Gg]
  rw [map_sum, Finset.sum_mul_sum, Complex.re_sum]
  apply Finset.sum_congr rfl; intro u _
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl; intro v _
  rw [map_mul, Complex.conj_ofReal, conj_ee]
  have : (g u : ℂ) * ee (u * t) * ((g v : ℂ) * ee (-(v * t))) =
      ((g u * g v : ℝ) : ℂ) * ee (u * t + -(v * t)) := by
    rw [ee_add]; push_cast; ring
  rw [this, Complex.re_ofReal_mul, re_ee]
  congr 2; ring

/-- Pointwise bound `‖G_g(t)‖ ≤ exp(−8g(0)g(1)‖t‖²)`. -/
theorem L12_pointwise (b : ℕ) (hb : 2 ≤ b) (g : ℕ → ℝ) (hg : IsDigitWeight b g) (t : ℝ) :
    ‖Gg b g t‖ ≤ Real.exp (-(8 * (g 0 * g 1)) * distZ t ^ 2) := by
  obtain ⟨hg0, hg1⟩ := hg
  set f : ℕ × ℕ → ℝ := fun p => g p.1 * g p.2 * (1 - Real.cos (2 * π * (((p.1 : ℝ) - p.2) * t))) with hf
  have hf0 : ∀ p, 0 ≤ f p := fun p => mul_nonneg (mul_nonneg (hg0 _) (hg0 _))
    (by linarith [Real.cos_le_one (2 * π * (((p.1 : ℝ) - p.2) * t))])
  set c := Real.cos (2 * π * t) with hcdef
  have hc : 1 - c ≥ 8 * distZ t ^ 2 := by
    have h2 : c = 1 - 2 * Real.sin (π * t) ^ 2 := by
      simp only [c]
      rw [show 2 * π * t = 2 * (π * t) by ring, Real.cos_two_mul, Real.cos_sq']; ring
    have h3 := abs_sin_pi_ge t
    have h4 : (2 * distZ t) ^ 2 ≤ Real.sin (π * t) ^ 2 := by
      rw [← sq_abs (Real.sin _)]; exact pow_le_pow_left₀ (by have := distZ_nonneg t; linarith) h3 2
    rw [h2]; nlinarith
  have hsum : ‖Gg b g t‖ ^ 2 = 1 - ∑ p ∈ range b ×ˢ range b, f p := by
    have e1 : ∑ p ∈ range b ×ˢ range b, f p =
        ∑ p ∈ range b ×ˢ range b, g p.1 * g p.2 -
          ∑ p ∈ range b ×ˢ range b, g p.1 * g p.2 * Real.cos (2 * π * (((p.1 : ℝ) - p.2) * t)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro p _; simp only [hf]; ring
    have e2 : ∑ p ∈ range b ×ˢ range b, g p.1 * g p.2 = 1 := by
      rw [Finset.sum_product, ← Finset.sum_mul_sum, hg1, one_mul]
    have e3 : ∑ p ∈ range b ×ˢ range b, g p.1 * g p.2 * Real.cos (2 * π * (((p.1 : ℝ) - p.2) * t)) =
        ‖Gg b g t‖ ^ 2 := by
      rw [Finset.sum_product, L12_normSq]
    rw [e1, e2, e3]; ring
  have hsub : ({(1, 0), (0, 1)} : Finset (ℕ × ℕ)) ⊆ range b ×ˢ range b := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rw [mem_product, mem_range, mem_range]
    rcases hp with rfl | rfl <;> constructor <;> simp <;> omega
  have hpair : ∑ p ∈ ({(1, 0), (0, 1)} : Finset (ℕ × ℕ)), f p = 2 * (g 0 * g 1) * (1 - c) := by
    rw [Finset.sum_pair (by simp)]
    simp only [hf, c]
    push_cast
    rw [show 2 * π * ((0 - 1) * t) = -(2 * π * t) by ring, Real.cos_neg,
      show 2 * π * ((1 - 0) * t) = 2 * π * t by ring]
    ring
  have hlow : 2 * (g 0 * g 1) * (1 - c) ≤ ∑ p ∈ range b ×ˢ range b, f p := by
    rw [← hpair]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => hf0 p)
  have hgs : 0 ≤ g 0 * g 1 := mul_nonneg (hg0 0) (hg0 1)
  have hsq : ‖Gg b g t‖ ^ 2 ≤ Real.exp (-(8 * (g 0 * g 1)) * distZ t ^ 2) ^ 2 := by
    rw [← Real.exp_natCast_mul]
    have := Real.add_one_le_exp ((2 : ℕ) * (-(8 * (g 0 * g 1)) * distZ t ^ 2))
    have h16 : 2 * (g 0 * g 1) * (8 * distZ t ^ 2) ≤ 2 * (g 0 * g 1) * (1 - c) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    push_cast at this ⊢
    nlinarith
  have hE0 : 0 ≤ Real.exp (-(8 * (g 0 * g 1)) * distZ t ^ 2) := (Real.exp_pos _).le
  by_contra hcon
  push Not at hcon
  have : Real.exp (-(8 * (g 0 * g 1)) * distZ t ^ 2) ^ 2 < ‖Gg b g t‖ ^ 2 := by
    exact pow_lt_pow_left₀ hcon hE0 (by norm_num)
  linarith

/-- `‖G_g(−t)‖ = ‖G_g(t)‖` (real weights). -/
theorem L12_norm_neg (b : ℕ) (g : ℕ → ℝ) (t : ℝ) : ‖Gg b g (-t)‖ = ‖Gg b g t‖ := by
  have h : Gg b g (-t) = starRingEnd ℂ (Gg b g t) := by
    simp only [Gg]
    rw [map_sum]
    apply Finset.sum_congr rfl; intro a _
    rw [map_mul, Complex.conj_ofReal, conj_ee, show (a : ℝ) * -t = -(a * t) by ring]
  rw [h, Complex.norm_conj]

/-- Lemma K for `h ≥ 0` (written with `h : ℕ`). -/
theorem L12_main_nat (b : ℕ) (hb : 2 ≤ b) (g : ℕ → ℝ) (hg : IsDigitWeight b g)
    (N q M h : ℕ) (k : ℤ) (hq : 2 ≤ q) (hh : Nat.Coprime h q) (hqB : Nat.Coprime q (bigB b))
    (hMN : M + 1 ≤ N) :
    ∏ n ∈ Icc 1 M, ‖Gg b g ((cK b N n : ℝ) * ((h : ℝ) / q + (k : ℝ) / (bigB b : ℝ)))‖ ≤
      Real.exp (-(g 0 * g 1) * (((M - 1) / max 1 (Nat.log b q) : ℕ) : ℝ) /
        ((b : ℝ) ^ 4 * ((b : ℝ) + 1) ^ 2)) := by
  rw [← Finset.Ico_add_one_right_eq_Icc]
  have hb1 : 1 ≤ b := by omega
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  set α : ℝ := (h : ℝ) / q + k / (bigB b : ℝ) with hα
  set d : ℕ → ℝ := fun n => distZ (cK b N n * α) with hd
  set κ : ℝ := 8 * (g 0 * g 1) with hκ
  have hκ0 : 0 ≤ κ := by rw [hκ]; have := mul_nonneg (hg.1 0) (hg.1 1); positivity
  have hA : ∀ n, ‖Gg b g ((cK b N n : ℝ) * α)‖ ≤ Real.exp (-κ * d n ^ 2) := by
    intro n; exact L12_pointwise b hb g hg _
  have hprod : ∏ n ∈ Ico 1 (M + 1), ‖Gg b g ((cK b N n : ℝ) * α)‖ ≤
      Real.exp (-κ * ∑ n ∈ Ico 1 (M + 1), d n ^ 2) := by
    calc _ ≤ ∏ n ∈ Ico 1 (M + 1), Real.exp (-κ * d n ^ 2) :=
          Finset.prod_le_prod₀ (fun n _ => norm_nonneg _) (fun n _ => hA n)
      _ = _ := by rw [← Real.exp_sum, Finset.mul_sum]
  refine hprod.trans ?_
  apply Real.exp_le_exp.2
  set L := max 1 (Nat.log b q) with hLdef
  have hL1 : 1 ≤ L := le_max_left _ _
  set W := (M - 1) / L
  set a := h * (b ^ 2 - 1)
  set E : ℕ → ℝ := fun n => distZ (((a * b ^ (2 * N - n - 1) : ℕ) : ℝ) / q)
  have hB : bigB b = b * (b ^ 2 - 1) := by
    rw [bigB_eq b hb1]
    obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
    rw [show c + 1 - 1 = c by omega]
    have : (c + 1) ^ 2 - 1 = c * (c + 2) := by
      rw [show (c + 1) ^ 2 = c * (c + 2) + 1 by ring]; omega
    rw [this]; ring
  have hqb : Nat.Coprime b q := by
    have := Nat.Coprime.coprime_dvd_right (show b ∣ bigB b from ⟨b ^ 2 - 1, hB⟩) hqB
    exact this.symm
  have hqa : Nat.Coprime a q := by
    have h2 := Nat.Coprime.coprime_dvd_right (show b ^ 2 - 1 ∣ bigB b from ⟨b, by rw [hB]; ring⟩) hqB
    exact Nat.Coprime.mul_left hh h2.symm
  -- pairing
  have hC : ∀ n ∈ Ico 1 M, E n ^ 2 ≤ ((b : ℝ) + 1) ^ 2 * (d n ^ 2 + d (n + 1) ^ 2) := by
    intro n hn
    rw [mem_Ico] at hn
    set jj := 2 * N - n - 1
    have hj1 : 1 ≤ jj := by omega
    have hcn : (cK b N n : ℝ) = (b : ℝ) ^ n + (b : ℝ) ^ (2 * N - n) := by
      simp [cK, show n < N by omega]
    have hcn1 : (cK b N (n + 1) : ℝ) = (b : ℝ) ^ (n + 1) + (b : ℝ) ^ jj := by
      simp only [cK, show n + 1 < N by omega, ite_true]; push_cast
      rw [show 2 * N - (n + 1) = jj by omega]
    have hid : (b : ℝ) * (cK b N n * α) - cK b N (n + 1) * α =
        ((a * b ^ jj : ℕ) : ℝ) / q + ((k * b ^ (jj - 1) : ℤ) : ℝ) := by
      rw [hcn, hcn1, hα, bigB_real b hb1]
      have hpow : (b : ℝ) ^ (2 * N - n) = (b : ℝ) ^ jj * b := by
        rw [← pow_succ]; congr 1; omega
      have hpow2 : (b : ℝ) ^ jj = (b : ℝ) ^ (jj - 1) * b := by
        rw [← pow_succ]; congr 1; omega
      have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
      have hb2 : (b : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
      have hb0 : (b : ℝ) ≠ 0 := by linarith
      simp only [a]
      push_cast [show 1 ≤ b ^ 2 by nlinarith]
      rw [hpow, hpow2]
      field_simp
      ring
    have hE : E n = distZ ((b : ℝ) * (cK b N n * α) - cK b N (n + 1) * α) := by
      rw [hid, distZ_add_int]
    have hle : E n ≤ (b : ℝ) * d n + d (n + 1) := by
      rw [hE]
      calc distZ ((b : ℝ) * (cK b N n * α) - cK b N (n + 1) * α)
          ≤ distZ ((b : ℝ) * (cK b N n * α)) + distZ (cK b N (n + 1) * α) := distZ_sub_le _ _
        _ ≤ (b : ℝ) * d n + d (n + 1) := by
            have := distZ_nat_mul_le b (cK b N n * α)
            simp only [hd]; linarith
    have h0 : 0 ≤ E n := distZ_nonneg _
    have hd0 : 0 ≤ d n := distZ_nonneg _
    have hd1 : 0 ≤ d (n + 1) := distZ_nonneg _
    nlinarith [sq_nonneg ((b : ℝ) * d (n + 1) - d n), sq_nonneg (d n - d (n + 1))]
  -- windows
  have hD : (W : ℝ) * (1 / (2 * (b : ℝ) ^ 2)) ^ 2 ≤ ∑ n ∈ Ico 1 M, E n ^ 2 := by
    have hw := window_sum_ge (fun n => E n ^ 2) (fun n => sq_nonneg _) 1 L W
      ((1 / (2 * (b : ℝ) ^ 2)) ^ 2) (by
        intro i hi
        set s := 1 + i * L
        obtain ⟨jx, hjx, hge⟩ := L12_window b q a hb hq hqa hqb (2 * N - s - L)
        rw [mem_Ico] at hjx
        have hWL : W * L ≤ M - 1 := Nat.div_mul_le_self _ _
        have hsL : s + L ≤ M := by
          have h3 : (i + 1) * L ≤ W * L := Nat.mul_le_mul_right _ (by omega)
          have h4 : (i + 1) * L ≤ M - 1 := le_trans h3 hWL
          have e1 : s + L = (i + 1) * L + 1 := by simp only [s]; ring
          rw [e1]; omega
        have hN2 : s + L ≤ N := le_trans hsL (by omega : M ≤ N)
        have hjx1 : 2 * N - s - L ≤ jx := hjx.1
        have hjx2 : jx < 2 * N - s - L + L := hjx.2
        refine ⟨2 * N - jx - 1, ?_, ?_⟩
        · rw [mem_Ico]; constructor <;> omega
        · have : 2 * N - (2 * N - jx - 1) - 1 = jx := by omega
          simp only [E, this]
          exact pow_le_pow_left₀ (by positivity) hge 2)
    calc (W : ℝ) * (1 / (2 * (b : ℝ) ^ 2)) ^ 2 ≤ ∑ n ∈ Ico 1 (1 + W * L), E n ^ 2 := hw
      _ ≤ _ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n hn; rw [mem_Ico] at hn ⊢
            have : W * L ≤ M - 1 := Nat.div_mul_le_self _ _
            omega
          · intro _ _ _; exact sq_nonneg _
  have hB2 : ∑ n ∈ Ico 1 M, (d n ^ 2 + d (n + 1) ^ 2) ≤ 2 * ∑ n ∈ Ico 1 (M + 1), d n ^ 2 := by
    rw [Finset.sum_add_distrib, two_mul]
    apply add_le_add
    · apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right (by omega))
      intro _ _ _; exact sq_nonneg _
    · rw [Finset.sum_Ico_add' (fun n => d n ^ 2)]
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico (by omega) le_rfl)
      intro _ _ _; exact sq_nonneg _
  have hsumC : ∑ n ∈ Ico 1 M, E n ^ 2 ≤ ((b : ℝ) + 1) ^ 2 * ∑ n ∈ Ico 1 M, (d n ^ 2 + d (n + 1) ^ 2) := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum hC
  have hfinal : (W : ℝ) / (8 * (b : ℝ) ^ 4 * ((b : ℝ) + 1) ^ 2) ≤ ∑ n ∈ Ico 1 (M + 1), d n ^ 2 := by
    have hpos : (0 : ℝ) < ((b : ℝ) + 1) ^ 2 := by positivity
    have : (W : ℝ) * (1 / (2 * (b : ℝ) ^ 2)) ^ 2 ≤ ((b : ℝ) + 1) ^ 2 * (2 * ∑ n ∈ Ico 1 (M + 1), d n ^ 2) :=
      hD.trans (hsumC.trans (mul_le_mul_of_nonneg_left hB2 hpos.le))
    rw [div_le_iff₀ (by positivity)]
    have e : (W : ℝ) * (1 / (2 * (b : ℝ) ^ 2)) ^ 2 = (W : ℝ) / (4 * (b : ℝ) ^ 4) := by field_simp; ring
    rw [e, div_le_iff₀ (by positivity)] at this
    nlinarith
  have hk : -(g 0 * g 1) * (W : ℝ) / ((b : ℝ) ^ 4 * ((b : ℝ) + 1) ^ 2) =
      -κ * ((W : ℝ) / (8 * (b : ℝ) ^ 4 * ((b : ℝ) + 1) ^ 2)) := by
    rw [hκ]; field_simp
  rw [hk]
  exact mul_le_mul_of_nonpos_left hfinal (by linarith)

theorem itemL12 : ItemL12 := by
  intro b g hb hg N q M h k hq hcop hM hMN
  have hqh : Nat.Coprime q h.natAbs := Nat.Coprime.coprime_dvd_right (dvd_mul_right _ _) hcop
  have hqB : Nat.Coprime q (bigB b) := Nat.Coprime.coprime_dvd_right (dvd_mul_left _ _) hcop
  rcases le_or_gt 0 h with h0 | h0
  · have hcast : (h : ℝ) = ((h.natAbs : ℕ) : ℝ) := by
      rw [Nat.cast_natAbs, abs_of_nonneg h0]
    rw [hcast]
    exact L12_main_nat b hb g hg N q M h.natAbs k hq hqh.symm hqB hMN
  · have hcast : (h : ℝ) = -((h.natAbs : ℕ) : ℝ) := by
      rw [Nat.cast_natAbs, abs_of_neg h0]; simp
    have hrw : ∀ n ∈ Icc 1 M, ‖Gg b g ((cK b N n : ℝ) * ((h : ℝ) / q + (k : ℝ) / (bigB b : ℝ)))‖ =
        ‖Gg b g ((cK b N n : ℝ) * (((h.natAbs : ℕ) : ℝ) / q + ((-k : ℤ) : ℝ) / (bigB b : ℝ)))‖ := by
      intro n _
      rw [← L12_norm_neg, hcast]
      congr 2
      push_cast; ring
    rw [Finset.prod_congr rfl hrw]
    exact L12_main_nat b hb g hg N q M h.natAbs (-k) hq hqh.symm hqB hMN

end Omega3
