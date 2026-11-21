import Palprimes.ExpSum.Farey

/-! # M8. Col's L^∞ bound (TP Prop. 6.2), elementary version

Instead of Mauduit–Rivat's expansion, `ψ(t) ≤ exp(−16(b−1)‖t‖²/b²)` (from
`φ² = Σ_{u,v} cos 2π(u−v)t` and Jordan's inequality on the `2(b−1)` adjacent pairs);
TP's pairing `b c_n − c_{n+1} = (b²−1) b^{2N−n−1}` removes the shift `k/(b³−b)`;
Maynard's window argument gives `‖a b^j/q‖ ≥ 1/(2b²)` in every window of `⌊log_b q⌋+1`
exponents. Result: `Π_{1≤n≤M} √ψ(c_n α) ≤ exp(−c_b ⌊(M−1)/(⌊log_b q⌋+1)⌋)`,
`c_b = (b−1)/(b⁶(b+1)²)`. -/

set_option linter.style.longLine false

open Finset Real

namespace Palprimes

theorem distZ_nonneg (t : ℝ) : 0 ≤ distZ t := abs_nonneg _

theorem distZ_sub_le (x y : ℝ) : distZ (x - y) ≤ distZ x + distZ y := by
  calc distZ (x - y) ≤ |x - y - ((round x - round y : ℤ) : ℝ)| := distZ_le _ _
    _ = |(x - round x) - (y - round y)| := by push_cast; ring_nf
    _ ≤ |x - round x| + |y - round y| := abs_sub _ _

theorem distZ_nat_mul_le (k : ℕ) (x : ℝ) : distZ (k * x) ≤ k * distZ x := by
  calc distZ (k * x) ≤ |k * x - ((k * round x : ℤ) : ℝ)| := distZ_le _ _
    _ = k * |x - round x| := by
        push_cast
        rw [show (k : ℝ) * x - k * round x = k * (x - round x) by ring, abs_mul,
          abs_of_nonneg (Nat.cast_nonneg k)]

/-- If `b‖x‖ ≤ 1/2` then `‖bx‖ = b‖x‖` (lower bound direction). -/
theorem distZ_mul_ge (b : ℕ) (x : ℝ) (h : (b : ℝ) * distZ x ≤ 1 / 2) :
    (b : ℝ) * distZ x ≤ distZ (b * x) := by
  set r := round x
  set m := round ((b : ℝ) * x)
  have hdx : distZ x = |x - r| := rfl
  by_cases hm : m = b * r
  · have : distZ ((b : ℝ) * x) = |(b : ℝ) * x - m| := rfl
    rw [this, hm, hdx]; push_cast
    rw [show (b : ℝ) * x - b * r = b * (x - r) by ring, abs_mul, Nat.abs_cast]
  · have hne : (1 : ℝ) ≤ |(m : ℝ) - (b * r : ℤ)| := by
      have : (m - b * r : ℤ) ≠ 0 := sub_ne_zero.2 hm
      have := Int.one_le_abs this
      exact_mod_cast this
    have : distZ ((b : ℝ) * x) = |(b : ℝ) * x - m| := rfl
    rw [this]
    have h1 : |(b : ℝ) * x - (b * r : ℤ)| = b * distZ x := by
      rw [hdx]; push_cast
      rw [show (b : ℝ) * x - b * r = b * (x - r) by ring, abs_mul, Nat.abs_cast]
    have h2 : |(m : ℝ) - (b * r : ℤ)| ≤ |(b : ℝ) * x - m| + |(b : ℝ) * x - (b * r : ℤ)| := by
      calc |(m : ℝ) - (b * r : ℤ)| = |((b : ℝ) * x - (b * r : ℤ)) - ((b : ℝ) * x - m)| := by ring_nf
        _ ≤ |(b : ℝ) * x - (b * r : ℤ)| + |(b : ℝ) * x - m| := abs_sub _ _
        _ = _ := by ring
    linarith

/-- `distZ(m/q) ≥ 1/q` unless `q ∣ m`. -/
theorem distZ_div_ge (m : ℤ) (q : ℕ) (hq : 0 < q) (hm : ¬ (q : ℤ) ∣ m) :
    1 / (q : ℝ) ≤ distZ ((m : ℝ) / q) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  set r := round ((m : ℝ) / q)
  have : distZ ((m : ℝ) / q) = |((m - r * q : ℤ) : ℝ)| / q := by
    have e : (m : ℝ) / q - r = ((m - r * q : ℤ) : ℝ) / q := by push_cast; field_simp
    change |(m : ℝ) / q - r| = _
    rw [e, abs_div, abs_of_pos hq0]
  rw [this, div_le_div_iff_of_pos_right hq0]
  have hne : (m - r * q : ℤ) ≠ 0 := by
    intro h0; apply hm; exact ⟨r, by linarith⟩
  have := Int.one_le_abs hne
  exact_mod_cast this

theorem re_ee (s : ℝ) : (ee s).re = Real.cos (2 * π * s) := by
  rw [ee_eq_exp, show (Complex.I * ((2 * π * s : ℝ) : ℂ)) = ((2 * π * s : ℝ) : ℂ) * Complex.I by ring,
    Complex.exp_ofReal_mul_I_re]

theorem norm_sq_sum_range_ee (b : ℕ) (t : ℝ) :
    ‖∑ u ∈ range b, ee (u * t)‖ ^ 2 = ∑ u ∈ range b, ∑ v ∈ range b, Real.cos (2 * π * (((u : ℝ) - v) * t)) := by
  set F := ∑ u ∈ range b, ee (u * t)
  have h1 : ‖F‖ ^ 2 = (F * starRingEnd ℂ F).re := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [h1, map_sum, Finset.sum_mul_sum, Complex.re_sum]
  apply Finset.sum_congr rfl; intro u _
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl; intro v _
  rw [conj_ee, ← ee_add, re_ee]
  congr 1; ring

/-- **Elementary bound for `ψ`**: `ψ(t) ≤ exp(−16(b−1)‖t‖²/b²)`. -/
theorem psiB_le_exp (b : ℕ) (hb : 2 ≤ b) (t : ℝ) :
    psiB b t ≤ Real.exp (-(16 * ((b : ℝ) - 1) / (b : ℝ) ^ 2) * distZ t ^ 2) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  set f : ℕ × ℕ → ℝ := fun p => Real.cos (2 * π * (((p.1 : ℝ) - p.2) * t)) with hf
  have hf1 : ∀ p, f p ≤ 1 := fun p => Real.cos_le_one _
  set c := Real.cos (2 * π * t)
  have hc : 1 - c ≥ 8 * distZ t ^ 2 := by
    have h2 : c = 1 - 2 * Real.sin (π * t) ^ 2 := by
      simp only [c]
      rw [show 2 * π * t = 2 * (π * t) by ring, Real.cos_two_mul, Real.cos_sq']; ring
    have h3 := abs_sin_pi_ge t
    have h4 : (2 * distZ t) ^ 2 ≤ Real.sin (π * t) ^ 2 := by
      rw [← sq_abs (Real.sin _)]; exact pow_le_pow_left₀ (by have := distZ_nonneg t; linarith) h3 2
    rw [h2]; nlinarith
  -- φ² as a double sum
  have hphi : phiB b t ^ 2 = ∑ p ∈ range b ×ˢ range b, f p := by
    unfold phiB
    rw [norm_sq_sum_range_ee, Finset.sum_product]
  set S1 := (range (b - 1)).image (fun u => (u + 1, u))
  set S2 := (range (b - 1)).image (fun u => (u, u + 1))
  have hS1 : S1 ⊆ range b ×ˢ range b := by
    intro p hp; obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hp
    rw [mem_range] at hu; rw [mem_product, mem_range, mem_range]; constructor <;> omega
  have hS2 : S2 ⊆ range b ×ˢ range b := by
    intro p hp; obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hp
    rw [mem_range] at hu; rw [mem_product, mem_range, mem_range]; constructor <;> omega
  have hdisj : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]; intro p h1 h2
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.1 h1
    obtain ⟨v, _, hv⟩ := Finset.mem_image.1 h2
    simp only [Prod.mk.injEq] at hv; omega
  have hsum1 : ∑ p ∈ S1, (1 - f p) = (b - 1 : ℕ) * (1 - c) := by
    rw [Finset.sum_image (fun x _ y _ h => by simp only [Prod.mk.injEq] at h; omega)]
    rw [Finset.sum_congr rfl (fun u _ => show 1 - f (u + 1, u) = 1 - c by
      simp only [hf, c]; push_cast; ring_nf), Finset.sum_const, card_range, nsmul_eq_mul]
  have hsum2 : ∑ p ∈ S2, (1 - f p) = (b - 1 : ℕ) * (1 - c) := by
    rw [Finset.sum_image (fun x _ y _ h => by simp only [Prod.mk.injEq] at h; omega)]
    rw [Finset.sum_congr rfl (fun u _ => show 1 - f (u, u + 1) = 1 - c by
      simp only [hf, c]; push_cast
      rw [show 2 * π * (((u : ℝ) - (u + 1)) * t) = -(2 * π * t) by ring, Real.cos_neg]),
      Finset.sum_const, card_range, nsmul_eq_mul]
  have hlow : 2 * ((b - 1 : ℕ) : ℝ) * (1 - c) ≤ ∑ p ∈ range b ×ˢ range b, (1 - f p) := by
    calc 2 * ((b - 1 : ℕ) : ℝ) * (1 - c) = ∑ p ∈ S1 ∪ S2, (1 - f p) := by
          rw [Finset.sum_union hdisj, hsum1, hsum2]; ring
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.union_subset hS1 hS2)
          (fun p _ _ => by linarith [hf1 p])
  have hb1 : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by push_cast [show 1 ≤ b by omega]; ring
  have hphi2 : phiB b t ^ 2 ≤ (b : ℝ) ^ 2 - 16 * ((b : ℝ) - 1) * distZ t ^ 2 := by
    rw [hphi]
    have : ∑ p ∈ range b ×ˢ range b, (1 - f p) = (b : ℝ) ^ 2 - ∑ p ∈ range b ×ˢ range b, f p := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, card_product, card_range, nsmul_eq_mul]
      push_cast; ring
    rw [hb1] at hlow
    have hb2 : (0 : ℝ) ≤ (b : ℝ) - 1 := by have : (2 : ℝ) ≤ b := by exact_mod_cast hb
                                           linarith
    nlinarith [hlow, this, mul_le_mul_of_nonneg_left hc (by linarith : (0 : ℝ) ≤ 2 * ((b : ℝ) - 1))]
  unfold psiB
  rw [div_pow]
  calc phiB b t ^ 2 / (b : ℝ) ^ 2 ≤ ((b : ℝ) ^ 2 - 16 * ((b : ℝ) - 1) * distZ t ^ 2) / (b : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hphi2 (by positivity)
    _ = 1 + (-(16 * ((b : ℝ) - 1) / (b : ℝ) ^ 2) * distZ t ^ 2) := by field_simp; ring
    _ ≤ Real.exp (-(16 * ((b : ℝ) - 1) / (b : ℝ) ^ 2) * distZ t ^ 2) := by
        have := Real.add_one_le_exp (-(16 * ((b : ℝ) - 1) / (b : ℝ) ^ 2) * distZ t ^ 2)
        linarith

/-- Windows: if every window `[s + iL, s + (i+1)L)` contains a point with `E ≥ c`, then the
sum over `W` windows is at least `W c`. -/
theorem window_sum_ge (E : ℕ → ℝ) (hE : ∀ n, 0 ≤ E n) (s L W : ℕ) (c : ℝ)
    (hw : ∀ i < W, ∃ n ∈ Ico (s + i * L) (s + i * L + L), c ≤ E n) :
    W * c ≤ ∑ n ∈ Ico s (s + W * L), E n := by
  induction W with
  | zero => simp
  | succ W ih =>
    rw [show s + (W + 1) * L = (s + W * L) + L by ring,
      ← Finset.sum_Ico_consecutive _ (by omega : s ≤ s + W * L) (by omega : s + W * L ≤ s + W * L + L)]
    obtain ⟨n, hn, hcn⟩ := hw W (by omega)
    have h1 := ih (fun i hi => hw i (by omega))
    have h2 : c ≤ ∑ m ∈ Ico (s + W * L) (s + W * L + L), E m :=
      hcn.trans (Finset.single_le_sum (fun m _ => hE m) hn)
    push_cast
    linarith

/-- **Maynard's window argument**: for `(a b, q) = 1`, every `⌊log_b q⌋+1` consecutive `j`
contain one with `‖a b^j / q‖ ≥ 1/(2b²)`. -/
theorem maynard_window (b q a : ℕ) (hb : 2 ≤ b) (hq : 2 ≤ q) (haq : Nat.Coprime a q)
    (hbq : Nat.Coprime b q) (j0 : ℕ) :
    ∃ j ∈ Ico j0 (j0 + (Nat.log b q + 1)),
      1 / (2 * (b : ℝ) ^ 2) ≤ distZ (((a * b ^ j : ℕ) : ℝ) / q) := by
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
  have hgrow : ∀ i, i < Nat.log b q + 1 → (b : ℝ) ^ i / q ≤ e (j0 + i) := by
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
  have hlast := hgrow (Nat.log b q) (by omega)
  have hlt : (q : ℝ) < (b : ℝ) ^ (Nat.log b q + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by omega : 1 < b) q
  have hge : 1 / (b : ℝ) < (b : ℝ) ^ (Nat.log b q) / q := by
    rw [div_lt_div_iff₀ (by positivity) (by exact_mod_cast hq0)]
    rw [pow_succ] at hlt; linarith
  have hsmall := hcon (j0 + Nat.log b q) (by rw [mem_Ico]; omega)
  have : 1 / (2 * (b : ℝ) ^ 2) ≤ 1 / b := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  linarith

theorem bigB_real (b : ℕ) (hb : 1 ≤ b) : ((bigB b : ℕ) : ℝ) = (b : ℝ) * ((b : ℝ) ^ 2 - 1) := by
  rw [bigB_eq b hb]; push_cast [hb]; ring

/-- **Col's L^∞ bound** (elementary form, TP Prop. 6.2): for `q ≥ 2`, `(q, h(b³−b)) = 1`,
`Π_{1≤n≤M} √ψ(c_n α) ≤ exp(−c_b ⌊(M−1)/(⌊log_b q⌋+1)⌋)` at `α = h/q + k/(b³−b)`. -/
theorem col_bound (b N M q h : ℕ) (k : ℤ) (hb : 2 ≤ b) (hq : 2 ≤ q) (hMN : M + 1 ≤ N)
    (hh : Nat.Coprime h q) (hqB : Nat.Coprime q (bigB b)) :
    ∏ n ∈ Ico 1 (M + 1), Real.sqrt (psiB b (cK b N n * ((h : ℝ) / q + k / (bigB b : ℝ)))) ≤
      Real.exp (-(((b : ℝ) - 1) / ((b : ℝ) ^ 6 * ((b : ℝ) + 1) ^ 2)) *
        (((M - 1) / (Nat.log b q + 1) : ℕ) : ℝ)) := by
  have hb1 : 1 ≤ b := by omega
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  set α : ℝ := (h : ℝ) / q + k / (bigB b : ℝ) with hα
  set d : ℕ → ℝ := fun n => distZ (cK b N n * α) with hd
  set κ : ℝ := 8 * ((b : ℝ) - 1) / (b : ℝ) ^ 2 with hκ
  have hκ0 : 0 ≤ κ := by rw [hκ]; have : (0 : ℝ) ≤ (b : ℝ) - 1 := by linarith
                         positivity
  -- step A
  have hA : ∀ n, Real.sqrt (psiB b (cK b N n * α)) ≤ Real.exp (-κ * d n ^ 2) := by
    intro n
    calc Real.sqrt (psiB b (cK b N n * α)) ≤
          Real.sqrt (Real.exp (-(16 * ((b : ℝ) - 1) / (b : ℝ) ^ 2) * d n ^ 2)) :=
          Real.sqrt_le_sqrt (psiB_le_exp b hb _)
      _ = Real.exp (-κ * d n ^ 2) := by
          rw [Real.sqrt_eq_iff_mul_self_eq (Real.exp_nonneg _) (Real.exp_nonneg _),
            ← Real.exp_add]
          congr 1; rw [hκ]; ring
  have hprod : ∏ n ∈ Ico 1 (M + 1), Real.sqrt (psiB b (cK b N n * α)) ≤
      Real.exp (-κ * ∑ n ∈ Ico 1 (M + 1), d n ^ 2) := by
    calc _ ≤ ∏ n ∈ Ico 1 (M + 1), Real.exp (-κ * d n ^ 2) :=
          Finset.prod_le_prod₀ (fun n _ => Real.sqrt_nonneg _) (fun n _ => hA n)
      _ = _ := by rw [← Real.exp_sum, Finset.mul_sum]
  refine hprod.trans ?_
  apply Real.exp_le_exp.2
  -- reduce to a lower bound for Σ d²
  set L := Nat.log b q + 1
  set W := (M - 1) / L
  set a := h * (b ^ 2 - 1)
  set E : ℕ → ℝ := fun n => distZ (((a * b ^ (2 * N - n - 1) : ℕ) : ℝ) / q)
  -- coprimality
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
  -- step C: pairing
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
  -- step D: windows
  have hD : (W : ℝ) * (1 / (2 * (b : ℝ) ^ 2)) ^ 2 ≤ ∑ n ∈ Ico 1 M, E n ^ 2 := by
    have hw := window_sum_ge (fun n => E n ^ 2) (fun n => sq_nonneg _) 1 L W
      ((1 / (2 * (b : ℝ) ^ 2)) ^ 2) (by
        intro i hi
        set s := 1 + i * L
        obtain ⟨jx, hjx, hge⟩ := maynard_window b q a hb hq hqa hqb (2 * N - s - L)
        rw [mem_Ico] at hjx
        have hWL : W * L ≤ M - 1 := Nat.div_mul_le_self _ _
        have hsL : s + L ≤ M := by
          have h3 : (i + 1) * L ≤ W * L := Nat.mul_le_mul_right _ (by omega)
          have h4 : (i + 1) * L ≤ M - 1 := le_trans h3 hWL
          have hL1 : 1 ≤ L := by simp only [L]; omega
          have hM1 : 1 ≤ M - 1 := le_trans (by nlinarith) h4
          have e1 : s + L = (i + 1) * L + 1 := by simp only [s]; ring
          rw [e1]
          calc (i + 1) * L + 1 ≤ (M - 1) + 1 := Nat.add_le_add_right h4 1
            _ = M := Nat.sub_add_cancel (le_trans (by norm_num) (Nat.le_of_lt_succ (Nat.lt_succ_of_le
                (le_trans hM1 (Nat.sub_le M 1)))))
        have hN2 : s + L ≤ N := le_trans hsL (by omega : M ≤ N)
        have hjx1 : 2 * N - s - L ≤ jx := hjx.1
        have hjx2 : jx < 2 * N - s - L + (Nat.log b q + 1) := hjx.2
        have hLdef : L = Nat.log b q + 1 := rfl
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
  -- step B and combination
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
  have hk : -(((b : ℝ) - 1) / ((b : ℝ) ^ 6 * ((b : ℝ) + 1) ^ 2)) * (W : ℝ) =
      -κ * ((W : ℝ) / (8 * (b : ℝ) ^ 4 * ((b : ℝ) + 1) ^ 2)) := by
    rw [hκ]; field_simp
  rw [hk]
  exact mul_le_mul_of_nonpos_left hfinal (by linarith)

end Palprimes
