import Omega3.Statements
import Palprimes.Level.Level

/-!
# Skeleton, part 1: level of distribution and squares for the weighted sequence of record

From the level items (L01–L17) and the square items (Q01–Q04):
* `tl1_rec`: `TL¹_w(θ, κ, θ₀)` for the record data of every `b ≥ 5`;
* `level_bound`: `Σ_{d ≤ y} μ²(d) 3^{ω(d)} |R_w(d)| ≤ (log x)^{−A}` for every `A` and large `N`;
* `squares_bound`: `Σ_{x^{c₀} < p ≤ x^{c₁}} A^w_{p²} ≤ (log x)^{−A}` for every `A` and large `N`.
-/

set_option linter.style.longLine false

open Finset Real Filter Asymptotics

namespace Omega3

open Palprimes

/-! ## Elementary asymptotics in `N` -/

theorem xx_pos (b N : ℕ) (hb : 2 ≤ b) : 0 < xx b N := by
  unfold xx; have : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  positivity

theorem one_lt_xx (b N : ℕ) (hb : 2 ≤ b) : 1 < xx b N := by
  unfold xx; exact one_lt_pow₀ (by exact_mod_cast (by omega : 1 < b)) (by omega)

theorem log_xx (b N : ℕ) : Real.log (xx b N) = (2 * N + 1 : ℕ) * Real.log b := by
  unfold xx; rw [Real.log_pow]

theorem log_xx_pos (b N : ℕ) (hb : 2 ≤ b) : 0 < Real.log (xx b N) := Real.log_pos (one_lt_xx b N hb)

/-- `log x → ∞`. -/
theorem logx_large (b : ℕ) (hb : 2 ≤ b) (C : ℝ) : ∃ N₀ : ℕ, ∀ N ≥ N₀, C ≤ Real.log (xx b N) := by
  have hlb : 0 < Real.log b := Real.log_pos (by exact_mod_cast (by omega : 1 < b))
  obtain ⟨M, hM⟩ := exists_nat_gt (C / Real.log b)
  refine ⟨M, fun N hN => ?_⟩
  rw [log_xx]
  rw [div_lt_iff₀ hlb] at hM
  have h1 : (M : ℝ) ≤ ((2 * N + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : M ≤ 2 * N + 1)
  nlinarith

/-- `x → ∞`: `x ≥ X` eventually. -/
theorem xx_large (b : ℕ) (hb : 2 ≤ b) (X : ℝ) : ∃ N₀ : ℕ, ∀ N ≥ N₀, X ≤ xx b N := by
  obtain ⟨N₀, h⟩ := logx_large b hb (Real.log (max X 1))
  refine ⟨N₀, fun N hN => ?_⟩
  have h1 := h N hN
  have hx := xx_pos b N hb
  have h2 : max X 1 ≤ xx b N := (Real.log_le_log_iff (by positivity) hx).1 h1
  exact le_trans (le_max_left _ _) h2

/-- `C (log X)^A ≤ X^ζ` for large `X`. -/
theorem log_pow_le_rpow {ζ : ℝ} (hζ : 0 < ζ) (A : ℕ) {C : ℝ} (hC : 0 < C) :
    ∃ X₀ : ℝ, ∀ X ≥ X₀, C * Real.log X ^ A ≤ X ^ ζ := by
  have h := (isLittleO_log_rpow_rpow_atTop (A : ℝ) hζ).def (show (0 : ℝ) < 1 / C by positivity)
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 h
  refine ⟨max X₀ 1, fun X hX => ?_⟩
  have hX1 : 1 ≤ X := le_trans (le_max_right _ _) hX
  have h1 := hX₀ X (le_trans (le_max_left _ _) hX)
  have hl : 0 ≤ Real.log X := Real.log_nonneg hX1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hl _), Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _),
    Real.rpow_natCast] at h1
  have := mul_le_mul_of_nonneg_left h1 hC.le
  rw [← mul_assoc, mul_one_div_cancel hC.ne', one_mul] at this
  exact this

/-- `C (log x)^A ≤ x^ζ` for large `N`. -/
theorem logx_pow_le_rpow (b : ℕ) (hb : 2 ≤ b) {ζ : ℝ} (hζ : 0 < ζ) (A : ℕ) {C : ℝ} (hC : 0 < C) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, C * Real.log (xx b N) ^ A ≤ xx b N ^ ζ := by
  obtain ⟨X₀, hX⟩ := log_pow_le_rpow hζ A hC
  obtain ⟨N₀, hN⟩ := xx_large b hb X₀
  exact ⟨N₀, fun N h => hX _ (hN N h)⟩

/-! ## TL¹ for the record data -/

theorem tl1_rec (hL01 : ItemL01) (hL02 : ItemL02) (hL03 : ItemL03) (hL04 : ItemL04) (hL05 : ItemL05)
    (hL06 : ItemL06) (hL07 : ItemL07) (hL08 : ItemL08) (hL09 : ItemL09) (hL10 : ItemL10) (hL16 : ItemL16)
    (b : ℕ) (hb : 5 ≤ b) : ∃ κ : ℝ, 0 < κ ∧ TL1w b (recGR b) thS κ th0 := by
  obtain ⟨hgw, -, -, -, hp0, hp1, hH⟩ := hL16 b hb
  have hmaj := hL06 hL02 hL01 hL04 hL05 b hb
  obtain ⟨ψ, lA, θw, κ, hτ0, hτψ, hmass, hmw, hθw, hκ, hii, hiii, -, -⟩ := hL07 hL03 b hb
  exact ⟨κ, hκ, hL10 b (recGR b) (recP b) (recH b) (recTau b) ψ lA θw thS κ th0 (by omega) hgw hp0 hp1 hH
    hmaj hτ0 hτψ hmass hmw hθw hκ (by norm_num [th0]) (by norm_num [th0, thS]) (by norm_num [thS]) hii hiii
    hL08 hL09⟩

/-! ## The level bound -/

theorem level_bound (hL01 : ItemL01) (hL02 : ItemL02) (hL03 : ItemL03) (hL04 : ItemL04) (hL05 : ItemL05)
    (hL06 : ItemL06) (hL07 : ItemL07) (hL08 : ItemL08) (hL09 : ItemL09) (hL10 : ItemL10) (hL11 : ItemL11)
    (hL12 : ItemL12) (hL14 : ItemL14) (hL15 : ItemL15) (hL16 : ItemL16)
    (b : ℕ) (hb : 5 ≤ b) (A : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, levelSum b (recGR b) N ⌊xx b N ^ thS⌋₊ ≤ 1 / Real.log (xx b N) ^ A := by
  obtain ⟨κ, hκ, hTL⟩ := tl1_rec hL01 hL02 hL03 hL04 hL05 hL06 hL07 hL08 hL09 hL10 hL16 b hb
  obtain ⟨hgw, hg0, hg1, -, -, -, -⟩ := hL16 b hb
  have hth0 : (0 : ℝ) < th0 := by norm_num [th0]
  have hth : th0 < thS := by norm_num [th0, thS]
  have hSS := hL11 b (recGR b) thS κ th0 (by omega) hgw hth0 hth hκ hTL
  have hLK := hL12 b (recGR b) (by omega) hgw
  obtain ⟨N₁, hN₁⟩ := hL15 b (recGR b) thS κ th0 (by omega) hgw hg0 hg1 hth0 hth (by norm_num [thS]) hκ
    hLK hSS hTL (A + 4)
  set τr : ℝ := ((bigB b).divisors.card : ℝ) with hτr
  have hτr0 : 0 ≤ τr := by positivity
  obtain ⟨N₂, hN₂⟩ := logx_large b (by omega) (8 * τr + 1)
  refine ⟨max N₁ N₂, fun N hN => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : N₂ ≤ N := le_trans (le_max_right _ _) hN
  set L := Real.log (xx b N) with hL
  have hL1 : 8 * τr + 1 ≤ L := hN₂ N hN2
  have hL0 : 0 < L := by linarith
  set D := ⌊xx b N ^ thS⌋₊ with hD
  set Kt : ℝ := 1 / L ^ (A + 4) with hKt
  have hF := hN₁ N hN1
  have hlev := hL14 b (recGR b) N D Kt (by omega) (fun k hk => hF k hk)
  -- the harmonic factor
  have hH : ∑ e ∈ Icc 1 D, (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors e / e ≤ (1 + L) ^ 3 := by
    refine le_trans (sum_three_pow_omega_div_le D) ?_
    have h0 : 0 ≤ ∑ a ∈ Icc 1 D, (1 : ℝ) / a := Finset.sum_nonneg (fun a _ => by positivity)
    have h1 := sum_inv_le_log D
    have hlogD : Real.log D ≤ L := by
      rcases Nat.eq_zero_or_pos D with h | h
      · rw [h]; simp; linarith
      · have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast h
        have hx1 := one_lt_xx b N (by omega)
        have hDx : (D : ℝ) ≤ xx b N := by
          have := Nat.floor_le (Real.rpow_nonneg (xx_pos b N (by omega)).le thS)
          refine le_trans this ?_
          calc xx b N ^ thS ≤ xx b N ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hx1.le (by norm_num [thS])
            _ = xx b N := Real.rpow_one _
        exact Real.log_le_log (by linarith) hDx
    have : ∑ a ∈ Icc 1 D, (1 : ℝ) / a ≤ 1 + L := by linarith
    gcongr
  have hKt0 : 0 ≤ Kt := by positivity
  calc levelSum b (recGR b) N D ≤ τr * (∑ e ∈ Icc 1 D, (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors e / e) * Kt :=
        hlev
    _ ≤ τr * (1 + L) ^ 3 * Kt := by gcongr
    _ ≤ 1 / L ^ A := by
        rw [hKt, pow_add]
        have hLA : 0 < L ^ A := by positivity
        have h8 : (1 + L) ^ 3 ≤ 8 * L ^ 3 := by
          have : 1 + L ≤ 2 * L := by linarith
          calc (1 + L) ^ 3 ≤ (2 * L) ^ 3 := by gcongr
            _ = 8 * L ^ 3 := by ring
        have h9 : τr * (1 + L) ^ 3 ≤ L ^ 4 := by
          calc τr * (1 + L) ^ 3 ≤ τr * (8 * L ^ 3) := by gcongr
            _ = (8 * τr) * L ^ 3 := by ring
            _ ≤ L * L ^ 3 := by gcongr; linarith
            _ = L ^ 4 := by ring
        rw [mul_one_div, div_le_div_iff₀ (by positivity) hLA]
        calc τr * (1 + L) ^ 3 * L ^ A ≤ L ^ 4 * L ^ A := mul_le_mul_of_nonneg_right h9 hLA.le
          _ = 1 * (L ^ A * L ^ 4) := by ring

/-! ## The square bound -/

theorem squares_bound (hL01 : ItemL01) (hL02 : ItemL02) (hL03 : ItemL03) (hL04 : ItemL04) (hL05 : ItemL05)
    (hL06 : ItemL06) (hL07 : ItemL07) (hL16 : ItemL16) (hL17 : ItemL17)
    (hQ01 : ItemQ01) (hQ02 : ItemQ02) (hQ03 : ItemQ03) (hQ04 : ItemQ04)
    (b : ℕ) (hb : 5 ≤ b) (A : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, SqW b (recGR b) N c0 c1 ≤ 1 / Real.log (xx b N) ^ A := by
  obtain ⟨hgw, -, -, -, hp0, hp1, hH⟩ := hL16 b hb
  have hmaj := hL06 hL02 hL01 hL04 hL05 b hb
  obtain ⟨ψ, lA, θw, κ, hτ0, hτψ, hmass, hmw, hθw, -, -, -, hQ1, hQ2⟩ := hL07 hL03 b hb
  obtain ⟨η, hη, N₁, hN₁⟩ := hQ04 b (recGR b) (recP b) (recH b) (recTau b) ψ lA θw c0 c1 (by omega) hgw hp0 hp1
    hH hmaj hτ0 hτψ hmass hmw hθw (by norm_num [c0]) (by norm_num [c0, c1]) (by norm_num [c1]) hQ1 hQ2
    hQ01 hQ02 hQ03
  set ζ : ℝ := min c0 η with hζ
  have hζ0 : 0 < ζ := lt_min (by norm_num [c0]) hη
  obtain ⟨N₂, hN₂⟩ := logx_pow_le_rpow b (by omega) hζ0 A (show (0 : ℝ) < 3 by norm_num)
  obtain ⟨N₃, hN₃⟩ := logx_large b (by omega) 1
  refine ⟨max N₁ (max N₂ N₃), fun N hN => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN3 : N₃ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hx1 := one_lt_xx b N (by omega)
  have hx0 : 0 < xx b N := by linarith
  have hXW : XW b (recGR b) N ≤ 1 :=
    ((hL17 b (recGR b) (1 / 3) N (by omega) hgw.1 (fun a => (hL16 b hb).2.2.2.1 a)).2.2) hgw
  have hS := hN₁ N hN1
  have hc0 : xx b N ^ (-c0) ≤ xx b N ^ (-ζ) :=
    Real.rpow_le_rpow_of_exponent_le hx1.le (by have := min_le_left c0 η; linarith)
  have hη' : xx b N ^ (-η) ≤ xx b N ^ (-ζ) :=
    Real.rpow_le_rpow_of_exponent_le hx1.le (by have := min_le_right c0 η; linarith)
  have hXW0 : 0 ≤ XW b (recGR b) N := by
    unfold XW AW
    exact Finset.sum_nonneg (fun d _ => by
      split_ifs
      · exact Finset.prod_nonneg (fun k _ => hgw.1 _)
      · exact le_rfl)
  have hsum : SqW b (recGR b) N c0 c1 ≤ 3 * xx b N ^ (-ζ) := by
    have h1 : 2 * XW b (recGR b) N * xx b N ^ (-c0) ≤ 2 * xx b N ^ (-ζ) := by
      have hpos : 0 ≤ xx b N ^ (-c0) := Real.rpow_nonneg hx0.le _
      nlinarith
    linarith
  have hL := hN₂ N hN2
  have hL0 : 0 < Real.log (xx b N) := Real.log_pos hx1
  have hpow : xx b N ^ (-ζ) = 1 / xx b N ^ ζ := by rw [Real.rpow_neg hx0.le, one_div]
  rw [hpow] at hsum
  have hxζ : 0 < xx b N ^ ζ := Real.rpow_pos_of_pos hx0 _
  calc SqW b (recGR b) N c0 c1 ≤ 3 * (1 / xx b N ^ ζ) := hsum
    _ ≤ 1 / Real.log (xx b N) ^ A := by
        rw [mul_one_div, div_le_div_iff₀ hxζ (by positivity)]
        linarith

end Omega3
