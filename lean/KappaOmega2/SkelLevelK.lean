import KappaOmega2.StatementsK
import Palprimes.Level.Level

/-!
# Skeleton K, part 1: level of distribution and squares for the weighted κ-sequence of record

From the κ items (L01–L03, LK01–LK17, QK01–QK04):
* `tl1K_rec`: `TL¹_κ(θ, η, 1/10)` for the record data of every `b ≥ 3`, `θ = 103/200`;
* `level_boundK`: `Σ_{d ≤ y} μ²(d) 3^{ω(d)} |R(d)| ≤ (log x)^{−A}` for every `A` and large `N`;
* `squares_boundK`: `Σ_{x^{c₀} < p ≤ x^{c₁}} A_{p²} ≤ (log x)^{−A}` for every `A` and large `N`.
-/

set_option linter.style.longLine false

open Finset Real Filter Asymptotics

namespace KappaOmega2

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

/-- The record data of base `b ≥ 3` with its scalar parameters. -/
theorem recK_data (hL01 : ItemL01) (hL02 : ItemL02) (hL03 : ItemL03) (hLK01 : ItemLK01) (hLK06 : ItemLK06)
    (hLK07 : ItemLK07) (b : ℕ) (hb : 3 ≤ b) :
    IsDigitWeight b (recGKR b) ∧ 0 < recGKR b 1 ∧ (∀ a, recGKR b a ≤ 1 / 2) ∧
    1 / 2 ≤ recPK b ∧ recPK b < 1 ∧ recHK b ≤ b * (b - 1) ∧
    (∀ t : ℝ, ‖Gg b (recGKR b) t‖ ^ recPK b ≤ trigEval (recHK b) (recTauK b) t) ∧
    0 < recTauK b 0 ∧ trigMass (recHK b) (recTauK b) ≤ 1 ∧ mw4 b (recGKR b) ≤ 1 / (b : ℝ) ∧
    ∃ ψ : ℝ, recTauK b 0 ≤ (b : ℝ) ^ (-ψ) ∧ thS + 1 / 1000 ≤ 7 / 20 * ψ + 3 / 10 * recPK b := by
  obtain ⟨hgw, hg1, hgle, hp0, hp1, hH, hτ0, hmass, hmw, hψ⟩ := hLK07 hL03 b hb
  exact ⟨hgw, hg1, hgle, hp0, hp1, hH, hLK06 hL02 hL01 hLK01 b hb, hτ0, hmass, hmw, hψ⟩

/-- `a = 1/100`, `η = a(1 − p)/2`. -/
noncomputable def etaRK (b : ℕ) : ℝ := 1 / 100 * (1 - recPK b) / 2

theorem etaRK_pos (b : ℕ) (hp1 : recPK b < 1) : 0 < etaRK b := by
  unfold etaRK; have : 0 < 1 - recPK b := by linarith
  positivity

theorem etaRK_lt (b : ℕ) (hp1 : recPK b < 1) : etaRK b < 1 / 100 * (1 - recPK b) := by
  unfold etaRK; have : 0 < 1 - recPK b := by linarith
  linarith

theorem etaRK_small (b : ℕ) (hp0 : 1 / 2 ≤ recPK b) : etaRK b ≤ 1 / 400 := by
  unfold etaRK; nlinarith

theorem tl1K_rec (hL01 : ItemL01) (hL02 : ItemL02) (hL03 : ItemL03) (hLK01 : ItemLK01) (hLK06 : ItemLK06)
    (hLK07 : ItemLK07) (hLK08 : ItemLK08) (hLK09 : ItemLK09) (hLKM : ItemLKM) (hLK10 : ItemLK10)
    (b : ℕ) (hb : 3 ≤ b) : TL1K b (recGKR b) thS (etaRK b) (1 / 10) := by
  obtain ⟨hgw, -, -, hp0, hp1, hH, hmaj, hτ0, hmass, hmw, ψ, hτψ, hψ⟩ :=
    recK_data hL01 hL02 hL03 hLK01 hLK06 hLK07 b hb
  have hη := etaRK_pos b hp1
  have hηlt := etaRK_lt b hp1
  have hηs := etaRK_small b hp0
  have h1p : 0 ≤ 1 - recPK b := by linarith
  exact hLK10 b (recGKR b) (recPK b) (recHK b) (recTauK b) ψ (1 / 100) (etaRK b) thS (1 / 10) hb hgw hp0 hp1 hH
    hmaj hτ0 hτψ hmass hmw (by norm_num) hη (by norm_num) (by norm_num [thS]) (by norm_num [thS])
    (by linarith) (by linarith) (by norm_num [thS]; linarith)
    (by have : 0 ≤ 1 / 100 * (1 - recPK b) := by positivity
        linarith)
    hηlt hLK08 hLK09 hLKM

/-! ## The level bound -/

theorem level_boundK (hL01 : ItemL01) (hL02 : ItemL02) (hL03 : ItemL03) (hLK01 : ItemLK01) (hLK06 : ItemLK06)
    (hLK07 : ItemLK07) (hLK08 : ItemLK08) (hLK09 : ItemLK09) (hLKM : ItemLKM) (hLK10 : ItemLK10)
    (hLK14 : ItemLK14) (hLK15 : ItemLK15)
    (b : ℕ) (hb : 3 ≤ b) (A : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, levelSumK b (recGKR b) N ⌊xx b N ^ thS⌋₊ ≤ 1 / Real.log (xx b N) ^ A := by
  have hTL := tl1K_rec hL01 hL02 hL03 hLK01 hLK06 hLK07 hLK08 hLK09 hLKM hLK10 b hb
  obtain ⟨hgw, -, -, hp0, hp1, -⟩ := recK_data hL01 hL02 hL03 hLK01 hLK06 hLK07 b hb
  obtain ⟨N₁, hN₁⟩ := hLK15 b (recGKR b) thS (etaRK b) (1 / 10) hb hgw (by norm_num) (by norm_num [thS])
    (by norm_num) (by norm_num [thS]) (etaRK_pos b hp1) hTL (A + 4)
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
  have hlev := hLK14 b (recGKR b) N D Kt hb (fun k hk => hF k hk)
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
  calc levelSumK b (recGKR b) N D ≤ τr * (∑ e ∈ Icc 1 D, (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors e / e) * Kt :=
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

theorem squares_boundK (hL01 : ItemL01) (hL02 : ItemL02) (hL03 : ItemL03) (hLK01 : ItemLK01) (hLK06 : ItemLK06)
    (hLK07 : ItemLK07) (hLK08 : ItemLK08) (hLK09 : ItemLK09) (hLKM : ItemLKM) (hLK10 : ItemLK10)
    (hLK17 : ItemLK17) (hQK01 : ItemQK01) (hQK03 : ItemQK03) (hQK04 : ItemQK04)
    (b : ℕ) (hb : 3 ≤ b) (A : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, SqK b (recGKR b) N c0 c1 ≤ 1 / Real.log (xx b N) ^ A := by
  have hTL := tl1K_rec hL01 hL02 hL03 hLK01 hLK06 hLK07 hLK08 hLK09 hLKM hLK10 b hb
  obtain ⟨hgw, -, hgle, hp0, hp1, hH, hmaj, hτ0, hmass, hmw, ψ, hτψ, hψ⟩ :=
    recK_data hL01 hL02 hL03 hLK01 hLK06 hLK07 b hb
  have hη := etaRK_pos b hp1
  have hηlt := etaRK_lt b hp1
  have hηs := etaRK_small b hp0
  obtain ⟨η, hη', N₁, hN₁⟩ := hQK04 b (recGKR b) (recPK b) (recHK b) (recTauK b) ψ (1 / 100) (etaRK b) thS (1 / 10)
    c0 c1 hb hgw hp0 hp1 hH hmaj hτ0 hτψ hmass hmw (by norm_num) hη (by linarith)
    (by norm_num [c1, thS] at hψ ⊢
        have : 0 ≤ 1 / 100 * (1 - recPK b) := by nlinarith
        nlinarith)
    hηlt (by norm_num [c0]) (by norm_num [c0, c1]) (by norm_num [c1]) (by norm_num) (by norm_num)
    (by norm_num [thS]) (by norm_num [c1, thS]) (by norm_num [thS]) hTL hQK01 hQK03 hLK08 hLKM
  set ζ : ℝ := min c0 η with hζ
  have hζ0 : 0 < ζ := lt_min (by norm_num [c0]) hη'
  obtain ⟨N₂, hN₂⟩ := logx_pow_le_rpow b (by omega) hζ0 A (show (0 : ℝ) < 3 by norm_num)
  obtain ⟨N₃, hN₃⟩ := logx_large b (by omega) 1
  refine ⟨max (max N₁ 1) (max N₂ N₃), fun N hN => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN1' : 1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hx1 := one_lt_xx b N (by omega)
  have hx0 : 0 < xx b N := by linarith
  have hXW : XK b (recGKR b) N ≤ 1 :=
    ((hLK17 b (recGKR b) (1 / 2) N hb hN1' hgw.1 hgle).2.2) hgw
  have hS := hN₁ N hN1
  have hc0 : xx b N ^ (-c0) ≤ xx b N ^ (-ζ) :=
    Real.rpow_le_rpow_of_exponent_le hx1.le (by have := min_le_left c0 η; linarith)
  have hη2 : xx b N ^ (-η) ≤ xx b N ^ (-ζ) :=
    Real.rpow_le_rpow_of_exponent_le hx1.le (by have := min_le_right c0 η; linarith)
  have hXW0 : 0 ≤ XK b (recGKR b) N := by
    unfold XK AK
    exact Finset.sum_nonneg (fun u _ => Finset.sum_nonneg (fun w _ => by
      split_ifs
      · exact div_nonneg (Finset.prod_nonneg (fun k _ => hgw.1 _)) (by positivity)
      · exact le_rfl))
  have hsum : SqK b (recGKR b) N c0 c1 ≤ 3 * xx b N ^ (-ζ) := by
    have h1 : 2 * XK b (recGKR b) N * xx b N ^ (-c0) ≤ 2 * xx b N ^ (-ζ) := by
      have hpos : 0 ≤ xx b N ^ (-c0) := Real.rpow_nonneg hx0.le _
      nlinarith
    linarith
  have hL := hN₂ N hN2
  have hL0 : 0 < Real.log (xx b N) := Real.log_pos hx1
  have hpow : xx b N ^ (-ζ) = 1 / xx b N ^ ζ := by rw [Real.rpow_neg hx0.le, one_div]
  rw [hpow] at hsum
  have hxζ : 0 < xx b N ^ ζ := Real.rpow_pos_of_pos hx0 _
  calc SqK b (recGKR b) N c0 c1 ≤ 3 * (1 / xx b N ^ ζ) := hsum
    _ ≤ 1 / Real.log (xx b N) ^ A := by
        rw [mul_one_div, div_le_div_iff₀ hxζ (by positivity)]
        linarith

end KappaOmega2
