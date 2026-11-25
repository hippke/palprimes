import Omega3.Statements
import Palprimes.MainTerm.VB

/-!
# M04 helper: the band sum of one band (Mertens 2 + 3, Riemann sum against `bandI`)

For `1/3 ≤ a < c ≤ 2U − 1` and every set `S` of primes in `[y^a, y^c)`, eventually in `y`,
`Σ_{p ∈ S} (U − x_p) gB(p) V(√(y/p)) ≤ 2 V(y) (I(a, c) + ε)`, `x_p = log p / log y`.
-/

set_option linter.style.longLine false

open Finset Real Filter Topology

namespace Omega3

open Palprimes Palprimes.MT Palprimes.Greaves

/-- `h(x) = (U − x)/(1 − x)`. -/
noncomputable def m04h (x : ℝ) : ℝ := (UU - x) / (1 - x)

theorem m04h_anti {s x : ℝ} (hsx : s ≤ x) (hx : x < 1) : m04h x ≤ m04h s := by
  unfold m04h
  have hs : s < 1 := lt_of_le_of_lt hsx hx
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  have hU : UU = 83 / 85 := rfl
  rw [hU]; nlinarith

theorem m04h_nonneg {x : ℝ} (hx : x ≤ UU) (hx1 : x < 1) : 0 ≤ m04h x :=
  div_nonneg (by linarith) (by linarith)

theorem m04h_le_one {x : ℝ} (hx1 : x < 1) : m04h x ≤ 1 := by
  unfold m04h
  rw [div_le_one (by linarith)]
  have hU : UU = 83 / 85 := rfl
  rw [hU]; linarith

/-- One Riemann piece against `F(x) = U log x + (1 − U) log(1 − x)`. -/
theorem m04_piece {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (ht : t < 1) :
    m04h s * (Real.log t - Real.log s) ≤
      (UU * Real.log t + (1 - UU) * Real.log (1 - t)) - (UU * Real.log s + (1 - UU) * Real.log (1 - s)) +
        (1 - UU) * (t - s) ^ 2 / ((1 - t) * (1 - s) * t) := by
  have ht0 : 0 < t := lt_of_lt_of_le hs hst
  have h1t : 0 < 1 - t := by linarith
  have h1s : 0 < 1 - s := by linarith
  have hA : (t - s) / t ≤ Real.log t - Real.log s := by
    have := Real.one_sub_inv_le_log_of_pos (div_pos ht0 hs)
    rw [Real.log_div ht0.ne' hs.ne', inv_div] at this
    have e : 1 - s / t = (t - s) / t := by field_simp
    linarith
  have hB : Real.log (1 - s) - Real.log (1 - t) ≤ (t - s) / (1 - t) := by
    have := Real.log_le_sub_one_of_pos (div_pos h1s h1t)
    rw [Real.log_div h1s.ne' h1t.ne'] at this
    have e : (1 - s) / (1 - t) - 1 = (t - s) / (1 - t) := by field_simp; ring
    linarith
  have hU0 : 0 ≤ 1 - UU := by have hU : UU = 83 / 85 := rfl; rw [hU]; norm_num
  have hh : m04h s = UU - (1 - UU) * (s / (1 - s)) := by
    unfold m04h; field_simp; ring
  have hss : 0 ≤ s / (1 - s) := div_nonneg hs.le h1s.le
  have key : (t - s) / (1 - t) = s / (1 - s) * ((t - s) / t) + (t - s) ^ 2 / ((1 - t) * (1 - s) * t) := by
    field_simp; ring
  set A := Real.log t - Real.log s
  set Bq := Real.log (1 - s) - Real.log (1 - t)
  have h2 : s / (1 - s) * ((t - s) / t) ≤ s / (1 - s) * A := mul_le_mul_of_nonneg_left hA hss
  have h3 : (1 - UU) * Bq ≤ (1 - UU) * (s / (1 - s) * A) + (1 - UU) * ((t - s) ^ 2 / ((1 - t) * (1 - s) * t)) := by
    rw [← mul_add]; apply mul_le_mul_of_nonneg_left _ hU0; rw [key] at hB; linarith
  rw [hh, mul_div_assoc]
  have : (UU * Real.log t + (1 - UU) * Real.log (1 - t)) - (UU * Real.log s + (1 - UU) * Real.log (1 - s)) =
      UU * A - (1 - UU) * Bq := by simp only [A, Bq]; ring
  rw [this]
  nlinarith

/-- Indicator telescoping. -/
theorem m04_tele (L : ℕ → ℝ) (hL : Monotone L) (v : ℝ) (n : ℕ) :
    ∑ j ∈ range n, (if v ∈ Set.Ioc (L j) (L (j + 1)) then (1 : ℝ) else 0) =
      if v ∈ Set.Ioc (L 0) (L n) then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    have h0n : L 0 ≤ L n := hL (Nat.zero_le n)
    have hn1 : L n ≤ L (n + 1) := hL (Nat.le_succ n)
    by_cases h1 : v ∈ Set.Ioc (L 0) (L n)
    · have h2 : v ∉ Set.Ioc (L n) (L (n + 1)) := fun h => by
        simp only [Set.mem_Ioc] at h h1; linarith
      have h3 : v ∈ Set.Ioc (L 0) (L (n + 1)) := by
        simp only [Set.mem_Ioc] at h1 ⊢; exact ⟨h1.1, by linarith⟩
      rw [if_pos h1, if_neg h2, if_pos h3]; ring
    · rw [if_neg h1, zero_add]
      by_cases h2 : v ∈ Set.Ioc (L n) (L (n + 1))
      · have h3 : v ∈ Set.Ioc (L 0) (L (n + 1)) := by
          simp only [Set.mem_Ioc] at h2 ⊢; exact ⟨by linarith, h2.2⟩
        rw [if_pos h2, if_pos h3]
      · have h3 : v ∉ Set.Ioc (L 0) (L (n + 1)) := by
          intro h3
          simp only [Set.mem_Ioc] at h1 h2 h3
          by_cases hv : v ≤ L n
          · exact h1 ⟨h3.1, hv⟩
          · exact h2 ⟨lt_of_not_ge hv, h3.2⟩
        rw [if_neg h2, if_neg h3]

theorem m04_VB_nonneg (b : ℕ) (w : ℝ) : 0 ≤ VB b w := by
  unfold VB
  apply Finset.prod_nonneg
  intro p hp
  have : gB b p ≤ 1 := by
    unfold gB
    split_ifs with h
    · have : (1 : ℝ) ≤ p := by exact_mod_cast h.1.one_lt.le
      exact div_le_one_of_le₀ this (by linarith)
    · norm_num
  linarith


/-- Riemann sum of `h` against `d log` on the points `s_j = a + (j − 1)Δ`, compared with `I(a, c)`. -/
theorem m04_riemann (a c Δ : ℝ) (K : ℕ) (s : ℕ → ℝ) (hs : ∀ j, s j = a + ((j : ℝ) - 1) * Δ)
    (ha : 1 / 3 ≤ a) (hac : a < c) (hc1 : c < 1) (hcU : c < UU) (hΔ0 : 0 < Δ) (hΔ6 : Δ ≤ 1 / 6)
    (hKΔ : (K : ℝ) * Δ = c - a) (hca1 : c - a ≤ 1) :
    ∑ j ∈ range (K + 1), m04h (s j) * (Real.log (s (j + 1)) - Real.log (s j)) ≤
      bandI a c + 6 * Δ + 3 / (1 - c) ^ 2 * Δ := by
  have hU : UU = 83 / 85 := rfl
  have h1c : 0 < 1 - c := by linarith
  have hs0 : s 0 = a - Δ := by rw [hs]; push_cast; ring
  have hs1 : s 1 = a := by rw [hs]; push_cast; ring
  have hsK : s (K + 1) = c := by rw [hs]; push_cast; linarith
  have hsmono : Monotone s := by
    intro i j hij
    rw [hs, hs]
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    nlinarith
  have hspos : ∀ j, 1 / 6 ≤ s j := by
    intro j; have := hsmono (Nat.zero_le j); rw [hs0] at this; linarith
  have hsc : ∀ j, j ≤ K + 1 → s j ≤ c := by
    intro j hj; have := hsmono hj; rw [hsK] at this; exact this
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, F = fun t => UU * Real.log t + (1 - UU) * Real.log (1 - t) := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 3 / (1 - c) ^ 2 := ⟨_, rfl⟩
  rw [← hD, sum_range_succ']
  have hfirst : m04h (s 0) * (Real.log (s (0 + 1)) - Real.log (s 0)) ≤ 6 * Δ := by
    rw [zero_add, hs1, hs0]
    have ha0 : 0 < a - Δ := by linarith
    have hl : Real.log a - Real.log (a - Δ) ≤ Δ / (a - Δ) := by
      have := Real.log_le_sub_one_of_pos (div_pos (by linarith : (0 : ℝ) < a) ha0)
      rw [Real.log_div (by linarith) ha0.ne'] at this
      have e : a / (a - Δ) - 1 = Δ / (a - Δ) := by field_simp; ring
      linarith
    have hl0 : 0 ≤ Real.log a - Real.log (a - Δ) := by
      have := Real.log_le_log ha0 (by linarith : a - Δ ≤ a); linarith
    have h1 := m04h_le_one (x := a - Δ) (by linarith)
    have h2 : Δ / (a - Δ) ≤ 6 * Δ := by
      rw [div_le_iff₀ ha0]; nlinarith
    nlinarith [m04h_nonneg (x := a - Δ) (by linarith) (by linarith)]
  have hpieces : ∀ j ∈ range K, m04h (s (j + 1)) * (Real.log (s (j + 1 + 1)) - Real.log (s (j + 1))) ≤
      (F (s (j + 1 + 1)) - F (s (j + 1))) + D * Δ ^ 2 := by
    intro j hj
    have hjK : j + 1 + 1 ≤ K + 1 := by simp at hj; omega
    have hst : s (j + 1) ≤ s (j + 1 + 1) := hsmono (Nat.le_succ _)
    have hdiff : s (j + 1 + 1) - s (j + 1) = Δ := by rw [hs, hs]; push_cast; ring
    have ht1 : s (j + 1 + 1) < 1 := by linarith [hsc _ hjK]
    have hp := m04_piece (s := s (j + 1)) (t := s (j + 1 + 1)) (by linarith [hspos (j + 1)]) hst ht1
    have hs1' : a ≤ s (j + 1) := by rw [← hs1]; exact hsmono (by omega)
    have hden : (1 - c) ^ 2 * (1 / 3) ≤ (1 - s (j + 1 + 1)) * (1 - s (j + 1)) * s (j + 1 + 1) := by
      have e1 : 1 - c ≤ 1 - s (j + 1 + 1) := by linarith [hsc _ hjK]
      have e2 : 1 - c ≤ 1 - s (j + 1) := by linarith [hsc (j + 1) (by omega)]
      have e3 : 1 / 3 ≤ s (j + 1 + 1) := by linarith
      have : (1 - c) * (1 - c) ≤ (1 - s (j + 1 + 1)) * (1 - s (j + 1)) := mul_le_mul e1 e2 h1c.le (by linarith)
      calc (1 - c) ^ 2 * (1 / 3) = (1 - c) * (1 - c) * (1 / 3) := by ring
        _ ≤ _ := mul_le_mul this e3 (by norm_num) (by nlinarith)
    have herr : (1 - UU) * (s (j + 1 + 1) - s (j + 1)) ^ 2 /
        ((1 - s (j + 1 + 1)) * (1 - s (j + 1)) * s (j + 1 + 1)) ≤ D * Δ ^ 2 := by
      rw [hdiff, hD]
      have hpos : 0 < (1 - c) ^ 2 * (1 / 3) := by positivity
      calc (1 - UU) * Δ ^ 2 / ((1 - s (j + 1 + 1)) * (1 - s (j + 1)) * s (j + 1 + 1))
          ≤ (1 - UU) * Δ ^ 2 / ((1 - c) ^ 2 * (1 / 3)) := by
            apply div_le_div_of_nonneg_left _ hpos hden
            rw [hU]; positivity
        _ ≤ 3 / (1 - c) ^ 2 * Δ ^ 2 := by
            rw [div_le_iff₀ hpos]
            have : 3 / (1 - c) ^ 2 * Δ ^ 2 * ((1 - c) ^ 2 * (1 / 3)) = Δ ^ 2 := by field_simp
            rw [this, hU]; nlinarith
    rw [hF]; linarith
  have hsumP := sum_le_sum hpieces
  rw [sum_add_distrib, sum_range_sub (fun j => F (s (j + 1))), sum_const, card_range, nsmul_eq_mul] at hsumP
  have hFI : F (s (K + 1)) - F (s (0 + 1)) = bandI a c := by
    rw [zero_add, hsK, hs1, hF]; unfold bandI
    rw [Real.log_div (by linarith) (by linarith), Real.log_div (by linarith) (by linarith)]; ring
  rw [hFI] at hsumP
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hKD : (K : ℝ) * (D * Δ ^ 2) ≤ D * Δ := by
    have : (K : ℝ) * (D * Δ ^ 2) = D * Δ * (c - a) := by rw [← hKΔ]; ring
    rw [this]
    exact mul_le_of_le_one_right (mul_nonneg hD0 hΔ0.le) hca1
  linarith

/-- Mertens 3 ratio: `V(√(y/p)) ≤ 2R V(y)/(1 − x)`. -/
theorem m04_ratio (Vw Vy lw ly x κ η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (hly : 0 < ly) (hx : x < 1)
    (hVy : (1 - η) * κ ≤ Vy * ly) (hVw : Vw * lw ≤ (1 + η) * κ) (hlw : lw = (1 - x) * ly / 2) :
    Vw ≤ 2 * ((1 + η) / (1 - η)) * Vy / (1 - x) := by
  have h1x : 0 < 1 - x := by linarith
  have h1η : 0 < 1 - η := by linarith
  rw [hlw] at hVw
  have h3 : Vw * (1 - x) * (1 - η) * ly ≤ 2 * (1 + η) * Vy * ly := by nlinarith
  have hkey : Vw * (1 - x) * (1 - η) ≤ 2 * (1 + η) * Vy := le_of_mul_le_mul_right h3 hly
  rw [le_div_iff₀ h1x]
  have : 2 * ((1 + η) / (1 - η)) * Vy = 2 * (1 + η) * Vy / (1 - η) := by ring
  rw [this, le_div_iff₀ h1η]
  linarith

/-- Splitting `Σ_S h(x_p) gB(p)` into the pieces `(s_j, s_{j+1}]`. -/
theorem m04_split (b : ℕ) (y a c : ℝ) (K : ℕ) (s : ℕ → ℝ) (hy1 : 1 < y) (hsmono : Monotone s)
    (hs0 : 0 < s 0) (hs0a : s 0 < a) (hsK : s (K + 1) = c) (hc1 : c < 1) (hcU : c < UU)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ y ^ a ≤ (p : ℝ) ∧ (p : ℝ) < y ^ c) :
    ∑ p ∈ S, m04h (Real.log p / Real.log y) * gB b p ≤
      ∑ j ∈ range (K + 1), m04h (s j) * mu1 b y (s 0) (Real.log (s j)) (Real.log (s (j + 1))) := by
  classical
  have hy0 : 0 < y := by linarith
  have hlogy : 0 < Real.log y := Real.log_pos hy1
  have hspos : ∀ j, 0 < s j := fun j => lt_of_lt_of_le hs0 (hsmono (Nat.zero_le j))
  have hsc : ∀ j, j ≤ K + 1 → s j ≤ c := by
    intro j hj; have := hsmono hj; rw [hsK] at this; exact this
  obtain ⟨Lg, hLg⟩ : ∃ Lg : ℕ → ℝ, Lg = fun j => Real.log (s j) := ⟨_, rfl⟩
  have hLgm : Monotone Lg := by
    intro i j hij; rw [hLg]; exact Real.log_le_log (hspos i) (hsmono hij)
  have hsub : S ⊆ Pset y (s 0) := by
    intro p hp
    obtain ⟨hpp, hpa, hpc⟩ := hS p hp
    unfold Pset
    rw [mem_filter, mem_Ioc]
    refine ⟨⟨?_, ?_⟩, hpp⟩
    · rw [Nat.floor_lt (Real.rpow_nonneg hy0.le _)]
      have : y ^ (s 0) < y ^ a := Real.rpow_lt_rpow_of_exponent_lt hy1 hs0a
      linarith
    · apply Nat.le_floor
      have : y ^ c ≤ y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hy1.le hc1.le
      rw [Real.rpow_one] at this; linarith
  have hpt2 : ∀ p ∈ S, m04h (Real.log p / Real.log y) * gB b p ≤
      ∑ j ∈ range (K + 1), (if sig y p ∈ Set.Ioc (Lg j) (Lg (j + 1)) then m04h (s j) * gB b p else 0) := by
    intro p hp
    obtain ⟨hpp, hpa, hpc⟩ := hS p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hlp0 : 0 < Real.log p := Real.log_pos (by exact_mod_cast hpp.one_lt)
    obtain ⟨x, hx⟩ : ∃ x, x = Real.log p / Real.log y := ⟨_, rfl⟩
    rw [← hx]
    have hx0 : 0 < x := by rw [hx]; exact div_pos hlp0 hlogy
    have hlp : Real.log p = x * Real.log y := by rw [hx]; field_simp
    have hxc : x < c := by
      have := Real.log_lt_log hp0 hpc
      rw [Real.log_rpow hy0, hlp] at this
      exact lt_of_mul_lt_mul_right this hlogy.le
    have hxa : a ≤ x := by
      have := Real.log_le_log (Real.rpow_pos_of_pos hy0 _) hpa
      rw [Real.log_rpow hy0, hlp] at this
      exact le_of_mul_le_mul_right this hlogy
    have hsig : sig y p = Real.log x := by rw [hx]; rfl
    have hmem : sig y p ∈ Set.Ioc (Lg 0) (Lg (K + 1)) := by
      rw [hsig, Set.mem_Ioc, hLg]
      simp only
      rw [hsK]
      exact ⟨Real.log_lt_log hs0 (by linarith), Real.log_le_log hx0 hxc.le⟩
    have htele := m04_tele Lg hLgm (sig y p) (K + 1)
    rw [if_pos hmem] at htele
    calc m04h x * gB b p = (∑ j ∈ range (K + 1), (if sig y p ∈ Set.Ioc (Lg j) (Lg (j + 1)) then (1 : ℝ) else 0)) *
          (m04h x * gB b p) := by rw [htele, one_mul]
      _ = ∑ j ∈ range (K + 1), (if sig y p ∈ Set.Ioc (Lg j) (Lg (j + 1)) then m04h x * gB b p else 0) := by
          rw [sum_mul]; apply sum_congr rfl; intro j _; split_ifs <;> simp
      _ ≤ _ := by
          apply sum_le_sum; intro j _
          split_ifs with hj
          · apply mul_le_mul_of_nonneg_right _ (gB_nonneg b p)
            apply m04h_anti _ (by linarith)
            have h1 := hj.1
            rw [hLg, hsig] at h1
            exact ((Real.log_lt_log_iff (hspos j) hx0).1 h1).le
          · exact le_refl _
  have hnn : ∀ p, 0 ≤ ∑ j ∈ range (K + 1), (if sig y p ∈ Set.Ioc (Lg j) (Lg (j + 1)) then m04h (s j) * gB b p else 0) := by
    intro p; apply sum_nonneg; intro j hj
    have hj' : j ≤ K + 1 := by simp at hj; omega
    split_ifs
    · exact mul_nonneg (m04h_nonneg (by linarith [hsc j hj']) (by linarith [hsc j hj'])) (gB_nonneg b p)
    · exact le_refl _
  calc _ ≤ ∑ p ∈ S, ∑ j ∈ range (K + 1), (if sig y p ∈ Set.Ioc (Lg j) (Lg (j + 1)) then m04h (s j) * gB b p else 0) :=
        sum_le_sum hpt2
    _ ≤ ∑ p ∈ Pset y (s 0), ∑ j ∈ range (K + 1), (if sig y p ∈ Set.Ioc (Lg j) (Lg (j + 1)) then m04h (s j) * gB b p else 0) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => hnn p)
    _ = _ := by
        rw [sum_comm]; apply sum_congr rfl; intro j _
        unfold mu1
        rw [mul_sum, sum_filter]
        apply sum_congr rfl; intro p _
        rw [hLg]

set_option maxHeartbeats 2000000 in
/-- The band sum of one band. -/
theorem m04_band (b : ℕ) (hb : 2 ≤ b) (a c : ℝ) (ha : 1 / 3 ≤ a) (hac : a < c) (hc : c ≤ 2 * UU - 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ y in atTop, ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ y ^ a ≤ (p : ℝ) ∧ (p : ℝ) < y ^ c) →
      ∑ p ∈ S, (UU - Real.log p / Real.log y) * gB b p * VB b (Real.sqrt (y / p)) ≤
        2 * VB b y * (bandI a c + ε) := by
  classical
  have hU : UU = 83 / 85 := rfl
  have hc1 : c < 1 := by rw [hU] at hc; linarith
  have hcU : c < UU := by rw [hU] at hc ⊢; linarith
  have h1c : 0 < 1 - c := by linarith
  obtain ⟨C, hC0, hC⟩ := VB_log b hb
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = kappaB b := ⟨_, rfl⟩
  rw [← hκdef] at hC
  have hκ : 0 < κ := by rw [hκdef]; exact kappaB_pos b
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = min (1 / 3) (ε / (9 * (2 + ε))) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hηdef]; exact lt_min (by norm_num) (by positivity)
  have hη3 : η ≤ 1 / 3 := by rw [hηdef]; exact min_le_left _ _
  have hηε : 3 * η * (2 + ε) ≤ ε / 3 := by
    have h : η ≤ ε / (9 * (2 + ε)) := by rw [hηdef]; exact min_le_right _ _
    have h2 : 0 < 2 + ε := by linarith
    rw [le_div_iff₀ (by positivity)] at h
    nlinarith
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 3 / (1 - c) ^ 2 := ⟨_, rfl⟩
  have hD0 : 0 < D := by rw [hD]; positivity
  obtain ⟨δ0, hδ0⟩ : ∃ δ0 : ℝ, δ0 = min (1 / 6) (ε / (3 * (6 + D))) := ⟨_, rfl⟩
  have hδ00 : 0 < δ0 := by rw [hδ0]; exact lt_min (by norm_num) (by positivity)
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌈(c - a) / δ0⌉₊ + 1 := ⟨_, rfl⟩
  have hK1 : (1 : ℝ) ≤ K := by
    rw [hK]; push_cast; have := Nat.cast_nonneg (α := ℝ) ⌈(c - a) / δ0⌉₊; linarith
  have hK0 : (0 : ℝ) < K := by linarith
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : ℝ, Δ = (c - a) / K := ⟨_, rfl⟩
  have hΔ0 : 0 < Δ := by rw [hΔ]; exact div_pos (by linarith) hK0
  have hΔle : Δ ≤ δ0 := by
    rw [hΔ, div_le_iff₀ hK0]
    have h1 : (c - a) / δ0 ≤ K := by
      rw [hK]; push_cast; linarith [Nat.le_ceil ((c - a) / δ0)]
    rw [div_le_iff₀ hδ00] at h1; linarith
  have hδ6 : δ0 ≤ 1 / 6 := by rw [hδ0]; exact min_le_left _ _
  have hδε : δ0 ≤ ε / (3 * (6 + D)) := by rw [hδ0]; exact min_le_right _ _
  have hΔ6 : Δ ≤ 1 / 6 := le_trans hΔle hδ6
  have hΔε : (6 + D) * Δ ≤ ε / 3 := by
    have := le_trans hΔle hδε
    rw [le_div_iff₀ (by positivity)] at this; linarith
  have hKΔ : (K : ℝ) * Δ = c - a := by rw [hΔ]; field_simp
  have hca1 : c - a ≤ 1 := by rw [hU] at hc; linarith
  obtain ⟨s, hs⟩ : ∃ s : ℕ → ℝ, s = fun j : ℕ => a + ((j : ℝ) - 1) * Δ := ⟨_, rfl⟩
  have hs' : ∀ j, s j = a + ((j : ℝ) - 1) * Δ := fun j => by rw [hs]
  have hs0 : s 0 = a - Δ := by rw [hs']; push_cast; ring
  have hsK : s (K + 1) = c := by rw [hs']; push_cast; linarith
  have hsmono : Monotone s := by
    intro i j hij
    rw [hs', hs']
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    nlinarith
  have hspos : ∀ j, 1 / 6 ≤ s j := by
    intro j; have := hsmono (Nat.zero_le j); rw [hs0] at this; linarith
  have hsc : ∀ j, j ≤ K + 1 → s j ≤ c := by
    intro j hj; have := hsmono hj; rw [hsK] at this; exact this
  obtain ⟨η', hη'⟩ : ∃ η' : ℝ, η' = ε / (3 * (K + 1)) := ⟨_, rfl⟩
  have hη'0 : 0 < η' := by rw [hη']; positivity
  obtain ⟨L0, hL0⟩ : ∃ L0 : ℝ, L0 = max (Real.log ((bigB b : ℝ) + 4)) (C / (η * κ)) := ⟨_, rfl⟩
  -- eventually conditions
  have ev1 : ∀ᶠ y : ℝ in atTop, 2 ≤ y := eventually_ge_atTop 2
  have ev2 : ∀ᶠ y : ℝ in atTop, 2 * L0 / (1 - c) ≤ Real.log y :=
    tendsto_log_atTop.eventually_ge_atTop _
  have ev3 : ∀ᶠ y : ℝ in atTop, ∀ j ∈ range (K + 1),
      mu1 b y (s 0) (Real.log (s j)) (Real.log (s (j + 1))) ≤ Real.log (s (j + 1)) - Real.log (s j) + η' := by
    rw [eventually_all_finset]
    intro j hj
    have hj' : j + 1 ≤ K + 1 := by simp at hj; omega
    have hT := mu1_tendsto b hb (s 0) (Real.log (s j)) (Real.log (s (j + 1))) (by linarith [hspos 0])
      (Real.log_le_log (by linarith [hspos 0]) (hsmono (Nat.zero_le j)))
      (Real.log_le_log (by linarith [hspos j]) (hsmono (Nat.le_succ j)))
      (Real.log_nonpos (by linarith [hspos (j + 1)]) (by linarith [hsc _ hj']))
    filter_upwards [hT.eventually (Iic_mem_nhds (lt_add_of_pos_right _ hη'0))] with y hy
    exact hy
  filter_upwards [ev1, ev2, ev3] with y hy2 hyL hmu
  intro S hS
  have hy1 : 1 < y := by linarith
  have hy0 : 0 < y := by linarith
  have hlogy : 0 < Real.log y := Real.log_pos hy1
  have hL0y : L0 ≤ (1 - c) / 2 * Real.log y := by
    rw [div_le_iff₀ h1c] at hyL; linarith
  have hL0y' : L0 ≤ Real.log y := by nlinarith
  have hB4 : 0 < (bigB b : ℝ) + 4 := by positivity
  -- Mertens 3 at a point `w` with `L0 ≤ log w`
  have hM3 : ∀ w : ℝ, 0 < w → L0 ≤ Real.log w →
      (1 - η) * κ ≤ VB b w * Real.log w ∧ VB b w * Real.log w ≤ (1 + η) * κ := by
    intro w hw hLw
    have hm1 : Real.log ((bigB b : ℝ) + 4) ≤ L0 := by rw [hL0]; exact le_max_left _ _
    have hm2 : C / (η * κ) ≤ L0 := by rw [hL0]; exact le_max_right _ _
    have hw4 : (bigB b : ℝ) + 4 ≤ w := (Real.log_le_log_iff hB4 hw).1 (le_trans hm1 hLw)
    have hlw : 0 < Real.log w := by
      have : 0 < Real.log ((bigB b : ℝ) + 4) := Real.log_pos (by linarith [Nat.cast_nonneg (α := ℝ) (bigB b)])
      linarith
    have h := hC w hw4
    have hCw : C / Real.log w ≤ η * κ := by
      rw [div_le_iff₀ hlw]
      have := le_trans hm2 hLw
      rw [div_le_iff₀ (by positivity)] at this; linarith
    rw [abs_le] at h
    obtain ⟨h1, h2⟩ := h
    constructor <;> linarith
  obtain ⟨hVy, -⟩ := hM3 y hy0 hL0y'
  have hVy0 : 0 ≤ VB b y := m04_VB_nonneg b y
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = (1 + η) / (1 - η) := ⟨_, rfl⟩
  have hR3 : R ≤ 1 + 3 * η := by
    rw [hR, div_le_iff₀ (by linarith)]
    have e : (1 + 3 * η) * (1 - η) = 1 + 2 * η - 3 * (η * η) := by ring
    have : η * η ≤ η * (1 / 3) := mul_le_mul_of_nonneg_left hη3 hη0.le
    rw [e]; linarith
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = ∑ p ∈ S, m04h (Real.log p / Real.log y) * gB b p := ⟨_, rfl⟩
  -- pointwise bound on S
  have hpt : ∀ p ∈ S, (UU - Real.log p / Real.log y) * gB b p * VB b (Real.sqrt (y / p)) ≤
      2 * VB b y * R * (m04h (Real.log p / Real.log y) * gB b p) := by
    intro p hp
    obtain ⟨hpp, hpa, hpc⟩ := hS p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    obtain ⟨x, hx⟩ : ∃ x, x = Real.log p / Real.log y := ⟨_, rfl⟩
    rw [← hx]
    have hlp : Real.log p = x * Real.log y := by rw [hx]; field_simp
    have hxc : x < c := by
      have := Real.log_lt_log hp0 hpc
      rw [Real.log_rpow hy0, hlp] at this
      exact lt_of_mul_lt_mul_right this hlogy.le
    have hyp : 0 < y / p := div_pos hy0 hp0
    have hw0 : 0 < Real.sqrt (y / p) := Real.sqrt_pos.2 hyp
    have hlw : Real.log (Real.sqrt (y / p)) = (1 - x) * Real.log y / 2 := by
      rw [Real.log_sqrt hyp.le, Real.log_div hy0.ne' hp0.ne', hlp]; ring
    have hLw : L0 ≤ Real.log (Real.sqrt (y / p)) := by
      rw [hlw]
      have h := mul_le_mul_of_nonneg_right (show (1 - c) / 2 ≤ (1 - x) / 2 by linarith) hlogy.le
      have e : (1 - x) * Real.log y / 2 = (1 - x) / 2 * Real.log y := by ring
      rw [e]; linarith
    obtain ⟨-, hVw⟩ := hM3 _ hw0 hLw
    have h1x : 0 < 1 - x := by linarith
    have hVw' := m04_ratio _ _ _ _ x κ η hη0 (by linarith) hlogy (by linarith) hVy hVw hlw
    rw [← hR] at hVw'
    have hg0 : 0 ≤ gB b p := gB_nonneg b p
    have hUx : 0 ≤ UU - x := by linarith
    calc (UU - x) * gB b p * VB b (Real.sqrt (y / p)) ≤ (UU - x) * gB b p * (2 * R * VB b y / (1 - x)) :=
          mul_le_mul_of_nonneg_left hVw' (mul_nonneg hUx hg0)
      _ = 2 * VB b y * R * (m04h x * gB b p) := by unfold m04h; field_simp
  have hsum1 : ∑ p ∈ S, (UU - Real.log p / Real.log y) * gB b p * VB b (Real.sqrt (y / p)) ≤
      2 * VB b y * R * X := by
    rw [hX, mul_sum]; exact sum_le_sum hpt
  have hX0 : 0 ≤ X := by
    rw [hX]; apply sum_nonneg; intro p hp
    obtain ⟨hpp, hpa, hpc⟩ := hS p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hxc : Real.log p / Real.log y < c := by
      rw [div_lt_iff₀ hlogy]
      have := Real.log_lt_log hp0 hpc
      rw [Real.log_rpow hy0] at this; linarith
    exact mul_nonneg (m04h_nonneg (by linarith) (by linarith)) (gB_nonneg b p)
  have hX1 := m04_split b y a c K s hy1 hsmono (by linarith [hspos 0]) (by rw [hs0]; linarith) hsK hc1 hcU S hS
  rw [← hX] at hX1
  -- Mertens 2 on each piece
  have hX2 : ∑ j ∈ range (K + 1), m04h (s j) * mu1 b y (s 0) (Real.log (s j)) (Real.log (s (j + 1))) ≤
      ∑ j ∈ range (K + 1), m04h (s j) * (Real.log (s (j + 1)) - Real.log (s j)) + (K + 1) * η' := by
    have : ∑ j ∈ range (K + 1), m04h (s j) * mu1 b y (s 0) (Real.log (s j)) (Real.log (s (j + 1))) ≤
        ∑ j ∈ range (K + 1), (m04h (s j) * (Real.log (s (j + 1)) - Real.log (s j)) + η') := by
      apply sum_le_sum; intro j hj
      have hj' : j ≤ K + 1 := by simp at hj; omega
      have h0 := m04h_nonneg (x := s j) (by linarith [hsc j hj']) (by linarith [hsc j hj'])
      have h1 := m04h_le_one (x := s j) (by linarith [hsc j hj'])
      have hm := hmu j hj
      have hmu0 : 0 ≤ mu1 b y (s 0) (Real.log (s j)) (Real.log (s (j + 1))) := by
        unfold mu1; exact sum_nonneg (fun p _ => gB_nonneg b p)
      have : m04h (s j) * mu1 b y (s 0) (Real.log (s j)) (Real.log (s (j + 1))) ≤
          m04h (s j) * (Real.log (s (j + 1)) - Real.log (s j) + η') := mul_le_mul_of_nonneg_left hm h0
      nlinarith
    rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul] at this
    push_cast at this ⊢; linarith
  have hX3 := m04_riemann a c Δ K s hs' ha hac hc1 hcU hΔ0 hΔ6 hKΔ hca1
  rw [← hD] at hX3
  have hbI : bandI a c ≤ 2 := by
    unfold bandI
    have h1 : Real.log (c / a) ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (div_pos (by linarith : (0 : ℝ) < c) (by linarith : (0 : ℝ) < a))
      have : c / a ≤ 3 := by rw [div_le_iff₀ (by linarith)]; linarith
      linarith
    have h2 : Real.log ((1 - c) / (1 - a)) ≤ 0 :=
      Real.log_nonpos (div_nonneg h1c.le (by linarith)) (by rw [div_le_one (by linarith)]; linarith)
    have hl0 : 0 ≤ Real.log (c / a) := Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
    rw [hU]; nlinarith
  have hKη : ((K : ℝ) + 1) * η' = ε / 3 := by rw [hη']; field_simp
  have hXle : X ≤ bandI a c + 2 * ε / 3 := by linarith
  have hRX : R * X ≤ bandI a c + ε := by
    have : R * X ≤ (1 + 3 * η) * X := mul_le_mul_of_nonneg_right hR3 hX0
    have h2 : 3 * η * X ≤ 3 * η * (2 + ε) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith
  calc _ ≤ 2 * VB b y * R * X := hsum1
    _ = 2 * VB b y * (R * X) := by ring
    _ ≤ 2 * VB b y * (bandI a c + ε) := mul_le_mul_of_nonneg_left hRX (by linarith)

end Omega3
