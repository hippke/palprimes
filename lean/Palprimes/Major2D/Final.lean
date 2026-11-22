import Palprimes.Major2D.Maj
import Palprimes.Major2D.Comp
import Palprimes.TL1.Asymp

/-! # Generic assembly: `BlockMaj` from a full term list, and the conditions (ii), (iii) from integer inequalities -/

set_option linter.style.longLine false
set_option maxRecDepth 8000

open Real Finset

namespace Palprimes.M2

/-- conditions (ii), (iii) from an integer inequality `x^D b^N1 (2b²+1)^N2 ≤ (3b²)^N2 (2^52)^D`, `x = xn/2^52`. -/
theorem cond_from_int (b : ℕ) (hb : 2 ≤ b) (l D N1 N2 xn : ℕ) (hl : 0 < l) (hD : 0 < D) (hxn : 0 < xn)
    (hb' : Nat.ble (condL xn D b N1 N2) (condR D b N2) = true) :
    Real.logb b ((xn : ℝ) / 2 ^ 52) / l + (N1 : ℝ) / (D * l) ≤ (N2 : ℝ) / (D * l) * thetaB b := by
  have h : xn ^ D * b ^ N1 * (2 * b ^ 2 + 1) ^ N2 ≤ (3 * b ^ 2) ^ N2 * (2 ^ 52) ^ D := by
    have := Nat.le_of_ble_eq_true hb'
    unfold condL condR at this
    simp only [Nat.pow_eq, Nat.mul_eq, Nat.add_eq] at this
    convert this using 2 <;> ring
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hlogb : 0 < Real.log b := Real.log_pos hb1
  have hlr : (0 : ℝ) < l := by exact_mod_cast hl
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  set x : ℝ := (xn : ℝ) / 2 ^ 52 with hx
  have hx0 : 0 < x := by rw [hx]; have : (0 : ℝ) < xn := by exact_mod_cast hxn
                         positivity
  set ρ : ℝ := 3 * (b : ℝ) ^ 2 / (2 * (b : ℝ) ^ 2 + 1) with hρ
  have hρ0 : 0 < ρ := by positivity
  have hr : x ^ D * (b : ℝ) ^ N1 ≤ ρ ^ N2 := by
    have hc : ((xn ^ D * b ^ N1 * (2 * b ^ 2 + 1) ^ N2 : ℕ) : ℝ) ≤ (((3 * b ^ 2) ^ N2 * (2 ^ 52) ^ D : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at hc
    rw [hx, hρ, div_pow, div_pow]
    have h1 : (0 : ℝ) < (2 * (b : ℝ) ^ 2 + 1) ^ N2 := by positivity
    have h2 : (0 : ℝ) < ((2 : ℝ) ^ 52) ^ D := by positivity
    rw [div_mul_eq_mul_div, div_le_div_iff₀ h2 h1]
    rw [show ((2 : ℝ) ^ 52) ^ D = 4503599627370496 ^ D by norm_num]
    linarith
  have hl1 : Real.log (x ^ D * (b : ℝ) ^ N1) ≤ Real.log (ρ ^ N2) := Real.log_le_log (by positivity) hr
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow] at hl1
  unfold thetaB Real.logb
  rw [← hρ]
  rw [show Real.log x / Real.log b / l + (N1 : ℝ) / (D * l) = (D * Real.log x + N1 * Real.log b) / (D * l * Real.log b) by
    field_simp]
  rw [show (N2 : ℝ) / (D * l) * (Real.log ρ / Real.log b) = (N2 * Real.log ρ) / (D * l * Real.log b) by field_simp]
  exact div_le_div_of_nonneg_right hl1 (by positivity)

/-! ## Majorants from a full list -/

theorem mem_Sset (L : List ((ℤ × ℤ) × ℕ)) (w : ℤ × ℤ) (hw : w ∈ Sset L) : ∃ e ∈ L, e.1 = w := by
  unfold Sset at hw
  rw [List.mem_toFinset, List.mem_map] at hw
  exact hw

theorem tauF_nonneg (L : List ((ℤ × ℤ) × ℕ)) (w : ℤ × ℤ) : 0 ≤ tauF L w := by unfold tauF; positivity

theorem A_list (L : List ((ℤ × ℤ) × ℕ)) (hnd : (L.map Prod.fst).Nodup) :
    ∑ w ∈ Sset L, |tauF L w| = ((L.map Prod.snd).sum : ℝ) / 2 ^ 52 := by
  unfold Sset
  rw [List.sum_toFinset _ hnd, List.map_map]
  have : ∀ e ∈ L, ((fun w => |tauF L w|) ∘ Prod.fst) e = (e.2 : ℝ) / 2 ^ 52 := by
    intro e he
    show |tauF L e.1| = (e.2 : ℝ) / 2 ^ 52
    rw [abs_of_nonneg (tauF_nonneg _ _)]
    unfold tauF; rw [lk_mem L hnd e he]
  rw [List.map_congr_left this]
  clear this
  induction L with
  | nil => simp
  | cons e L ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    simp only [List.map_cons, List.sum_cons, Nat.cast_add]
    rw [ih hnd.2]; ring

end Palprimes.M2
