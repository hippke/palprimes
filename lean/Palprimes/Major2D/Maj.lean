import Palprimes.Major2D.Sym
import Palprimes.Major2D.Comp
import Palprimes.TL1.Majorant

/-! # From the checked trigonometric sums to `Tval` and `BlockMaj`

The majorant is given as a full list `L` of `((u, v), num)` (`τ_uv = num/2^52`, keys distinct), and the checker
uses the half list `Th` of doubled frequencies; `expandH` relates them (checked by `decide`). -/

set_option linter.style.longLine false
set_option maxRecDepth 8000

open Real Finset

namespace Palprimes.M2

theorem lk_mem (L : List ((ℤ × ℤ) × ℕ)) (hnd : (L.map Prod.fst).Nodup) (e : (ℤ × ℤ) × ℕ) (he : e ∈ L) : lk L e.1 = e.2 := by
  induction L with
  | nil => simp at he
  | cons f L ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    simp only [lk]
    rcases List.mem_cons.1 he with h | h
    · rw [h]; simp
    · have hne : f.1 ≠ e.1 := by
        intro hfe; apply hnd.1; rw [hfe]; exact List.mem_map_of_mem h
      rw [if_neg hne]; exact ih hnd.2 h

/-- the support and the coefficients. -/
def Sset (L : List ((ℤ × ℤ) × ℕ)) : Finset (ℤ × ℤ) := (L.map Prod.fst).toFinset
noncomputable def tauF (L : List ((ℤ × ℤ) × ℕ)) (w : ℤ × ℤ) : ℝ := (lk L w : ℝ) / 2 ^ 52

theorem tval_list (L : List ((ℤ × ℤ) × ℕ)) (hnd : (L.map Prod.fst).Nodup) (x y : ℝ) :
    Tval (Sset L) (tauF L) x y = (L.map (fun e => (e.2 : ℝ) / 2 ^ 52 * Real.cos (2 * π * ((e.1.1 : ℝ) * x + (e.1.2 : ℝ) * y)))).sum := by
  unfold Tval Sset
  rw [List.sum_toFinset _ hnd, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro e he
  simp only [Function.comp, tauF, lk_mem L hnd e he]

theorem expandH_sum (t : ℤ × ℤ × ℕ) (ht : (t.1 = 0 ∧ t.2.1 = 0) ∨ (t.1 % 2 = 0 ∧ t.2.1 % 2 = 0 ∧ t.2.2 % 2 = 0)) (x y : ℝ) :
    ((expandH t).map (fun e => (e.2 : ℝ) * Real.cos (2 * π * ((e.1.1 : ℝ) * x + (e.1.2 : ℝ) * y)))).sum =
      (t.2.2 : ℝ) * Real.cos (π * (t.1 * x + t.2.1 * y)) := by
  unfold expandH
  split_ifs with h0
  · simp [h0.1, h0.2]
  · have h1 : t.1 % 2 = 0 ∧ t.2.1 % 2 = 0 ∧ t.2.2 % 2 = 0 := by tauto
    obtain ⟨hU, hV, hc⟩ := h1
    have eU : ((t.1 / 2 : ℤ) : ℝ) = (t.1 : ℝ) / 2 := by
      rw [Int.cast_div (Int.dvd_of_emod_eq_zero hU) (by norm_num)]; norm_num
    have eV : ((t.2.1 / 2 : ℤ) : ℝ) = (t.2.1 : ℝ) / 2 := by
      rw [Int.cast_div (Int.dvd_of_emod_eq_zero hV) (by norm_num)]; norm_num
    have ec : ((t.2.2 / 2 : ℕ) : ℝ) = (t.2.2 : ℝ) / 2 := by
      rw [Nat.cast_div (Nat.dvd_of_mod_eq_zero hc) (by norm_num)]; norm_num
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Int.cast_neg, eU, eV, ec]
    rw [show 2 * π * (-((t.1 : ℝ) / 2) * x + -((t.2.1 : ℝ) / 2) * y) = -(2 * π * ((t.1 : ℝ) / 2 * x + (t.2.1 : ℝ) / 2 * y)) by ring,
      Real.cos_neg, show 2 * π * ((t.1 : ℝ) / 2 * x + (t.2.1 : ℝ) / 2 * y) = π * (t.1 * x + t.2.1 * y) by ring]
    ring

theorem sumC_expand (Th : List (ℤ × ℤ × ℕ)) (hev : evenOK Th = true) (x y : ℝ) :
    ((Th.flatMap expandH).map (fun e => (e.2 : ℝ) * Real.cos (2 * π * ((e.1.1 : ℝ) * x + (e.1.2 : ℝ) * y)))).sum = sumC Th x y := by
  induction Th with
  | nil => simp [sumC]
  | cons t Th ih =>
    simp only [evenOK, List.all_cons, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hev
    rw [List.flatMap_cons, List.map_append, List.sum_append, expandH_sum t (by tauto) x y,
      ih hev.2, sumC_cons]

/-- **`Tval` is the checked sum.** -/
theorem tval_eq (L : List ((ℤ × ℤ) × ℕ)) (Th : List (ℤ × ℤ × ℕ)) (hnd : (L.map Prod.fst).Nodup)
    (hperm : (Th.flatMap expandH).Perm L) (hev : evenOK Th = true) (x y : ℝ) :
    Tval (Sset L) (tauF L) x y = sumVal Th (2 ^ 52) x y := by
  rw [tval_list L hnd, sumVal_eq, ← sumC_expand Th hev, (hperm.map _).sum_eq]
  have : ∀ (M : List ((ℤ × ℤ) × ℕ)), (M.map (fun e => (e.2 : ℝ) / 2 ^ 52 * Real.cos (2 * π * ((e.1.1 : ℝ) * x + (e.1.2 : ℝ) * y)))).sum =
      (M.map (fun e => (e.2 : ℝ) * Real.cos (2 * π * ((e.1.1 : ℝ) * x + (e.1.2 : ℝ) * y)))).sum / 2 ^ 52 := by
    intro M; induction M with
    | nil => simp
    | cons e M ih => simp only [List.map_cons, List.sum_cons]; rw [ih]; ring
  rw [this]; norm_num

end Palprimes.M2
