import Palprimes.Greaves.Brun

/-! # Rosser's conditions in log coordinates

`RosX σ c xs`: the real version of `RosOK` (budget `c`, checks `3x ≤ c` in the plus state).
* `RosOK_iff_RosX`: for positive integers, `RosOK σ z ps ↔ RosX σ (log z / log y) (log p / log y)`.
* `RosX_false_iff`: `RosX false c xs ↔ ∀ j ≥ 1, 2j ≤ |xs| → Σ_{i<2j−1} xs_i + 3 xs_{2j−1} ≤ c`. -/

set_option linter.style.longLine false

open Finset Real

namespace Palprimes.MT

open Palprimes.Greaves

/-- Real Rosser conditions with a log budget. -/
def RosX : Bool → ℝ → List ℝ → Prop
  | _, _, [] => True
  | false, c, x :: xs => RosX true (c - x) xs
  | true, c, x :: xs => 3 * x ≤ c ∧ RosX false (c - x) xs

theorem RosOK_iff_RosX (y : ℝ) (hy : 1 < y) : ∀ (ps : List ℕ) (σ : Bool) (z : ℝ), 0 < z →
    (∀ p ∈ ps, 0 < p) →
    (RosOK σ z ps ↔ RosX σ (Real.log z / Real.log y) (ps.map (fun p : ℕ => Real.log p / Real.log y))) := by
  have hL : 0 < Real.log y := Real.log_pos hy
  intro ps
  induction ps with
  | nil => intro σ z _ _; simp [RosOK, RosX]
  | cons P ps ih =>
    intro σ z hz hpos
    have hP : (0 : ℝ) < P := by exact_mod_cast hpos P (by simp)
    have hzP : 0 < z / P := div_pos hz hP
    have hrest : ∀ p ∈ ps, 0 < p := fun p hp => hpos p (List.mem_cons_of_mem P hp)
    have hlog : Real.log (z / P) / Real.log y = Real.log z / Real.log y - Real.log P / Real.log y := by
      rw [Real.log_div hz.ne' hP.ne', sub_div]
    cases σ with
    | false =>
      simp only [RosOK, headOK, true_and, Bool.not_false, List.map_cons, RosX]
      rw [ih true (z / P) hzP hrest, hlog]
    | true =>
      simp only [RosOK, headOK, Bool.not_true, List.map_cons, RosX]
      rw [ih false (z / P) hzP hrest, hlog]
      apply and_congr_left'
      rw [← Real.log_le_log_iff (by positivity) hz, Real.log_pow, ← mul_div_assoc,
        div_le_div_iff_of_pos_right hL]
      push_cast; rfl

/-- Prefix sum of a list. -/
noncomputable def psum (xs : List ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, xs.getD i 0

theorem psum_cons (a : ℝ) (xs : List ℝ) (n : ℕ) : psum (a :: xs) (n + 1) = a + psum xs n := by
  unfold psum
  rw [Finset.sum_range_succ']
  simp [add_comm]

/-- **Sum form of Rosser's lower-bound conditions.** -/
theorem RosX_false_iff : ∀ (xs : List ℝ) (c : ℝ), RosX false c xs ↔
    ∀ j : ℕ, 1 ≤ j → 2 * j ≤ xs.length → psum xs (2 * j - 1) + 3 * xs.getD (2 * j - 1) 0 ≤ c
  | [], c => by
    simp only [RosX, List.length_nil, true_iff]
    intro j hj h2; omega
  | [a], c => by
    simp only [RosX, List.length_singleton, true_iff]
    intro j hj h2; omega
  | a :: b :: rest, c => by
    simp only [RosX]
    rw [RosX_false_iff rest (c - a - b)]
    constructor
    · rintro ⟨h1, h2⟩ j hj hjl
      rcases Nat.lt_or_ge j 2 with hj2 | hj2
      · have : j = 1 := by omega
        subst this
        simp [psum]; linarith
      · have hl : 2 * (j - 1) ≤ rest.length := by simp at hjl; omega
        have := h2 (j - 1) (by omega) hl
        have e1 : 2 * j - 1 = (2 * (j - 1) - 1) + 2 := by omega
        rw [e1, psum_cons, psum_cons]
        simp only [List.getD_cons_succ]
        have : psum rest (2 * (j - 1) - 1) + 3 * rest.getD (2 * (j - 1) - 1) 0 ≤ c - a - b := this
        linarith
    · intro h
      refine ⟨?_, ?_⟩
      · have := h 1 le_rfl (by simp)
        simp [psum] at this; linarith
      · intro j hj hjl
        have := h (j + 1) (by omega) (by simp; omega)
        have e1 : 2 * (j + 1) - 1 = (2 * j - 1) + 2 := by omega
        rw [e1, psum_cons, psum_cons] at this
        simp only [List.getD_cons_succ] at this
        linarith

theorem psum_succ (xs : List ℝ) (n : ℕ) : psum xs (n + 1) = psum xs n + xs.getD n 0 := by
  unfold psum; rw [Finset.sum_range_succ]

/-- **Range for even chains**: `1 − Σ ≥ 2 x_r`. -/
theorem RosX_range_even (l : List ℝ) (hl : RosX false 1 l) (j : ℕ) (hj : 1 ≤ j) (hr : l.length = 2 * j) :
    2 * l.getD (2 * j - 1) 0 ≤ 1 - psum l (2 * j) := by
  have h := (RosX_false_iff l 1).1 hl j hj (by omega)
  have e : psum l (2 * j) = psum l (2 * j - 1) + l.getD (2 * j - 1) 0 := by
    rw [show 2 * j = (2 * j - 1) + 1 by omega, psum_succ]; congr 1
  rw [e]; linarith

/-- **Range for odd chains of length ≥ 3**: `1 − Σ ≥ x_r` when the chain decreases. -/
theorem RosX_range_odd (l : List ℝ) (hl : RosX false 1 l) (j : ℕ) (hj : 1 ≤ j) (hr : l.length = 2 * j + 1)
    (hdec : l.getD (2 * j) 0 ≤ l.getD (2 * j - 1) 0) :
    l.getD (2 * j) 0 ≤ 1 - psum l (2 * j + 1) := by
  have h := (RosX_false_iff l 1).1 hl j hj (by omega)
  have e : psum l (2 * j + 1) = psum l (2 * j - 1) + l.getD (2 * j - 1) 0 + l.getD (2 * j) 0 := by
    rw [psum_succ, show 2 * j = (2 * j - 1) + 1 by omega, psum_succ]
    congr 2
  rw [e]; linarith

end Palprimes.MT
