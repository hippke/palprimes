import Omega3.Statements

/-!
# S10 helpers, part 3: Nat arithmetic facts and the log chain
-/

set_option linter.style.longLine false

open Real

namespace Omega3
namespace S10

def Qn : ℕ := 1048576
def TP : ℕ := 18446744073709551616
def En : ℕ := 100000
def NS : ℕ := 12
def QN : ℕ := Qn * NS
def D0 : ℕ := 10000000

lemma Qn_pos : (0 : ℝ) < Qn := by norm_num [Qn]
lemma TP_pos : (0 : ℝ) < TP := by norm_num [TP]

lemma tsub_lo (a b : ℕ) (x : ℝ) (h : (a : ℝ) - b ≤ x) (h0 : 0 ≤ x) : ((a - b : ℕ) : ℝ) ≤ x := by
  rcases le_total b a with hb | hb
  · rw [Nat.cast_sub hb]; exact h
  · rw [Nat.sub_eq_zero_of_le hb]; simpa using h0

lemma tsub_hi (a b : ℕ) (x : ℝ) (h : x ≤ (a : ℝ) - b) : x ≤ ((a - b : ℕ) : ℝ) := by
  rcases le_total b a with hb | hb
  · rw [Nat.cast_sub hb]; exact h
  · rw [Nat.sub_eq_zero_of_le hb]
    have : (a : ℝ) ≤ b := by exact_mod_cast hb
    simp only [Nat.cast_zero]; linarith

lemma ndiv_le (a b : ℕ) : ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / b := Nat.cast_div_le

lemma cdiv_ge (a b : ℕ) (hb : 0 < b) : (a : ℝ) / b ≤ (((a + b - 1) / b : ℕ) : ℝ) := by
  have h1 := Nat.div_add_mod (a + b - 1) b
  have h2 := Nat.mod_lt (a + b - 1) hb
  have h3 : a ≤ b * ((a + b - 1) / b) := by omega
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_le_iff₀ hb']
  have : (a : ℝ) ≤ (b : ℝ) * (((a + b - 1) / b : ℕ) : ℝ) := by exact_mod_cast h3
  linarith

/-- `−log(n/Q) = log Q − log n`. -/
noncomputable def NL (n : ℕ) : ℝ := Real.log Qn - Real.log n

/-- Valid log entry: `lo ≤ TP·(−log(n/Q)) ≤ hi`. -/
def LogOK (t : ℕ × ℕ × ℕ) : Prop := (t.2.1 : ℝ) ≤ TP * NL t.1 ∧ TP * NL t.1 ≤ t.2.2

def lstepLo (n n2 : ℕ) : ℕ :=
  (TP * ((12 * (n - n2) * n2 ^ 3 + 4 * (n - n2) ^ 3 * n2) * (n2 - (n - n2)) -
    ((6 * (n - n2) ^ 2 * n2 ^ 2 + 3 * (n - n2) ^ 4) * (n2 - (n - n2)) + 12 * (n - n2) ^ 5))) /
    (12 * n2 ^ 4 * (n2 - (n - n2)))

def lstepHi (n n2 : ℕ) : ℕ :=
  (TP * ((12 * (n - n2) * n2 ^ 3 + 4 * (n - n2) ^ 3 * n2) * (n2 - (n - n2)) + 12 * (n - n2) ^ 5 -
    (6 * (n - n2) ^ 2 * n2 ^ 2 + 3 * (n - n2) ^ 4) * (n2 - (n - n2))) + 12 * n2 ^ 4 * (n2 - (n - n2)) - 1) /
    (12 * n2 ^ 4 * (n2 - (n - n2)))

lemma log_series (y : ℝ) (h0 : 0 < y) (h1 : y < 1) :
    y - y ^ 2 / 2 + y ^ 3 / 3 - y ^ 4 / 4 - y ^ 5 / (1 - y) ≤ Real.log (1 + y) ∧
    Real.log (1 + y) ≤ y - y ^ 2 / 2 + y ^ 3 / 3 - y ^ 4 / 4 + y ^ 5 / (1 - y) := by
  have hy : |(-y)| < 1 := by rw [abs_neg, abs_of_pos h0]; exact h1
  have h := Real.abs_log_sub_add_sum_range_le hy 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, abs_of_pos h0, sub_neg_eq_add] at h
  have h' := abs_le.mp h
  constructor <;> nlinarith [h'.1, h'.2]

theorem lstep_ok (n n2 : ℕ) (h1 : n2 < n) (h2 : n < 2 * n2) :
    (lstepLo n n2 : ℝ) ≤ TP * Real.log ((n : ℝ) / n2) ∧ TP * Real.log ((n : ℝ) / n2) ≤ lstepHi n n2 := by
  set d := n - n2 with hd
  have hdn : d < n2 := by omega
  have hd0 : 0 < d := by omega
  have hn2 : (0 : ℝ) < n2 := by exact_mod_cast (show 0 < n2 by omega)
  have hdR : (d : ℝ) = n - n2 := by rw [hd, Nat.cast_sub h1.le]
  have hnd : ((n2 - d : ℕ) : ℝ) = n2 - d := Nat.cast_sub hdn.le
  have hd0R : (0 : ℝ) < d := by exact_mod_cast hd0
  have hdnR : (d : ℝ) < n2 := by exact_mod_cast hdn
  set y : ℝ := d / n2 with hy
  have hy0 : 0 < y := div_pos hd0R hn2
  have hy1 : y < 1 := by rw [hy, div_lt_one hn2]; exact hdnR
  have hlog : Real.log ((n : ℝ) / n2) = Real.log (1 + y) := by
    congr 1; rw [hy]; field_simp; rw [hdR]; ring
  obtain ⟨hl, hu⟩ := log_series y hy0 hy1
  have hlogpos : 0 ≤ Real.log (1 + y) := Real.log_nonneg (by linarith)
  set den : ℕ := 12 * n2 ^ 4 * (n2 - d)
  have hden : (0 : ℝ) < den := by
    simp only [den]; push_cast [hnd]; have : (0:ℝ) < n2 - d := by linarith
    positivity
  have hdenpos : 0 < den := by exact_mod_cast hden
  have key : ((12 * d * n2 ^ 3 + 4 * d ^ 3 * n2 : ℕ) : ℝ) * ((n2 - d : ℕ) : ℝ) -
      (((6 * d ^ 2 * n2 ^ 2 + 3 * d ^ 4 : ℕ) : ℝ) * ((n2 - d : ℕ) : ℝ) + 12 * (d : ℝ) ^ 5) =
      (den : ℝ) * (y - y ^ 2 / 2 + y ^ 3 / 3 - y ^ 4 / 4 - y ^ 5 / (1 - y)) := by
    simp only [den]; push_cast [hnd]
    have : (1 : ℝ) - y = (n2 - d) / n2 := by rw [hy]; field_simp
    rw [this, hy]
    have : (n2 : ℝ) - d ≠ 0 := by linarith
    field_simp; ring
  have key2 : ((12 * d * n2 ^ 3 + 4 * d ^ 3 * n2 : ℕ) : ℝ) * ((n2 - d : ℕ) : ℝ) + 12 * (d : ℝ) ^ 5 -
      ((6 * d ^ 2 * n2 ^ 2 + 3 * d ^ 4 : ℕ) : ℝ) * ((n2 - d : ℕ) : ℝ) =
      (den : ℝ) * (y - y ^ 2 / 2 + y ^ 3 / 3 - y ^ 4 / 4 + y ^ 5 / (1 - y)) := by
    simp only [den]; push_cast [hnd]
    have : (1 : ℝ) - y = (n2 - d) / n2 := by rw [hy]; field_simp
    rw [this, hy]
    have : (n2 : ℝ) - d ≠ 0 := by linarith
    field_simp; ring
  rw [hlog]
  constructor
  · -- lower
    have hN : (((12 * d * n2 ^ 3 + 4 * d ^ 3 * n2) * (n2 - d) - ((6 * d ^ 2 * n2 ^ 2 + 3 * d ^ 4) * (n2 - d) + 12 * d ^ 5) : ℕ) : ℝ)
        ≤ den * Real.log (1 + y) := by
      apply tsub_lo
      · push_cast; push_cast at key; rw [key]
        exact mul_le_mul_of_nonneg_left hl hden.le
      · positivity
    have := ndiv_le (TP * ((12 * d * n2 ^ 3 + 4 * d ^ 3 * n2) * (n2 - d) - ((6 * d ^ 2 * n2 ^ 2 + 3 * d ^ 4) * (n2 - d) + 12 * d ^ 5))) den
    unfold lstepLo
    rw [← hd]
    refine le_trans this ?_
    rw [div_le_iff₀ hden]; push_cast
    have := mul_le_mul_of_nonneg_left hN TP_pos.le
    push_cast at this; nlinarith
  · have hN : (den : ℝ) * Real.log (1 + y) ≤
        (((12 * d * n2 ^ 3 + 4 * d ^ 3 * n2) * (n2 - d) + 12 * d ^ 5 - (6 * d ^ 2 * n2 ^ 2 + 3 * d ^ 4) * (n2 - d) : ℕ) : ℝ) := by
      apply tsub_hi
      push_cast; push_cast at key2; rw [key2]
      exact mul_le_mul_of_nonneg_left hu hden.le
    have := cdiv_ge (TP * ((12 * d * n2 ^ 3 + 4 * d ^ 3 * n2) * (n2 - d) + 12 * d ^ 5 - (6 * d ^ 2 * n2 ^ 2 + 3 * d ^ 4) * (n2 - d))) den hdenpos
    unfold lstepHi
    rw [← hd]
    refine le_trans ?_ this
    rw [le_div_iff₀ hden]; push_cast
    have := mul_le_mul_of_nonneg_left hN TP_pos.le
    push_cast at this; nlinarith

end S10
end Omega3
