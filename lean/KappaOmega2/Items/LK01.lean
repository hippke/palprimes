import KappaOmega2.StatementsK
import KappaOmega2.Items.L01

/-!
# LK01: `|G_g| ≤ (F_M + F_{M+1})/2` for the product weight

`Σ_{a<2M} prodW M a e(ay) = D_M(y) D_{M+1}(y)/(M(M+1))` with `D_n(y) = Σ_{j<n} e(jy)`, `|D_n|²/n² = F_n` (from L01),
then AM–GM.
-/

namespace KappaOmega2

open Finset Complex Palprimes

/-- Dirichlet sum `D_n(y) = Σ_{j<n} e(jy)`. -/
noncomputable def lkD (n : ℕ) (y : ℝ) : ℂ := ∑ j ∈ range n, ee ((j : ℝ) * y)

lemma LK01_count_pairs (M a : ℕ) (ha : a < 2 * M) :
    (∑ i ∈ range M, ∑ j ∈ range (M + 1), if i + j = a then 1 else 0 : ℕ) =
      min (min (a + 1) M) (2 * M - a) := by
  have inner : ∀ i ∈ range M, (∑ j ∈ range (M + 1), if i + j = a then 1 else 0 : ℕ) =
      if (i ≤ a ∧ a < i + (M + 1)) then 1 else 0 := by
    intro i _
    by_cases h : i ≤ a
    · have hj : ∀ j : ℕ, (i + j = a ↔ j = a - i) := fun j => by omega
      simp only [hj, Finset.sum_ite_eq', Finset.mem_range]
      split_ifs <;> omega
    · have hz : ∀ j ∈ range (M + 1), (if i + j = a then (1 : ℕ) else 0) = 0 :=
        fun j _ => if_neg (by omega)
      rw [Finset.sum_eq_zero hz, if_neg (by omega : ¬ (i ≤ a ∧ a < i + (M + 1)))]
  rw [Finset.sum_congr rfl inner, ← Finset.card_filter]
  have hf : (range M).filter (fun i => i ≤ a ∧ a < i + (M + 1)) =
      Finset.Ico (a - M) (min M (a + 1)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hf, Nat.card_Ico, min_def, min_def, min_def]
  split_ifs <;> omega

lemma LK01_sum_pairs {R : Type*} [CommSemiring R] (M : ℕ) (G : ℕ → R) :
    ∑ i ∈ range M, ∑ j ∈ range (M + 1), G (i + j) =
      ∑ a ∈ range (2 * M), ((min (min (a + 1) M) (2 * M - a) : ℕ) : R) * G a := by
  have hc : ∀ a ∈ range (2 * M), ((min (min (a + 1) M) (2 * M - a) : ℕ) : R) =
      ∑ i ∈ range M, ∑ j ∈ range (M + 1), if i + j = a then (1 : R) else 0 := by
    intro a ha
    have h := congrArg (fun k : ℕ => (k : R)) (LK01_count_pairs M a (Finset.mem_range.mp ha))
    push_cast at h
    exact h.symm
  have hL : ∀ i ∈ range M, ∀ j ∈ range (M + 1), G (i + j) =
      ∑ a ∈ range (2 * M), if i + j = a then G a else 0 := by
    intro i hi j hj
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (show i + j < 2 * M by omega))]
  calc ∑ i ∈ range M, ∑ j ∈ range (M + 1), G (i + j)
      = ∑ i ∈ range M, ∑ a ∈ range (2 * M), ∑ j ∈ range (M + 1), if i + j = a then G a else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun j hj => hL i hi j hj)
    _ = ∑ a ∈ range (2 * M), ∑ i ∈ range M, ∑ j ∈ range (M + 1), if i + j = a then G a else 0 :=
        Finset.sum_comm
    _ = ∑ a ∈ range (2 * M), ((min (min (a + 1) M) (2 * M - a) : ℕ) : R) * G a := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hc a ha, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        simp only [ite_mul, one_mul, zero_mul]

lemma LK01_prodW_cast (M a : ℕ) (ha : a < 2 * M) :
    ((prodW M a : ℚ) : ℂ) = ((min (min (a + 1) M) (2 * M - a) : ℕ) : ℂ) * (((M : ℂ) * (M + 1))⁻¹) := by
  unfold prodW
  rw [if_pos ha]
  simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_add, Rat.cast_one]
  rw [div_eq_mul_inv]

/-- The product weight's exponential sum is `D_M D_{M+1}/(M(M+1))`. -/
lemma LK01_prod_eq (M : ℕ) (y : ℝ) :
    ∑ a ∈ range (2 * M), ((prodW M a : ℚ) : ℂ) * ee (a * y) =
      lkD M y * lkD (M + 1) y * (((M : ℂ) * (M + 1))⁻¹) := by
  have h1 : ∑ a ∈ range (2 * M), ((prodW M a : ℚ) : ℂ) * ee (a * y) =
      (∑ a ∈ range (2 * M), ((min (min (a + 1) M) (2 * M - a) : ℕ) : ℂ) * ee ((a : ℝ) * y)) *
        (((M : ℂ) * (M + 1))⁻¹) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    rw [LK01_prodW_cast M a (Finset.mem_range.mp ha)]
    ring
  rw [h1, ← LK01_sum_pairs (R := ℂ) M (fun a : ℕ => ee ((a : ℝ) * y))]
  congr 1
  unfold lkD
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← L01_e_add]
  congr 1
  push_cast
  ring

/-- The Fejér weight's exponential sum is `D_m²/m²`. -/
lemma LK01_fejer_eq (m : ℕ) (y : ℝ) :
    ∑ a ∈ range (2 * m - 1), ((fejerW m a : ℚ) : ℂ) * ee (a * y) =
      lkD m y * lkD m y * (((m : ℂ) ^ 2)⁻¹) := by
  have h1 : ∑ a ∈ range (2 * m - 1), ((fejerW m a : ℚ) : ℂ) * ee (a * y) =
      (∑ a ∈ range (2 * m - 1), ((min (a + 1) (2 * m - 1 - a) : ℕ) : ℂ) * ee ((a : ℝ) * y)) *
        (((m : ℂ) ^ 2)⁻¹) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    rw [L01_fejerW_cast m a (Finset.mem_range.mp ha)]
    ring
  rw [h1, ← L01_sum_pairs (R := ℂ) m (fun a : ℕ => ee ((a : ℝ) * y))]
  congr 1
  unfold lkD
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← L01_e_add]
  congr 1
  push_cast
  ring

/-- `F_m = |D_m|²/m²`. -/
lemma LK01_fejerK_eq (m : ℕ) (hm : 1 ≤ m) (y : ℝ) :
    fejerK m y = (‖lkD m y‖ / m) ^ 2 := by
  have h := itemL01 m hm y
  rw [LK01_fejer_eq] at h
  rw [← h, norm_mul, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  field_simp

lemma LK01_fejerK_nonneg (m : ℕ) (hm : 1 ≤ m) (y : ℝ) : 0 ≤ fejerK m y := by
  rw [LK01_fejerK_eq m hm y]; positivity

theorem itemLK01 : ItemLK01 := by
  unfold ItemLK01 ProdAbsStmt
  intro M hM y
  rw [LK01_prod_eq, LK01_fejerK_eq M hM y, LK01_fejerK_eq (M + 1) (by omega) y]
  rw [norm_mul, norm_mul, norm_inv, norm_mul]
  have e1 : ‖((M : ℂ) + 1)‖ = ((M + 1 : ℕ) : ℝ) := by
    rw [show ((M : ℂ) + 1) = ((M + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
  rw [e1, Complex.norm_natCast]
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
  set x := ‖lkD M y‖ / M
  set z := ‖lkD (M + 1) y‖ / ((M + 1 : ℕ) : ℝ)
  have hxz : ‖lkD M y‖ * ‖lkD (M + 1) y‖ * ((M : ℝ) * ((M + 1 : ℕ) : ℝ))⁻¹ = x * z := by
    simp only [x, z]
    field_simp
  rw [hxz]
  nlinarith [sq_nonneg (x - z)]

end KappaOmega2
