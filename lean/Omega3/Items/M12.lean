import Omega3.Statements
import Omega3.Items.M12_Sem
import Omega3.Items.M12_Crude
import Omega3.Items.M12_Base
import Omega3.Items.M12_KF
import Omega3.Items.M12_KC

/-!
# Item M12: an `h`-table with `MvalLower ≥ 0.009`

Table: the fine cells `ξ_j = (101/100)^j/85` (`j < 308`) and `1/4`; bound
`H_j = (h₂-row_j + rest_{⌊j/2⌋})/2^64 + τ/ξ_j` where the first two are the kernel-checked fine level-2 and coarse
level-4…16 tables (`M12_KF`, `M12_KC`) and `τ = Σ_{18 ≤ i ≤ 82, i even} 4^i/i!` the crude tail.
-/

set_option linter.style.longLine false

open MeasureTheory Finset Real
open scoped ENNReal

namespace Omega3

open M12

namespace M12

/-! ## Grid validity -/

theorem gF_ok : GridOK gF where
  hB := by decide
  hBA := by decide
  hM := by decide
  hN := by decide +kernel
  hSY := by decide +kernel
  hSH := by decide +kernel
  hS3 := by decide +kernel
  hS3H := by decide
  side := by decide +kernel

theorem gC_ok : GridOK gC where
  hB := by decide
  hBA := by decide
  hM := by decide
  hN := by decide +kernel
  hSY := by decide +kernel
  hSH := by decide +kernel
  hS3 := by decide +kernel
  hS3H := by decide
  side := by decide +kernel

/-! ## Semantics of the computed tables -/

theorem sem_tab1 {g : Grid} (hg : GridOK g) : Sem g 1 (tabF (tab1 g)) := by
  apply sem_base hg
  intro k hk j hj
  obtain ⟨-, h1, h2⟩ := CUT_spec hg hk
  rw [tab1_spec g hk h1 h2 j]
  apply le_of_eq
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [if_pos hj]

theorem sem_iter {g : Grid} (hg : GridOK g) : ∀ n : ℕ, Sem g (n + 1) (tabF ((step g)^[n] (tab1 g))) ∧
    ((step g)^[n] (tab1 g)).length = g.SY + 1
  | 0 => ⟨sem_tab1 hg, length_tab1 g⟩
  | n + 1 => by
    obtain ⟨h1, h2⟩ := sem_iter hg n
    refine ⟨?_, ?_⟩
    · rw [Function.iterate_succ_apply']
      refine sem_step hg (by omega) h1 fun k hk j _ => le_of_eq ?_
      rw [step_spec g _ (by omega) hk j]
    · rw [Function.iterate_succ_apply', length_step]

/-! ## Grids and cells -/

lemma xiR_gC (J : ℕ) : xiR gC J = xiR gF (2 * J) := by
  unfold xiR gC gF
  simp only
  rw [pow_mul, pow_mul]
  norm_num

lemma toReal_le {a : ℝ≥0∞} {b : ℝ} (hb : 0 ≤ b) (h : a ≤ ENNReal.ofReal b) : a.toReal ≤ b :=
  ENNReal.toReal_le_of_le_ofReal hb h

/-- `log (85/2) < 4`. -/
lemma log_lt_four : Real.log (85 / 2) < 4 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h := Real.exp_one_gt_d9
  have : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283) h.le 4]

/-- The crude tail constant. -/
def tauQ : ℚ := ∑ k ∈ range 33, (4 : ℚ) ^ (2 * (9 + k)) / ((2 * (9 + k)).factorial)

lemma crude_le {i : ℕ} {t : ℝ} (ht : 1 / 85 ≤ t) {a : ℝ} (ha : 0 < a) (hat : a ≤ t) :
    crude i t 1 ≤ (1 / a) * 4 ^ i / (i.factorial) := by
  unfold crude
  have ht0 : 0 < t := by linarith
  have hmin : min (1 : ℝ) (1 / 2) = 1 / 2 := by norm_num
  rw [hmin]
  have h1 : max 0 (Real.log (1 / 2 / t)) ≤ 4 := by
    apply max_le (by norm_num)
    have : 1 / 2 / t ≤ 85 / 2 := by rw [div_le_iff₀ ht0]; nlinarith
    exact (Real.log_le_log (by positivity) this).trans log_lt_four.le
  have h0 : 0 ≤ max 0 (Real.log (1 / 2 / t)) := le_max_left _ _
  have hp := pow_le_pow_left₀ h0 h1 i
  have hf : (0 : ℝ) < (i.factorial : ℝ) := by positivity
  have : 1 / t ≤ 1 / a := one_div_le_one_div_of_le ha hat
  gcongr

/-! ## The table -/

def xiQ (j : ℕ) : ℚ := (101 : ℚ) ^ j / (85 * (100 : ℚ) ^ j)

def HbQ (j : ℕ) : ℚ := ((h2Lit.getD j 0 + restLit.getD (j / 2) 0 : ℕ) : ℚ) / TT + 85 * (100 : ℚ) ^ j / (101 : ℚ) ^ j * tauQ

def xiL : List ℚ := (List.range 308).map xiQ ++ [1 / 4]
def HbL : List ℚ := (List.range 308).map HbQ

lemma xiQ_cast (j : ℕ) : ((xiQ j : ℚ) : ℝ) = xiR gF j := by
  unfold xiQ xiR gF; push_cast; ring

lemma xiL_getD {j : ℕ} (hj : j < 308) : xiL.getD j 0 = xiQ j := by
  unfold xiL
  rw [List.getD_eq_getElem (hn := by simp; omega), List.getElem_append_left (by simp; omega)]
  simp

lemma xiL_getD_last : xiL.getD 308 0 = 1 / 4 := by
  unfold xiL
  rw [List.getD_eq_getElem (hn := by simp), List.getElem_append_right (by simp)]
  simp

lemma HbL_getD {j : ℕ} (hj : j < 308) : HbL.getD j 0 = HbQ j := by
  unfold HbL; rw [getD_map_range, if_pos hj]

lemma xiQ_strictMono : StrictMono xiQ := by
  refine strictMono_nat_of_lt_succ fun j => ?_
  unfold xiQ
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have : (0 : ℚ) < 101 ^ j * 100 ^ j := by positivity
  rw [pow_succ, pow_succ]
  nlinarith

lemma xiQ_last : xiQ 307 < 1 / 4 := by decide +kernel
lemma xiQ_top : 1 / 4 ≤ xiQ 308 := by decide +kernel

/-- The `h`-bound on a table cell. -/
theorem hS_le {j : ℕ} (hj : j < 308) {t : ℝ} (ht1 : xiR gF j ≤ t) (ht2 : t ≤ xiR gF (j + 1)) :
    hS t ≤ (HbQ j : ℝ) := by
  have hx0 : xiR gF 0 = 1 / 85 := by simp [xiR]
  have ht85 : 1 / 85 ≤ t := by rw [← hx0]; exact le_trans (xiR_mono gF_ok (Nat.zero_le j)) ht1
  have ht0 : 0 < t := by linarith
  have hξ := xiR_pos gF_ok j
  set f : ℕ → ℝ := fun k => (G (2 * k) t 1).toReal with hf
  -- step 1: hS ≤ Σ_{k ≤ 41} f k
  have hzero : ∀ k, 42 ≤ k → f k = 0 := by
    intro k hk
    have hk' : (42 : ℝ) ≤ k := by exact_mod_cast hk
    have h86 : (86 : ℝ) ≤ ((2 * k : ℕ) : ℝ) + 2 := by push_cast; linarith
    have : 1 ≤ (((2 * k : ℕ) : ℝ) + 2) * t := by nlinarith
    simp only [hf]
    rw [G_eq_zero (by omega) (Or.inr this)]
    simp
  have h1 : hS t ≤ ∑ k ∈ Icc 1 41, f k := by
    unfold hS
    calc ∑ k ∈ Icc 1 (⌊1 / t⌋₊ + 1), h86 (2 * k) t ≤ ∑ k ∈ Icc 1 (⌊1 / t⌋₊ + 1), f k :=
          Finset.sum_le_sum fun k hk => h86_le_G (by simp at hk; omega) ht0.le
      _ = ∑ k ∈ (Icc 1 (⌊1 / t⌋₊ + 1)).filter (· ≤ 41), f k := by
          rw [Finset.sum_filter_of_ne]
          intro k _ hk
          by_contra h; push_neg at h; exact hk (hzero k h)
      _ ≤ ∑ k ∈ Icc 1 41, f k := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro k hk; simp only [Finset.mem_filter, Finset.mem_Icc] at hk ⊢; omega
          · intro k _ _; exact ENNReal.toReal_nonneg
  -- step 2: split the levels
  have hsplit : ∑ k ∈ Icc 1 41, f k = f 1 + ∑ k ∈ range 7, f (2 + k) + ∑ k ∈ range 33, f (9 + k) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
      show 41 + 1 - 1 = 1 + (7 + 33) by rfl, Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_one]
    ring_nf
  -- level 2 (fine table)
  have hL2 : f 1 ≤ (h2Lit.getD j 0 : ℝ) / TT := by
    have := ((sem_iter gF_ok 1).1 gF.SY le_rfl j t ht1 ht2 1 (fun h => absurd h (lt_irrefl _)))
    have e : tabF ((step gF)^[1] (tab1 gF)) gF.SY j = h2F.getD j 0 := rfl
    rw [e, h2F_eq] at this
    simp only [hf]
    exact toReal_le (div_nonneg (by positivity) TT_posR.le) this
  -- levels 4..16 (coarse table)
  have hC : ∀ k ∈ range 7, f (2 + k) ≤ (tabF ((step gC)^[2 * k + 3] (tab1 gC)) gC.SY (j / 2) : ℝ) / TT := by
    intro k _
    have hc1 : xiR gC (j / 2) ≤ t := by
      rw [xiR_gC]; exact le_trans (xiR_mono gF_ok (by omega)) ht1
    have hc2 : t ≤ xiR gC (j / 2 + 1) := by
      rw [xiR_gC]; exact le_trans ht2 (xiR_mono gF_ok (by omega))
    have := (sem_iter gC_ok (2 * k + 3)).1 gC.SY le_rfl (j / 2) t hc1 hc2 1 (fun h => absurd h (lt_irrefl _))
    simp only [hf]
    refine toReal_le (div_nonneg (by positivity) TT_posR.le) ?_
    rw [show 2 * (2 + k) = 2 * k + 3 + 1 by ring]
    exact this
  have hrest : ∑ k ∈ range 7, f (2 + k) ≤ (restLit.getD (j / 2) 0 : ℝ) / TT := by
    refine (Finset.sum_le_sum hC).trans (le_of_eq ?_)
    rw [← Finset.sum_div, ← restC_eq]
    unfold restC
    rw [run_spec]
    simp only [List.getD_nil, zero_add]
    push_cast
    congr 1
  -- levels 18..82 (crude)
  have htail : ∑ k ∈ range 33, f (9 + k) ≤ (1 / xiR gF j) * (tauQ : ℝ) := by
    unfold tauQ
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    simp only [hf]
    refine toReal_le (by positivity) ((G_crude _ (by omega) ht0 1).trans (ENNReal.ofReal_le_ofReal ?_))
    have := crude_le (i := 2 * (9 + k)) ht85 hξ ht1
    calc crude (2 * (9 + k)) t 1 ≤ (1 / xiR gF j) * 4 ^ (2 * (9 + k)) / ((2 * (9 + k)).factorial) := this
      _ = _ := by ring
  -- assemble
  rw [hsplit] at h1
  have hinv : 1 / xiR gF j = 85 * (100 : ℝ) ^ j / (101 : ℝ) ^ j := by
    unfold xiR gF; simp only; push_cast; field_simp
  calc hS t ≤ f 1 + ∑ k ∈ range 7, f (2 + k) + ∑ k ∈ range 33, f (9 + k) := h1
    _ ≤ (h2Lit.getD j 0 : ℝ) / TT + (restLit.getD (j / 2) 0 : ℝ) / TT + (1 / xiR gF j) * (tauQ : ℝ) := by linarith
    _ = (HbQ j : ℝ) := by
      unfold HbQ; rw [hinv]; push_cast; ring

/-! ## The certificate -/

/-- `∫_{ξ_j}^{ξ_{j+1}} W/t` upper bound. -/
def IQ (a b : ℚ) : ℚ := min ((b - a) * (1 - (1 / 85) / b)) (9999 / 1000 * (b ^ 2 - a ^ 2) / 2)

set_option maxRecDepth 100000 in
theorem sum_le : ∑ j ∈ range 308, HbQ j * IQ (xiL.getD j 0) (xiL.getD (j + 1) 0) ≤ 23 / 1000 := by
  decide +kernel

theorem HbQ_nonneg (j : ℕ) : 0 ≤ HbQ j := by
  unfold HbQ tauQ; positivity

end M12

theorem itemM12 : ItemM12 := by
  refine ⟨M12.xiL, M12.HbL, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp [M12.xiL, M12.HbL]
  · decide +kernel
  · decide +kernel
  · rw [M12.xiL, List.pairwise_append]
    refine ⟨?_, List.pairwise_singleton _ _, ?_⟩
    · rw [List.pairwise_map]
      exact (List.pairwise_lt_range).imp fun h => M12.xiQ_strictMono h
    · intro a ha b hb
      simp only [List.mem_map, List.mem_range] at ha
      simp only [List.mem_singleton] at hb
      obtain ⟨j, hj, rfl⟩ := ha
      subst hb
      exact lt_of_le_of_lt (M12.xiQ_strictMono.monotone (by omega : j ≤ 307)) M12.xiQ_last
  · intro j hj t ht1 ht2
    have hj' : j < 308 := by simpa [M12.HbL] using hj
    rw [M12.HbL_getD hj']
    rw [M12.xiL_getD hj', M12.xiQ_cast] at ht1
    have ht2' : t ≤ M12.xiR M12.gF (j + 1) := by
      rcases Nat.lt_or_ge (j + 1) 308 with h | h
      · rwa [M12.xiL_getD h, M12.xiQ_cast] at ht2
      · have : j + 1 = 308 := by omega
        rw [this, M12.xiL_getD_last] at ht2
        rw [this, ← M12.xiQ_cast]
        exact le_trans ht2 (by exact_mod_cast M12.xiQ_top)
    exact M12.hS_le hj' ht1 ht2'
  · unfold MvalLower
    have hlen : M12.HbL.length = 308 := by simp [M12.HbL]
    rw [hlen]
    have hb := M12.base_ge
    have hcell : ∀ j ∈ range 308, ((M12.HbL.getD j 0 : ℚ) : ℝ) * ∫ t in ((M12.xiL.getD j 0 : ℚ) : ℝ)..((M12.xiL.getD (j + 1) 0 : ℚ) : ℝ), Wf t / t ≤
        ((M12.HbQ j * M12.IQ (M12.xiL.getD j 0) (M12.xiL.getD (j + 1) 0) : ℚ) : ℝ) := by
      intro j hj
      have hj' : j < 308 := Finset.mem_range.mp hj
      rw [M12.HbL_getD hj']
      have hH : (0 : ℝ) ≤ (M12.HbQ j : ℝ) := by exact_mod_cast M12.HbQ_nonneg j
      have ha : (1 / 85 : ℝ) ≤ ((M12.xiL.getD j 0 : ℚ) : ℝ) := by
        rw [M12.xiL_getD hj', M12.xiQ_cast]
        have : M12.xiR M12.gF 0 = 1 / 85 := by simp [M12.xiR]
        rw [← this]; exact M12.xiR_mono M12.gF_ok (Nat.zero_le j)
      have hab : ((M12.xiL.getD j 0 : ℚ) : ℝ) ≤ ((M12.xiL.getD (j + 1) 0 : ℚ) : ℝ) := by
        rw [M12.xiL_getD hj']
        rcases Nat.lt_or_ge (j + 1) 308 with h | h
        · rw [M12.xiL_getD h]
          exact_mod_cast (M12.xiQ_strictMono (Nat.lt_succ_self j)).le
        · rw [show j + 1 = 308 by omega, M12.xiL_getD_last]
          have : M12.xiQ j ≤ 1 / 4 := le_trans (M12.xiQ_strictMono.monotone (by omega : j ≤ 307)) M12.xiQ_last.le
          exact (Rat.cast_le (K := ℝ)).mpr this
      have hb3 : ((M12.xiL.getD (j + 1) 0 : ℚ) : ℝ) ≤ 1 / 3 := by
        rcases Nat.lt_or_ge (j + 1) 308 with h | h
        · rw [M12.xiL_getD h]
          have : M12.xiQ (j + 1) ≤ 1 / 3 := le_trans (M12.xiQ_strictMono.monotone (by omega : j + 1 ≤ 307)) (le_trans M12.xiQ_last.le (by norm_num))
          have := (Rat.cast_le (K := ℝ)).mpr this
          push_cast at this
          exact this
        · rw [show j + 1 = 308 by omega, M12.xiL_getD_last]; norm_num
      have hW := M12.intW_le ha hab hb3
      calc ((M12.HbQ j : ℚ) : ℝ) * ∫ t in ((M12.xiL.getD j 0 : ℚ) : ℝ)..((M12.xiL.getD (j + 1) 0 : ℚ) : ℝ), Wf t / t
          ≤ ((M12.HbQ j : ℚ) : ℝ) * ((M12.IQ (M12.xiL.getD j 0) (M12.xiL.getD (j + 1) 0) : ℚ) : ℝ) := by
            apply mul_le_mul_of_nonneg_left _ hH
            refine hW.trans (le_of_eq ?_)
            unfold M12.IQ; push_cast; rfl
        _ = _ := by push_cast; rfl
    have hsum := Finset.sum_le_sum hcell
    have hq : ((∑ j ∈ range 308, M12.HbQ j * M12.IQ (M12.xiL.getD j 0) (M12.xiL.getD (j + 1) 0) : ℚ) : ℝ) ≤ ((23 / 1000 : ℚ) : ℝ) :=
      Rat.cast_le.mpr M12.sum_le
    push_cast at hq hsum
    linarith

end Omega3
