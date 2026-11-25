import KappaOmega2.Statements
import KappaOmega2.Items.M12_Sem
import KappaOmega2.Items.M12_Crude
import KappaOmega2.Items.M12_Base
import KappaOmega2.Items.M12_KF
import KappaOmega2.Items.M12_KC

/-!
# Item M12: an `h`-table with `MvalLower ≥ 0.009` (R = 2 weight, cells from `m = 2/103` to `1/4`)

`h`-bounds (independent of `θ`, `U`, `W`): the fine cells `ξ_j = (101/100)^j/85` (`j < 308`) and `1/4`; bound
`H_j = (h₂-row_j + rest_{⌊j/2⌋})/2^64 + τ/ξ_j` where the first two are the kernel-checked fine level-2 and coarse
level-4…16 tables (`M12_KF`, `M12_KC`) and `τ = Σ_{18 ≤ i ≤ 82, i even} 4^i/i!` the crude tail.
The table of the item is the restriction to `[2/103, 1/4]`: `ξ'_0 = 2/103 ∈ [ξ_50, ξ_51)`, `ξ'_i = ξ_{50+i}`
(`1 ≤ i < 258`), `ξ'_258 = 1/4`, `H'_i = H_{50+i}` (generator and check: `scripts/sieve_port/m12_restrict.py`:
base `0.03747 ≥ 0.030`, cell sum `0.016638 ≤ 0.017`, `MvalLower ≥ 0.0208`).
-/

set_option linter.style.longLine false

open MeasureTheory Finset Real
open scoped ENNReal

namespace KappaOmega2

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


lemma xiQ_cast (j : ℕ) : ((xiQ j : ℚ) : ℝ) = xiR gF j := by
  unfold xiQ xiR gF; push_cast; ring

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

/-- `∫_{a}^{b} W/t` upper bound (`W ≤ t − m`, `W ≤ k²t²`). -/
def IQ (a b : ℚ) : ℚ := min ((b - a) * (1 - (2 / 103) / b)) (582 / 103 * (b ^ 2 - a ^ 2) / 2)

/-- Cell edges of the restricted table. -/
def xi2 (i : ℕ) : ℚ := if i = 0 then 2 / 103 else xiQ (50 + i)

def xiL : List ℚ := (List.range 258).map xi2 ++ [1 / 4]
def HbL : List ℚ := (List.range 258).map (fun i => HbQ (50 + i))

lemma xiQ_50 : xiQ 50 ≤ 2 / 103 := by decide +kernel
lemma xiQ_51 : 2 / 103 < xiQ 51 := by decide +kernel

lemma xi2_ge (i : ℕ) : xiQ (50 + i) ≤ xi2 i := by
  unfold xi2
  split_ifs with h
  · subst h; exact xiQ_50
  · exact le_rfl

lemma xi2_lo (i : ℕ) : 2 / 103 ≤ xi2 i := by
  unfold xi2
  split_ifs with h
  · exact le_rfl
  · exact (xiQ_51.trans_le (xiQ_strictMono.monotone (by omega))).le

lemma xi2_strictMono : StrictMono xi2 := by
  intro i j hij
  have hj : j ≠ 0 := by omega
  have e : xi2 j = xiQ (50 + j) := by unfold xi2; rw [if_neg hj]
  rw [e]
  unfold xi2
  split_ifs with h
  · exact xiQ_51.trans_le (xiQ_strictMono.monotone (by omega))
  · exact xiQ_strictMono (by omega)

lemma xi2_top {i : ℕ} (hi : i < 258) : xi2 i < 1 / 4 := by
  unfold xi2
  split_ifs with h
  · norm_num
  · exact lt_of_le_of_lt (xiQ_strictMono.monotone (by omega : 50 + i ≤ 307)) xiQ_last

lemma xiL_getD {i : ℕ} (hi : i < 258) : xiL.getD i 0 = xi2 i := by
  unfold xiL
  rw [List.getD_eq_getElem (hn := by simp; omega), List.getElem_append_left (by simp; omega)]
  simp

lemma xiL_getD_last : xiL.getD 258 0 = 1 / 4 := by
  unfold xiL
  rw [List.getD_eq_getElem (hn := by simp), List.getElem_append_right (by simp)]
  simp

lemma HbL_getD {i : ℕ} (hi : i < 258) : HbL.getD i 0 = HbQ (50 + i) := by
  unfold HbL; rw [getD_map_range, if_pos hi]

/-- The right edge of cell `i` lies in `[ξ'_i, ξ_{50+i+1}]`. -/
lemma next_bounds {i : ℕ} (hi : i < 258) :
    xi2 i ≤ xiL.getD (i + 1) 0 ∧ xiL.getD (i + 1) 0 ≤ xiQ (50 + i + 1) ∧ xiL.getD (i + 1) 0 ≤ 1 / 4 := by
  rcases Nat.lt_or_ge (i + 1) 258 with h | h
  · rw [xiL_getD h]
    refine ⟨(xi2_strictMono (Nat.lt_succ_self i)).le, ?_, (xi2_top h).le⟩
    unfold xi2; rw [if_neg (by omega), show 50 + (i + 1) = 50 + i + 1 by ring]
  · rw [show i + 1 = 258 by omega, xiL_getD_last]
    refine ⟨(xi2_top hi).le, ?_, le_rfl⟩
    rw [show 50 + i + 1 = 308 by omega]; exact xiQ_top

set_option maxRecDepth 100000 in
theorem sum_le : ∑ i ∈ range 258, HbQ (50 + i) * IQ (xiL.getD i 0) (xiL.getD (i + 1) 0) ≤ 17 / 1000 := by
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
      exact (List.pairwise_lt_range).imp fun h => M12.xi2_strictMono h
    · intro a ha b hb
      simp only [List.mem_map, List.mem_range] at ha
      simp only [List.mem_singleton] at hb
      obtain ⟨i, hi, rfl⟩ := ha
      subst hb
      exact M12.xi2_top hi
  · intro i hi t ht1 ht2
    have hi' : i < 258 := by simpa [M12.HbL] using hi
    rw [M12.HbL_getD hi']
    rw [M12.xiL_getD hi'] at ht1
    obtain ⟨-, hn2, -⟩ := M12.next_bounds hi'
    have h1 : M12.xiR M12.gF (50 + i) ≤ t := by
      rw [← M12.xiQ_cast]
      exact le_trans (by exact_mod_cast M12.xi2_ge i) ht1
    have h2 : t ≤ M12.xiR M12.gF (50 + i + 1) := by
      rw [← M12.xiQ_cast]
      exact le_trans ht2 (by exact_mod_cast hn2)
    exact M12.hS_le (by omega) h1 h2
  · unfold MvalLower
    have hlen : M12.HbL.length = 258 := by simp [M12.HbL]
    rw [hlen]
    have hb := M12.base_ge
    have hcell : ∀ i ∈ range 258, ((M12.HbL.getD i 0 : ℚ) : ℝ) * ∫ t in ((M12.xiL.getD i 0 : ℚ) : ℝ)..((M12.xiL.getD (i + 1) 0 : ℚ) : ℝ), Wf t / t ≤
        ((M12.HbQ (50 + i) * M12.IQ (M12.xiL.getD i 0) (M12.xiL.getD (i + 1) 0) : ℚ) : ℝ) := by
      intro i hi
      have hi' : i < 258 := Finset.mem_range.mp hi
      rw [M12.HbL_getD hi']
      have hH : (0 : ℝ) ≤ (M12.HbQ (50 + i) : ℝ) := by exact_mod_cast M12.HbQ_nonneg _
      obtain ⟨hn1, -, hn3⟩ := M12.next_bounds hi'
      have ha : (2 / 103 : ℝ) ≤ ((M12.xiL.getD i 0 : ℚ) : ℝ) := by
        rw [M12.xiL_getD hi']
        have := (Rat.cast_le (K := ℝ)).mpr (M12.xi2_lo i)
        push_cast at this; exact this
      have hab : ((M12.xiL.getD i 0 : ℚ) : ℝ) ≤ ((M12.xiL.getD (i + 1) 0 : ℚ) : ℝ) := by
        rw [M12.xiL_getD hi']; exact_mod_cast hn1
      have hb3 : ((M12.xiL.getD (i + 1) 0 : ℚ) : ℝ) ≤ 1 / 3 := by
        have := (Rat.cast_le (K := ℝ)).mpr (hn3.trans (by norm_num : (1 / 4 : ℚ) ≤ 1 / 3))
        push_cast at this; exact this
      have hW := M12.intW_le ha hab hb3
      calc ((M12.HbQ (50 + i) : ℚ) : ℝ) * ∫ t in ((M12.xiL.getD i 0 : ℚ) : ℝ)..((M12.xiL.getD (i + 1) 0 : ℚ) : ℝ), Wf t / t
          ≤ ((M12.HbQ (50 + i) : ℚ) : ℝ) * ((M12.IQ (M12.xiL.getD i 0) (M12.xiL.getD (i + 1) 0) : ℚ) : ℝ) := by
            apply mul_le_mul_of_nonneg_left _ hH
            refine hW.trans (le_of_eq ?_)
            unfold M12.IQ; push_cast; rfl
        _ = _ := by push_cast; rfl
    have hsum := Finset.sum_le_sum hcell
    have hq : ((∑ i ∈ range 258, M12.HbQ (50 + i) * M12.IQ (M12.xiL.getD i 0) (M12.xiL.getD (i + 1) 0) : ℚ) : ℝ) ≤ ((17 / 1000 : ℚ) : ℝ) :=
      Rat.cast_le.mpr M12.sum_le
    push_cast at hq hsum
    linarith

end KappaOmega2
