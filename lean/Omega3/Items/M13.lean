import Omega3.Statements
import Omega3.Items.M13_H

/-! # Item M13: an `h`-table gives a lower bound for `𝓜(W)`. Proof plan in `Omega3/Items/M13_PLAN.md`. -/

namespace Omega3

open Finset MeasureTheory

set_option linter.style.longLine false

lemma m13_list_facts (ξ : List ℚ) (n : ℕ) (hlen : ξ.length = n + 1) (hhead : ξ.head? = some (1 / 85))
    (hlast : ξ.getLastD 0 = 1 / 4) (hpw : ξ.Pairwise (· < ·)) :
    ((ξ.getD 0 0 : ℚ) : ℝ) = 1 / 85 ∧ ((ξ.getD n 0 : ℚ) : ℝ) = 1 / 4 ∧
      (∀ j < n, ((ξ.getD j 0 : ℚ) : ℝ) < ((ξ.getD (j + 1) 0 : ℚ) : ℝ)) ∧
      (∀ j ≤ n, (1 / 85 : ℝ) ≤ ((ξ.getD j 0 : ℚ) : ℝ) ∧ ((ξ.getD j 0 : ℚ) : ℝ) ≤ 1 / 4) := by
  have hget : ∀ j (hj : j < ξ.length), ξ.getD j 0 = ξ[j] := fun j hj => List.getD_eq_getElem ξ 0 hj
  have h0 : ξ.getD 0 0 = 1 / 85 := by
    rw [hget 0 (by omega)]
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hhead
    exact Option.some_inj.1 hhead
  have hn : ξ.getD n 0 = 1 / 4 := by
    rw [hget n (by omega)]
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, hlen, show n + 1 - 1 = n by omega,
      List.getElem?_eq_getElem (by omega)] at hlast
    simpa using hlast
  have hlt : ∀ i j, i < j → j ≤ n → ξ.getD i 0 < ξ.getD j 0 := by
    intro i j hij hj
    rw [hget i (by omega), hget j (by omega)]
    exact List.pairwise_iff_getElem.1 hpw i j (by omega) (by omega) hij
  refine ⟨by rw [h0]; norm_num, by rw [hn]; norm_num, fun j hj => by exact_mod_cast hlt j (j + 1) (by omega) (by omega), ?_⟩
  intro j hj
  constructor
  · rcases Nat.eq_zero_or_pos j with rfl | hpos
    · rw [h0]; norm_num
    · have := hlt 0 j hpos hj; rw [h0] at this
      have : ((1 / 85 : ℚ) : ℝ) ≤ ((ξ.getD j 0 : ℚ) : ℝ) := by exact_mod_cast this.le
      simpa using this
  · rcases lt_or_eq_of_le hj with hlt' | rfl
    · have := hlt j n hlt' le_rfl; rw [hn] at this
      have : ((ξ.getD j 0 : ℚ) : ℝ) ≤ ((1 / 4 : ℚ) : ℝ) := by exact_mod_cast this.le
      simpa using this
    · rw [hn]; norm_num

theorem itemM13 : ItemM13 := by
  intro ξ Hb hT
  obtain ⟨hlen, hhead, hlast, hpw, hcell⟩ := hT
  set n := Hb.length with hn
  set a : ℕ → ℝ := fun k => ((ξ.getD k 0 : ℚ) : ℝ) with ha
  obtain ⟨ha0', han', hamono, harange⟩ := m13_list_facts ξ n hlen hhead hlast hpw
  have ha0 : a 0 = 1 / 85 := ha0'
  have han : a n = 1 / 4 := han'
  set hSum : ℝ → ℝ := fun t => ∑ k ∈ Icc 1 100, h86 (2 * k) t with hSumdef
  have hSum_meas : Measurable hSum := m13_hSum_meas
  set g : ℝ → ℝ := fun t => Wf t * hSum t / t with hg
  have hg_meas : Measurable g := ((m13_W_meas.mul hSum_meas).div measurable_id)
  have hgS : ∀ t, 1 / 85 ≤ t → g t = Wf t * hS t / t := by
    intro t ht; simp only [hg, hSumdef]; rw [m13_hS_eq t ht]
  -- `g` vanishes on `[0, 1/85]` and on `[1/4, 1/2]`
  have hg0 : ∀ t, t ≤ 1 / 85 → g t = 0 := by
    intro t ht; simp only [hg]; rw [m13_W_zero t ht]; ring
  have hg1 : ∀ t, 1 / 4 ≤ t → g t = 0 := by
    intro t ht; rw [hgS t (by linarith), m13_hS_zero t ht]; ring
  -- integrability on cells
  have hHj : ∀ j < n, 0 ≤ (Hb.getD j 0 : ℝ) := by
    intro j hj
    have := hcell j hj (a j) le_rfl (hamono j hj).le
    have h2 := m13_hS_nonneg (a j) (by linarith [(harange j hj.le).1])
    linarith
  have hWt : ∀ j < n, IntervalIntegrable (fun t => Wf t / t) volume (a j) (a (j + 1)) := by
    intro j hj
    apply IntervalIntegrable.mono_fun' (g := fun _ => (85 : ℝ)) intervalIntegrable_const
    · exact (m13_W_meas.div measurable_id).aestronglyMeasurable
    · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
      apply Filter.Eventually.of_forall
      intro t ht
      rw [Set.uIoc_of_le (hamono j hj).le] at ht
      have h1 := (harange j hj.le).1
      have h2 := (harange (j + 1) (by omega)).2
      have ht0 : 0 < t := by linarith [ht.1]
      simp only [Real.norm_eq_abs]
      rw [abs_div, abs_of_pos ht0, abs_of_nonneg (m13_W_nonneg t ht0.le), div_le_iff₀ ht0]
      have := m13_W_le t (by linarith [ht.2])
      nlinarith [ht.1]
  have hgcell : ∀ j < n, IntervalIntegrable g volume (a j) (a (j + 1)) := by
    intro j hj
    apply IntervalIntegrable.mono_fun' (g := fun _ => (Hb.getD j 0 : ℝ) * 85) intervalIntegrable_const
    · exact hg_meas.aestronglyMeasurable
    · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
      apply Filter.Eventually.of_forall
      intro t ht
      rw [Set.uIoc_of_le (hamono j hj).le] at ht
      have h1 := (harange j hj.le).1
      have h2 := (harange (j + 1) (by omega)).2
      have ht0 : 0 < t := by linarith [ht.1]
      have ht85 : 1 / 85 ≤ t := by linarith [ht.1]
      simp only [Real.norm_eq_abs]
      rw [hgS t ht85]
      have hW0 := m13_W_nonneg t ht0.le
      have hW1 := m13_W_le t (by linarith [ht.2])
      have hh0 := m13_hS_nonneg t ht0.le
      have hh1 := hcell j hj t ht.1.le ht.2
      rw [abs_div, abs_of_pos ht0, abs_of_nonneg (mul_nonneg hW0 hh0), div_le_iff₀ ht0]
      have : Wf t * hS t ≤ 1 * (Hb.getD j 0 : ℝ) := mul_le_mul hW1 hh1 hh0 zero_le_one
      nlinarith [ht.1]
  have hgmid : IntervalIntegrable g volume (1 / 85) (1 / 4) := by
    have := IntervalIntegrable.trans_iterate (a := a) (n := n) hgcell
    rwa [ha0, han] at this
  have hgL : IntervalIntegrable g volume 0 (1 / 85) := by
    refine (intervalIntegrable_congr (f := fun _ => (0 : ℝ)) ?_).1 intervalIntegrable_const
    intro t ht
    rw [Set.uIoc_of_le (by norm_num)] at ht
    exact (hg0 t ht.2).symm
  have hgR : IntervalIntegrable g volume (1 / 4) (1 / 2) := by
    refine (intervalIntegrable_congr (f := fun _ => (0 : ℝ)) ?_).1 intervalIntegrable_const
    intro t ht
    rw [Set.uIoc_of_le (by norm_num)] at ht
    exact (hg1 t ht.1.le).symm
  have hgall : IntervalIntegrable g volume 0 (1 / 2) := (hgL.trans hgmid).trans hgR
  -- `f₂ = W h/t` agrees with `g` on `[0, 1/2]`
  have hf2g : ∀ t ∈ Set.uIcc (0 : ℝ) (1 / 2), Wf t * hS t / t = g t := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    rcases le_total t (1 / 85) with h | h
    · rw [hg0 t h, m13_W_zero t h]; ring
    · rw [hgS t h]
  have hf2int : IntervalIntegrable (fun t => Wf t * hS t / t) volume 0 (1 / 2) :=
    (intervalIntegrable_congr (fun t ht => (hf2g t (Set.uIoc_subset_uIcc ht)).symm)).1 hgall
  -- `f₁ = W/((1 − t)t)` is integrable
  have hf1int : IntervalIntegrable (fun t => Wf t / ((1 - t) * t)) volume 0 (1 / 2) := by
    apply IntervalIntegrable.mono_fun' (g := fun _ => (2 * 85 : ℝ)) intervalIntegrable_const
    · exact (m13_W_meas.div ((measurable_const.sub measurable_id).mul measurable_id)).aestronglyMeasurable
    · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
      apply Filter.Eventually.of_forall
      intro t ht
      rw [Set.uIoc_of_le (by norm_num)] at ht
      simp only [Real.norm_eq_abs]
      rcases le_total t (1 / 85) with h | h
      · rw [m13_W_zero t h]; simp
      · have ht0 : 0 < t := by linarith
        have h1t : 1 / 2 ≤ 1 - t := by linarith [ht.2]
        have hW0 := m13_W_nonneg t ht0.le
        have hW1 := m13_W_le t ht.2
        rw [abs_div, abs_of_nonneg hW0, abs_of_pos (by positivity), div_le_iff₀ (by positivity)]
        have h3 := mul_le_mul h1t h (by norm_num) (by linarith)
        have : (1 : ℝ) ≤ 2 * 85 * ((1 - t) * t) := by linarith
        linarith
  -- the main comparison
  have hsplit : ∫ t in (0 : ℝ)..(1 / 2), Wf t * (1 / (1 - t) - hS t) / t =
      (∫ t in (0 : ℝ)..(1 / 2), Wf t / ((1 - t) * t)) - ∫ t in (0 : ℝ)..(1 / 2), Wf t * hS t / t := by
    rw [← intervalIntegral.integral_sub hf1int hf2int]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [div_eq_mul_inv, mul_inv]
    ring
  have hf2 : ∫ t in (0 : ℝ)..(1 / 2), Wf t * hS t / t ≤
      ∑ j ∈ range n, (Hb.getD j 0 : ℝ) * ∫ t in (ξ.getD j 0 : ℝ)..(ξ.getD (j + 1) 0 : ℝ), Wf t / t := by
    rw [intervalIntegral.integral_congr hf2g, ← intervalIntegral.integral_add_adjacent_intervals (hgL.trans hgmid) hgR,
      ← intervalIntegral.integral_add_adjacent_intervals hgL hgmid]
    have hz1 : ∫ t in (0 : ℝ)..(1 / 85), g t = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun t ht => by
        rw [Set.uIcc_of_le (by norm_num)] at ht; exact hg0 t ht.2)]
      simp
    have hz2 : ∫ t in (1 / 4 : ℝ)..(1 / 2), g t = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun t ht => by
        rw [Set.uIcc_of_le (by norm_num)] at ht; exact hg1 t ht.1)]
      simp
    have hmid := intervalIntegral.sum_integral_adjacent_intervals (a := a) (n := n) hgcell
    rw [ha0, han] at hmid
    rw [hz1, hz2, zero_add, add_zero, ← hmid]
    apply Finset.sum_le_sum
    intro j hj
    rw [Finset.mem_range] at hj
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (hamono j hj).le (hgcell j hj) ((hWt j hj).const_mul _)
    intro t ht
    have h1 := (harange j hj.le).1
    have ht0 : 0 < t := by linarith [ht.1]
    rw [hgS t (by linarith [ht.1])]
    have hW0 := m13_W_nonneg t ht0.le
    have hh1 := hcell j hj t ht.1 ht.2
    rw [mul_div_assoc', div_le_div_iff_of_pos_right ht0]
    nlinarith
  unfold mvalW MvalLower
  rw [hsplit]
  linarith

end Omega3
