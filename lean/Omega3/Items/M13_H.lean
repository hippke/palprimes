import Omega3.Statements

/-! # M13 helpers: facts on `W`, `h86`, `hS` (nonnegativity, vanishing, measurability). -/

namespace Omega3

open Finset MeasureTheory

set_option linter.style.longLine false

lemma m13_W_nonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ Wf t := by
  unfold Wf
  have hm : mm = 1 / 85 := rfl
  have hU : UU = 83 / 85 := rfl
  have hW : W1 = 82 / 85 := rfl
  have hk : kSq = 9999 / 1000 := rfl
  split_ifs with h1 h2 h3
  · exact le_rfl
  · push_neg at h1
    exact le_min (by rw [hk]; positivity) (by linarith)
  · push_neg at h1; linarith
  · rw [hW]; norm_num

lemma m13_W_le (t : ℝ) (ht1 : t ≤ 1 / 2) : Wf t ≤ 1 := by
  unfold Wf
  have hm : mm = 1 / 85 := rfl
  have hU : UU = 83 / 85 := rfl
  have hW : W1 = 82 / 85 := rfl
  split_ifs with h1 h2 h3
  · norm_num
  · exact le_trans (min_le_right _ _) (by rw [hm]; linarith)
  · rw [hm]; linarith
  · rw [hW]; norm_num

lemma m13_W_zero (t : ℝ) (ht : t ≤ 1 / 85) : Wf t = 0 := by
  unfold Wf
  have hm : mm = 1 / 85 := rfl
  rw [if_pos (by rw [hm]; exact ht)]

lemma m13_W_meas : Measurable Wf := by
  unfold Wf
  refine Measurable.ite measurableSet_Iic measurable_const ?_
  refine Measurable.ite measurableSet_Iic ?_ ?_
  · fun_prop
  · exact Measurable.ite measurableSet_Iic (by fun_prop) measurable_const

lemma m13_chainV_meas {n : ℕ} (j : ℕ) : Measurable (fun v : Fin n → ℝ => chainV v j) := by
  unfold chainV
  by_cases h : j < n
  · simp only [h, dif_pos]; exact measurable_pi_apply _
  · simp only [h, dif_neg, not_false_eq_true]; exact measurable_const

lemma m13_meas_imp {α : Type*} [MeasurableSpace α] (P : Prop) (s : Set α) (hs : MeasurableSet s) :
    MeasurableSet {a | P → a ∈ s} := by
  by_cases hP : P
  · simpa [hP] using hs
  · simp [hP]

lemma m13_region_meas (i : ℕ) : MeasurableSet {p : ℝ × (Fin i → ℝ) | HRegion86 i p.1 p.2} := by
  have hc : ∀ j : ℕ, Measurable (fun p : ℝ × (Fin i → ℝ) => chainV p.2 j) :=
    fun j => (m13_chainV_meas j).comp measurable_snd
  have hsum : ∀ m : ℕ, Measurable (fun p : ℝ × (Fin i → ℝ) => ∑ l ∈ range m, chainV p.2 l) :=
    fun m => Finset.measurable_sum _ (fun l _ => hc l)
  have hv : ∀ j : Fin i, Measurable (fun p : ℝ × (Fin i → ℝ) => p.2 j) :=
    fun j => (measurable_pi_apply j).comp measurable_snd
  have hS1 : MeasurableSet {p : ℝ × (Fin i → ℝ) | StrictAnti p.2} := by
    have : {p : ℝ × (Fin i → ℝ) | StrictAnti p.2} = ⋂ a : Fin i, ⋂ b : Fin i, {p | a < b → p.2 b < p.2 a} := by
      ext p; simp [StrictAnti]
    rw [this]
    exact MeasurableSet.iInter (fun a => MeasurableSet.iInter (fun b =>
      m13_meas_imp (a < b) {p : ℝ × (Fin i → ℝ) | p.2 b < p.2 a} (measurableSet_lt (hv b) (hv a))))
  have hS2 : MeasurableSet {p : ℝ × (Fin i → ℝ) | ∀ j, p.1 < p.2 j} := by
    have : {p : ℝ × (Fin i → ℝ) | ∀ j, p.1 < p.2 j} = ⋂ j : Fin i, {p | p.1 < p.2 j} := by ext p; simp
    rw [this]; exact MeasurableSet.iInter (fun j => measurableSet_lt measurable_fst (hv j))
  have hS3 : MeasurableSet {p : ℝ × (Fin i → ℝ) | ∀ j, p.2 j < 1} := by
    have : {p : ℝ × (Fin i → ℝ) | ∀ j, p.2 j < 1} = ⋂ j : Fin i, {p | p.2 j < 1} := by ext p; simp
    rw [this]; exact MeasurableSet.iInter (fun j => measurableSet_lt (hv j) measurable_const)
  have hS4 : MeasurableSet {p : ℝ × (Fin i → ℝ) | ∀ j : ℕ, 1 ≤ j → j < i →
      3 * chainV p.2 (j - 1) + ∑ l ∈ range (j - 1), chainV p.2 l ≤ 1} := by
    have : {p : ℝ × (Fin i → ℝ) | ∀ j : ℕ, 1 ≤ j → j < i →
        3 * chainV p.2 (j - 1) + ∑ l ∈ range (j - 1), chainV p.2 l ≤ 1} =
        ⋂ j : ℕ, {p | (1 ≤ j ∧ j < i) → p ∈ {p : ℝ × (Fin i → ℝ) | 3 * chainV p.2 (j - 1) + ∑ l ∈ range (j - 1), chainV p.2 l ≤ 1}} := by
      ext p; simp only [Set.mem_setOf_eq, Set.mem_iInter, and_imp]
    rw [this]
    exact MeasurableSet.iInter (fun j => m13_meas_imp _ _
      (measurableSet_le ((measurable_const.mul (hc _)).add (hsum _)) measurable_const))
  have hS5 : MeasurableSet {p : ℝ × (Fin i → ℝ) | 1 < 3 * chainV p.2 (i - 1) + ∑ l ∈ range (i - 1), chainV p.2 l} :=
    measurableSet_lt measurable_const ((measurable_const.mul (hc _)).add (hsum _))
  have hS6 : MeasurableSet {p : ℝ × (Fin i → ℝ) | chainV p.2 (i - 1) < 1 - p.1 - ∑ j, p.2 j} :=
    measurableSet_lt (hc _) (by fun_prop)
  have : {p : ℝ × (Fin i → ℝ) | HRegion86 i p.1 p.2} =
      {p | StrictAnti p.2} ∩ {p | ∀ j, p.1 < p.2 j} ∩ {p | ∀ j, p.2 j < 1} ∩
        {p : ℝ × (Fin i → ℝ) | ∀ j : ℕ, 1 ≤ j → j < i → 3 * chainV p.2 (j - 1) + ∑ l ∈ range (j - 1), chainV p.2 l ≤ 1} ∩
        {p | 1 < 3 * chainV p.2 (i - 1) + ∑ l ∈ range (i - 1), chainV p.2 l} ∩
        {p | chainV p.2 (i - 1) < 1 - p.1 - ∑ j, p.2 j} := by
    ext p; simp only [HRegion86, Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
  rw [this]
  exact ((((hS1.inter hS2).inter hS3).inter hS4).inter hS5).inter hS6

lemma m13_h86_meas (i : ℕ) : Measurable (fun x => h86 i x) := by
  classical
  unfold h86
  have hF : Measurable (Function.uncurry (fun (x : ℝ) (v : Fin i → ℝ) =>
      if HRegion86 i x v then 1 / ((∏ j, v j) * (1 - x - ∑ j, v j)) else 0)) := by
    have : Function.uncurry (fun (x : ℝ) (v : Fin i → ℝ) =>
        if HRegion86 i x v then 1 / ((∏ j, v j) * (1 - x - ∑ j, v j)) else 0) =
        fun p : ℝ × (Fin i → ℝ) => if HRegion86 i p.1 p.2 then 1 / ((∏ j, p.2 j) * (1 - p.1 - ∑ j, p.2 j)) else 0 := by
      funext p; rfl
    rw [this]
    exact Measurable.ite (m13_region_meas i) (by fun_prop) measurable_const
  exact (hF.stronglyMeasurable.integral_prod_right (ν := volume)).measurable

lemma m13_region_pos (i : ℕ) (hi : 1 ≤ i) (x : ℝ) (hx : 0 ≤ x) (v : Fin i → ℝ) (h : HRegion86 i x v) :
    0 < (∏ j, v j) * (1 - x - ∑ j, v j) ∧ (i + 2 : ℝ) * x < 1 := by
  obtain ⟨_, h2, _, _, _, h6⟩ := h
  have hlast : chainV v (i - 1) = v ⟨i - 1, by omega⟩ := by unfold chainV; rw [dif_pos (by omega)]
  have hvx : x < chainV v (i - 1) := by rw [hlast]; exact h2 _
  have hprod : 0 < ∏ j, v j := Finset.prod_pos (fun j _ => lt_of_le_of_lt hx (h2 j))
  have hu : 0 < 1 - x - ∑ j, v j := by linarith
  refine ⟨mul_pos hprod hu, ?_⟩
  have hsum : (i : ℝ) * x ≤ ∑ j, v j := by
    have : ∑ _j : Fin i, x ≤ ∑ j, v j := Finset.sum_le_sum (fun j _ => (h2 j).le)
    simpa using this
  linarith

lemma m13_h86_nonneg (i : ℕ) (hi : 1 ≤ i) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ h86 i x := by
  unfold h86
  apply integral_nonneg
  intro v
  simp only
  split_ifs with h
  · exact le_of_lt (one_div_pos.2 (m13_region_pos i hi x hx v h).1)
  · exact le_rfl

lemma m13_h86_zero (i : ℕ) (hi : 1 ≤ i) (x : ℝ) (hx : 0 ≤ x) (hix : 1 ≤ (i + 2 : ℝ) * x) : h86 i x = 0 := by
  classical
  unfold h86
  have : (fun v : Fin i → ℝ => if HRegion86 i x v then 1 / ((∏ j, v j) * (1 - x - ∑ j, v j)) else 0) = fun _ => 0 := by
    funext v
    rw [if_neg]
    intro h
    have := (m13_region_pos i hi x hx v h).2
    linarith
  rw [this]; simp

lemma m13_hS_nonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ hS t := by
  unfold hS
  exact Finset.sum_nonneg (fun k hk => m13_h86_nonneg _ (by rw [Finset.mem_Icc] at hk; omega) t ht)

lemma m13_hS_zero (t : ℝ) (ht : 1 / 4 ≤ t) : hS t = 0 := by
  unfold hS
  apply Finset.sum_eq_zero
  intro k hk
  rw [Finset.mem_Icc] at hk
  apply m13_h86_zero _ (by omega) t (by linarith)
  have : (4 : ℝ) ≤ (2 * k : ℕ) + 2 := by
    have : 2 ≤ 2 * k := by omega
    have : (2 : ℝ) ≤ (2 * k : ℕ) := by exact_mod_cast this
    linarith
  nlinarith

/-- For `t ≥ 1/85`, `hS t = Σ_{k = 1}^{100} h86(2k, t)`. -/
lemma m13_hS_eq (t : ℝ) (ht : 1 / 85 ≤ t) : hS t = ∑ k ∈ Icc 1 100, h86 (2 * k) t := by
  unfold hS
  have ht0 : 0 < t := by linarith
  have hfl : ⌊1 / t⌋₊ ≤ 85 := by
    have : 1 / t ≤ 85 := by rw [div_le_iff₀ ht0]; linarith
    have := Nat.floor_le_floor this
    simpa using this
  have hsub : Icc 1 (⌊1 / t⌋₊ + 1) ⊆ Icc 1 100 := Finset.Icc_subset_Icc le_rfl (by omega)
  apply Finset.sum_subset hsub
  intro k hk hnk
  rw [Finset.mem_Icc] at hk hnk
  have hk2 : ⌊1 / t⌋₊ + 1 < k := by omega
  apply m13_h86_zero _ (by omega) t ht0.le
  have h1 : 1 / t < ⌊1 / t⌋₊ + 1 := Nat.lt_floor_add_one _
  have h2 : ((⌊1 / t⌋₊ + 1 : ℕ) : ℝ) < k := by exact_mod_cast hk2
  push_cast at h2 h1
  have h3 : 1 / t < k := by linarith
  rw [div_lt_iff₀ ht0] at h3
  push_cast
  nlinarith

lemma m13_hSum_meas : Measurable (fun t => ∑ k ∈ Icc 1 100, h86 (2 * k) t) :=
  Finset.measurable_sum _ (fun k _ => m13_h86_meas _)

end Omega3
