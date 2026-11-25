import Omega3.DefsSieve

/-!
# M12 helper: the capped functions `G_i(x, c)` and the cap recursion

`G i x c = ∫⁻_{𝓡_i(x), x₁ < c} dv/(v₁⋯v_i u)` (lintegral, so no integrability side conditions).
Main facts:
* `h86_le_G`: `h86 i x ≤ (G i x 1).toReal`;
* `G_eq_zero`: `G i x c = 0` when `x ≥ 1/3` or `(i + 2) x ≥ 1`;
* `G_succ_le` (cap recursion, `i ≥ 1`):
  `G (i+1) x c ≤ ∫⁻ y in {x < y ≤ 1/3, y < c}, (y(1 − y))⁻¹ G i (x/(1 − y)) (y/(1 − y))`;
* `G_one_le`: `G 1 x c ≤ ∫⁻ z in {1/3 < z < (1 − x)/2, z < c}, (z(1 − x − z))⁻¹`.
-/

set_option linter.style.longLine false

open MeasureTheory Finset Real
open scoped ENNReal

namespace Omega3.M12

open Omega3

/-- Integrand of `G`. -/
noncomputable def fI (i : ℕ) (x c : ℝ) (v : Fin i → ℝ) : ℝ≥0∞ :=
  open Classical in
  if HRegion86 i x v ∧ chainV v 0 < c then ENNReal.ofReal (1 / ((∏ j, v j) * (1 - x - ∑ j, v j))) else 0

/-- `G_i(x, c)`. -/
noncomputable def G (i : ℕ) (x c : ℝ) : ℝ≥0∞ := ∫⁻ v, fI i x c v

/-! ## `chainV` bookkeeping -/

lemma chainV_of_lt {n : ℕ} (v : Fin n → ℝ) {j : ℕ} (h : j < n) : chainV v j = v ⟨j, h⟩ := by
  simp [chainV, h]

lemma chainV_cons_zero {n : ℕ} (y : ℝ) (w : Fin n → ℝ) : chainV (Fin.cons y w : Fin (n + 1) → ℝ) 0 = y := by
  simp [chainV]

lemma chainV_cons_succ {n : ℕ} (y : ℝ) (w : Fin n → ℝ) (j : ℕ) :
    chainV (Fin.cons y w : Fin (n + 1) → ℝ) (j + 1) = chainV w j := by
  unfold chainV
  by_cases h : j < n
  · have h' : j + 1 < n + 1 := by omega
    simp only [h, h', dite_true]
    exact Fin.cons_succ (α := fun _ => ℝ) y w ⟨j, h⟩
  · have h' : ¬ j + 1 < n + 1 := by omega
    simp [h, h']

lemma chainV_smul {n : ℕ} (r : ℝ) (w : Fin n → ℝ) (j : ℕ) : chainV (r • w) j = r * chainV w j := by
  unfold chainV
  split_ifs <;> simp

lemma sum_chainV_cons {n : ℕ} (y : ℝ) (w : Fin n → ℝ) (j : ℕ) :
    ∑ l ∈ range (j + 1), chainV (Fin.cons y w : Fin (n + 1) → ℝ) l = y + ∑ l ∈ range j, chainV w l := by
  rw [Finset.sum_range_succ', chainV_cons_zero, add_comm]
  simp only [chainV_cons_succ]

lemma sum_chainV_smul {n : ℕ} (r : ℝ) (w : Fin n → ℝ) (j : ℕ) :
    ∑ l ∈ range j, chainV (r • w) l = r * ∑ l ∈ range j, chainV w l := by
  rw [Finset.mul_sum]; simp only [chainV_smul]

/-! ## Facts from the region -/

lemma region_pos {i : ℕ} {x : ℝ} {v : Fin i → ℝ} (hx : 0 ≤ x) (h : HRegion86 i x v) (j : Fin i) : 0 < v j :=
  lt_of_le_of_lt hx (h.2.1 j)

lemma region_u_pos {i : ℕ} {x : ℝ} {v : Fin i → ℝ} (hi : 1 ≤ i) (hx : 0 ≤ x) (h : HRegion86 i x v) :
    0 < 1 - x - ∑ j, v j := by
  have h6 := h.2.2.2.2.2
  rw [chainV_of_lt v (by omega : i - 1 < i)] at h6
  have := region_pos hx h ⟨i - 1, by omega⟩
  linarith

/-- `(i + 2) x < 1` on the region. -/
lemma region_size {i : ℕ} {x : ℝ} {v : Fin i → ℝ} (hi : 1 ≤ i) (h : HRegion86 i x v) :
    ((i : ℝ) + 2) * x < 1 := by
  have h6 := h.2.2.2.2.2
  rw [chainV_of_lt v (by omega : i - 1 < i)] at h6
  have hl := h.2.1 ⟨i - 1, by omega⟩
  have hs : ∑ _j : Fin i, x ≤ ∑ j, v j := Finset.sum_le_sum fun j _ => (h.2.1 j).le
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  nlinarith

/-- `x < 1/3` on the region. -/
lemma region_third {i : ℕ} {x : ℝ} {v : Fin i → ℝ} (hi : 1 ≤ i) (h : HRegion86 i x v) : x < 1 / 3 := by
  rcases Nat.lt_or_ge i 2 with h2 | h2
  · obtain rfl : i = 1 := by omega
    have h5 := h.2.2.2.2.1
    have h6 := h.2.2.2.2.2
    simp only [Nat.sub_self, Finset.range_zero, Finset.sum_empty, add_zero] at h5 h6
    rw [chainV_of_lt v (by omega : 0 < 1)] at h5 h6
    rw [Fin.sum_univ_one] at h6
    have e : (⟨0, by omega⟩ : Fin 1) = 0 := rfl
    rw [e] at h5 h6
    linarith
  · have h4 := h.2.2.2.1 1 le_rfl (by omega)
    simp only [Nat.sub_self, Finset.range_zero, Finset.sum_empty, add_zero] at h4
    rw [chainV_of_lt v (by omega : 0 < i)] at h4
    have := h.2.1 ⟨0, by omega⟩
    linarith

lemma fI_eq_zero {i : ℕ} {x c : ℝ} (hi : 1 ≤ i) (hx : 1 / 3 ≤ x ∨ 1 ≤ ((i : ℝ) + 2) * x) (v : Fin i → ℝ) :
    fI i x c v = 0 := by
  unfold fI
  rw [if_neg]
  rintro ⟨h, -⟩
  rcases hx with hx | hx
  · linarith [region_third hi h]
  · linarith [region_size hi h]

theorem G_eq_zero {i : ℕ} {x c : ℝ} (hi : 1 ≤ i) (hx : 1 / 3 ≤ x ∨ 1 ≤ ((i : ℝ) + 2) * x) : G i x c = 0 := by
  unfold G
  simp [fI_eq_zero hi hx]

/-! ## `h86 ≤ G` -/

theorem h86_le_G {i : ℕ} {x : ℝ} (hi : 1 ≤ i) (hx : 0 ≤ x) : h86 i x ≤ (G i x 1).toReal := by
  classical
  set f : (Fin i → ℝ) → ℝ := fun v => if HRegion86 i x v then 1 / ((∏ j, v j) * (1 - x - ∑ j, v j)) else 0 with hf
  have hf0 : ∀ v, 0 ≤ f v := by
    intro v
    simp only [hf]
    split_ifs with h
    · have h1 : 0 < ∏ j, v j := Finset.prod_pos fun j _ => region_pos hx h j
      have h2 := region_u_pos hi hx h
      positivity
    · exact le_rfl
  have hG : G i x 1 = ∫⁻ v, ENNReal.ofReal (f v) := by
    unfold G
    refine lintegral_congr fun v => ?_
    simp only [fI, hf]
    by_cases h : HRegion86 i x v
    · have h1 : chainV v 0 < 1 := by
        rw [chainV_of_lt v (by omega : 0 < i)]; exact h.2.2.1 _
      simp [h, h1]
    · simp [h]
  have hh : h86 i x = ∫ v, f v := by unfold h86; rfl
  rw [hh, hG]
  by_cases hm : AEStronglyMeasurable f
  · rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf0) hm]
  · rw [integral_non_aestronglyMeasurable hm]
    exact ENNReal.toReal_nonneg

/-! ## Scaling -/

theorem lintegral_inv_smul (n : ℕ) {r : ℝ} (hr : 0 < r) (φ : (Fin n → ℝ) → ℝ≥0∞) :
    ∫⁻ w, φ (r⁻¹ • w) = ENNReal.ofReal (r ^ n) * ∫⁻ w, φ w := by
  have hs : r⁻¹ ≠ 0 := inv_ne_zero hr.ne'
  have e1 : ∫⁻ w, φ (r⁻¹ • w) = ∫⁻ w, φ ((MeasurableEquiv.smul₀ r⁻¹ hs : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ)) w) := rfl
  rw [e1, ← lintegral_map_equiv]
  have e2 : Measure.map (⇑(MeasurableEquiv.smul₀ r⁻¹ hs : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ))) (volume : Measure (Fin n → ℝ)) =
      ENNReal.ofReal (abs ((r⁻¹) ^ Module.finrank ℝ (Fin n → ℝ))⁻¹) • (volume : Measure (Fin n → ℝ)) := by
    rw [MeasurableEquiv.coe_smul₀]
    exact Measure.map_addHaar_smul volume hs
  rw [e2, lintegral_smul_measure, Module.finrank_fin_fun, inv_pow, inv_inv, abs_of_pos (pow_pos hr n)]
  rfl

/-! ## The recursion -/

/-- The `y`-range of the recursion. -/
def Sy (x c : ℝ) : Set ℝ := {y | x < y ∧ y ≤ 1 / 3 ∧ y < c}

lemma fI_cons_le {i : ℕ} (hi : 1 ≤ i) {x c : ℝ} (hx : 0 ≤ x) (y : ℝ) (w : Fin i → ℝ) :
    fI (i + 1) x c (Fin.cons y w) ≤ (Sy x c).indicator (fun y => ENNReal.ofReal (1 / (y * (1 - y))) *
      (ENNReal.ofReal (1 / (1 - y) ^ i) * fI i (x / (1 - y)) (y / (1 - y)) ((1 - y)⁻¹ • w))) y := by
  classical
  unfold fI
  by_cases hR : HRegion86 (i + 1) x (Fin.cons y w : Fin (i + 1) → ℝ) ∧ chainV (Fin.cons y w : Fin (i + 1) → ℝ) 0 < c
  swap
  · rw [if_neg hR]; exact zero_le
  rw [if_pos hR]
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, hc⟩ := hR
  rw [chainV_cons_zero] at hc
  have hxy : x < y := by simpa using h2 0
  have hy3 : y ≤ 1 / 3 := by
    have := h4 1 le_rfl (by omega)
    simp only [Nat.sub_self, Finset.range_zero, Finset.sum_empty, add_zero, chainV_cons_zero] at this
    linarith
  have hr : 0 < 1 - y := by linarith
  set r := 1 - y with hr_def
  have hrne : r ≠ 0 := hr.ne'
  have hyS : y ∈ Sy x c := ⟨hxy, hy3, hc⟩
  rw [Set.indicator_of_mem hyS]
  -- the tail
  have hw : ∀ j : Fin i, w j = (Fin.cons y w : Fin (i + 1) → ℝ) j.succ := fun j => (Fin.cons_succ (α := fun _ => ℝ) y w j).symm
  have hwS : StrictAnti w := by
    intro a b hab
    rw [hw a, hw b]; exact h1 (Fin.succ_lt_succ_iff.mpr hab)
  have hw0 : w ⟨0, by omega⟩ < y := by
    rw [hw]
    have := h1 (show (0 : Fin (i + 1)) < (⟨0, by omega⟩ : Fin i).succ from Fin.succ_pos _)
    simpa using this
  set w' : Fin i → ℝ := r⁻¹ • w with hw'
  have hw'j : ∀ j, w' j = w j / r := fun j => by simp [hw', div_eq_inv_mul]
  have hsumv : ∑ j, (Fin.cons y w : Fin (i + 1) → ℝ) j = y + ∑ j, w j := by
    rw [Fin.sum_univ_succ]; simp
  have hsumw' : ∑ j, w' j = (∑ j, w j) / r := by
    simp only [hw'j]; rw [Finset.sum_div]
  have hprodv : ∏ j, (Fin.cons y w : Fin (i + 1) → ℝ) j = y * ∏ j, w j := by
    rw [Fin.prod_univ_succ]; simp
  have hprodw' : ∏ j, w' j = (∏ j, w j) / r ^ i := by
    simp only [hw'j]; rw [Finset.prod_div_distrib]; simp
  have hreg : HRegion86 i (x / r) w' := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a b hab; rw [hw'j, hw'j]; exact div_lt_div_of_pos_right (hwS hab) hr
    · intro j; rw [hw'j]; rw [hw j]; exact div_lt_div_of_pos_right (h2 j.succ) hr
    · intro j
      rw [hw'j, div_lt_one hr]
      have : w j ≤ w ⟨0, by omega⟩ := hwS.antitone (Fin.le_def.mpr (Nat.zero_le _))
      linarith
    · intro j hj1 hj2
      have := h4 (j + 1) (by omega) (by omega)
      have e1 : j + 1 - 1 = (j - 1) + 1 := by omega
      rw [e1, chainV_cons_succ, sum_chainV_cons] at this
      rw [hw', chainV_smul, sum_chainV_smul]
      have : 3 * chainV w (j - 1) + ∑ l ∈ range (j - 1), chainV w l ≤ r := by linarith
      calc 3 * (r⁻¹ * chainV w (j - 1)) + r⁻¹ * ∑ l ∈ range (j - 1), chainV w l
          = (3 * chainV w (j - 1) + ∑ l ∈ range (j - 1), chainV w l) / r := by field_simp
        _ ≤ r / r := div_le_div_of_nonneg_right this hr.le
        _ = 1 := div_self hr.ne'
    · have e1 : i + 1 - 1 = (i - 1) + 1 := by omega
      rw [e1, chainV_cons_succ, sum_chainV_cons] at h5
      rw [hw', chainV_smul, sum_chainV_smul]
      have : r < 3 * chainV w (i - 1) + ∑ l ∈ range (i - 1), chainV w l := by linarith
      calc (1 : ℝ) = r / r := (div_self hr.ne').symm
        _ < (3 * chainV w (i - 1) + ∑ l ∈ range (i - 1), chainV w l) / r := div_lt_div_of_pos_right this hr
        _ = 3 * (r⁻¹ * chainV w (i - 1)) + r⁻¹ * ∑ l ∈ range (i - 1), chainV w l := by field_simp
    · have e1 : i + 1 - 1 = (i - 1) + 1 := by omega
      rw [e1, chainV_cons_succ, hsumv] at h6
      rw [hw', chainV_smul, ← hw', hsumw']
      have : chainV w (i - 1) < r - x - ∑ j, w j := by linarith
      calc r⁻¹ * chainV w (i - 1) < r⁻¹ * (r - x - ∑ j, w j) := mul_lt_mul_of_pos_left this (inv_pos.mpr hr)
        _ = 1 - x / r - (∑ j, w j) / r := by field_simp
  have hcap : chainV w' 0 < y / r := by
    rw [chainV_of_lt w' (by omega : 0 < i), hw'j]
    exact div_lt_div_of_pos_right hw0 hr
  rw [if_pos ⟨hreg, hcap⟩]
  -- value identity
  have hy0 : 0 < y := lt_of_le_of_lt hx hxy
  have hpw : 0 < ∏ j, w' j := Finset.prod_pos fun j _ => region_pos (div_nonneg hx hr.le) hreg j
  have hu' : 0 < 1 - x / r - ∑ j, w' j := region_u_pos hi (div_nonneg hx hr.le) hreg
  have hri : 0 < r ^ i := pow_pos hr i
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  apply le_of_eq
  congr 1
  rw [hprodv, hsumv]
  have e3 : ∏ j, w j = r ^ i * ∏ j, w' j := by rw [hprodw']; field_simp
  have e4 : ∑ j, w j = r * ∑ j, w' j := by rw [hsumw']; field_simp
  rw [e3, e4]
  have e5 : 1 - x - (y + r * ∑ j, w' j) = r * (1 - x / r - ∑ j, w' j) := by
    have hxr : r * (x / r) = x := by field_simp
    linear_combination (-1 : ℝ) * hr_def + hxr
  rw [e5, one_div_mul_one_div (r ^ i), one_div_mul_one_div]
  congr 1
  ring

theorem G_succ_le {i : ℕ} (hi : 1 ≤ i) {x c : ℝ} (hx : 0 ≤ x) :
    G (i + 1) x c ≤ ∫⁻ y, (Sy x c).indicator (fun y => ENNReal.ofReal (1 / (y * (1 - y))) * G i (x / (1 - y)) (y / (1 - y))) y := by
  unfold G
  have hmp := MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (i + 1) => ℝ) 0
  have e1 : ∫⁻ v, fI (i + 1) x c v =
      ∫⁻ p, fI (i + 1) x c ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (i + 1) => ℝ) 0).symm p) := by
    rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
    simp
  rw [e1, Measure.volume_eq_prod]
  refine (lintegral_prod_le _).trans (lintegral_mono fun y => ?_)
  have e2 : ∀ w : Fin i → ℝ, (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (i + 1) => ℝ) 0).symm (y, w) = Fin.cons y w := by
    intro w
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply]
  simp only [e2]
  by_cases hy : y ∈ Sy x c
  · rw [Set.indicator_of_mem hy]
    have hr : 0 < 1 - y := by have := hy.2.1; linarith
    calc ∫⁻ w, fI (i + 1) x c (Fin.cons y w)
        ≤ ∫⁻ w, ENNReal.ofReal (1 / (y * (1 - y))) * (ENNReal.ofReal (1 / (1 - y) ^ i) *
            fI i (x / (1 - y)) (y / (1 - y)) ((1 - y)⁻¹ • w)) := by
          refine lintegral_mono fun w => ?_
          have := fI_cons_le hi hx (c := c) y w
          rwa [Set.indicator_of_mem hy] at this
      _ = ENNReal.ofReal (1 / (y * (1 - y))) * (ENNReal.ofReal (1 / (1 - y) ^ i) *
            ∫⁻ w, fI i (x / (1 - y)) (y / (1 - y)) ((1 - y)⁻¹ • w)) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = ENNReal.ofReal (1 / (y * (1 - y))) * ∫⁻ w, fI i (x / (1 - y)) (y / (1 - y)) w := by
          rw [lintegral_inv_smul i hr, ← mul_assoc (ENNReal.ofReal (1 / (1 - y) ^ i)),
            ← ENNReal.ofReal_mul (div_nonneg zero_le_one (pow_pos hr i).le)]
          rw [one_div_mul_cancel (pow_pos hr i).ne', ENNReal.ofReal_one, one_mul]
  · rw [Set.indicator_of_notMem hy]
    have : ∀ w : Fin i → ℝ, fI (i + 1) x c (Fin.cons y w) = 0 := by
      intro w
      have := fI_cons_le hi hx (c := c) y w
      rw [Set.indicator_of_notMem hy] at this
      exact le_antisymm this zero_le
    simp [this]

/-! ## The first level -/

/-- The `z`-range of `G 1`. -/
def S1 (x c : ℝ) : Set ℝ := {z | 1 / 3 < z ∧ z < (1 - x) / 2 ∧ z < c}

theorem G_one_le {x c : ℝ} (hx : 0 ≤ x) :
    G 1 x c ≤ ∫⁻ z, (S1 x c).indicator (fun z => ENNReal.ofReal (1 / (z * (1 - x - z)))) z := by
  classical
  unfold G
  have hmp := (volume_preserving_funUnique (Fin 1) ℝ).symm
  have e1 : ∫⁻ v, fI 1 x c v = ∫⁻ z, fI 1 x c ((MeasurableEquiv.funUnique (Fin 1) ℝ).symm z) := by
    rw [hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
    rfl
  rw [e1]
  refine lintegral_mono fun z => ?_
  have ev : (MeasurableEquiv.funUnique (Fin 1) ℝ).symm z = fun _ => z := rfl
  rw [ev]
  unfold fI
  by_cases hR : HRegion86 1 x (fun _ : Fin 1 => z) ∧ chainV (fun _ : Fin 1 => z) 0 < c
  swap
  · rw [if_neg hR]; exact zero_le
  rw [if_pos hR]
  obtain ⟨⟨_, _, _, _, h5, h6⟩, hc⟩ := hR
  simp only [Nat.sub_self, Finset.range_zero, Finset.sum_empty, add_zero] at h5 h6
  rw [chainV_of_lt _ (by omega : 0 < 1)] at h5 h6 hc
  simp only [Fin.sum_univ_one, Fin.prod_univ_one] at h6 ⊢
  have hz : z ∈ S1 x c := ⟨by linarith, by linarith, hc⟩
  rw [Set.indicator_of_mem hz]

end Omega3.M12
