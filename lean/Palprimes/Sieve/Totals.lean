import Palprimes.Sieve.Numerics
import Palprimes.Sieve.Assembly

/-! # Totals over the grids (M13/M14) -/

open Finset Real

namespace Palprimes

/-- The error part `Σ_j M_j C₂/(a_j L)` tends to `0`. -/
theorem grid_err_eventually (C₂ : ℝ) (n : ℕ) (a M : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in Filter.atTop, ∑ j ∈ range n, M j * (C₂ / (a j * Real.log x)) ≤ δ := by
  have h : Filter.Tendsto (fun x : ℝ => ∑ j ∈ range n, M j * (C₂ / a j) * (Real.log x)⁻¹)
      Filter.atTop (nhds (∑ j ∈ range n, M j * (C₂ / a j) * 0)) :=
    tendsto_finsetSum _ (fun j _ => (Real.tendsto_log_atTop.inv_tendsto_atTop).const_mul _)
  simp only [mul_zero, Finset.sum_const_zero] at h
  filter_upwards [h.eventually (gt_mem_nhds hδ)] with x hx
  have : ∑ j ∈ range n, M j * (C₂ / (a j * Real.log x)) = ∑ j ∈ range n, M j * (C₂ / a j) * (Real.log x)⁻¹ := by
    apply Finset.sum_congr rfl; intro j _; rw [div_mul_eq_div_div]; ring
  rw [this]; exact hx.le

/-- Generic total over a grid of primes `(x^{a_0}, x^{a_n}]`. -/
theorem grid_total (C₂ : ℝ)
    (hC₂ : ∀ a t : ℝ, 2 ≤ a → a ≤ t →
      |∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊t⌋₊).filter Nat.Prime, (1 : ℝ) / p -
        (Real.log (Real.log t) - Real.log (Real.log a))| ≤ C₂ / Real.log a)
    (F : ℝ → ℕ → ℝ) (V : ℝ → ℝ) (n : ℕ) (a M q : ℕ → ℝ) (ha0 : 0 < a 0) (hmono : Monotone a)
    (hM0 : ∀ j < n, 0 ≤ M j)
    (hloc : ∀ j < n, ∀ᶠ x : ℝ in Filter.atTop, ∀ p : ℕ, p.Prime → x ^ (a j) < p →
      (p : ℝ) ≤ x ^ (a (j + 1)) → F x p ≤ M j * V x / p)
    (hq : ∀ j < n, M j * Real.log (a (j + 1) / a j) ≤ q j) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in Filter.atTop, 0 ≤ V x →
      ∑ p ∈ (Ioc ⌊x ^ (a 0)⌋₊ ⌊x ^ (a n)⌋₊).filter Nat.Prime, F x p ≤ (∑ j ∈ range n, q j + δ) * V x := by
  have hall : ∀ᶠ x : ℝ in Filter.atTop, ∀ j ∈ range n, ∀ p : ℕ, p.Prime → x ^ (a j) < p →
      (p : ℝ) ≤ x ^ (a (j + 1)) → F x p ≤ M j * V x / p :=
    (Filter.eventually_all_finset _).2 (fun j hj => hloc j (mem_range.1 hj))
  filter_upwards [hall, grid_err_eventually C₂ n a M δ hδ, eventually_le_rpow 2 (a 0) ha0,
    Filter.eventually_gt_atTop (1 : ℝ)] with x h1 h2 h3 hx hV
  have hg := prime_grid_sum C₂ hC₂ x hx a n ha0 hmono h3 (F x) (fun j => M j * V x)
    (fun j hj => mul_nonneg (hM0 j hj) hV) (fun j hj p hp hlo hhi => h1 j (mem_range.2 hj) p hp hlo hhi)
  refine le_trans hg ?_
  have e : ∑ j ∈ range n, M j * V x * (Real.log (a (j + 1) / a j) + C₂ / (a j * Real.log x)) =
      V x * (∑ j ∈ range n, M j * Real.log (a (j + 1) / a j) + ∑ j ∈ range n, M j * (C₂ / (a j * Real.log x))) := by
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [e]
  have hs : ∑ j ∈ range n, M j * Real.log (a (j + 1) / a j) ≤ ∑ j ∈ range n, q j :=
    Finset.sum_le_sum (fun j hj => hq j (mem_range.1 hj))
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (by linarith) hV

/-- Richert summand. -/
noncomputable def fR (B : ℕ) (x : ℝ) (p : ℕ) : ℝ :=
  (1 - Real.log p / Real.log (x ^ ((23 : ℝ) / 100))) / (p * selS (PB B (Zc x)) (x ^ ((6 : ℝ) / 25) / p))

/-- Buchstab summand. -/
noncomputable def fB (B : ℕ) (x : ℝ) (p : ℕ) : ℝ :=
  1 / (p * selS (PB B p) (x ^ ((6 : ℝ) / 25) / p)) - (∏ q ∈ PB B p, (1 - 1 / (q : ℝ))) / p

theorem fB_nonneg (B : ℕ) (x : ℝ) (hx : 1 < x) (p : ℕ) (hp : p.Prime) (hpx : (p : ℝ) ≤ x ^ ((6 : ℝ) / 25)) :
    0 ≤ fB B x p := by
  unfold fB
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hS := one_le_selS (PB B p) (PB_primes B p) (x ^ ((6 : ℝ) / 25) / p) (by rw [le_div_iff₀ hp0]; linarith)
  have hVS := V_mul_selS_le_one B p (x ^ ((6 : ℝ) / 25) / p)
  have hV := V_PB_pos B p
  rw [sub_nonneg, div_le_div_iff₀ hp0 (by positivity)]
  nlinarith

theorem fR_nonneg (B : ℕ) (x : ℝ) (hx : 1 < x) (p : ℕ) (hp : p.Prime) (hpy : (p : ℝ) ≤ x ^ ((23 : ℝ) / 100)) :
    0 ≤ fR B x p := by
  unfold fR
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hL : 0 < Real.log x := Real.log_pos hx
  have hy : x ^ ((23 : ℝ) / 100) ≤ x ^ ((6 : ℝ) / 25) := Real.rpow_le_rpow_of_exponent_le hx.le (by norm_num)
  have hS := one_le_selS (PB B (Zc x)) (PB_primes B (Zc x)) (x ^ ((6 : ℝ) / 25) / p)
    (by rw [le_div_iff₀ hp0]; linarith)
  apply div_nonneg _ (by positivity)
  rw [sub_nonneg, Real.log_rpow (by linarith), div_le_one (by positivity)]
  have := Real.log_le_log hp0 hpy
  rw [Real.log_rpow (by linarith)] at this; exact this

/-- The Richert primes `[Z_c, ⌈y⌉)` lie in the grid range `(x^{49/1000}, x^{23/100}]`. -/
theorem R_glue (B : ℕ) (x : ℝ) (hx : 1 < x) :
    ∑ p ∈ (Ico (Zc x) ⌈x ^ ((23 : ℝ) / 100)⌉₊).filter Nat.Prime, fR B x p ≤
      ∑ p ∈ (Ioc ⌊x ^ ((49 : ℝ) / 1000)⌋₊ ⌊x ^ ((23 : ℝ) / 100)⌋₊).filter Nat.Prime, fR B x p := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    simp only [mem_filter, mem_Ico, mem_Ioc] at hp ⊢
    refine ⟨⟨?_, Nat.le_floor (Nat.lt_ceil.1 hp.1.2).le⟩, hp.2⟩
    have h1 : x ^ ((1 : ℝ) / 20) ≤ p := le_trans (Nat.le_ceil _) (by exact_mod_cast hp.1.1)
    have h2 : x ^ ((49 : ℝ) / 1000) < x ^ ((1 : ℝ) / 20) := Real.rpow_lt_rpow_of_exponent_lt hx (by norm_num)
    exact Nat.floor_lt (by positivity) |>.2 (by linarith)
  · intro p hp _
    simp only [mem_filter, mem_Ioc] at hp
    exact fR_nonneg B x hx p hp.2 (le_trans (by exact_mod_cast hp.1.2) (Nat.floor_le (by positivity)))

/-- The Buchstab primes `[W, Z_c)` split into the tail `p ≤ x^{1/200}` and the grid range. -/
theorem B_glue (B : ℕ) (x : ℝ) (hx : 1 < x) :
    ∑ p ∈ (Ico (Wc x) (Zc x)).filter (fun p => p.Prime ∧ ¬ p ∣ B), fB B x p ≤
      ∑ p ∈ ((Icc 1 ⌊x ^ ((1 : ℝ) / 200)⌋₊).filter Nat.Prime).filter (fun p => Wc x ≤ p), fB B x p +
      ∑ p ∈ (Ioc ⌊x ^ ((1 : ℝ) / 200)⌋₊ ⌊x ^ ((1 : ℝ) / 20)⌋₊).filter Nat.Prime, fB B x p := by
  classical
  have hsub : (Ico (Wc x) (Zc x)).filter (fun p => p.Prime ∧ ¬ p ∣ B) ⊆
      ((Icc 1 ⌊x ^ ((1 : ℝ) / 200)⌋₊).filter Nat.Prime).filter (fun p => Wc x ≤ p) ∪
      (Ioc ⌊x ^ ((1 : ℝ) / 200)⌋₊ ⌊x ^ ((1 : ℝ) / 20)⌋₊).filter Nat.Prime := by
    intro p hp
    simp only [mem_filter, mem_Ico] at hp
    rw [mem_union]
    by_cases hpl : p ≤ ⌊x ^ ((1 : ℝ) / 200)⌋₊
    · left; simp only [mem_filter, mem_Icc]; exact ⟨⟨⟨hp.2.1.one_lt.le, hpl⟩, hp.2.1⟩, hp.1.1⟩
    · right; simp only [mem_filter, mem_Ioc]
      refine ⟨⟨by omega, Nat.le_floor (Nat.lt_ceil.1 hp.1.2).le⟩, hp.2.1⟩
  have hnn : ∀ p ∈ ((Icc 1 ⌊x ^ ((1 : ℝ) / 200)⌋₊).filter Nat.Prime).filter (fun p => Wc x ≤ p) ∪
      (Ioc ⌊x ^ ((1 : ℝ) / 200)⌋₊ ⌊x ^ ((1 : ℝ) / 20)⌋₊).filter Nat.Prime, 0 ≤ fB B x p := by
    intro p hp
    have h20 : x ^ ((1 : ℝ) / 200) ≤ x ^ ((6 : ℝ) / 25) := Real.rpow_le_rpow_of_exponent_le hx.le (by norm_num)
    have h21 : x ^ ((1 : ℝ) / 20) ≤ x ^ ((6 : ℝ) / 25) := Real.rpow_le_rpow_of_exponent_le hx.le (by norm_num)
    rw [mem_union] at hp
    rcases hp with hp | hp
    · simp only [mem_filter, mem_Icc] at hp
      exact fB_nonneg B x hx p hp.1.2 (le_trans (le_trans (by exact_mod_cast hp.1.1.2)
        (Nat.floor_le (by positivity))) h20)
    · simp only [mem_filter, mem_Ioc] at hp
      exact fB_nonneg B x hx p hp.2 (le_trans (le_trans (by exact_mod_cast hp.1.2)
        (Nat.floor_le (by positivity))) h21)
  calc _ ≤ ∑ p ∈ ((Icc 1 ⌊x ^ ((1 : ℝ) / 200)⌋₊).filter Nat.Prime).filter (fun p => Wc x ≤ p) ∪
        (Ioc ⌊x ^ ((1 : ℝ) / 200)⌋₊ ⌊x ^ ((1 : ℝ) / 20)⌋₊).filter Nat.Prime, fB B x p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => hnn p hp)
    _ ≤ _ := by
        have hu := Finset.sum_union_inter (s₁ := ((Icc 1 ⌊x ^ ((1 : ℝ) / 200)⌋₊).filter Nat.Prime).filter
          (fun p => Wc x ≤ p)) (s₂ := (Ioc ⌊x ^ ((1 : ℝ) / 200)⌋₊ ⌊x ^ ((1 : ℝ) / 20)⌋₊).filter Nat.Prime)
          (f := fB B x)
        have : 0 ≤ ∑ p ∈ ((Icc 1 ⌊x ^ ((1 : ℝ) / 200)⌋₊).filter Nat.Prime).filter (fun p => Wc x ≤ p) ∩
            (Ioc ⌊x ^ ((1 : ℝ) / 200)⌋₊ ⌊x ^ ((1 : ℝ) / 20)⌋₊).filter Nat.Prime, fB B x p :=
          Finset.sum_nonneg (fun p hp => hnn p (mem_union_left _ (mem_inter.1 hp).1))
        linarith

/-- **Tail total** `≤ (1/2000 + δ) V(Z_c)`. -/
theorem tail_total (c₁ : ℝ)
    (hc₁ : ∀ t : ℝ, 1 ≤ t → ∑ p ∈ (Finset.Icc 1 ⌊t⌋₊).filter Nat.Prime, Real.log p / p ≤ Real.log t + c₁)
    (C₃ : ℝ)
    (hC₃ : ∀ t : ℝ, 2 ≤ t →
      |(∏ p ∈ (Finset.Icc 1 ⌊t⌋₊).filter Nat.Prime, (1 - 1 / (p : ℝ))) * Real.log t -
        Real.exp (-Real.eulerMascheroniConstant)| ≤ C₃ / Real.log t)
    (B : ℕ) (hB : 1 ≤ B) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in Filter.atTop,
      ∑ p ∈ ((Icc 1 ⌊x ^ ((1 : ℝ) / 200)⌋₊).filter Nat.Prime).filter (fun p => Wc x ≤ p), fB B x p ≤
        (1 / 2000 + δ) * ∏ q ∈ PB B (Zc x), (1 - 1 / (q : ℝ)) := by
  have hc := (Real.tendsto_log_atTop.inv_tendsto_atTop.const_mul (c₁ / 10)).eventually
    (gt_mem_nhds (by simpa using hδ : c₁ / 10 * 0 < δ))
  filter_upwards [buchstab_tail c₁ hc₁ C₃ hC₃ B hB, hc, Filter.eventually_gt_atTop (1 : ℝ)] with x h1 h2 hx
  have hL : 0 < Real.log x := Real.log_pos hx
  set VZ := ∏ q ∈ PB B (Zc x), (1 - 1 / (q : ℝ))
  have hVZ := V_PB_pos B (Zc x)
  have ht1 : 1 ≤ x ^ ((1 : ℝ) / 200) := Real.one_le_rpow hx.le (by norm_num)
  calc ∑ p ∈ ((Icc 1 ⌊x ^ ((1 : ℝ) / 200)⌋₊).filter Nat.Prime).filter (fun p => Wc x ≤ p), fB B x p
      ≤ ∑ p ∈ ((Icc 1 ⌊x ^ ((1 : ℝ) / 200)⌋₊).filter Nat.Prime).filter (fun p => Wc x ≤ p),
          1 / 10 * (Real.log p / Real.log x) * VZ / p := by
        apply Finset.sum_le_sum; intro p hp
        simp only [mem_filter, mem_Icc] at hp
        exact h1 p hp.1.2 hp.2 (le_trans (by exact_mod_cast hp.1.1.2) (Nat.floor_le (by positivity)))
    _ ≤ ∑ p ∈ (Icc 1 ⌊x ^ ((1 : ℝ) / 200)⌋₊).filter Nat.Prime,
          1 / 10 * (Real.log p / Real.log x) * VZ / p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        intro p hp _
        simp only [mem_filter, mem_Icc] at hp
        have : (1 : ℝ) ≤ p := by exact_mod_cast hp.1.1
        have := Real.log_nonneg this
        positivity
    _ = (1 / 10 * VZ / Real.log x) * ∑ p ∈ (Icc 1 ⌊x ^ ((1 : ℝ) / 200)⌋₊).filter Nat.Prime,
          Real.log p / p := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
    _ ≤ (1 / 10 * VZ / Real.log x) * (Real.log (x ^ ((1 : ℝ) / 200)) + c₁) :=
        mul_le_mul_of_nonneg_left (hc₁ _ ht1) (by positivity)
    _ = (1 / 2000 + c₁ / 10 * (Real.log x)⁻¹) * VZ := by
        rw [Real.log_rpow (by linarith)]; field_simp; ring
    _ ≤ (1 / 2000 + δ) * VZ := by
        apply mul_le_mul_of_nonneg_right _ hVZ.le
        simp only [Pi.inv_apply] at h2; linarith

end Palprimes
