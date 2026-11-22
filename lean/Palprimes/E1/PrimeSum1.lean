import Palprimes.E1.Mertens

/-! # E1, Part B.2: uniform one-dimensional prime sums (blueprint §3.2)

For `D > 1`, `w > 1` put `s = log D / log w` and, for a prime `p`, `s_p = log D / log p − 1`.

**Lemma B.2** (`primeSum1`). Let `1 ≤ c < M`, `1 ≤ σ₀ ≤ S₁`, and `ψ` continuous on `[c, M]` with `ψ = 0`
on `(M, ∞)`. For every `ε > 0` there is `D₁` such that for all `D ≥ D₁` and all `w` with
`D^{1/S₁} ≤ w ≤ D^{1/σ₀}`:
`|Σ_{p<w, s_p ≥ c} g(p) V(p) ψ(s_p) − V(w) · s⁻¹ ∫_{u > max(s−1, c)} ψ(u) du| ≤ ε V(w)`.

The closed end `s_p ≥ c` is included in the sum (for `c = 2` this is `p³ ≤ D`, the `headOK` convention).
The integral is the set integral over `Set.Ioi (max (s − 1) c)`, the form used by `betaP`/`betaM` in `Cont.lean`.

Proof (blueprint §3.2): the cumulative mass `Φ(t) = Σ_{p<w, s_p ≤ t} g(p)V(p)` equals `V(min(D^{1/(1+t)}, w)) − V(w)`
exactly (A.7, `cum_sp_eq`), and `VB_ratio_mul` gives `Φ(t) = V(w) (max(t, s−1) − (s−1))/s ± δ V(w)` uniformly in
`t ∈ [0, M]` and in `s` (`cum_sp_asymp`). On a fixed grid `u_i = c + i (M−c)/N` the sum is compared with the
Stieltjes step sum `Σ_i ψ(u_{i+1}) (Φ(u_{i+1}) − Φ(u_i))` (uniform continuity; the point `s_p = c` is a cell
`(c − δ, c]` of mass `≤ 3 δ V(w)`), and the same step sum with `Φ` replaced by its continuous limit is compared with
the integral.

Also exported for B.3 (E5): the mass bounds `mass_sp_le`, `mass_sp_lt_le` (`Σ_{p<w, s_p ≤ M} g(p)V(p) ≤ (M+1) V(w)`),
the `s`-form `primeSum1_s` (hypotheses `1 < w`, `σ₀ ≤ s ≤ S₁`), and the identity
`log (D/p) / log p = log D / log p − 1` (`log_div_div_log`). -/

set_option linter.style.longLine false

open Finset Real MeasureTheory

namespace Palprimes.E1

open Palprimes.MT Palprimes.Greaves

/-! ## Step functions on a grid (generic, no primes) -/

section Generic

/-- `1[x ≤ t]` as a real number. -/
private noncomputable def ind (x t : ℝ) : ℝ := if x ≤ t then 1 else 0

private lemma ind_sub_nonneg (x : ℝ) {t t' : ℝ} (h : t ≤ t') : 0 ≤ ind x t' - ind x t := by
  unfold ind
  by_cases h1 : x ≤ t
  · rw [ite_eq_left h1, ite_eq_left (h1.trans h)]; norm_num
  · by_cases h2 : x ≤ t'
    · rw [ite_eq_right h1, ite_eq_left h2]; norm_num
    · rw [ite_eq_right h1, ite_eq_right h2]; norm_num

private lemma ind_cell (x : ℝ) {t t' : ℝ} (h : t ≤ t') :
    ind x t' - ind x t = 0 ∨ (ind x t' - ind x t = 1 ∧ t < x ∧ x ≤ t') := by
  unfold ind
  by_cases h1 : x ≤ t
  · left; rw [ite_eq_left h1, ite_eq_left (h1.trans h)]; ring
  · by_cases h2 : x ≤ t'
    · right; rw [ite_eq_right h1, ite_eq_left h2]; exact ⟨by ring, not_le.mp h1, h2⟩
    · left; rw [ite_eq_right h1, ite_eq_right h2]; ring

private lemma grid_ge {c : ℝ} {u : ℕ → ℝ} (hu0 : u 0 = c) (hmono : ∀ i, u i ≤ u (i + 1)) :
    ∀ i, c ≤ u i := by
  intro i
  induction i with
  | zero => rw [hu0]
  | succ i ih => exact ih.trans (hmono i)

/-- Pointwise step-function estimate on the grid `u_0 = c < … < u_N = M`. -/
private lemma step_pointwise (ψ : ℝ → ℝ) {c M B ω η : ℝ} {N : ℕ} {u : ℕ → ℝ}
    (hu0 : u 0 = c) (huN : u N = M) (hmono : ∀ i, u i ≤ u (i + 1)) (hη : 0 < η)
    (hB : |ψ c| ≤ B) (hψM : ∀ t, M < t → ψ t = 0)
    (hosc : ∀ i < N, ∀ t, u i < t → t ≤ u (i + 1) → |ψ t - ψ (u (i + 1))| ≤ ω) (x : ℝ) :
    |(if c ≤ x then ψ x else 0) - ∑ i ∈ range N, ψ (u (i + 1)) * (ind x (u (i + 1)) - ind x (u i))|
      ≤ B * (ind x c - ind x (c - η)) + ω * (ind x M - ind x c) := by
  have hge := grid_ge hu0 hmono
  have hcM : c ≤ M := huN ▸ hge N
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hB
  have hsum : ∑ i ∈ range N, (ind x (u (i + 1)) - ind x (u i)) = ind x M - ind x c := by
    have := Finset.sum_range_sub (fun i => ind x (u i)) N
    rw [this, huN, hu0]
  by_cases hxc : x = c
  · rw [hxc]
    have h0 : ∀ i ∈ range N, ψ (u (i + 1)) * (ind c (u (i + 1)) - ind c (u i)) = 0 := by
      intro i _
      unfold ind; rw [ite_eq_left (hge (i + 1)), ite_eq_left (hge i)]; ring
    rw [Finset.sum_eq_zero h0, ite_eq_left le_rfl, sub_zero]
    have h1 : ind c c - ind c (c - η) = 1 := by
      unfold ind; rw [ite_eq_left le_rfl, ite_eq_right (by linarith)]; ring
    have h2 : ind c M - ind c c = 0 := by
      unfold ind; rw [ite_eq_left hcM, ite_eq_left le_rfl]; ring
    rw [h1, h2]; linarith
  · have hL : (if c ≤ x then ψ x else 0) = ψ x * (ind x M - ind x c) := by
      unfold ind
      by_cases h1 : x ≤ c
      · have : x < c := lt_of_le_of_ne h1 hxc
        rw [ite_eq_right (not_le.mpr this), ite_eq_left (h1.trans hcM), ite_eq_left h1]; ring
      · rw [ite_eq_left (not_le.mp h1).le, ite_eq_right h1]
        by_cases h2 : x ≤ M
        · rw [ite_eq_left h2]; ring
        · rw [ite_eq_right h2, hψM x (not_le.mp h2)]; ring
    have key : ψ x * (ind x M - ind x c) -
        ∑ i ∈ range N, ψ (u (i + 1)) * (ind x (u (i + 1)) - ind x (u i)) =
        ∑ i ∈ range N, (ψ x - ψ (u (i + 1))) * (ind x (u (i + 1)) - ind x (u i)) := by
      rw [← hsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hL, key]
    have hnn := ind_sub_nonneg x (show c - η ≤ c by linarith)
    calc |∑ i ∈ range N, (ψ x - ψ (u (i + 1))) * (ind x (u (i + 1)) - ind x (u i))|
        ≤ ∑ i ∈ range N, |(ψ x - ψ (u (i + 1))) * (ind x (u (i + 1)) - ind x (u i))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ range N, ω * (ind x (u (i + 1)) - ind x (u i)) := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          rcases ind_cell x (hmono i) with h | ⟨h, h1, h2⟩
          · rw [h]; simp
          · rw [h, mul_one, mul_one]; exact hosc i (Finset.mem_range.1 hi) x h1 h2
      _ = ω * (ind x M - ind x c) := by rw [← Finset.mul_sum, hsum]
      _ ≤ B * (ind x c - ind x (c - η)) + ω * (ind x M - ind x c) := by
          nlinarith [mul_nonneg hB0 hnn]

/-- Cumulative mass `Φ(t) = Σ_{p ∈ P} f(p) 1[x_p ≤ t]`. -/
private noncomputable def cum (P : Finset ℕ) (f x : ℕ → ℝ) (t : ℝ) : ℝ := ∑ p ∈ P, f p * ind (x p) t

/-- The sum against the Stieltjes step sum on the grid. -/
private lemma step_bound (P : Finset ℕ) (f x : ℕ → ℝ) (hf : ∀ p ∈ P, 0 ≤ f p) (ψ : ℝ → ℝ)
    {c M B ω η : ℝ} {N : ℕ} {u : ℕ → ℝ}
    (hu0 : u 0 = c) (huN : u N = M) (hmono : ∀ i, u i ≤ u (i + 1)) (hη : 0 < η)
    (hB : |ψ c| ≤ B) (hψM : ∀ t, M < t → ψ t = 0)
    (hosc : ∀ i < N, ∀ t, u i < t → t ≤ u (i + 1) → |ψ t - ψ (u (i + 1))| ≤ ω) :
    |∑ p ∈ P, f p * (if c ≤ x p then ψ (x p) else 0) -
        ∑ i ∈ range N, ψ (u (i + 1)) * (cum P f x (u (i + 1)) - cum P f x (u i))|
      ≤ B * (cum P f x c - cum P f x (c - η)) + ω * (cum P f x M - cum P f x c) := by
  have e1 : ∑ i ∈ range N, ψ (u (i + 1)) * (cum P f x (u (i + 1)) - cum P f x (u i)) =
      ∑ p ∈ P, f p * ∑ i ∈ range N, ψ (u (i + 1)) * (ind (x p) (u (i + 1)) - ind (x p) (u i)) := by
    simp only [cum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun i _ => by ring))
  have e2 : B * (cum P f x c - cum P f x (c - η)) + ω * (cum P f x M - cum P f x c) =
      ∑ p ∈ P, f p * (B * (ind (x p) c - ind (x p) (c - η)) + ω * (ind (x p) M - ind (x p) c)) := by
    simp only [cum, ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  rw [e1, e2, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun p hp => ?_))
  rw [← mul_sub, abs_mul, abs_of_nonneg (hf p hp)]
  exact mul_le_mul_of_nonneg_left (step_pointwise ψ hu0 huN hmono hη hB hψM hosc (x p)) (hf p hp)

private lemma max_sub_max_le' {t t' : ℝ} (a : ℝ) (h : t ≤ t') : max t' a - max t a ≤ t' - t := by
  have := max_sub_max_le_max t' a t a
  rw [sub_self] at this
  exact this.trans (le_of_eq (max_eq_left (by linarith)))

private lemma div_le_of_one_le' {x y s : ℝ} (hs : 1 ≤ s) (hx : x ≤ y) (hy : 0 ≤ y) : x / s ≤ y := by
  rw [div_le_iff₀ (by linarith)]; nlinarith

/-- The continuous step sum against the integral: `Δφ_i = (max(u_{i+1}, a) − max(u_i, a))/s`. -/
private lemma cont_step (ψ : ℝ → ℝ) {c M a s ω : ℝ} {N : ℕ} {u : ℕ → ℝ}
    (hu0 : u 0 = c) (huN : u N = M) (hmono : ∀ i, u i ≤ u (i + 1)) (hs : 0 < s)
    (hint : IntegrableOn ψ (Set.Ioi c)) (hψM : ∀ t, M < t → ψ t = 0)
    (hosc : ∀ i < N, ∀ t, u i < t → t ≤ u (i + 1) → |ψ t - ψ (u (i + 1))| ≤ ω) :
    |∑ i ∈ range N, ψ (u (i + 1)) * ((max (u (i + 1)) a - max (u i) a) / s) -
        s⁻¹ * ∫ t in Set.Ioi (max a c), ψ t| ≤ ω * ((max M a - max c a) / s) := by
  have hge := grid_ge hu0 hmono
  have hcM : c ≤ M := huN ▸ hge N
  have hAc : ∀ i, c ≤ max (u i) a := fun i => (hge i).trans (le_max_left _ _)
  have hII : ∀ i, IntervalIntegrable ψ volume (max (u i) a) (max (u (i + 1)) a) := fun i =>
    ⟨hint.mono_set (fun t ht => lt_of_le_of_lt (hAc i) ht.1),
      hint.mono_set (fun t ht => lt_of_le_of_lt (hAc (i + 1)) ht.1)⟩
  have h1 := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := ψ)
    (a := fun i => max (u i) a) (n := N) (fun i _ => hII i)
  rw [hu0, huN] at h1
  have hle : max c a ≤ max M a := max_le_max hcM le_rfl
  have hIoi : ∫ t in Set.Ioi (max a c), ψ t = ∫ t in (max c a)..(max M a), ψ t := by
    have hi1 : IntegrableOn ψ (Set.Ioc (max c a) (max M a)) :=
      hint.mono_set (fun t ht => lt_of_le_of_lt (le_max_left c a) ht.1)
    have hi2 : IntegrableOn ψ (Set.Ioi (max M a)) :=
      hint.mono_set (fun t (ht : max M a < t) => lt_of_le_of_lt ((le_max_left c a).trans hle) ht)
    have hsplit := setIntegral_union (μ := volume) (f := ψ) (Set.Ioc_disjoint_Ioi (le_refl (max M a)))
      measurableSet_Ioi hi1 hi2
    rw [max_comm a c, intervalIntegral.integral_of_le hle, ← Set.Ioc_union_Ioi_eq_Ioi hle, hsplit,
      setIntegral_eq_zero_of_forall_eq_zero (t := Set.Ioi (max M a))
        (fun t ht => hψM t (lt_of_le_of_lt (le_max_left M a) ht)), add_zero]
  have hterm : ∀ i ∈ range N,
      |ψ (u (i + 1)) * ((max (u (i + 1)) a - max (u i) a) / s) -
          s⁻¹ * ∫ t in (max (u i) a)..(max (u (i + 1)) a), ψ t| ≤
        ω * ((max (u (i + 1)) a - max (u i) a) / s) := by
    intro i hi
    have hle' : max (u i) a ≤ max (u (i + 1)) a := max_le_max (hmono i) le_rfl
    have hconst : ∫ t in (max (u i) a)..(max (u (i + 1)) a), (ψ t - ψ (u (i + 1))) =
        (∫ t in (max (u i) a)..(max (u (i + 1)) a), ψ t) -
          (max (u (i + 1)) a - max (u i) a) * ψ (u (i + 1)) := by
      rw [intervalIntegral.integral_sub (hII i) intervalIntegrable_const, intervalIntegral.integral_const,
        smul_eq_mul]
    have hbd : ‖∫ t in (max (u i) a)..(max (u (i + 1)) a), (ψ t - ψ (u (i + 1)))‖ ≤
        ω * |max (u (i + 1)) a - max (u i) a| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      rw [Set.uIoc_of_le hle'] at ht
      have h1 : u i < t := lt_of_le_of_lt (le_max_left _ _) ht.1
      have h2 : t ≤ u (i + 1) := by
        by_contra h
        push Not at h
        rcases le_max_iff.1 ht.2 with h' | h'
        · linarith
        · linarith [le_max_right (u i) a, ht.1]
      rw [Real.norm_eq_abs]
      exact hosc i (Finset.mem_range.1 hi) t h1 h2
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hle'), hconst] at hbd
    have e : ψ (u (i + 1)) * ((max (u (i + 1)) a - max (u i) a) / s) -
          s⁻¹ * ∫ t in (max (u i) a)..(max (u (i + 1)) a), ψ t =
        -s⁻¹ * ((∫ t in (max (u i) a)..(max (u (i + 1)) a), ψ t) -
          (max (u (i + 1)) a - max (u i) a) * ψ (u (i + 1))) := by ring
    rw [e, abs_mul, abs_neg, abs_of_pos (inv_pos.2 hs)]
    calc s⁻¹ * |(∫ t in (max (u i) a)..(max (u (i + 1)) a), ψ t) -
            (max (u (i + 1)) a - max (u i) a) * ψ (u (i + 1))|
        ≤ s⁻¹ * (ω * (max (u (i + 1)) a - max (u i) a)) :=
          mul_le_mul_of_nonneg_left hbd (inv_nonneg.2 hs.le)
      _ = ω * ((max (u (i + 1)) a - max (u i) a) / s) := by ring
  rw [hIoi, ← h1, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have htel := Finset.sum_range_sub (fun i => max (u i) a) N
  rw [hu0, huN] at htel
  calc _ ≤ ∑ i ∈ range N, |ψ (u (i + 1)) * ((max (u (i + 1)) a - max (u i) a) / s) -
          s⁻¹ * ∫ t in (max (u i) a)..(max (u (i + 1)) a), ψ t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range N, ω * ((max (u (i + 1)) a - max (u i) a) / s) := Finset.sum_le_sum hterm
    _ = ω * ((max M a - max c a) / s) := by
        rw [← Finset.mul_sum, ← Finset.sum_div, htel]

end Generic

/-! ## The cumulative prime mass in `s_p` -/

/-- `log (D/p) / log p = log D / log p − 1` (the inner level `D/p` at the prime `p`). -/
theorem log_div_div_log {D p : ℝ} (hD : 0 < D) (hp : 1 < p) :
    Real.log (D / p) / Real.log p = Real.log D / Real.log p - 1 := by
  rw [Real.log_div hD.ne' (by linarith : p ≠ 0), sub_div, div_self (Real.log_pos hp).ne']

/-- The primes `p < w` with `s_p ≤ t` are the primes in `[min(D^{1/(1+t)}, w), w)`. -/
theorem filter_sp_le_eq {D : ℝ} (hD : 0 < D) (w : ℝ) {t : ℝ} (ht : 0 < 1 + t) :
    (primesBelow w).filter (fun p : ℕ => Real.log D / Real.log p - 1 ≤ t) =
      primesIco (min (D ^ (1 / (1 + t))) w) w := by
  ext p
  rw [Finset.mem_filter, mem_primesBelow, mem_primesIco]
  constructor
  · rintro ⟨⟨hp, hpw⟩, h⟩
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    exact ⟨hp, (min_le_left _ _).trans ((rpow_le_iff_sp_le hD hp1 ht).2 h), hpw⟩
  · rintro ⟨hp, hlo, hpw⟩
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    refine ⟨⟨hp, hpw⟩, (rpow_le_iff_sp_le hD hp1 ht).1 ?_⟩
    rcases min_le_iff.1 hlo with h | h
    · exact h
    · exact absurd hpw (not_lt.2 h)

/-- **Cumulative mass (exact, A.7)**: `Σ_{p<w, s_p ≤ t} g(p)V(p) = V(min(D^{1/(1+t)}, w)) − V(w)`. -/
theorem cum_sp_eq (b : ℕ) {D : ℝ} (hD : 0 < D) (w : ℝ) {t : ℝ} (ht : 0 < 1 + t) :
    ∑ p ∈ (primesBelow w).filter (fun p : ℕ => Real.log D / Real.log p - 1 ≤ t), gB b p * VB b p =
      VB b (min (D ^ (1 / (1 + t))) w) - VB b w := by
  rw [filter_sp_le_eq hD w ht, telescope b (min_le_right _ _)]

/-- **Cumulative mass (asymptotic, uniform)**: with `s = log D / log w`,
`V(min(D^{1/(1+t)}, w)) − V(w) = V(w) (max(t, s−1) − (s−1))/s ± δ V(w)` for `y₀ ≤ w ≤ D`, `0 ≤ t ≤ M`. -/
theorem cum_sp_asymp (b : ℕ) (hb : 2 ≤ b) {M : ℝ} (hM : 0 ≤ M) {δ : ℝ} (hδ : 0 < δ) :
    ∃ y₀ : ℝ, 1 < y₀ ∧ ∀ D w : ℝ, y₀ ≤ w → w ≤ D → ∀ t : ℝ, 0 ≤ t → t ≤ M →
      |VB b (min (D ^ (1 / (1 + t))) w) - VB b w -
          (max t (Real.log D / Real.log w - 1) - (Real.log D / Real.log w - 1)) /
            (Real.log D / Real.log w) * VB b w| ≤ δ * VB b w := by
  obtain ⟨y₀, hy₀, h⟩ := VB_ratio_mul b hb (1 / (1 + M)) (by positivity)
    (by rw [div_le_one (by linarith)]; linarith) δ hδ
  refine ⟨y₀, hy₀, fun D w hw hwD t ht0 htM => ?_⟩
  have hw1 : 1 < w := lt_of_lt_of_le hy₀ hw
  have hD1 : 1 < D := lt_of_lt_of_le hw1 hwD
  have hlw : 0 < Real.log w := Real.log_pos hw1
  have hlD : 0 < Real.log D := Real.log_pos hD1
  have ht1 : 0 < 1 + t := by linarith
  have hx0 : 0 < D ^ (1 / (1 + t)) := Real.rpow_pos_of_pos (by linarith) _
  have hlx : Real.log (D ^ (1 / (1 + t))) = Real.log D / (1 + t) := by
    rw [Real.log_rpow (by linarith)]; ring
  rcases le_total (D ^ (1 / (1 + t))) w with hxw | hwx
  · rw [min_eq_left hxw]
    have hlxw : Real.log (D ^ (1 / (1 + t))) ≤ Real.log w := Real.log_le_log hx0 hxw
    rw [hlx, div_le_iff₀ ht1] at hlxw
    have hst : Real.log D / Real.log w - 1 ≤ t := by
      rw [sub_le_iff_le_add, div_le_iff₀ hlw]; nlinarith
    rw [max_eq_left hst]
    have hwa : w ^ (1 / (1 + M)) ≤ D ^ (1 / (1 + t)) := by
      calc w ^ (1 / (1 + M)) ≤ w ^ (1 / (1 + t)) :=
            Real.rpow_le_rpow_of_exponent_le hw1.le (one_div_le_one_div_of_le ht1 (by linarith))
        _ ≤ D ^ (1 / (1 + t)) := Real.rpow_le_rpow (by linarith) hwD (by positivity)
    have key := h w hw (D ^ (1 / (1 + t))) hwa hxw
    have e : VB b (D ^ (1 / (1 + t))) - VB b w -
        (t - (Real.log D / Real.log w - 1)) / (Real.log D / Real.log w) * VB b w =
        VB b (D ^ (1 / (1 + t))) - Real.log w / Real.log (D ^ (1 / (1 + t))) * VB b w := by
      rw [hlx]; field_simp; ring
    rw [e]; exact key
  · rw [min_eq_right hwx]
    have hlwx : Real.log w ≤ Real.log (D ^ (1 / (1 + t))) := Real.log_le_log (by linarith) hwx
    rw [hlx, le_div_iff₀ ht1] at hlwx
    have hst : t ≤ Real.log D / Real.log w - 1 := by
      rw [le_sub_iff_add_le, le_div_iff₀ hlw]; nlinarith
    rw [max_eq_right hst]; simp only [sub_self, zero_div, zero_mul, abs_zero]
    exact mul_nonneg hδ.le (VB_pos' b w).le

/-- From `D ≥ y₀^{S₁}` and `D^{1/S₁} ≤ w ≤ D^{1/σ₀}` (`σ₀ ≥ 1`): `1 < D`, `y₀ ≤ w ≤ D`. -/
private lemma range_setup {y₀ S₁ σ₀ D w : ℝ} (hy₀ : 1 < y₀) (hS : 0 < S₁) (hσ₀ : 1 ≤ σ₀)
    (hD : y₀ ^ S₁ ≤ D) (hw1 : D ^ (1 / S₁) ≤ w) (hw2 : w ≤ D ^ (1 / σ₀)) :
    1 < D ∧ y₀ ≤ w ∧ w ≤ D := by
  have hY : 1 < y₀ ^ S₁ := Real.one_lt_rpow hy₀ hS
  have hD1 : 1 < D := lt_of_lt_of_le hY hD
  refine ⟨hD1, ?_, ?_⟩
  · have : (y₀ ^ S₁) ^ (1 / S₁) ≤ D ^ (1 / S₁) := Real.rpow_le_rpow (by linarith) hD (by positivity)
    rw [← Real.rpow_mul (by linarith), mul_one_div_cancel hS.ne', Real.rpow_one] at this
    linarith
  · have : D ^ (1 / σ₀) ≤ D ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hD1.le (by rw [div_le_one (by linarith)]; exact hσ₀)
    rw [Real.rpow_one] at this
    linarith

/-- **Mass bound** (for B.3): `Σ_{p<w, s_p ≤ M} g(p)V(p) ≤ (M + 1) V(w)` uniformly for
`D ≥ D₁`, `D^{1/S₁} ≤ w ≤ D^{1/σ₀}`. -/
theorem mass_sp_le (b : ℕ) (hb : 2 ≤ b) {M σ₀ S₁ : ℝ} (hM : 0 ≤ M) (hσ₀ : 1 ≤ σ₀) (hσS : σ₀ ≤ S₁) :
    ∃ D₁ : ℝ, 1 < D₁ ∧ ∀ D : ℝ, D₁ ≤ D → ∀ w : ℝ, D ^ (1 / S₁) ≤ w → w ≤ D ^ (1 / σ₀) →
      ∑ p ∈ (primesBelow w).filter (fun p : ℕ => Real.log D / Real.log p - 1 ≤ M), gB b p * VB b p ≤
        (M + 1) * VB b w := by
  obtain ⟨y₀, hy₀, hasym⟩ := cum_sp_asymp b hb hM (by norm_num : (0 : ℝ) < 1)
  have hS : 0 < S₁ := by linarith
  refine ⟨y₀ ^ S₁, Real.one_lt_rpow hy₀ hS, fun D hD w hw1 hw2 => ?_⟩
  obtain ⟨hD1, hyw, hwD⟩ := range_setup hy₀ hS hσ₀ hD hw1 hw2
  have hw1' : 1 < w := lt_of_lt_of_le hy₀ hyw
  have hlw : 0 < Real.log w := Real.log_pos hw1'
  have hlwD : Real.log w ≤ Real.log D := Real.log_le_log (by linarith) hwD
  have hs1 : 1 ≤ Real.log D / Real.log w := by rw [le_div_iff₀ hlw]; linarith
  have hφ : (max M (Real.log D / Real.log w - 1) - (Real.log D / Real.log w - 1)) /
      (Real.log D / Real.log w) ≤ M := by
    have h0 : 0 ≤ max M (Real.log D / Real.log w - 1) - (Real.log D / Real.log w - 1) := by
      linarith [le_max_right M (Real.log D / Real.log w - 1)]
    have h1 : max M (Real.log D / Real.log w - 1) - (Real.log D / Real.log w - 1) ≤ M := by
      rcases le_total M (Real.log D / Real.log w - 1) with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    exact (div_le_self h0 hs1).trans h1
  have hV := VB_pos' b w
  have := (abs_le.1 (hasym D w hyw hwD M hM le_rfl)).2
  rw [cum_sp_eq b (by linarith) w (by linarith : (0 : ℝ) < 1 + M)]
  have := mul_le_mul_of_nonneg_right hφ hV.le
  nlinarith

/-- **Mass bound**, strict cut `s_p < M`. -/
theorem mass_sp_lt_le (b : ℕ) (hb : 2 ≤ b) {M σ₀ S₁ : ℝ} (hM : 0 ≤ M) (hσ₀ : 1 ≤ σ₀) (hσS : σ₀ ≤ S₁) :
    ∃ D₁ : ℝ, 1 < D₁ ∧ ∀ D : ℝ, D₁ ≤ D → ∀ w : ℝ, D ^ (1 / S₁) ≤ w → w ≤ D ^ (1 / σ₀) →
      ∑ p ∈ (primesBelow w).filter (fun p : ℕ => Real.log D / Real.log p - 1 < M), gB b p * VB b p ≤
        (M + 1) * VB b w := by
  obtain ⟨D₁, hD₁, h⟩ := mass_sp_le b hb hM hσ₀ hσS
  refine ⟨D₁, hD₁, fun D hD w hw1 hw2 => le_trans ?_ (h D hD w hw1 hw2)⟩
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_)
    (fun p _ _ => mul_nonneg (gB_nonneg b p) (VB_pos' b p).le)
  rw [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, hp.2.le⟩

/-! ## Lemma B.2 -/

/-- **Lemma B.2 (uniform one-dimensional prime sums).** Let `1 ≤ c < M`, `1 ≤ σ₀ ≤ S₁`, `ψ` continuous on
`[c, M]` and `ψ = 0` on `(M, ∞)`. For every `ε > 0` there is `D₁ > 1` such that for all `D ≥ D₁` and all `w`
with `D^{1/S₁} ≤ w ≤ D^{1/σ₀}`, with `s = log D / log w` and `s_p = log D / log p − 1`:
`|Σ_{p<w, s_p ≥ c} g(p) V(p) ψ(s_p) − V(w) · s⁻¹ ∫_{u > max(s−1, c)} ψ(u)| ≤ ε V(w)`. -/
theorem primeSum1 (b : ℕ) (hb : 2 ≤ b) {c M σ₀ S₁ : ℝ} (hc : 1 ≤ c) (hcM : c < M)
    (hσ₀ : 1 ≤ σ₀) (hσS : σ₀ ≤ S₁) {ψ : ℝ → ℝ} (hψ : ContinuousOn ψ (Set.Icc c M))
    (hψM : ∀ u, M < u → ψ u = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ D₁ : ℝ, 1 < D₁ ∧ ∀ D : ℝ, D₁ ≤ D → ∀ w : ℝ, D ^ (1 / S₁) ≤ w → w ≤ D ^ (1 / σ₀) →
      |∑ p ∈ (primesBelow w).filter (fun p : ℕ => c ≤ Real.log D / Real.log p - 1),
          gB b p * VB b p * ψ (Real.log D / Real.log p - 1) -
        VB b w * ((Real.log D / Real.log w)⁻¹ *
          ∫ u in Set.Ioi (max (Real.log D / Real.log w - 1) c), ψ u)| ≤ ε * VB b w := by
  -- bound, uniform continuity, grid
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hψ
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB c ⟨le_rfl, hcM.le⟩)
  have hBabs : ∀ t ∈ Set.Icc c M, |ψ t| ≤ B := fun t ht => by rw [← Real.norm_eq_abs]; exact hB t ht
  have hMc : 0 < M - c + 1 := by linarith
  set ω : ℝ := ε / (4 * (M - c + 1)) with hω_def
  have hω0 : 0 < ω := by positivity
  obtain ⟨ρ, hρ, hρψ⟩ :=
    Metric.uniformContinuousOn_iff.1 (isCompact_Icc.uniformContinuousOn_of_continuous hψ) ω hω0
  set N : ℕ := ⌈(M - c) / ρ⌉₊ + 1 with hN_def
  have hNcast : (N : ℝ) = (⌈(M - c) / ρ⌉₊ : ℝ) + 1 := by rw [hN_def]; push_cast; ring
  have hNpos : (0 : ℝ) < N := by rw [hNcast]; positivity
  set h : ℝ := (M - c) / N with hh_def
  have hh0 : 0 ≤ h := div_nonneg (by linarith) hNpos.le
  have hhρ : h < ρ := by
    have h1 : (M - c) / ρ ≤ (⌈(M - c) / ρ⌉₊ : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ hρ] at h1
    rw [hh_def, div_lt_iff₀ hNpos, hNcast]; nlinarith
  have hNh : (N : ℝ) * h = M - c := by rw [hh_def]; field_simp
  set u : ℕ → ℝ := fun i => c + (i : ℝ) * h with hu_def
  have hu0 : u 0 = c := by simp [hu_def]
  have huN : u N = M := by simp only [hu_def]; linarith
  have hmono : ∀ i, u i ≤ u (i + 1) := by intro i; simp only [hu_def]; push_cast; nlinarith
  have hge : ∀ i, c ≤ u i := fun i => by
    simp only [hu_def]; nlinarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
  have hle : ∀ i, i ≤ N → u i ≤ M := by
    intro i hi
    have : (i : ℝ) ≤ N := by exact_mod_cast hi
    simp only [hu_def]; nlinarith
  have hosc : ∀ i < N, ∀ t, u i < t → t ≤ u (i + 1) → |ψ t - ψ (u (i + 1))| ≤ ω := by
    intro i hi t h1 h2
    have hstep : u (i + 1) = u i + h := by simp only [hu_def]; push_cast; ring
    have hui1 : u (i + 1) ≤ M := hle (i + 1) (Nat.succ_le_of_lt hi)
    have hdist : dist t (u (i + 1)) < ρ := by
      rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
    have := hρψ t ⟨by linarith [hge i], by linarith⟩ (u (i + 1)) ⟨hge (i + 1), hui1⟩ hdist
    rw [Real.dist_eq] at this; exact this.le
  have hint : IntegrableOn ψ (Set.Ioi c) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hcM.le]
    exact (hψ.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).union
      ((integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Set.Ioi M)).congr_fun
        (fun x hx => (hψM x hx).symm) measurableSet_Ioi)
  -- the Mertens precision δ
  set δ : ℝ := min 1 (ε / (2 * (2 * N + 3) * (B + 1))) with hδ_def
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ * ((2 * N + 3) * (B + 1)) ≤ ε / 2 := by
    have h1 : δ ≤ ε / (2 * (2 * N + 3) * (B + 1)) := min_le_right _ _
    have hpos : 0 < (2 * (N : ℝ) + 3) * (B + 1) := by positivity
    calc δ * ((2 * N + 3) * (B + 1)) ≤ ε / (2 * (2 * N + 3) * (B + 1)) * ((2 * N + 3) * (B + 1)) :=
          mul_le_mul_of_nonneg_right h1 hpos.le
      _ = ε / 2 := by
          rw [div_mul_eq_mul_div, div_eq_div_iff (by positivity) (by norm_num)]; ring
  have hωε : ω * (2 * (M - c) + 2) = ε / 2 := by
    rw [hω_def, div_mul_eq_mul_div, div_eq_div_iff (by positivity) (by norm_num)]; ring
  obtain ⟨y₀, hy₀, hasym⟩ := cum_sp_asymp b hb (M := M) (by linarith) hδ0
  have hS : 0 < S₁ := by linarith
  refine ⟨y₀ ^ S₁, Real.one_lt_rpow hy₀ hS, fun D hD w hw1 hw2 => ?_⟩
  obtain ⟨hD1, hyw, hwD⟩ := range_setup hy₀ hS hσ₀ hD hw1 hw2
  have hD0 : 0 < D := by linarith
  have hw1' : 1 < w := lt_of_lt_of_le hy₀ hyw
  have hlw : 0 < Real.log w := Real.log_pos hw1'
  have hlwD : Real.log w ≤ Real.log D := Real.log_le_log (by linarith) hwD
  have hs1 : 1 ≤ Real.log D / Real.log w := by rw [le_div_iff₀ hlw]; linarith
  have hs0 : 0 < Real.log D / Real.log w := by linarith
  have hV0 : 0 < VB b w := VB_pos' b w
  -- weights and points
  have hf0 : ∀ p ∈ primesBelow w, 0 ≤ (fun p : ℕ => gB b p * VB b p) p :=
    fun p _ => mul_nonneg (gB_nonneg b p) (VB_pos' b p).le
  -- cumulative mass against its limit
  have hcumV : ∀ t, 0 ≤ t → t ≤ M →
      |cum (primesBelow w) (fun p : ℕ => gB b p * VB b p) (fun p : ℕ => Real.log D / Real.log p - 1) t -
        (max t (Real.log D / Real.log w - 1) - (Real.log D / Real.log w - 1)) /
          (Real.log D / Real.log w) * VB b w| ≤ δ * VB b w := by
    intro t ht0 htM
    have e : cum (primesBelow w) (fun p : ℕ => gB b p * VB b p) (fun p : ℕ => Real.log D / Real.log p - 1) t =
        VB b (min (D ^ (1 / (1 + t))) w) - VB b w := by
      rw [← cum_sp_eq b hD0 w (by linarith : (0 : ℝ) < 1 + t)]
      simp only [cum, ind, mul_ite, mul_one, mul_zero, Finset.sum_filter]
    rw [e]
    exact hasym D w hyw hwD t ht0 htM
  -- the sum as a sum over all primes below `w`
  have hS_eq : ∑ p ∈ (primesBelow w).filter (fun p : ℕ => c ≤ Real.log D / Real.log p - 1),
        gB b p * VB b p * ψ (Real.log D / Real.log p - 1) =
      ∑ p ∈ primesBelow w, (fun p : ℕ => gB b p * VB b p) p *
        (if c ≤ (fun p : ℕ => Real.log D / Real.log p - 1) p then
          ψ ((fun p : ℕ => Real.log D / Real.log p - 1) p) else 0) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    split_ifs <;> simp
  rw [hS_eq]
  have E1 := step_bound (primesBelow w) (fun p : ℕ => gB b p * VB b p)
    (fun p : ℕ => Real.log D / Real.log p - 1) hf0 ψ hu0 huN hmono hδ0
    (hBabs c ⟨le_rfl, hcM.le⟩) hψM hosc
  have E3 := cont_step ψ (a := Real.log D / Real.log w - 1) hu0 huN hmono hs0 hint hψM hosc
  set Φ : ℝ → ℝ := cum (primesBelow w) (fun p : ℕ => gB b p * VB b p)
    (fun p : ℕ => Real.log D / Real.log p - 1) with hΦ_def
  set s := Real.log D / Real.log w with hs_def
  set V := VB b w with hV_def
  set φ : ℝ → ℝ := fun t => (max t (s - 1) - (s - 1)) / s with hφ_def
  set S := ∑ p ∈ primesBelow w, (fun p : ℕ => gB b p * VB b p) p *
        (if c ≤ (fun p : ℕ => Real.log D / Real.log p - 1) p then
          ψ ((fun p : ℕ => Real.log D / Real.log p - 1) p) else 0) with hS_def
  set T := ∑ i ∈ range N, ψ (u (i + 1)) * (Φ (u (i + 1)) - Φ (u i)) with hT_def
  set Sc := ∑ i ∈ range N, ψ (u (i + 1)) * ((max (u (i + 1)) (s - 1) - max (u i) (s - 1)) / s) with hSc_def
  set I := ∫ t in Set.Ioi (max (s - 1) c), ψ t with hI_def
  have hcumV' : ∀ t, 0 ≤ t → t ≤ M → |Φ t - φ t * V| ≤ δ * V := hcumV
  -- E2: the step sums
  have hterm : ∀ i ∈ range N, |ψ (u (i + 1)) * ((Φ (u (i + 1)) - φ (u (i + 1)) * V) - (Φ (u i) - φ (u i) * V))| ≤
      B * (2 * δ * V) := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    rw [abs_mul]
    have hb1 := hBabs (u (i + 1)) ⟨hge _, hle _ (Nat.succ_le_of_lt hi')⟩
    have hc1 := hcumV' (u (i + 1)) (by linarith [hge (i + 1)]) (hle _ (Nat.succ_le_of_lt hi'))
    have hc2 := hcumV' (u i) (by linarith [hge i]) (hle _ hi'.le)
    have h3 : |(Φ (u (i + 1)) - φ (u (i + 1)) * V) - (Φ (u i) - φ (u i) * V)| ≤ 2 * δ * V :=
      (abs_sub _ _).trans (by linarith)
    exact mul_le_mul hb1 h3 (abs_nonneg _) hB0
  have E2 : |T - V * Sc| ≤ N * (B * (2 * δ * V)) := by
    have e : T - V * Sc = ∑ i ∈ range N,
        ψ (u (i + 1)) * ((Φ (u (i + 1)) - φ (u (i + 1)) * V) - (Φ (u i) - φ (u i) * V)) := by
      rw [hT_def, hSc_def, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [hφ_def]; ring
    rw [e]
    calc _ ≤ ∑ i ∈ range N, |ψ (u (i + 1)) * ((Φ (u (i + 1)) - φ (u (i + 1)) * V) -
            (Φ (u i) - φ (u i) * V))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ range N, B * (2 * δ * V) := Finset.sum_le_sum hterm
      _ = N * (B * (2 * δ * V)) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- the limit cumulative function
  have hφ1 : φ c * V - φ (c - δ) * V ≤ δ * V := by
    rw [← sub_mul]
    refine mul_le_mul_of_nonneg_right ?_ hV0.le
    simp only [hφ_def]
    have := max_sub_max_le' (s - 1) (show c - δ ≤ c by linarith)
    rw [div_sub_div_same]; exact div_le_of_one_le' hs1 (by linarith) hδ0.le
  have hφ2 : φ M * V - φ c * V ≤ (M - c) * V := by
    rw [← sub_mul]
    refine mul_le_mul_of_nonneg_right ?_ hV0.le
    simp only [hφ_def]
    have := max_sub_max_le' (s - 1) hcM.le
    rw [div_sub_div_same]; exact div_le_of_one_le' hs1 (by linarith) (by linarith)
  have hφ3 : (max M (s - 1) - max c (s - 1)) / s ≤ M - c := by
    have := max_sub_max_le' (s - 1) hcM.le
    exact div_le_of_one_le' hs1 this (by linarith)
  have hc_c := abs_le.1 (hcumV' c (by linarith) hcM.le)
  have hc_cδ := abs_le.1 (hcumV' (c - δ) (by linarith) (by linarith))
  have hc_M := abs_le.1 (hcumV' M (by linarith) le_rfl)
  -- E1 in terms of `V`
  have E1' : |S - T| ≤ B * (3 * δ * V) + ω * ((M - c) * V + 2 * δ * V) := by
    refine E1.trans (add_le_add (mul_le_mul_of_nonneg_left ?_ hB0) (mul_le_mul_of_nonneg_left ?_ hω0.le))
    · linarith [hc_c.2, hc_cδ.1]
    · linarith [hc_M.2, hc_c.1]
  have E3' : V * |Sc - s⁻¹ * I| ≤ V * (ω * (M - c)) := by
    refine mul_le_mul_of_nonneg_left (E3.trans ?_) hV0.le
    exact mul_le_mul_of_nonneg_left hφ3 hω0.le
  have key : |S - V * (s⁻¹ * I)| ≤ |S - T| + |T - V * Sc| + V * |Sc - s⁻¹ * I| := by
    have e : S - V * (s⁻¹ * I) = (S - T) + (T - V * Sc) + V * (Sc - s⁻¹ * I) := by ring
    rw [e]
    calc _ ≤ |(S - T) + (T - V * Sc)| + |V * (Sc - s⁻¹ * I)| := abs_add_le _ _
      _ ≤ |S - T| + |T - V * Sc| + V * |Sc - s⁻¹ * I| := by
          rw [abs_mul, abs_of_pos hV0]; linarith [abs_add_le (S - T) (T - V * Sc)]
  -- the budget
  have hfin : B * (3 * δ * V) + ω * ((M - c) * V + 2 * δ * V) + N * (B * (2 * δ * V)) + V * (ω * (M - c))
      ≤ ε * V := by
    have e : B * (3 * δ * V) + ω * ((M - c) * V + 2 * δ * V) + N * (B * (2 * δ * V)) + V * (ω * (M - c)) =
        (δ * ((2 * N + 3) * B)) * V + (ω * (2 * (M - c) + 2 * δ)) * V := by ring
    rw [e]
    have h1 : δ * ((2 * N + 3) * B) ≤ ε / 2 := by
      refine le_trans ?_ hδε
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hδ0.le
    have h2 : ω * (2 * (M - c) + 2 * δ) ≤ ε / 2 := by
      rw [← hωε]; exact mul_le_mul_of_nonneg_left (by linarith) hω0.le
    have h1' := mul_le_mul_of_nonneg_right h1 hV0.le
    have h2' := mul_le_mul_of_nonneg_right h2 hV0.le
    linarith
  linarith

/-! ## Forms for B.3 (E5) -/

/-- `s ≤ S₁ → D^{1/S₁} ≤ w` and `σ₀ ≤ s → w ≤ D^{1/σ₀}` (`s = log D / log w`, `D, w > 1`). -/
theorem rpow_bounds_of_s {D w σ₀ S₁ : ℝ} (hD : 1 < D) (hw : 1 < w) (hσ₀ : 0 < σ₀)
    (h1 : σ₀ ≤ Real.log D / Real.log w) (h2 : Real.log D / Real.log w ≤ S₁) :
    D ^ (1 / S₁) ≤ w ∧ w ≤ D ^ (1 / σ₀) := by
  have hlw : 0 < Real.log w := Real.log_pos hw
  have hS : 0 < S₁ := by linarith [div_pos (Real.log_pos hD) hlw]
  have hD0 : 0 < D := by linarith
  rw [div_le_iff₀ hlw] at h2
  rw [le_div_iff₀ hlw] at h1
  constructor
  · rw [← Real.log_le_log_iff (Real.rpow_pos_of_pos hD0 _) (by linarith), Real.log_rpow hD0, one_div,
      inv_mul_le_iff₀ hS]
    linarith
  · rw [← Real.log_le_log_iff (by linarith) (Real.rpow_pos_of_pos hD0 _), Real.log_rpow hD0, one_div,
      le_inv_mul_iff₀ hσ₀]
    linarith

/-- **B.2, `s`-form**: the hypotheses `D^{1/S₁} ≤ w ≤ D^{1/σ₀}` replaced by `1 < w`, `σ₀ ≤ s ≤ S₁`. -/
theorem primeSum1_s (b : ℕ) (hb : 2 ≤ b) {c M σ₀ S₁ : ℝ} (hc : 1 ≤ c) (hcM : c < M)
    (hσ₀ : 1 ≤ σ₀) (hσS : σ₀ ≤ S₁) {ψ : ℝ → ℝ} (hψ : ContinuousOn ψ (Set.Icc c M))
    (hψM : ∀ u, M < u → ψ u = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ D₁ : ℝ, 1 < D₁ ∧ ∀ D : ℝ, D₁ ≤ D → ∀ w : ℝ, 1 < w →
      σ₀ ≤ Real.log D / Real.log w → Real.log D / Real.log w ≤ S₁ →
      |∑ p ∈ (primesBelow w).filter (fun p : ℕ => c ≤ Real.log D / Real.log p - 1),
          gB b p * VB b p * ψ (Real.log D / Real.log p - 1) -
        VB b w * ((Real.log D / Real.log w)⁻¹ *
          ∫ u in Set.Ioi (max (Real.log D / Real.log w - 1) c), ψ u)| ≤ ε * VB b w := by
  obtain ⟨D₁, hD₁, h⟩ := primeSum1 b hb hc hcM hσ₀ hσS hψ hψM hε
  refine ⟨D₁, hD₁, fun D hD w hw h1 h2 => ?_⟩
  obtain ⟨hw1, hw2⟩ := rpow_bounds_of_s (lt_of_lt_of_le hD₁ hD) hw (by linarith) h1 h2
  exact h D hD w hw1 hw2

/-- **B.2 for `B⁻` (`c = 1`, `s ≥ 2`)**: the sum runs over all primes `p < w`, and the integral is over
`u > s − 1` (the form of `betaM (k+1)`). For `w ≤ D^{1/2}` every prime `p < w` has `s_p > s − 1 ≥ 1`. -/
theorem primeSum1_all (b : ℕ) (hb : 2 ≤ b) {M S₁ : ℝ} (hM : 1 < M) (hS : 2 ≤ S₁)
    {ψ : ℝ → ℝ} (hψ : ContinuousOn ψ (Set.Icc 1 M)) (hψM : ∀ u, M < u → ψ u = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ D₁ : ℝ, 1 < D₁ ∧ ∀ D : ℝ, D₁ ≤ D → ∀ w : ℝ, D ^ (1 / S₁) ≤ w → w ≤ D ^ (1 / (2 : ℝ)) →
      |∑ p ∈ primesBelow w, gB b p * VB b p * ψ (Real.log D / Real.log p - 1) -
        VB b w * ((Real.log D / Real.log w)⁻¹ *
          ∫ u in Set.Ioi (Real.log D / Real.log w - 1), ψ u)| ≤ ε * VB b w := by
  obtain ⟨D₁, hD₁, h⟩ := primeSum1 b hb le_rfl hM (by norm_num) hS hψ hψM hε
  refine ⟨D₁, hD₁, fun D hD w hw1 hw2 => ?_⟩
  have hD1 : 1 < D := lt_of_lt_of_le hD₁ hD
  have hD0 : 0 < D := by linarith
  have hw1' : 1 < w :=
    lt_of_lt_of_le (Real.one_lt_rpow hD1 (by positivity)) hw1
  have hlw : 0 < Real.log w := Real.log_pos hw1'
  have hs2 : 2 ≤ Real.log D / Real.log w := by
    have := Real.log_le_log (by linarith) hw2
    rw [Real.log_rpow hD0] at this
    rw [le_div_iff₀ hlw]; linarith
  have hfilt : (primesBelow w).filter (fun p : ℕ => 1 ≤ Real.log D / Real.log p - 1) = primesBelow w := by
    refine Finset.filter_true_of_mem (fun p hp => ?_)
    rw [mem_primesBelow] at hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.1.one_lt
    have := (lt_iff_s_sub_one_lt_sp hD1 hp1 hw1').1 hp.2
    linarith
  have hmax : max (Real.log D / Real.log w - 1) 1 = Real.log D / Real.log w - 1 :=
    max_eq_left (by linarith)
  have := h D hD w hw1 hw2
  rwa [hfilt, hmax] at this

/-- **B.2 for `B⁺` (`c = 2`)**: the closed end as `p³ ≤ D` (`headOK true`), the integral over
`u > max(s − 1, 2)` (the form of `betaP (k+1)`). -/
theorem primeSum1_cube (b : ℕ) (hb : 2 ≤ b) {M σ₀ S₁ : ℝ} (hM : 2 < M) (hσ₀ : 1 ≤ σ₀) (hσS : σ₀ ≤ S₁)
    {ψ : ℝ → ℝ} (hψ : ContinuousOn ψ (Set.Icc 2 M)) (hψM : ∀ u, M < u → ψ u = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ D₁ : ℝ, 1 < D₁ ∧ ∀ D : ℝ, D₁ ≤ D → ∀ w : ℝ, D ^ (1 / S₁) ≤ w → w ≤ D ^ (1 / σ₀) →
      |∑ p ∈ (primesBelow w).filter (fun p : ℕ => (p : ℝ) ^ 3 ≤ D),
          gB b p * VB b p * ψ (Real.log D / Real.log p - 1) -
        VB b w * ((Real.log D / Real.log w)⁻¹ *
          ∫ u in Set.Ioi (max (Real.log D / Real.log w - 1) 2), ψ u)| ≤ ε * VB b w := by
  obtain ⟨D₁, hD₁, h⟩ := primeSum1 b hb (by norm_num) hM hσ₀ hσS hψ hψM hε
  refine ⟨D₁, hD₁, fun D hD w hw1 hw2 => ?_⟩
  have hD0 : 0 < D := by linarith [lt_of_lt_of_le hD₁ hD]
  have hfilt : (primesBelow w).filter (fun p : ℕ => (p : ℝ) ^ 3 ≤ D) =
      (primesBelow w).filter (fun p : ℕ => 2 ≤ Real.log D / Real.log p - 1) := by
    refine Finset.filter_congr (fun p hp => ?_)
    rw [mem_primesBelow] at hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.1.one_lt
    exact (two_le_sp_iff hD0 hp1).symm
  rw [hfilt]
  exact h D hD w hw1 hw2

end Palprimes.E1
