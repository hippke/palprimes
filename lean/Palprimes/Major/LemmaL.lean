import Palprimes.Major.Trig

/-! # Lemma L (dossier §2.13.2) with weights `ω₁ = 57/50`, `ω_M = 19/25` (`M ≥ 2`)

`Λ(t) = (1/sin πt) Σ_{1≤M≤0.7/t} ω_M sin²(πMt)/M² ≥ 1` on `(0, 1/2]`, in the form
`sin(πt) ≤ LamS n t` for every `n` with `(n+1)t > 7/10` (extra terms are `≥ 0`).
* `t ≤ 1/100`: sum ≥ integral of the antitone `g(x) = sin²(πx)/x²`, integral ≥ a lower Riemann sum
  (`intOK`, kernel-checked);
* `1/100 ≤ t ≤ 35/100`: adaptive cells with first-order (Lipschitz) remainders (`cellRec`, kernel-checked);
* `35/100 ≤ t ≤ 1/2`: `ω₁ sin(0.35π) ≥ 1` (`regC`, kernel-checked). -/

set_option linter.style.longLine false

open Finset Real

namespace Palprimes

/-- The weights. -/
noncomputable def omg (M : ℕ) : ℝ := if M = 1 then 57 / 50 else 19 / 25
def omN (M : ℕ) : ℕ := if M = 1 then 57 else 19
def omD (M : ℕ) : ℕ := if M = 1 then 50 else 25

theorem omg_eq (M : ℕ) : omg M = (omN M : ℝ) / omD M := by
  unfold omg omN omD; split_ifs <;> norm_num

theorem omg_ge (M : ℕ) : (19 / 25 : ℝ) ≤ omg M := by unfold omg; split_ifs <;> norm_num
theorem omg_pos (M : ℕ) : 0 < omg M := lt_of_lt_of_le (by norm_num) (omg_ge M)
theorem omD_pos (M : ℕ) : 0 < omD M := by unfold omD; split_ifs <;> norm_num

/-- One term `ω_k sin²(πkt)/k²`. -/
noncomputable def lamTerm (t : ℝ) (k : ℕ) : ℝ := omg k * Real.sin (π * k * t) ^ 2 / (k : ℝ) ^ 2

/-- `Σ_{M<n} ω_{M+1} sin²(π(M+1)t)/(M+1)²`. -/
noncomputable def LamS (n : ℕ) (t : ℝ) : ℝ := ∑ M ∈ range n, lamTerm t (M + 1)

theorem lamTerm_nonneg (t : ℝ) (k : ℕ) : 0 ≤ lamTerm t k := by
  unfold lamTerm; have := omg_pos k; positivity

theorem LamS_mono (t : ℝ) {k n : ℕ} (h : k ≤ n) : LamS k t ≤ LamS n t := by
  unfold LamS
  exact Finset.sum_le_sum_of_subset_of_nonneg (range_subset_range.2 h) (fun i _ _ => lamTerm_nonneg t _)

/-- `sin² a − sin² b = sin(a − b) sin(a + b)`. -/
theorem sin_sq_sub_sin_sq' (a b : ℝ) : Real.sin a ^ 2 - Real.sin b ^ 2 = Real.sin (a - b) * Real.sin (a + b) := by
  rw [Real.sin_sub, Real.sin_add]
  have ha := Real.sin_sq_add_cos_sq a
  have hb := Real.sin_sq_add_cos_sq b
  linear_combination (Real.sin b ^ 2) * ha - (Real.sin a ^ 2) * hb

theorem sin_sq_lip (a b : ℝ) : Real.sin b ^ 2 - |a - b| ≤ Real.sin a ^ 2 := by
  have h := sin_sq_sub_sin_sq' a b
  have h1 : |Real.sin (a - b) * Real.sin (a + b)| ≤ |a - b| := by
    rw [abs_mul]
    calc |Real.sin (a - b)| * |Real.sin (a + b)| ≤ |a - b| * 1 :=
          mul_le_mul Real.abs_sin_le_abs (Real.abs_sin_le_one _) (abs_nonneg _) (abs_nonneg _)
      _ = _ := mul_one _
  have := (abs_le.1 h1).1
  linarith

/-! ## Cells -/

def posTerm (c D M : ℕ) : ℕ := omN M * sinPiLo (M * c) D ^ 2 / (omD M * M ^ 2)
def penTerm (w D M : ℕ) : ℕ := (omN M * Ph * w * Sc ^ 2 + (omD M * Pd * D * M - 1)) / (omD M * Pd * D * M)

def posSum (c D : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => posSum c D k + posTerm c D (k + 1)

def penSum (w D : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => penSum w D k + penTerm w D (k + 1)

/-- One cell `[lo/D, hi/D]`. -/
def cellOK (lo hi D : ℕ) : Bool :=
  decide (0 < lo) && decide (lo ≤ hi) && decide (2 * hi ≤ D) &&
    decide (penSum (hi - lo) (2 * D) (7 * D / (10 * hi)) + sinPiHi hi D * Sc ≤
      posSum (lo + hi) (2 * D) (7 * D / (10 * hi)))

/-- Adaptive bisection. -/
def cellRec : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, lo, hi, D => cellOK lo hi D
  | f + 1, lo, hi, D => cellOK lo hi D || (cellRec f (2 * lo) (lo + hi) (2 * D) && cellRec f (lo + hi) (2 * hi) (2 * D))

theorem posSum_eq (c D : ℕ) (k : ℕ) : (posSum c D k : ℝ) = ∑ M ∈ range k, (posTerm c D (M + 1) : ℝ) := by
  induction k with
  | zero => simp [posSum]
  | succ k ih => rw [posSum, Nat.cast_add, ih, Finset.sum_range_succ]

theorem penSum_eq (w D : ℕ) (k : ℕ) : (penSum w D k : ℝ) = ∑ M ∈ range k, (penTerm w D (M + 1) : ℝ) := by
  induction k with
  | zero => simp [penSum]
  | succ k ih => rw [penSum, Nat.cast_add, ih, Finset.sum_range_succ]

/-- Termwise bound on a cell with centre `c/D` and radius `w/D` (here `D` is the doubled denominator). -/
theorem lamTerm_ge (c w D k : ℕ) (hD : 0 < D) (hk : 0 < k) (t : ℝ) (ht : |t - c / D| ≤ w / D) :
    (posTerm c D k : ℝ) / (Sc : ℝ) ^ 2 - (penTerm w D k : ℝ) / (Sc : ℝ) ^ 2 ≤ lamTerm t k := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hSc := Sc_pos
  have hom := omg_eq k
  have hodp : (0 : ℝ) < omD k := by exact_mod_cast omD_pos k
  have hPd : (0 : ℝ) < Pd := by norm_num [Pd]
  -- the sine at the centre
  have hs := sinPiLo_le (k * c) D hD
  set s : ℝ := (sinPiLo (k * c) D : ℝ) with hsdef
  have hs0 : 0 ≤ s := by positivity
  have hsq : (s / Sc) ^ 2 ≤ Real.sin (π * ((k * c : ℕ) : ℝ) / D) ^ 2 := by
    rw [← sq_abs (Real.sin _)]; exact pow_le_pow_left₀ (by positivity) hs 2
  -- Lipschitz step
  have hlip := sin_sq_lip (π * k * t) (π * ((k * c : ℕ) : ℝ) / D)
  have hdist : |π * k * t - π * ((k * c : ℕ) : ℝ) / D| ≤ π * k * (w / D) := by
    have e : π * k * t - π * ((k * c : ℕ) : ℝ) / D = (π * k) * (t - c / D) := by
      push_cast; field_simp
    rw [e, abs_mul, abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left ht (by positivity)
  have hsin : (s / Sc) ^ 2 - π * k * (w / D) ≤ Real.sin (π * k * t) ^ 2 := by linarith
  -- posTerm
  have hpos : (posTerm c D k : ℝ) / (Sc : ℝ) ^ 2 ≤ omg k * (s / Sc) ^ 2 / (k : ℝ) ^ 2 := by
    have h1 : (posTerm c D k : ℝ) ≤ ((omN k * sinPiLo (k * c) D ^ 2 : ℕ) : ℝ) / ((omD k * k ^ 2 : ℕ) : ℝ) :=
      Nat.cast_div_le
    rw [div_le_iff₀ (by positivity)]
    refine le_trans h1 (le_of_eq ?_)
    rw [hom, hsdef]; push_cast; field_simp
  -- penTerm
  have hpen : omg k * (π * k * (w / D)) / (k : ℝ) ^ 2 ≤ (penTerm w D k : ℝ) / (Sc : ℝ) ^ 2 := by
    have hd : 0 < omD k * Pd * D * k := by
      have := omD_pos k; simp only [Pd]; positivity
    have h1 := le_ceil_div (omN k * Ph * w * Sc ^ 2) (omD k * Pd * D * k) hd
    rw [le_div_iff₀ (by positivity)]
    refine le_trans ?_ h1
    rw [hom]; push_cast
    have hPh : π * Pd ≤ (Ph : ℝ) := by have := pi_hi; rw [lt_div_iff₀ hPd] at this; linarith
    rw [show (omN k : ℝ) / omD k * (π * k * (w / D)) / (k : ℝ) ^ 2 * (Sc : ℝ) ^ 2 =
        (omN k * (π * Pd) * w * Sc ^ 2) / (omD k * Pd * D * k) by field_simp]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : (0 : ℝ) ≤ omN k * w * Sc ^ 2 := by positivity
    nlinarith
  unfold lamTerm
  have h3 : omg k * ((s / Sc) ^ 2 - π * k * (w / D)) / (k : ℝ) ^ 2 ≤ omg k * Real.sin (π * k * t) ^ 2 / (k : ℝ) ^ 2 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hsin (omg_pos k).le
  have h4 : omg k * ((s / Sc) ^ 2 - π * k * (w / D)) / (k : ℝ) ^ 2 =
      omg k * (s / Sc) ^ 2 / (k : ℝ) ^ 2 - omg k * (π * k * (w / D)) / (k : ℝ) ^ 2 := by ring
  linarith

theorem cellOK_sound (lo hi D : ℕ) (h : cellOK lo hi D = true) (t : ℝ) (ht1 : (lo : ℝ) / D ≤ t)
    (ht2 : t ≤ (hi : ℝ) / D) (n : ℕ) (hn : 7 / 10 < ((n : ℝ) + 1) * t) :
    Real.sin (π * t) ≤ LamS n t := by
  simp only [cellOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hlo, hlh⟩, hhD⟩, hmain⟩ := h
  have hD : 0 < D := by omega
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hhi' : (0 : ℝ) < hi := by exact_mod_cast (by omega : 0 < hi)
  have hSc := Sc_pos
  set n0 := 7 * D / (10 * hi) with hn0
  -- n0 ≤ n
  have hn0n : n0 ≤ n := by
    have h1 : 7 / 10 < ((n : ℝ) + 1) * (hi / D) :=
      lt_of_lt_of_le hn (mul_le_mul_of_nonneg_left ht2 (by positivity))
    have h2 : 7 * D < (n + 1) * (10 * hi) := by
      have : (7 : ℝ) * D < ((n : ℝ) + 1) * (10 * hi) := by
        rw [mul_div_assoc', lt_div_iff₀ hD'] at h1; linarith
      exact_mod_cast this
    have : n0 < n + 1 := (Nat.div_lt_iff_lt_mul (by omega)).2 h2
    omega
  refine le_trans ?_ (LamS_mono t hn0n)
  -- lower bound of LamS n0 t
  have hcell : |t - ((lo + hi : ℕ) : ℝ) / ((2 * D : ℕ) : ℝ)| ≤ ((hi - lo : ℕ) : ℝ) / ((2 * D : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hlh]
    have e1 : ((lo : ℝ) + hi) / (2 * D) - (hi - lo) / (2 * D) = lo / D := by field_simp; ring
    have e2 : ((lo : ℝ) + hi) / (2 * D) + (hi - lo) / (2 * D) = hi / D := by field_simp; ring
    rw [abs_le]; constructor <;> linarith
  have hsum : ((posSum (lo + hi) (2 * D) n0 : ℕ) : ℝ) / (Sc : ℝ) ^ 2 - ((penSum (hi - lo) (2 * D) n0 : ℕ) : ℝ) / (Sc : ℝ) ^ 2 ≤
      LamS n0 t := by
    rw [posSum_eq, penSum_eq, Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
    unfold LamS
    apply Finset.sum_le_sum
    intro M _
    exact lamTerm_ge (lo + hi) (hi - lo) (2 * D) (M + 1) (by omega) (by omega) t hcell
  -- the denominator side
  have hsinhi : Real.sin (π * t) ≤ (sinPiHi hi D : ℝ) / Sc := by
    have h1 := le_sinPiHi hi D hD
    have hhalf : (hi : ℝ) / D ≤ 1 / 2 := by
      rw [div_le_iff₀ hD']; have : (2 * hi : ℝ) ≤ D := by exact_mod_cast hhD
      linarith
    have ht0 : 0 ≤ t := le_trans (by positivity) ht1
    have h2 : Real.sin (π * t) ≤ Real.sin (π * hi / D) := by
      apply Real.sin_le_sin_of_le_of_le_pi_div_two
      · have : 0 ≤ π * t := by positivity
        linarith [Real.pi_pos]
      · rw [mul_div_assoc]; nlinarith [Real.pi_pos]
      · rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left ht2 Real.pi_pos.le
    exact le_trans h2 (le_trans (le_abs_self _) h1)
  have hmain' : (sinPiHi hi D : ℝ) / Sc ≤
      ((posSum (lo + hi) (2 * D) n0 : ℕ) : ℝ) / (Sc : ℝ) ^ 2 - ((penSum (hi - lo) (2 * D) n0 : ℕ) : ℝ) / (Sc : ℝ) ^ 2 := by
    have : ((penSum (hi - lo) (2 * D) n0 : ℕ) : ℝ) + (sinPiHi hi D : ℝ) * Sc ≤ (posSum (lo + hi) (2 * D) n0 : ℕ) := by
      exact_mod_cast hmain
    rw [div_sub_div_same, le_div_iff₀ (by positivity)]
    rw [div_mul_eq_mul_div, div_le_iff₀ hSc]
    nlinarith
  linarith

theorem cellRec_sound : ∀ (f lo hi D : ℕ), cellRec f lo hi D = true → ∀ t : ℝ, (lo : ℝ) / D ≤ t →
    t ≤ (hi : ℝ) / D → ∀ n : ℕ, 7 / 10 < ((n : ℝ) + 1) * t → Real.sin (π * t) ≤ LamS n t := by
  intro f
  induction f with
  | zero => intro lo hi D h; exact cellOK_sound lo hi D h
  | succ f ih =>
    intro lo hi D h t ht1 ht2
    simp only [cellRec, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h1, h2⟩
    · exact cellOK_sound lo hi D h t ht1 ht2
    · have e1 : ((2 * lo : ℕ) : ℝ) / ((2 * D : ℕ) : ℝ) = (lo : ℝ) / D := by
        push_cast; rw [mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
      have e2 : ((2 * hi : ℕ) : ℝ) / ((2 * D : ℕ) : ℝ) = (hi : ℝ) / D := by
        push_cast; rw [mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
      rcases le_total t (((lo + hi : ℕ) : ℝ) / ((2 * D : ℕ) : ℝ)) with ht | ht
      · exact ih _ _ _ h1 t (by rw [e1]; exact ht1) ht
      · exact ih _ _ _ h2 t ht (by rw [e2]; exact ht2)

/-! ## Small `t`: sum ≥ integral ≥ lower Riemann sum -/

/-- `g(x) = sin²(πx)/x²`. -/
noncomputable def gL (x : ℝ) : ℝ := Real.sin (π * x) ^ 2 / x ^ 2

theorem gL_nonneg (x : ℝ) : 0 ≤ gL x := by unfold gL; positivity

theorem gL_anti : AntitoneOn gL (Set.Ioc 0 1) := by
  intro x hx y hy hxy
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  have hc := strictConcaveOn_sin_Icc.concaveOn
  have hpy : π * y ∈ Set.Icc 0 π := ⟨by positivity, by nlinarith [Real.pi_pos]⟩
  have h0 : (0 : ℝ) ∈ Set.Icc 0 π := ⟨le_rfl, Real.pi_pos.le⟩
  have key := hc.2 hpy h0 (show (0 : ℝ) ≤ x / y by positivity)
    (show (0 : ℝ) ≤ 1 - x / y by rw [sub_nonneg, div_le_one hy0]; exact hxy) (show x / y + (1 - x / y) = 1 by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.sin_zero] at key
  have e : x / y * (π * y) = π * x := by field_simp
  rw [e] at key
  -- key : x / y * sin(π y) ≤ sin(π x)
  have hsy : 0 ≤ Real.sin (π * y) := Real.sin_nonneg_of_nonneg_of_le_pi hpy.1 hpy.2
  have hr : Real.sin (π * y) / y ≤ Real.sin (π * x) / x := by
    rw [div_le_div_iff₀ hy0 hx0]
    have := mul_le_mul_of_nonneg_left key hy0.le
    rw [← mul_assoc, mul_div_cancel₀ _ hy0.ne'] at this
    linarith
  unfold gL
  rw [← div_pow, ← div_pow]
  exact pow_le_pow_left₀ (by positivity) hr 2

/-- `∫_t^{(k+1)t} g ≤ t Σ_{M<k} g((M+1)t)`. -/
theorem int_le_sum (t : ℝ) (ht : 0 < t) (k : ℕ) (hk : ((k : ℝ) + 1) * t ≤ 1) :
    ∫ x in t..((k : ℝ) + 1) * t, gL x ≤ t * ∑ M ∈ range k, gL (((M : ℝ) + 1) * t) := by
  have hf : AntitoneOn (fun x => gL (t * x)) (Set.Icc 1 (1 + (k : ℝ))) := by
    intro x hx y hy hxy
    apply gL_anti
    · exact ⟨by nlinarith [hx.1], by nlinarith [hx.2]⟩
    · exact ⟨by nlinarith [hy.1], by nlinarith [hy.2]⟩
    · exact mul_le_mul_of_nonneg_left hxy ht.le
  have h := hf.integral_le_sum
  have e := intervalIntegral.smul_integral_comp_mul_left (a := 1) (b := 1 + (k : ℝ)) gL t
  rw [smul_eq_mul, mul_one, show t * (1 + (k : ℝ)) = ((k : ℝ) + 1) * t by ring] at e
  rw [← e]
  apply mul_le_mul_of_nonneg_left _ ht.le
  refine le_trans h (le_of_eq ?_)
  apply Finset.sum_congr rfl; intro M _; congr 1; ring

/-- `(1/100) Σ_{i<69} g((i+2)/100) ≤ ∫_{1/100}^{7/10} g`. -/
theorem sum_le_int : (1 / 100 : ℝ) * ∑ i ∈ range 69, gL (((i : ℝ) + 2) / 100) ≤ ∫ x in (1 / 100 : ℝ)..(7 / 10), gL x := by
  have hf : AntitoneOn (fun x => gL ((1 / 100) * x)) (Set.Icc 1 (1 + ((69 : ℕ) : ℝ))) := by
    intro x hx y hy hxy
    have := hx.2; have := hy.2; push_cast at *
    apply gL_anti
    · exact ⟨by nlinarith [hx.1], by nlinarith⟩
    · exact ⟨by nlinarith [hy.1], by nlinarith⟩
    · linarith
  have h := hf.sum_le_integral
  have e := intervalIntegral.smul_integral_comp_mul_left (a := 1) (b := 1 + ((69 : ℕ) : ℝ)) gL (1 / 100)
  rw [smul_eq_mul] at e
  have e2 : (1 / 100 : ℝ) * (1 + ((69 : ℕ) : ℝ)) = 7 / 10 := by norm_num
  rw [mul_one, e2] at e
  rw [← e]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  refine le_trans (le_of_eq ?_) h
  apply Finset.sum_congr rfl; intro i _; congr 1; push_cast; ring

theorem int_mono (t : ℝ) (ht0 : 0 < t) (ht : t ≤ 1 / 100) (k : ℕ) (hk1 : 7 / 10 ≤ ((k : ℝ) + 1) * t)
    (hk2 : ((k : ℝ) + 1) * t ≤ 1) :
    ∫ x in (1 / 100 : ℝ)..(7 / 10), gL x ≤ ∫ x in t..((k : ℝ) + 1) * t, gL x := by
  apply intervalIntegral.integral_mono_interval ht (by norm_num) hk1
  · exact Filter.Eventually.of_forall (fun x => gL_nonneg x)
  · apply AntitoneOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    exact gL_anti.mono (fun x hx => ⟨by linarith [hx.1], le_trans hx.2 hk2⟩)

def intTerm (i : ℕ) : ℕ := 1900 * sinPiLo (i + 2) 100 ^ 2 / (25 * (i + 2) ^ 2)

def intSum : ℕ → ℕ
  | 0 => 0
  | k + 1 => intSum k + intTerm k

/-- `Σ_{j=2}^{70} (19/25)·100·sin²(πj/100)/j² ≥ π`. -/
def intOK : Bool := decide ((Ph * Sc ^ 2 + (Pd - 1)) / Pd ≤ intSum 69)

theorem intSum_eq (k : ℕ) : (intSum k : ℝ) = ∑ i ∈ range k, (intTerm i : ℝ) := by
  induction k with
  | zero => simp [intSum]
  | succ k ih => rw [intSum, Nat.cast_add, ih, Finset.sum_range_succ]

theorem intOK_sound (h : intOK = true) :
    π ≤ ∑ i ∈ range 69, (19 / 25 : ℝ) * 100 * Real.sin (π * ((i : ℝ) + 2) / 100) ^ 2 / ((i : ℝ) + 2) ^ 2 := by
  simp only [intOK, decide_eq_true_eq] at h
  have hSc := Sc_pos
  have hPd : (0 : ℝ) < Pd := by norm_num [Pd]
  have h1 : π * (Sc : ℝ) ^ 2 ≤ intSum 69 := by
    have a := le_ceil_div (Ph * Sc ^ 2) Pd (by norm_num [Pd])
    have b : ((((Ph * Sc ^ 2 + (Pd - 1)) / Pd : ℕ)) : ℝ) ≤ intSum 69 := by exact_mod_cast h
    have c : π * (Sc : ℝ) ^ 2 ≤ ((Ph * Sc ^ 2 : ℕ) : ℝ) / Pd := by
      push_cast
      rw [le_div_iff₀ hPd]
      have := pi_hi; rw [lt_div_iff₀ hPd] at this
      nlinarith [sq_nonneg (Sc : ℝ)]
    linarith
  have h2 : ∀ i ∈ range 69, (intTerm i : ℝ) ≤ (Sc : ℝ) ^ 2 *
      ((19 / 25 : ℝ) * 100 * Real.sin (π * ((i : ℝ) + 2) / 100) ^ 2 / ((i : ℝ) + 2) ^ 2) := by
    intro i _
    have hs := sinPiLo_le (i + 2) 100 (by norm_num)
    have hs0 : (0 : ℝ) ≤ sinPiLo (i + 2) 100 := by positivity
    have hsq : ((sinPiLo (i + 2) 100 : ℝ) / Sc) ^ 2 ≤ Real.sin (π * ((i : ℝ) + 2) / 100) ^ 2 := by
      rw [← sq_abs (Real.sin _)]
      have : π * (((i + 2 : ℕ) : ℝ)) / ((100 : ℕ) : ℝ) = π * ((i : ℝ) + 2) / 100 := by push_cast; ring
      rw [this] at hs
      exact pow_le_pow_left₀ (by positivity) hs 2
    have h1 : (intTerm i : ℝ) ≤ ((1900 * sinPiLo (i + 2) 100 ^ 2 : ℕ) : ℝ) / ((25 * (i + 2) ^ 2 : ℕ) : ℝ) :=
      Nat.cast_div_le
    refine le_trans h1 ?_
    push_cast
    rw [div_pow] at hsq
    have hi2 : (0 : ℝ) < ((i : ℝ) + 2) ^ 2 := by positivity
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hsq
    have : (Sc : ℝ) ^ 2 * ((19 / 25 : ℝ) * 100 * Real.sin (π * ((i : ℝ) + 2) / 100) ^ 2 / ((i : ℝ) + 2) ^ 2) *
        (25 * ((i : ℝ) + 2) ^ 2) = 1900 * (Real.sin (π * ((i : ℝ) + 2) / 100) ^ 2 * (Sc : ℝ) ^ 2) := by
      field_simp; ring
    rw [this]
    nlinarith
  have h3 := Finset.sum_le_sum h2
  rw [← Finset.mul_sum] at h3
  have h4 : π * (Sc : ℝ) ^ 2 ≤ (Sc : ℝ) ^ 2 * ∑ i ∈ range 69,
      (19 / 25 : ℝ) * 100 * Real.sin (π * ((i : ℝ) + 2) / 100) ^ 2 / ((i : ℝ) + 2) ^ 2 := by
    rw [intSum_eq] at h1; linarith
  rw [mul_comm] at h4
  exact le_of_mul_le_mul_left h4 (by positivity)

/-! ## The three certificates (kernel-checked) -/

/-- `ω₁ sin(0.35π) ≥ 1`. -/
def regC : Bool := decide (50 * Sc ≤ 57 * sinPiLo 35 100)

theorem regC_ok : regC = true := by decide +kernel
theorem intOK_ok : intOK = true := by decide +kernel
theorem cells_ok : cellRec 20 1 35 100 = true := by decide +kernel

/-! ## Lemma L -/

theorem lamS_regC (t : ℝ) (ht1 : 35 / 100 ≤ t) (ht2 : t ≤ 1 / 2) (n : ℕ) (hn : 7 / 10 < ((n : ℝ) + 1) * t) :
    Real.sin (π * t) ≤ LamS n t := by
  have hn1 : 1 ≤ n := by
    by_contra h
    have : n = 0 := by omega
    subst this; simp at hn; linarith
  refine le_trans ?_ (LamS_mono t hn1)
  have h1 : LamS 1 t = 57 / 50 * Real.sin (π * t) ^ 2 := by
    simp [LamS, lamTerm, omg]
  rw [h1]
  have hc := regC_ok
  simp only [regC, decide_eq_true_eq] at hc
  have hs := sinPiLo_le 35 100 (by norm_num)
  have hSc := Sc_pos
  have hs1 : (50 : ℝ) / 57 ≤ (sinPiLo 35 100 : ℝ) / Sc := by
    rw [div_le_div_iff₀ (by norm_num) hSc]
    have : ((50 * Sc : ℕ) : ℝ) ≤ ((57 * sinPiLo 35 100 : ℕ) : ℝ) := by exact_mod_cast hc
    push_cast at this; linarith
  have e : π * ((35 : ℕ) : ℝ) / ((100 : ℕ) : ℝ) = π * (35 / 100) := by push_cast; ring
  rw [e, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos]))] at hs
  have hmono : Real.sin (π * (35 / 100)) ≤ Real.sin (π * t) := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
    · exact mul_le_mul_of_nonneg_left ht1 Real.pi_pos.le
  have hst : (50 : ℝ) / 57 ≤ Real.sin (π * t) := by linarith
  nlinarith

theorem lamS_small (t : ℝ) (ht0 : 0 < t) (ht : t ≤ 1 / 100) (n : ℕ) (hn : 7 / 10 < ((n : ℝ) + 1) * t) :
    Real.sin (π * t) ≤ LamS n t := by
  set k := ⌊7 / (10 * t)⌋₊ with hkdef
  have hk1 : (k : ℝ) ≤ 7 / (10 * t) := Nat.floor_le (by positivity)
  have hk2 : 7 / (10 * t) < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hkt : (k : ℝ) * t ≤ 7 / 10 := by
    rw [le_div_iff₀ (by positivity)] at hk1; linarith
  have hkt2 : 7 / 10 < ((k : ℝ) + 1) * t := by
    rw [div_lt_iff₀ (by positivity)] at hk2; linarith
  have hkt3 : ((k : ℝ) + 1) * t ≤ 1 := by nlinarith
  have hkn : k ≤ n := by
    have : (k : ℝ) < (n : ℝ) + 1 := by
      by_contra h; push Not at h
      have := mul_le_mul_of_nonneg_right h ht0.le
      linarith
    have : k < n + 1 := by exact_mod_cast this
    omega
  refine le_trans ?_ (LamS_mono t hkn)
  -- LamS k t ≥ (19/25) t² Σ g
  have h1 : (19 / 25 : ℝ) * t ^ 2 * ∑ M ∈ range k, gL (((M : ℝ) + 1) * t) ≤ LamS k t := by
    rw [Finset.mul_sum]
    unfold LamS
    apply Finset.sum_le_sum
    intro M _
    unfold lamTerm gL
    have hM : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    have e : (19 / 25 : ℝ) * t ^ 2 * (Real.sin (π * (((M : ℝ) + 1) * t)) ^ 2 / (((M : ℝ) + 1) * t) ^ 2) =
        19 / 25 * Real.sin (π * (((M + 1 : ℕ) : ℝ)) * t) ^ 2 / (((M + 1 : ℕ) : ℝ)) ^ 2 := by
      push_cast; rw [mul_assoc π]; field_simp
    rw [e]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (omg_ge _) (by positivity)
  have h2 := int_le_sum t ht0 k hkt3
  have h3 := int_mono t ht0 ht k hkt2.le hkt3
  have h4 := sum_le_int
  have h5 := intOK_sound intOK_ok
  have h6 : (1 / 100 : ℝ) * ∑ i ∈ range 69, gL (((i : ℝ) + 2) / 100) * (19 / 25) =
      ∑ i ∈ range 69, (19 / 25 : ℝ) * 100 * Real.sin (π * ((i : ℝ) + 2) / 100) ^ 2 / ((i : ℝ) + 2) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    unfold gL
    have : (0 : ℝ) < (i : ℝ) + 2 := by positivity
    rw [mul_div_assoc π]
    field_simp
  have h7 : π ≤ (19 / 25 : ℝ) * ∫ x in t..((k : ℝ) + 1) * t, gL x := by
    rw [← Finset.sum_mul] at h6
    have : (19 / 25 : ℝ) * ((1 / 100 : ℝ) * ∑ i ∈ range 69, gL (((i : ℝ) + 2) / 100)) ≤
        (19 / 25 : ℝ) * ∫ x in t..((k : ℝ) + 1) * t, gL x :=
      mul_le_mul_of_nonneg_left (le_trans h4 h3) (by norm_num)
    have e : (19 / 25 : ℝ) * ((1 / 100 : ℝ) * ∑ i ∈ range 69, gL (((i : ℝ) + 2) / 100)) =
        (1 / 100 : ℝ) * (∑ i ∈ range 69, gL (((i : ℝ) + 2) / 100)) * (19 / 25) := by ring
    linarith
  have h8 : π * t ≤ LamS k t := by
    have : (19 / 25 : ℝ) * t * (∫ x in t..((k : ℝ) + 1) * t, gL x) ≤
        (19 / 25 : ℝ) * t ^ 2 * ∑ M ∈ range k, gL (((M : ℝ) + 1) * t) := by
      have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 19 / 25 * t)
      calc _ ≤ _ := this
        _ = _ := by ring
    have h9 : π * t ≤ (19 / 25 : ℝ) * t * (∫ x in t..((k : ℝ) + 1) * t, gL x) := by
      have := mul_le_mul_of_nonneg_right h7 ht0.le
      calc π * t ≤ _ := this
        _ = _ := by ring
    linarith
  exact le_trans (Real.sin_le (by positivity)) h8

/-- **Lemma L.** For `0 < t ≤ 1/2` and every `n` with `(n+1)t > 7/10`,
`sin(πt) ≤ Σ_{M<n} ω_{M+1} sin²(π(M+1)t)/(M+1)²`. -/
theorem lemmaL (t : ℝ) (ht0 : 0 < t) (ht : t ≤ 1 / 2) (n : ℕ) (hn : 7 / 10 < ((n : ℝ) + 1) * t) :
    Real.sin (π * t) ≤ LamS n t := by
  rcases le_or_gt t (1 / 100) with h | h
  · exact lamS_small t ht0 h n hn
  rcases le_or_gt t (35 / 100) with h' | h'
  · exact cellRec_sound 20 1 35 100 cells_ok t (by norm_num; linarith) (by norm_num; linarith) n hn
  · exact lamS_regC t h'.le ht n hn

end Palprimes
