import KappaOmega2.Items.LK10_Base

/-!
# LK10_Aux: the choice of `j` for the large values, the block split, the exponent inequalities
-/

namespace KappaOmega2

open Finset Real Palprimes

/-- Choice of the inner block length `j < m` for the large values at the modulus size `D`:
`(D² + bWb^{2j}) b^{−j}/W ≤ (b⁴ + b) + 2bD²/(b^m W) + 2b²D/b^{⌊ℓ/2⌋}`, `W = b^ℓ`. -/
lemma LK10_large_choice (b m ℓ D : ℕ) (hb : 2 ≤ b) (hm : 1 ≤ m) (hD : 1 ≤ D) :
    ∃ j < m, ((D : ℝ) ^ 2 + b * (b : ℝ) ^ ℓ * (b : ℝ) ^ (2 * j)) * ((b : ℝ)⁻¹) ^ j / (b : ℝ) ^ ℓ ≤
      ((b : ℝ) ^ 4 + b) + 2 * b * (D : ℝ) ^ 2 / ((b : ℝ) ^ m * (b : ℝ) ^ ℓ) +
        2 * (b : ℝ) ^ 2 * D / (b : ℝ) ^ (ℓ / 2) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  set j₀ := Nat.log b D with hj₀
  set s := (ℓ + 2) / 2 with hs
  have hj0 : b ^ j₀ ≤ D := Nat.pow_log_le_self b (by omega)
  have hj0' : D < b ^ (j₀ + 1) := Nat.lt_pow_succ_log_self (by omega) D
  have hT2 : 0 ≤ 2 * b * (D : ℝ) ^ 2 / ((b : ℝ) ^ m * (b : ℝ) ^ ℓ) := by positivity
  have hT3 : 0 ≤ 2 * (b : ℝ) ^ 2 * D / (b : ℝ) ^ (ℓ / 2) := by positivity
  have hbl : (0 : ℝ) < (b : ℝ) ^ ℓ := by positivity
  have hb4 : (0 : ℝ) ≤ (b : ℝ) ^ 4 + b := by positivity
  by_cases hc : j₀ ≤ s
  · refine ⟨0, hm, ?_⟩
    have hD2 : D ^ 2 ≤ b ^ 4 * b ^ ℓ := by
      have h1 : D ≤ b ^ (s + 1) := le_trans hj0'.le (Nat.pow_le_pow_right (by omega) (by omega))
      calc D ^ 2 ≤ (b ^ (s + 1)) ^ 2 := Nat.pow_le_pow_left h1 2
        _ = b ^ (2 * s + 2) := by ring
        _ ≤ b ^ (4 + ℓ) := Nat.pow_le_pow_right (by omega) (by omega)
        _ = b ^ 4 * b ^ ℓ := by ring
    have hD2R : (D : ℝ) ^ 2 ≤ (b : ℝ) ^ 4 * (b : ℝ) ^ ℓ := by exact_mod_cast hD2
    have h1 : ((D : ℝ) ^ 2 + b * (b : ℝ) ^ ℓ * (b : ℝ) ^ (2 * 0)) * ((b : ℝ)⁻¹) ^ 0 / (b : ℝ) ^ ℓ ≤
        (b : ℝ) ^ 4 + b := by
      rw [div_le_iff₀ hbl]; simp only [mul_zero, pow_zero, mul_one]; nlinarith
    linarith
  · push Not at hc
    set j₁ := j₀ - s with hj₁
    refine ⟨min (m - 1) j₁, by omega, ?_⟩
    set j := min (m - 1) j₁ with hj
    have hbig : b * b ^ ℓ * b ^ (2 * j) ≤ D ^ 2 := by
      calc b * b ^ ℓ * b ^ (2 * j) = b ^ (1 + ℓ + 2 * j) := by ring
        _ ≤ b ^ (2 * j₀) := Nat.pow_le_pow_right (by omega) (by omega)
        _ = (b ^ j₀) ^ 2 := by ring
        _ ≤ D ^ 2 := Nat.pow_le_pow_left hj0 2
    have hbigR : (b : ℝ) * (b : ℝ) ^ ℓ * (b : ℝ) ^ (2 * j) ≤ (D : ℝ) ^ 2 := by exact_mod_cast hbig
    have hbj : (0 : ℝ) < (b : ℝ) ^ j := by positivity
    have hstep : ((D : ℝ) ^ 2 + b * (b : ℝ) ^ ℓ * (b : ℝ) ^ (2 * j)) * ((b : ℝ)⁻¹) ^ j / (b : ℝ) ^ ℓ ≤
        2 * (D : ℝ) ^ 2 / ((b : ℝ) ^ j * (b : ℝ) ^ ℓ) := by
      rw [inv_pow, div_le_div_iff₀ hbl (by positivity)]
      have : ((D : ℝ) ^ 2 + b * (b : ℝ) ^ ℓ * (b : ℝ) ^ (2 * j)) * ((b : ℝ) ^ j)⁻¹ * ((b : ℝ) ^ j * (b : ℝ) ^ ℓ)
          = ((D : ℝ) ^ 2 + b * (b : ℝ) ^ ℓ * (b : ℝ) ^ (2 * j)) * (b : ℝ) ^ ℓ := by
        field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_right (by linarith) hbl.le
    rcases le_total (m - 1) j₁ with hmj | hmj
    · have hjm : j = m - 1 := by rw [hj]; exact min_eq_left hmj
      have e : 2 * (D : ℝ) ^ 2 / ((b : ℝ) ^ j * (b : ℝ) ^ ℓ) =
          2 * b * (D : ℝ) ^ 2 / ((b : ℝ) ^ m * (b : ℝ) ^ ℓ) := by
        have hm' : m = j + 1 := by omega
        rw [hm']
        field_simp
        ring
      linarith
    · have hjj : j = j₁ := by rw [hj]; exact min_eq_right hmj
      have hnat : D * b ^ (ℓ / 2) ≤ b ^ 2 * b ^ j * b ^ ℓ := by
        calc D * b ^ (ℓ / 2) ≤ b ^ (j₀ + 1) * b ^ (ℓ / 2) := Nat.mul_le_mul_right _ hj0'.le
          _ = b ^ (j₀ + 1 + ℓ / 2) := by ring
          _ ≤ b ^ (2 + j + ℓ) := Nat.pow_le_pow_right (by omega) (by omega)
          _ = b ^ 2 * b ^ j * b ^ ℓ := by ring
      have hnatR : (D : ℝ) * (b : ℝ) ^ (ℓ / 2) ≤ (b : ℝ) ^ 2 * (b : ℝ) ^ j * (b : ℝ) ^ ℓ := by
        exact_mod_cast hnat
      have hD0 : (0 : ℝ) ≤ D := by positivity
      have e : 2 * (D : ℝ) ^ 2 / ((b : ℝ) ^ j * (b : ℝ) ^ ℓ) ≤ 2 * (b : ℝ) ^ 2 * D / (b : ℝ) ^ (ℓ / 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have := mul_le_mul_of_nonneg_left hnatR (by positivity : (0 : ℝ) ≤ 2 * D)
        nlinarith
      linarith

/-- The pointwise cut summed over a block (small part over all residues by positivity). -/
lemma LK10_block_split (b : ℕ) (g : ℕ → ℝ) (hg : IsDigitWeight b g) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (H : ℕ) (τ : ℕ → ℝ) (hT : ∀ t : ℝ, ‖Gg b g t‖ ^ p ≤ trigEval H τ t) (S : ℕ) (κ : ℕ → ℝ) (N : ℕ)
    (hK : ∀ β : ℝ, ‖Mmid (WK b N) β‖ ^ p ≤ trigEval S κ β) (hm : 1 ≤ mK N) (j : ℕ) (hj : j ≤ mK N)
    (Qs : Finset ℕ) (β t : ℝ) (ht : 0 < t) :
    ∑ d ∈ Qs, ∑ h ∈ redRes d, ‖fK b g N ((h : ℝ) / d + β)‖ ≤
      t ^ (1 - p) * (∑ d ∈ Qs, ∑ h ∈ range d,
        (∏ k ∈ Ico 1 (mK N), trigEval H τ ((cK b N k : ℝ) * ((h : ℝ) / d + β))) *
          trigEval S κ ((b : ℝ) ^ mK N * ((h : ℝ) / d + β))) +
      t⁻¹ ^ 3 * (∑ d ∈ Qs, ∑ h ∈ redRes d, ‖gJK b g N j ((h : ℝ) / d + β)‖ ^ 4) := by
  have hpt : ∀ α : ℝ, ‖fK b g N α‖ ≤ t ^ (1 - p) * ((∏ k ∈ Ico 1 (mK N), trigEval H τ ((cK b N k : ℝ) * α)) *
      trigEval S κ ((b : ℝ) ^ mK N * α)) + t⁻¹ ^ 3 * ‖gJK b g N j α‖ ^ 4 := fun α =>
    cut_pointwise _ _ _ _ _ (norm_nonneg _) (LK10_fK_le_gJK b g hg N j hj α) ht hp0 hp1
      (LK10_fKp_le b g hg p hp0 H τ hT S κ N hK hm α)
  have hT0 : ∀ α : ℝ, 0 ≤ (∏ k ∈ Ico 1 (mK N), trigEval H τ ((cK b N k : ℝ) * α)) *
      trigEval S κ ((b : ℝ) ^ mK N * α) := fun α =>
    (Real.rpow_nonneg (norm_nonneg _) p).trans (LK10_fKp_le b g hg p hp0 H τ hT S κ N hK hm α)
  calc _ ≤ ∑ d ∈ Qs, ∑ h ∈ redRes d, (t ^ (1 - p) * ((∏ k ∈ Ico 1 (mK N),
          trigEval H τ ((cK b N k : ℝ) * ((h : ℝ) / d + β))) *
            trigEval S κ ((b : ℝ) ^ mK N * ((h : ℝ) / d + β))) +
          t⁻¹ ^ 3 * ‖gJK b g N j ((h : ℝ) / d + β)‖ ^ 4) :=
        Finset.sum_le_sum (fun d _ => Finset.sum_le_sum (fun h _ => hpt _))
    _ = t ^ (1 - p) * (∑ d ∈ Qs, ∑ h ∈ redRes d,
          (∏ k ∈ Ico 1 (mK N), trigEval H τ ((cK b N k : ℝ) * ((h : ℝ) / d + β))) *
            trigEval S κ ((b : ℝ) ^ mK N * ((h : ℝ) / d + β))) +
        t⁻¹ ^ 3 * (∑ d ∈ Qs, ∑ h ∈ redRes d, ‖gJK b g N j ((h : ℝ) / d + β)‖ ^ 4) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := by
        apply add_le_add _ le_rfl
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg ht.le _)
        exact Finset.sum_le_sum (fun d _ => Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => hT0 _))

/-- The diagonal exponent (condition (ii) of Proposition C_κ). -/
lemma LK10_expA (n m ℓ lb δ a p ψ η θ ε₂ ε : ℝ) (hlb : 0 < lb) (hn : 0 ≤ n) (hℓ : ℓ + 2 * m = n)
    (hm1 : 20 * m ≤ 7 * n) (hm2 : 7 * n < 20 * m + 20) (hδ : δ ≤ n * lb * θ)
    (hD1 : θ + η < 7 / 20 * ψ + 3 / 10 * p + a * (1 - p)) (hψ : 0 ≤ ψ) (hp0 : 0 ≤ p)
    (hε₂ : ε₂ ≤ ε / 2) :
    -(a * (n * lb)) * (1 - p) + 2 * δ + (m - 1) * (lb * (-ψ)) + ε₂ * (n * lb) + ℓ * lb * (-p) ≤
      lb * (2 * ψ + 2) + (δ - η * (n * lb) + ε / 2 * (n * lb)) := by
  have key : n * (θ + η - a * (1 - p) - p) + m * (2 * p - ψ) ≤ ψ + 2 := by
    have h1 : n * (θ + η) ≤ n * (7 / 20 * ψ + 3 / 10 * p + a * (1 - p)) :=
      mul_le_mul_of_nonneg_left hD1.le hn
    rcases le_total 0 (2 * p - ψ) with hc | hc
    · have : m * (2 * p - ψ) ≤ 7 * n / 20 * (2 * p - ψ) := mul_le_mul_of_nonneg_right (by linarith) hc
      nlinarith
    · have : m * (2 * p - ψ) ≤ (7 * n / 20 - 1) * (2 * p - ψ) :=
        mul_le_mul_of_nonpos_right (by linarith) hc
      nlinarith
  have k2 := mul_le_mul_of_nonneg_left key hlb.le
  have hl : ℓ = n - 2 * m := by linarith
  rw [hl]
  have k3 : 0 ≤ (ε / 2 - ε₂) * (n * lb) := mul_nonneg (by linarith) (by positivity)
  nlinarith

end KappaOmega2
