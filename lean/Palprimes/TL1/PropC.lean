import Palprimes.TL1.Ortho

/-! # Proposition C with the inner-only cut (finite form)

`F(α) = Π_{1≤n<N} √ψ(c_n α)`. For a threshold `τ > 0`, pointwise
`F ≤ τ^{1-p} Π_r T(…) + τ^{-3} G_J⁴` with `G_J = Π_{m≤n<N} √ψ(c_n α)`. Summed over Farey pairs this
gives `tl1_finite`. -/

set_option linter.style.longLine false

open Finset Real

namespace Palprimes

/-- The product over the positions `1 ≤ n < N`. -/
noncomputable def Fprod (b N : ℕ) (α : ℝ) : ℝ := ∏ n ∈ Ico 1 N, Real.sqrt (psiB b (cK b N n * α))

theorem sqrt_psiB_le_one (b : ℕ) (hb : 1 ≤ b) (t : ℝ) : Real.sqrt (psiB b t) ≤ 1 :=
  Real.sqrt_le_one.2 (psiB_le_one b hb t)

theorem Fprod_nonneg (b N : ℕ) (α : ℝ) : 0 ≤ Fprod b N α :=
  Finset.prod_nonneg (fun _ _ => Real.sqrt_nonneg _)

/-- Dropping factors in `[0,1]` increases a product. -/
theorem prod_le_prod_subset (s t : Finset ℕ) (hst : s ⊆ t) (g : ℕ → ℝ) (hg0 : ∀ n, 0 ≤ g n)
    (hg1 : ∀ n, g n ≤ 1) : ∏ n ∈ t, g n ≤ ∏ n ∈ s, g n := by
  rw [← Finset.prod_sdiff hst]
  have h1 : ∏ n ∈ t \ s, g n ≤ 1 := Finset.prod_le_one₀ (fun n _ => hg0 n) (fun n _ => hg1 n)
  have h2 : 0 ≤ ∏ n ∈ s, g n := Finset.prod_nonneg (fun n _ => hg0 n)
  calc (∏ n ∈ t \ s, g n) * ∏ n ∈ s, g n ≤ 1 * ∏ n ∈ s, g n := mul_le_mul_of_nonneg_right h1 h2
    _ = _ := one_mul _

/-- Blocks of length `l`: `Π_{k<lR} g(1+k) = Π_{r<R} Π_{i<l} g(1+lr+i)`. -/
theorem prod_blocks (l R : ℕ) (g : ℕ → ℝ) :
    ∏ k ∈ range (l * R), g (1 + k) = ∏ r : Fin R, ∏ i ∈ range l, g (sB l r + i) := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [show l * (R + 1) = l * R + l by ring, Finset.prod_range_add, ih, Fin.prod_univ_castSucc]
    congr 1
    apply Finset.prod_congr rfl; intro i _
    congr 1
    simp only [sB, Fin.val_last]; ring

/-- `F ≤ Π_r ‖Γ(b^{s_r}α, b^{e_r}α)‖`. -/
theorem Fprod_le_blocks (b N l R : ℕ) (hb : 1 ≤ b) (hR : l * R + 1 ≤ N) (α : ℝ) :
    Fprod b N α ≤ ∏ r : Fin R, ‖Gam b l ((b : ℝ) ^ sB l r * α) ((b : ℝ) ^ eB N l r * α)‖ := by
  have hsub : Ico 1 (l * R + 1) ⊆ Ico 1 N := Finset.Ico_subset_Ico_right hR
  refine (prod_le_prod_subset _ _ hsub _ (fun _ => Real.sqrt_nonneg _)
    (fun n => sqrt_psiB_le_one b hb _)).trans (le_of_eq ?_)
  rw [Finset.prod_Ico_eq_prod_range, show l * R + 1 - 1 = l * R by omega,
    prod_blocks l R (fun n => Real.sqrt (psiB b (cK b N n * α)))]
  apply Finset.prod_congr rfl; intro r _
  have hr : (r : ℕ) < R := r.2
  have hs : sB l r + l ≤ N := by
    simp only [sB]
    have : l * ((r : ℕ) + 1) ≤ l * R := Nat.mul_le_mul_left _ hr
    nlinarith
  have key : 2 * N - sB l r - l + 1 = eB N l r := by
    have h1 : l * ((r : ℕ) + 1) ≤ l * R := Nat.mul_le_mul_left _ hr
    have e : l * ((r : ℕ) + 1) = l * r + l := by ring
    simp only [sB, eB]
    omega
  rw [block_eq b N l (sB l r) hb hs α, key]

/-- `F^p ≤ Π_r T(b^{s_r}α, b^{e_r}α)`. -/
theorem Fprod_rpow_le {b l : ℕ} (M : BlockMaj b l) (hb : 1 ≤ b) (N R : ℕ) (hR : l * R + 1 ≤ N) (α : ℝ) :
    Fprod b N α ^ M.p ≤ ∏ r : Fin R, Tval M.S M.τ ((b : ℝ) ^ sB l r * α) ((b : ℝ) ^ eB N l r * α) := by
  calc Fprod b N α ^ M.p ≤ (∏ r : Fin R, ‖Gam b l ((b : ℝ) ^ sB l r * α) ((b : ℝ) ^ eB N l r * α)‖) ^ M.p :=
        Real.rpow_le_rpow (Fprod_nonneg b N α) (Fprod_le_blocks b N l R hb hR α) M.hp0.le
    _ = ∏ r : Fin R, ‖Gam b l ((b : ℝ) ^ sB l r * α) ((b : ℝ) ^ eB N l r * α)‖ ^ M.p :=
        (Real.finsetProd_rpow _ _ (fun _ _ => norm_nonneg _) _).symm
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)
        (fun r _ => M.hmaj _ _)

/-- `F ≤ G_J` for `J = [m, N)`, `m ≥ 1`, and `G_J⁴ = piK(J)²`. -/
theorem Fprod_le_inner (b N m : ℕ) (hb : 1 ≤ b) (hm : 1 ≤ m) (α : ℝ) :
    Fprod b N α ≤ Real.sqrt (piK b N (Ico m N) α) := by
  unfold Fprod piK
  rw [← prod_sqrt_eq _ _ (fun n => psiB_nonneg b _)]
  exact prod_le_prod_subset _ _ (Finset.Ico_subset_Ico_left hm) _ (fun _ => Real.sqrt_nonneg _)
    (fun n => sqrt_psiB_le_one b hb _)

/-- **The pointwise cut.** -/
theorem cut_pointwise (F G T τ p : ℝ) (hF0 : 0 ≤ F) (hFG : F ≤ G) (hτ : 0 < τ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hT : F ^ p ≤ T) : F ≤ τ ^ (1 - p) * T + τ⁻¹ ^ 3 * G ^ 4 := by
  have hG0 : 0 ≤ G := hF0.trans hFG
  have hT0 : 0 ≤ T := (Real.rpow_nonneg hF0 _).trans hT
  rcases hF0.eq_or_lt with hF | hFpos
  · rw [← hF]; positivity
  rcases lt_or_ge F τ with hlt | hge
  · -- small value
    have h1 : F = F ^ (1 - p) * F ^ p := by
      rw [← Real.rpow_add hFpos]; simp
    have h2 : F ^ (1 - p) ≤ τ ^ (1 - p) := Real.rpow_le_rpow hF0 hlt.le (by linarith)
    have h3 : F ^ (1 - p) * F ^ p ≤ τ ^ (1 - p) * T :=
      mul_le_mul h2 hT (Real.rpow_nonneg hF0 _) (Real.rpow_nonneg hτ.le _)
    have h4 : 0 ≤ τ⁻¹ ^ 3 * G ^ 4 := by positivity
    linarith
  · -- large value: `G ≥ F ≥ τ`, so `G ≤ G⁴/τ³`
    have hGτ : τ ≤ G := hge.trans hFG
    have h1 : G ≤ τ⁻¹ ^ 3 * G ^ 4 := by
      have hτ3 : 0 < τ ^ 3 := by positivity
      rw [inv_pow, ← div_eq_inv_mul, le_div_iff₀ hτ3]
      have : τ ^ 3 ≤ G ^ 3 := pow_le_pow_left₀ hτ.le hGτ 3
      nlinarith [pow_nonneg hG0 3]
    have h2 : 0 ≤ τ ^ (1 - p) * T := mul_nonneg (Real.rpow_nonneg hτ.le _) hT0
    linarith

/-- **Proposition C (finite form, inner-only cut).** -/
theorem tl1_finite {b l : ℕ} (M : BlockMaj b l) (hb : 2 ≤ b) (hl : 1 ≤ l) (N R m : ℕ)
    (hR : l * R + 1 ≤ N) (hm : 1 ≤ m) (_hmN : m ≤ N)
    (R0 : ℕ) (hR0 : 1 ≤ R0) (Qs : Finset ℕ) (hQs : ∀ q ∈ Qs, R0 ≤ q ∧ q ≤ 2 * R0 ∧ Nat.Coprime q b)
    (Tdiv : ℝ) (hT0 : 0 ≤ Tdiv)
    (hT : ∀ w : ℤ, w ≠ 0 → |w| ≤ (R : ℤ) * (2 * ((b : ℤ) ^ l * (b : ℤ) ^ (2 * N))) →
      (#(Qs.filter (fun q : ℕ => (q : ℤ) ∣ w)) : ℝ) ≤ Tdiv)
    (τ : ℝ) (hτ : 0 < τ) (β : ℝ) :
    ∑ q ∈ Qs, ∑ h ∈ redRes q, Fprod b N ((h : ℝ) / q + β) ≤
      τ ^ (1 - M.p) * ((∑ q ∈ Qs, (q : ℝ)) * M.t00 ^ R + 2 * R0 * Tdiv * M.A ^ R) +
      τ⁻¹ ^ 3 * ((4 * ((4 * b * (N - m) * b ^ (2 * (N - m)) + 1 : ℕ) : ℝ) + 12 * (R0 : ℝ) ^ 2 + 2) *
        (((2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 3)) ^ (N - m))) := by
  classical
  have hb1 : 1 ≤ b := by omega
  set Tp : ℝ → ℝ := fun α => ∏ r : Fin R, Tval M.S M.τ ((b : ℝ) ^ sB l r * α) ((b : ℝ) ^ eB N l r * α)
  have hTp0 : ∀ α, 0 ≤ Tp α := fun α =>
    (Real.rpow_nonneg (Fprod_nonneg b N α) _).trans (Fprod_rpow_le M hb1 N R hR α)
  -- pointwise
  have hpt : ∀ α, Fprod b N α ≤ τ ^ (1 - M.p) * Tp α + τ⁻¹ ^ 3 * piK b N (Ico m N) α ^ 2 := by
    intro α
    have h := cut_pointwise (Fprod b N α) (Real.sqrt (piK b N (Ico m N) α)) (Tp α) τ M.p
      (Fprod_nonneg b N α) (Fprod_le_inner b N m hb1 hm α) hτ M.hp0 M.hp1 (Fprod_rpow_le M hb1 N R hR α)
    have e : Real.sqrt (piK b N (Ico m N) α) ^ 4 = piK b N (Ico m N) α ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, Real.sq_sqrt (piK_nonneg _ _ _ _)]
    rw [e] at h; exact h
  -- sum over the Farey pairs
  have hsum1 : ∑ q ∈ Qs, ∑ h ∈ redRes q, Fprod b N ((h : ℝ) / q + β) ≤
      τ ^ (1 - M.p) * ∑ q ∈ Qs, ∑ h ∈ range q, Tp ((h : ℝ) / q + β) +
      τ⁻¹ ^ 3 * ∑ q ∈ Qs, ∑ h ∈ redRes q, piK b N (Ico m N) ((h : ℝ) / q + β) ^ 2 := by
    calc _ ≤ ∑ q ∈ Qs, ∑ h ∈ redRes q, (τ ^ (1 - M.p) * Tp ((h : ℝ) / q + β) +
          τ⁻¹ ^ 3 * piK b N (Ico m N) ((h : ℝ) / q + β) ^ 2) :=
        Finset.sum_le_sum (fun q _ => Finset.sum_le_sum (fun h _ => hpt _))
      _ = τ ^ (1 - M.p) * ∑ q ∈ Qs, ∑ h ∈ redRes q, Tp ((h : ℝ) / q + β) +
          τ⁻¹ ^ 3 * ∑ q ∈ Qs, ∑ h ∈ redRes q, piK b N (Ico m N) ((h : ℝ) / q + β) ^ 2 := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ _ := by
        have hsub : ∀ q, redRes q ⊆ range q := fun q => Finset.filter_subset _ _
        have : ∑ q ∈ Qs, ∑ h ∈ redRes q, Tp ((h : ℝ) / q + β) ≤
            ∑ q ∈ Qs, ∑ h ∈ range q, Tp ((h : ℝ) / q + β) :=
          Finset.sum_le_sum (fun q _ => Finset.sum_le_sum_of_subset_of_nonneg (hsub q)
            (fun _ _ _ => hTp0 _))
        have hτp : 0 ≤ τ ^ (1 - M.p) := Real.rpow_nonneg hτ.le _
        nlinarith
  -- the majorant moment
  have hmaj := majorant_sum_le M hb hl N R hR Qs (R0 : ℝ) (by positivity)
    (fun q hq => ⟨by have := (hQs q hq).1; omega, by exact_mod_cast (hQs q hq).2.1⟩) Tdiv hT0 hT β
  -- the inner fourth moment
  have hls := ls_bound b N hb (Ico m N) ∅ (fun k hk => by simp [mem_Ico] at hk ⊢; omega)
    (by simp) (by simp) m (N - m) (fun k hk => by simp [mem_Ico] at hk; omega)
    (by simp) R0 hR0 Qs hQs β
  simp only [piK_empty, mul_one, Finset.card_empty, pow_zero, inv_one, Nat.card_Ico] at hls
  have hτ3 : 0 ≤ τ⁻¹ ^ 3 := by positivity
  have hτp : 0 ≤ τ ^ (1 - M.p) := Real.rpow_nonneg hτ.le _
  calc _ ≤ _ := hsum1
    _ ≤ _ := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hmaj hτp
        · exact mul_le_mul_of_nonneg_left hls hτ3

end Palprimes
