import KappaOmega2.StatementsK
import KappaOmega2.Items.L06

/-!
# LK06: the κ majorants `T = (1 − p) + p P ≥ |G_g|^p` for every `b ≥ 3`

`P = F_M` for odd `b = 2M − 1` (`|G_g| = F_M`, L01) and `P = (F_M + F_{M+1})/2` for even `b = 2M` (`|G_g| ≤ P`, LK01),
`P ≤ 1`, then Bernoulli.
-/

namespace KappaOmega2

open Finset Real Palprimes

/-- Raising the degree of a cosine polynomial by zero coefficients. -/
lemma LK06_trig_extend (n H : ℕ) (hnH : n ≤ H) (τ : ℕ → ℝ) (hτ : ∀ u, n < u → τ u = 0) (t : ℝ) :
    trigEval H τ t = trigEval n τ t := by
  unfold trigEval
  congr 2
  symm
  apply Finset.sum_subset
  · intro u hu
    simp only [Finset.mem_Icc] at hu ⊢
    omega
  · intro u hu hnu
    simp only [Finset.mem_Icc] at hu hnu
    rw [hτ u (by omega), zero_mul]

lemma LK06_trig_lin (H : ℕ) (c d : ℝ) (f g : ℕ → ℝ) (t : ℝ) :
    trigEval H (fun u => c * f u + d * g u) t = c * trigEval H f t + d * trigEval H g t := by
  unfold trigEval
  simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  ring

lemma LK06_fejTau_zero (m u : ℕ) (hu : m - 1 < u) (hm : 1 ≤ m) : fejTau m u = 0 := by
  unfold fejTau
  rw [if_neg (by omega), if_neg (by omega)]

/-- `F_m` as a cosine polynomial of any degree `H ≥ m − 1`. -/
lemma LK06_fejer_trig (m H : ℕ) (hm : 1 ≤ m) (hH : m ≤ H + 1) (t : ℝ) :
    trigEval H (fejTau m) t = fejerK m t := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [LK06_trig_extend n H (by omega) _ (fun u hu => LK06_fejTau_zero (n + 1) u (by omega) hm),
    l06_fejer_trig]

lemma LK06_fejer_le_one (m : ℕ) (hm : 1 ≤ m) (t : ℝ) : fejerK m t ≤ 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [l06_fejer_trig]
  exact l06_trig_fejer_le_one n t

lemma LK06_recPK_mem (b : ℕ) (hb : 3 ≤ b) : 0 ≤ recPK b ∧ recPK b ≤ 1 := by
  unfold recPK
  have hb' : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have h1 : 1 ≤ (b : ℝ) ^ 6 := one_le_pow₀ (by linarith)
  have h2 : 1 / (b : ℝ) ^ 6 ≤ 1 := by rw [div_le_one (by positivity)]; exact h1
  have h3 : 0 ≤ 1 / (b : ℝ) ^ 6 := by positivity
  constructor <;> linarith

/-- The polynomial part `P` of the κ majorant, its value, and `|G_g| ≤ P ≤ 1`. -/
lemma LK06_main (hF : FejerAbsStmt) (hP : ProdAbsStmt) (b : ℕ) (hb : 3 ≤ b) (t : ℝ) :
    ‖Gg b (recGKR b) t‖ ≤ trigEval (recHK b) (recPolyK b) t ∧
      trigEval (recHK b) (recPolyK b) t ≤ 1 := by
  by_cases hodd : b % 2 = 1
  · set m := (b + 1) / 2 with hm
    have hm1 : 1 ≤ m := by omega
    have h2m : 2 * m - 1 = b := by omega
    have hpoly : recPolyK b = fejTau m := by
      funext u; simp [recPolyK, hodd, hm]
    have hH : recHK b = m - 1 := by simp [recHK, hodd, hm]
    have hT : trigEval (recHK b) (recPolyK b) t = fejerK m t := by
      rw [hpoly, hH]; exact LK06_fejer_trig m (m - 1) hm1 (by omega) t
    have hG : Gg b (recGKR b) t =
        ∑ a ∈ Finset.range (2 * m - 1), ((fejerW m a : ℚ) : ℂ) * ee (a * t) := by
      rw [h2m]
      unfold Gg recGKR recGK
      simp only [hodd, ← hm, if_true, Complex.ofReal_ratCast]
    rw [hT, hG, hF m hm1 t]
    exact ⟨le_rfl, LK06_fejer_le_one m hm1 t⟩
  · set M := b / 2 with hM
    have hM1 : 1 ≤ M := by omega
    have h2M : 2 * M = b := by omega
    have hpoly : recPolyK b = fun u => (1 / 2 : ℝ) * fejTau M u + (1 / 2 : ℝ) * fejTau (M + 1) u := by
      funext u; simp only [recPolyK, hodd, if_false, ← hM]; ring
    have hH : recHK b = M := by simp [recHK, hodd, hM]
    have hT : trigEval (recHK b) (recPolyK b) t = (fejerK M t + fejerK (M + 1) t) / 2 := by
      rw [hpoly, hH, LK06_trig_lin, LK06_fejer_trig M M hM1 (by omega) t,
        LK06_fejer_trig (M + 1) M (by omega) (by omega) t]
      ring
    have hG : Gg b (recGKR b) t =
        ∑ a ∈ Finset.range (2 * M), ((prodW M a : ℚ) : ℂ) * ee (a * t) := by
      rw [h2M]
      unfold Gg recGKR recGK
      simp only [hodd, ← hM, if_false, Complex.ofReal_ratCast]
    rw [hT, hG]
    refine ⟨hP M hM1 t, ?_⟩
    have := LK06_fejer_le_one M hM1 t
    have := LK06_fejer_le_one (M + 1) (by omega) t
    linarith

theorem itemLK06 : ItemLK06 := by
  unfold ItemLK06 RecMajKStmt
  intro hB hF hP b hb t
  obtain ⟨hp0, hp1⟩ := LK06_recPK_mem b hb
  obtain ⟨hGP, hP1⟩ := LK06_main hF hP b hb t
  have hnn : 0 ≤ ‖Gg b (recGKR b) t‖ := norm_nonneg _
  have hBer := hB ‖Gg b (recGKR b) t‖ (recPK b) hnn (le_trans hGP hP1) hp0 hp1
  have hτ : recTauK b = fun u => (if u = 0 then 1 - recPK b else 0) + recPK b * recPolyK b u := by
    funext u; simp [recTauK]
  rw [hτ, l06_trig_affine]
  have := mul_le_mul_of_nonneg_left hGP hp0
  linarith

end KappaOmega2
