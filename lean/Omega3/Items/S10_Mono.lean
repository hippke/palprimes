import Omega3.Statements

/-!
# S10 helpers, part 2: monotonicity of `φ`, of `W`, and the reduction of the band condition to the left band edge
-/

set_option linter.style.longLine false

open Real Set

namespace Omega3
namespace S10

/-- `φ(a, b, s) = ∫_{min(a,s)}^{min(b,s)} (s − v)/v dv` in closed form. -/
noncomputable def phiC (a b s : ℝ) : ℝ :=
  s * (Real.log (min b s) - Real.log (min a s)) - (min b s - min a s)

lemma Lfact {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : y - x ≤ y * (Real.log y - Real.log x) := by
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne', inv_div] at h
  have : y * (1 - x / y) = y - x := by field_simp
  nlinarith

lemma Gmono {a s s' : ℝ} (ha : 0 < a) (has : a ≤ s) (hss : s ≤ s') :
    s * (Real.log s - Real.log a) - (s - a) ≤ s' * (Real.log s' - Real.log a) - (s' - a) := by
  have hs : 0 < s := lt_of_lt_of_le ha has
  have hs' : 0 < s' := lt_of_lt_of_le hs hss
  have h1 := Lfact hs hs'
  have h2 : 0 ≤ Real.log s - Real.log a := sub_nonneg.mpr (Real.log_le_log ha has)
  nlinarith

lemma Gnonneg {a s : ℝ} (ha : 0 < a) (has : a ≤ s) : 0 ≤ s * (Real.log s - Real.log a) - (s - a) := by
  have := Lfact ha (lt_of_lt_of_le ha has); linarith

lemma phiC_nonneg {a b s : ℝ} (ha : 0 < a) (hab : a ≤ b) (hs : 0 < s) : 0 ≤ phiC a b s := by
  unfold phiC
  rcases le_total s a with h1 | h1
  · rw [min_eq_right h1, min_eq_right (le_trans h1 hab)]; simp
  · rw [min_eq_left h1]
    rcases le_total s b with h2 | h2
    · rw [min_eq_right h2]; exact Gnonneg ha h1
    · rw [min_eq_left h2]
      have hlog : 0 ≤ Real.log b - Real.log a := sub_nonneg.mpr (Real.log_le_log ha hab)
      have := Gnonneg ha hab
      nlinarith

lemma phiC_mono {a b s s' : ℝ} (ha : 0 < a) (hab : a ≤ b) (hs : 0 < s) (hss : s ≤ s') :
    phiC a b s ≤ phiC a b s' := by
  have hs' : 0 < s' := lt_of_lt_of_le hs hss
  have hlog : 0 ≤ Real.log b - Real.log a := sub_nonneg.mpr (Real.log_le_log ha hab)
  rcases le_total s a with h1 | h1
  · have : phiC a b s = 0 := by
      unfold phiC; rw [min_eq_right h1, min_eq_right (le_trans h1 hab)]; simp
    rw [this]; exact phiC_nonneg ha hab hs'
  · unfold phiC
    rw [min_eq_left h1, min_eq_left (le_trans h1 hss)]
    rcases le_total s' b with h2 | h2
    · rw [min_eq_right h2, min_eq_right (le_trans hss h2)]; exact Gmono ha h1 hss
    · rw [min_eq_left h2]
      rcases le_total s b with h3 | h3
      · rw [min_eq_right h3]
        have := Gmono ha h1 h3
        nlinarith
      · rw [min_eq_left h3]; nlinarith

/-! ## The weight `W` -/

lemma Wf_of_le {t : ℝ} (ht : t ≤ mm) : Wf t = 0 := by unfold Wf; rw [if_pos ht]

lemma Wf_mid {t : ℝ} (h1 : mm < t) (h2 : t ≤ 1 / 3) : Wf t = min (kSq * t ^ 2) (t - mm) := by
  unfold Wf; rw [if_neg (not_le.mpr h1), if_pos h2]

lemma Wf_nonneg_mid {t : ℝ} (h2 : t ≤ 1 / 3) (h0 : 0 ≤ t) : 0 ≤ Wf t := by
  rcases le_or_gt t mm with h | h
  · rw [Wf_of_le h]
  · rw [Wf_mid h h2]
    apply le_min (by unfold kSq; positivity) (by linarith)

lemma Wf_mono {t t' : ℝ} (h0 : 0 ≤ t) (htt : t ≤ t') (h2 : t' ≤ 1 / 3) : Wf t ≤ Wf t' := by
  rcases le_or_gt t mm with h | h
  · rw [Wf_of_le h]; exact Wf_nonneg_mid h2 (le_trans h0 htt)
  · rw [Wf_mid h (le_trans htt h2), Wf_mid (lt_of_lt_of_le h htt) h2]
    apply min_le_min
    · unfold kSq; nlinarith
    · linarith

/-- The band condition at `x` follows from the condition at the left edge `xl` (same `u`). -/
lemma W_ratio {xl x u : ℝ} (hxl : 1 / 3 ≤ xl) (hx : xl ≤ x) (hxU : x ≤ 2 * UU - 1) (hu0 : 0 < u) (hu1 : u ≤ 1) :
    Wf (u * (1 - x) / 2) * (UU - xl) ≤ Wf (u * (1 - xl) / 2) * (UU - x) := by
  have hU : UU = 83 / 85 := rfl
  have hm : mm = 1 / 85 := rfl
  set t := u * (1 - x) / 2
  set t' := u * (1 - xl) / 2
  have hx1 : x ≤ 81 / 85 := by rw [hU] at hxU; linarith
  have ht0 : 0 ≤ t := by simp only [t]; apply div_nonneg (mul_nonneg hu0.le (by linarith)) (by norm_num)
  have htt : t ≤ t' := by simp only [t, t']; nlinarith
  have ht'3 : t' ≤ 1 / 3 := by simp only [t']; nlinarith
  have hUx : 0 ≤ UU - x := by rw [hU]; linarith
  have hUxl : 0 ≤ UU - xl := by rw [hU]; linarith
  rcases le_or_gt t mm with h | h
  · rw [Wf_of_le h, zero_mul]; exact mul_nonneg (Wf_nonneg_mid ht'3 (le_trans ht0 htt)) hUx
  · rw [Wf_mid h (le_trans htt ht'3), Wf_mid (lt_of_lt_of_le h htt) ht'3]
    rw [min_mul_of_nonneg _ _ hUxl, min_mul_of_nonneg _ _ hUx]
    apply min_le_min
    · -- quadratic part: (1-x)^2 (U - xl) ≤ (1-xl)^2 (U - x)
      have key : (1 - x) ^ 2 * (UU - xl) ≤ (1 - xl) ^ 2 * (UU - x) := by
        rw [hU]
        have hp : 0 ≤ x - xl := by linarith
        have e : (1 - xl) ^ 2 * (83 / 85 - x) - (1 - x) ^ 2 * (83 / 85 - xl) =
            (x - xl) * ((1 - xl) * (1 - x) - 2 / 85 * ((1 - xl) + (1 - x))) := by ring
        have h2 : 0 ≤ (1 - xl) * (1 - x) - 2 / 85 * ((1 - xl) + (1 - x)) := by nlinarith
        nlinarith [mul_nonneg hp h2]
      simp only [t, t']
      have hk : 0 ≤ kSq * u ^ 2 / 4 := by unfold kSq; positivity
      nlinarith [mul_le_mul_of_nonneg_left key hk]
    · simp only [t, t']; rw [hm, hU]; nlinarith

end S10
end Omega3
