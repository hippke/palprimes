import Palprimes.E1.Tail
import Palprimes.E1.Finite
import Palprimes.E1.Ident

set_option linter.style.longLine false

/-! # E1, phase E12: assembly of Greaves' Lemma 4.2 (blueprint §6)

`rosserAsymp_of_two_le`: `RosserAsymp b` for every `b ≥ 2`. ε/3 split: the truncation in depth
(`Splus_trunc`, `Sminus_trunc`, C.4), the finitely many depths (`finite_depth_sum_plus`,
`finite_depth_sum_minus`, B.3), and the tail of the continuous series (`tsum_betaP_tail_le_two`,
`tsum_betaM_tail_le_two`); finally `FI = FjrC`, `fI = fjr` (`Ident.lean`). -/

open Finset Real

namespace Palprimes.E1

open Palprimes.MT Palprimes.Greaves

/-- The continuous tail for `FI`: `FI s = 1 + Σ_{k<K} β⁺_k(s) + T`, `0 ≤ T ≤ 2 A^K/(1−A)`. -/
theorem FI_split (K : ℕ) {s : ℝ} (hs : 1 ≤ s) :
    ∃ T : ℝ, FI s = 1 + ∑ k ∈ range K, betaP k s + T ∧ 0 ≤ T ∧ T ≤ 2 * rateA ^ K / (1 - rateA) := by
  refine ⟨∑' k, betaP (k + K) s, ?_, tsum_nonneg fun k => betaP_nonneg _ (by linarith),
    tsum_betaP_tail_le_two K hs⟩
  rw [FI_def, ← (summable_betaP hs).sum_add_tsum_nat_add K]
  ring

/-- The continuous tail for `fI`: `fI s = 1 − Σ_{k<K} β⁻_k(s) − T`, `0 ≤ T ≤ 2 A^K/(1−A)`. -/
theorem fI_split (K : ℕ) {s : ℝ} (hs : 2 ≤ s) :
    ∃ T : ℝ, fI s = 1 - ∑ k ∈ range K, betaM k s - T ∧ 0 ≤ T ∧ T ≤ 2 * rateA ^ K / (1 - rateA) := by
  refine ⟨∑' k, betaM (k + K) s, ?_, tsum_nonneg fun k => betaM_nonneg _ (by linarith),
    tsum_betaM_tail_le_two K hs⟩
  rw [fI_def, ← (summable_betaM hs).sum_add_tsum_nat_add K]
  ring

/-- A depth `K` beyond which the continuous tails are at most `η`. -/
theorem exists_tail_small {η : ℝ} (hη : 0 < η) :
    ∃ K : ℕ, ∀ K' : ℕ, K ≤ K' → 2 * rateA ^ K' / (1 - rateA) ≤ η := by
  have h1 : 0 < 1 - rateA := by linarith [rateA_lt_one]
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (show 0 < η * (1 - rateA) / 2 by positivity) rateA_lt_one
  refine ⟨K, fun K' hKK' => ?_⟩
  have h2 : rateA ^ K' ≤ rateA ^ K := pow_le_pow_of_le_one rateA_nonneg rateA_lt_one.le hKK'
  rw [div_le_iff₀ h1]
  linarith

/-- **Greaves' Lemma 4.2** (Rosser–Iwaniec linear sieve, main terms) for the density `gB b`, `b ≥ 2`. -/
theorem rosserAsymp_of_two_le (b : ℕ) (hb : 2 ≤ b) : Palprimes.MT.RosserAsymp b := by
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨K₁, hK₁⟩ := Splus_trunc b hb hε3
  obtain ⟨K₂, hK₂⟩ := Sminus_trunc b hb hε3
  obtain ⟨K₃, hK₃⟩ := exists_tail_small hε3
  set K' := max (max K₁ K₂) K₃ with hK'
  have hK₁' : K₁ ≤ K' := le_trans (le_max_left _ _) (le_max_left _ _)
  have hK₂' : K₂ ≤ K' := le_trans (le_max_right _ _) (le_max_left _ _)
  have hK₃' : K₃ ≤ K' := le_max_right _ _
  obtain ⟨Dp, hDp⟩ := finite_depth_sum_plus b hb K' hε3
  obtain ⟨Dm, hDm⟩ := finite_depth_sum_minus b hb K' hε3
  refine ⟨max (max Dp Dm) (2 ^ (9 : ℕ)), fun z hz => ?_⟩
  have hzp : Dp ≤ z := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hz
  have hzm : Dm ≤ z := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hz
  have hz9 : (2 : ℝ) ^ (9 : ℕ) ≤ z := le_trans (le_max_right _ _) hz
  have hz1 : 1 < z := lt_of_lt_of_le (by norm_num) hz9
  have htail := hK₃ K' hK₃'
  constructor
  · intro s hs1 hs9
    have hs0 : 0 < s := by linarith
    set w := z ^ (1 / s) with hw
    have hVpos : 0 < VB b w := VB_pos' b w
    have hw2 : 2 ≤ w := two_le_rpow_one_div hz9 hs0 hs9
    have hwz : w ≤ z := rpow_one_div_le_self hz1.le hs1
    have h1 := hK₁ K' hK₁' z s hw2 hwz
    have h2 := hDp z hzp w hw2 hwz
    rw [hw, log_div_log_rpow hz1 hs0, ← hw] at h2
    obtain ⟨T, hFI, hT0, hT⟩ := FI_split K' hs1
    rw [← FI_eq_FjrC hs1, hFI]
    have hVT : VB b w * T ≤ ε / 3 * VB b w := by nlinarith
    have hVT0 : 0 ≤ VB b w * T := mul_nonneg hVpos.le hT0
    rw [abs_le] at h1 h2 ⊢
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
  · intro s hs2 hs9
    have hs0 : 0 < s := by linarith
    have hs1 : 1 ≤ s := by linarith
    set w := z ^ (1 / s) with hw
    have hVpos : 0 < VB b w := VB_pos' b w
    have hw2 : 2 ≤ w := two_le_rpow_one_div hz9 hs0 hs9
    have hwsq : w ^ 2 ≤ z := rpow_one_div_sq_le hz1.le hs2
    have hwh : w ≤ z ^ (1 / 2 : ℝ) := le_rpow_half_of_sq_le hwsq
    have h1 := hK₂ K' hK₂' z s hw2 hwsq
    have h2 := hDm z hzm w hw2 hwh
    rw [hw, log_div_log_rpow hz1 hs0, ← hw] at h2
    obtain ⟨T, hfI, hT0, hT⟩ := fI_split K' hs2
    rw [← fI_eq_fjr hs2, hfI]
    have hVT : VB b w * T ≤ ε / 3 * VB b w := by nlinarith
    have hVT0 : 0 ≤ VB b w * T := mul_nonneg hVpos.le hT0
    rw [abs_le] at h1 h2 ⊢
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

end Palprimes.E1
