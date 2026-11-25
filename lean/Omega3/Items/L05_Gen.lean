import Omega3.Statements
import Palprimes.Major1D.Poly

namespace Omega3.L05g

open Finset Palprimes Palprimes.M1D

set_option linter.style.longLine false

/-- Polynomial sum over `range n`. -/
def polySum (f : ℕ → List ℚ) : ℕ → List ℚ
  | 0 => []
  | n + 1 => padd (polySum f n) (f n)

theorem pev_polySum (f : ℕ → List ℚ) (x : ℝ) : ∀ n, pev (polySum f n) x = ∑ a ∈ range n, pev (f a) x
  | 0 => by simp [polySum, pev]
  | n + 1 => by rw [polySum, pev_padd, pev_polySum f x n, Finset.sum_range_succ]

/-- Polynomial product. -/
def pmul : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | a :: P, Q => padd (psmul a Q) (0 :: pmul P Q)

theorem pev_pmul : ∀ (P Q : List ℚ) (x : ℝ), pev (pmul P Q) x = pev P x * pev Q x
  | [], Q, x => by simp [pmul, pev]
  | a :: P, Q, x => by
    simp only [pmul, pev_padd, pev_psmul, pev, pev_pmul P Q x]; ring

/-- `|G|²` as a polynomial in `z = cos 2πt`. -/
def Apoly (gL : List ℚ) (n : ℕ) : List ℚ :=
  polySum (fun a => polySum (fun b => psmul (gL.getD a 0 * gL.getD b 0) (cheb (if a ≤ b then b - a else a - b))) n) n

/-- Majorant polynomial. -/
def Ppoly (τ : List ℚ) (H : ℕ) : List ℚ :=
  polySum (fun u => psmul (if u = 0 then τ.getD 0 0 else 2 * τ.getD u 0) (cheb u)) (H + 1)

def Fpoly (gL : List ℚ) (n : ℕ) (τ : List ℚ) (H : ℕ) : List ℚ :=
  padd (pmul (Ppoly τ H) (Ppoly τ H)) (psmul (-1) (Apoly gL n))

/-- Cell checker. -/
def chkP (F : List ℚ) : ℕ → ℚ → ℚ → Bool
  | 0, _, _ => false
  | k + 1, lo, hi =>
    if 0 ≤ lowbd ((hi - lo) / 2) (shift ((lo + hi) / 2) F) then true
    else chkP F k lo ((lo + hi) / 2) && chkP F k ((lo + hi) / 2) hi

theorem chkP_sound (F : List ℚ) : ∀ (k : ℕ) (lo hi : ℚ), chkP F k lo hi = true →
    ∀ x : ℝ, (lo : ℝ) ≤ x → x ≤ hi → 0 ≤ pev F x := by
  intro k
  induction k with
  | zero => intro lo hi h; simp [chkP] at h
  | succ k ih =>
    intro lo hi h x hlo hhi
    simp only [chkP] at h
    by_cases hc : 0 ≤ lowbd ((hi - lo) / 2) (shift ((lo + hi) / 2) F)
    · have hh : (0 : ℚ) ≤ (hi - lo) / 2 := by
        by_contra hneg
        push_neg at hneg
        have : (lo : ℝ) ≤ hi := le_trans hlo hhi
        have : lo ≤ hi := by exact_mod_cast this
        linarith
      have hx : |x - ((lo + hi) / 2 : ℚ)| ≤ (((hi - lo) / 2 : ℚ) : ℝ) := by
        rw [abs_le]; push_cast; constructor <;> linarith
      have h1 := lowbd_le ((hi - lo) / 2) hh (x - ((lo + hi) / 2 : ℚ)) hx (shift ((lo + hi) / 2) F)
      rw [pev_shift] at h1
      have h2 : (0 : ℝ) ≤ (lowbd ((hi - lo) / 2) (shift ((lo + hi) / 2) F) : ℝ) := by exact_mod_cast hc
      have : (((lo + hi) / 2 : ℚ) : ℝ) + (x - ((lo + hi) / 2 : ℚ)) = x := by ring
      rw [this] at h1
      linarith
    · rw [if_neg hc] at h
      simp only [Bool.and_eq_true] at h
      by_cases hxm : x ≤ (((lo + hi) / 2 : ℚ) : ℝ)
      · exact ih lo ((lo + hi) / 2) h.1 x hlo hxm
      · exact ih ((lo + hi) / 2) hi h.2 x (le_of_not_ge hxm) hhi

lemma ee_re_im (x : ℝ) : ee x = (Real.cos (2 * Real.pi * x) : ℂ) + (Real.sin (2 * Real.pi * x) : ℂ) * Complex.I := by
  unfold ee
  have : (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

theorem normsq (gL : List ℚ) (n : ℕ) (t : ℝ) :
    ‖∑ a ∈ range n, ((gL.getD a 0 : ℚ) : ℂ) * ee ((a : ℝ) * t)‖ ^ 2 =
      pev (Apoly gL n) (Real.cos (2 * Real.pi * t)) := by
  classical
  set θ := 2 * Real.pi * t with hθ
  set g : ℕ → ℝ := fun a => ((gL.getD a 0 : ℚ) : ℝ) with hg
  have hre : (∑ a ∈ range n, ((gL.getD a 0 : ℚ) : ℂ) * ee ((a : ℝ) * t)).re =
      ∑ a ∈ range n, g a * Real.cos (a * θ) := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl; intro a _
    have hq : ((gL.getD a 0 : ℚ) : ℂ) = (g a : ℂ) := by simp [hg]
    rw [hq, ee_re_im]
    have : 2 * Real.pi * ((a : ℝ) * t) = a * θ := by rw [hθ]; ring
    rw [this]
    simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.mul_im, Complex.add_im, Complex.ofReal_im, Complex.I_re, Complex.I_im, hg]
    ring
  have him : (∑ a ∈ range n, ((gL.getD a 0 : ℚ) : ℂ) * ee ((a : ℝ) * t)).im =
      ∑ a ∈ range n, g a * Real.sin (a * θ) := by
    rw [Complex.im_sum]
    apply Finset.sum_congr rfl; intro a _
    have hq : ((gL.getD a 0 : ℚ) : ℂ) = (g a : ℂ) := by simp [hg]
    rw [hq, ee_re_im]
    have : 2 * Real.pi * ((a : ℝ) * t) = a * θ := by rw [hθ]; ring
    rw [this]
    simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.mul_im, Complex.add_im, Complex.ofReal_im, Complex.I_re, Complex.I_im, hg]
    ring
  rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
  unfold Apoly
  rw [pev_polySum]
  have : ∀ a ∈ range n, pev (polySum (fun b => psmul (gL.getD a 0 * gL.getD b 0)
      (cheb (if a ≤ b then b - a else a - b))) n) (Real.cos θ) =
      ∑ b ∈ range n, g a * g b * Real.cos (((a : ℝ) - b) * θ) := by
    intro a _
    rw [pev_polySum]
    apply Finset.sum_congr rfl; intro b _
    rw [pev_psmul, pev_cheb]
    have hc : Real.cos (((if a ≤ b then b - a else a - b : ℕ) : ℝ) * θ) = Real.cos (((a : ℝ) - b) * θ) := by
      split_ifs with hab
      · rw [Nat.cast_sub hab, show ((b : ℝ) - a) * θ = -(((a : ℝ) - b) * θ) by ring, Real.cos_neg]
      · rw [Nat.cast_sub (by omega)]
    rw [hc]
    simp [hg]
  rw [Finset.sum_congr rfl this]
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro b _
  rw [sub_mul, Real.cos_sub]
  ring

theorem sum_Icc_range (f : ℕ → ℝ) : ∀ H : ℕ, ∑ u ∈ Icc 1 H, f u = ∑ i ∈ range H, f (i + 1)
  | 0 => by simp
  | H + 1 => by rw [Finset.sum_Icc_succ_top (by omega), sum_Icc_range f H, Finset.sum_range_succ]

theorem trig_eq (τ : List ℚ) (H : ℕ) (t : ℝ) :
    trigEval H (fun u => ((τ.getD u 0 : ℚ) : ℝ)) t = pev (Ppoly τ H) (Real.cos (2 * Real.pi * t)) := by
  unfold Ppoly
  rw [pev_polySum, Finset.sum_range_succ', trigEval, sum_Icc_range]
  have : ∀ i ∈ range H, pev (psmul (if i + 1 = 0 then τ.getD 0 0 else 2 * τ.getD (i + 1) 0) (cheb (i + 1))) (Real.cos (2 * Real.pi * t)) =
      2 * (((τ.getD (i + 1) 0 : ℚ) : ℝ) * Real.cos (2 * Real.pi * ((i + 1 : ℕ) : ℝ) * t)) := by
    intro i _
    rw [pev_psmul, pev_cheb, if_neg (by omega)]
    push_cast
    have : ((i : ℝ) + 1) * (2 * Real.pi * t) = 2 * Real.pi * ((i : ℝ) + 1) * t := by ring
    rw [this]; ring
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
  simp only [pev_psmul, pev_cheb, if_pos, Nat.cast_zero, zero_mul, Real.cos_zero, mul_one]
  push_cast
  ring

theorem cert_main (gL τ : List ℚ) (n H : ℕ)
    (hF : chkP (Fpoly gL n τ H) 60 (-1) 1 = true) (hP : chkP (Ppoly τ H) 60 (-1) 1 = true) (t : ℝ) :
    ‖∑ a ∈ range n, ((gL.getD a 0 : ℚ) : ℂ) * ee ((a : ℝ) * t)‖ ≤
      trigEval H (fun u => ((τ.getD u 0 : ℚ) : ℝ)) t := by
  set z := Real.cos (2 * Real.pi * t) with hz
  have hz1 : ((-1 : ℚ) : ℝ) ≤ z := by push_cast; exact Real.neg_one_le_cos _
  have hz2 : z ≤ ((1 : ℚ) : ℝ) := by push_cast; exact Real.cos_le_one _
  have hFz := chkP_sound _ 60 (-1) 1 hF z hz1 hz2
  have hPz := chkP_sound _ 60 (-1) 1 hP z hz1 hz2
  unfold Fpoly at hFz
  rw [pev_padd, pev_pmul, pev_psmul] at hFz
  have hn := normsq gL n t
  rw [trig_eq]
  have hnn : 0 ≤ ‖∑ a ∈ range n, ((gL.getD a 0 : ℚ) : ℂ) * ee ((a : ℝ) * t)‖ := norm_nonneg _
  by_contra hcon
  push_neg at hcon
  have : pev (Ppoly τ H) z ^ 2 < ‖∑ a ∈ range n, ((gL.getD a 0 : ℚ) : ℂ) * ee ((a : ℝ) * t)‖ ^ 2 := by
    nlinarith
  rw [hn] at this
  push_cast at hFz
  nlinarith

end Omega3.L05g
