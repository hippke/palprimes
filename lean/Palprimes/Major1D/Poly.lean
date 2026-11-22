import Mathlib

/-! # Major1D: list polynomials and an exact cell checker for `T ≥ ψ^q`

Polynomials are coefficient lists over `ℚ` (constant term first), evaluated by Horner.
* `pev_cheb`: `cheb n` evaluated at `cos θ` is `cos (n θ)`;
* `rpow_le_tangent`: `u^q ≤ A + B u` from `A ≥ (1−q) w^{nq}`, `B w^{dq−nq} ≥ q`, `q = nq/dq`
  (the tangent of the concave `u ↦ u^q` at `u₀ = w^{dq}`, weighted AM–GM);
* `chk_sound`: a passed cell list (`chk`) gives `P_ψ(c)^q ≤ P_T(c)` for all `c ∈ [lo, 1]`.
  On a cell `[lo, hi]` the checker shifts `P_T − B P_ψ − A` to the centre `m` and bounds it below
  by `a₀ − h Σ_{k≥1} |a_k| h^{k−1}`, `h` the half width. Everything is exact rational arithmetic,
  decided by the kernel. -/

set_option linter.style.longLine false

open Real

namespace Palprimes
namespace M1D

/-- Real Horner evaluation of a rational coefficient list. -/
noncomputable def pev : List ℚ → ℝ → ℝ
  | [], _ => 0
  | a :: L, x => (a : ℝ) + x * pev L x

/-- Rational Horner evaluation. -/
def qev : List ℚ → ℚ → ℚ
  | [], _ => 0
  | a :: L, x => a + x * qev L x

theorem pev_cast (L : List ℚ) (x : ℚ) : pev L x = (qev L x : ℝ) := by
  induction L with
  | nil => simp [pev, qev]
  | cons a L ih => simp [pev, qev, ih]

def padd : List ℚ → List ℚ → List ℚ
  | [], Q => Q
  | a :: P, [] => a :: P
  | a :: P, b :: Q => (a + b) :: padd P Q

theorem pev_padd : ∀ (P Q : List ℚ) (x : ℝ), pev (padd P Q) x = pev P x + pev Q x
  | [], Q, x => by simp [padd, pev]
  | a :: P, [], x => by simp [padd, pev]
  | a :: P, b :: Q, x => by simp only [padd, pev, pev_padd P Q x]; push_cast; ring

def psmul (s : ℚ) : List ℚ → List ℚ
  | [] => []
  | a :: P => (s * a) :: psmul s P

theorem pev_psmul (s : ℚ) : ∀ (P : List ℚ) (x : ℝ), pev (psmul s P) x = s * pev P x
  | [], x => by simp [psmul, pev]
  | a :: P, x => by simp only [psmul, pev, pev_psmul s P x]; push_cast; ring

/-- Add a constant. -/
def addC (c : ℚ) : List ℚ → List ℚ
  | [] => [c]
  | a :: P => (a + c) :: P

theorem pev_addC (c : ℚ) (P : List ℚ) (x : ℝ) : pev (addC c P) x = c + pev P x := by
  cases P with
  | nil => simp [addC, pev]
  | cons a P => simp only [addC, pev]; push_cast; ring

/-- `prev + (m + X) S(X)`. -/
def mlAux (m : ℚ) : ℚ → List ℚ → List ℚ
  | prev, [] => [prev]
  | prev, s :: S => (m * s + prev) :: mlAux m s S

theorem pev_mlAux (m : ℚ) : ∀ (prev : ℚ) (S : List ℚ) (x : ℝ),
    pev (mlAux m prev S) x = prev + (m + x) * pev S x
  | prev, [], x => by simp [mlAux, pev]
  | prev, s :: S, x => by simp only [mlAux, pev, pev_mlAux m s S x]; push_cast; ring

/-- Taylor shift: `shift m L (X) = L(m + X)`. -/
def shift (m : ℚ) : List ℚ → List ℚ
  | [] => []
  | a :: L => mlAux m a (shift m L)

theorem pev_shift (m : ℚ) : ∀ (L : List ℚ) (x : ℝ), pev (shift m L) x = pev L (m + x)
  | [], x => by simp [shift, pev]
  | a :: L, x => by rw [shift, pev_mlAux, pev_shift m L x]; simp [pev]

/-- `Σ |a_k| h^k`. -/
def absb (h : ℚ) : List ℚ → ℚ
  | [] => 0
  | a :: L => |a| + h * absb h L

theorem absb_nonneg (h : ℚ) (hh : 0 ≤ h) : ∀ L : List ℚ, 0 ≤ absb h L
  | [] => by simp [absb]
  | a :: L => by
    have := absb_nonneg h hh L
    simp only [absb]; positivity

theorem abs_pev_le (h : ℚ) (hh : 0 ≤ h) (x : ℝ) (hx : |x| ≤ h) :
    ∀ L : List ℚ, |pev L x| ≤ (absb h L : ℝ)
  | [] => by simp [pev, absb]
  | a :: L => by
    have ih := abs_pev_le h hh x hx L
    have h0 : (0 : ℝ) ≤ absb h L := by exact_mod_cast absb_nonneg h hh L
    simp only [pev, absb]; push_cast
    calc |(a : ℝ) + x * pev L x| ≤ |(a : ℝ)| + |x| * |pev L x| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |(a : ℝ)| + (h : ℝ) * absb h L := by
          gcongr

/-- Lower bound `a₀ − h Σ_{k≥1} |a_k| h^{k−1}` on `|X| ≤ h`. -/
def lowbd (h : ℚ) : List ℚ → ℚ
  | [] => 0
  | a :: L => a - h * absb h L

theorem lowbd_le (h : ℚ) (hh : 0 ≤ h) (x : ℝ) (hx : |x| ≤ h) (L : List ℚ) :
    (lowbd h L : ℝ) ≤ pev L x := by
  cases L with
  | nil => simp [lowbd, pev]
  | cons a L =>
    have h1 := abs_pev_le h hh x hx L
    have h2 : |x * pev L x| ≤ (h : ℝ) * absb h L := by
      rw [abs_mul]; exact mul_le_mul hx h1 (abs_nonneg _) (le_trans (abs_nonneg _) hx)
    simp only [lowbd, pev]; push_cast
    have := neg_abs_le (x * pev L x)
    linarith

/-! ## Chebyshev polynomials -/

/-- Chebyshev `T_n` as a coefficient list. -/
def cheb : ℕ → List ℚ
  | 0 => [1]
  | 1 => [0, 1]
  | n + 2 => padd (0 :: psmul 2 (cheb (n + 1))) (psmul (-1) (cheb n))

theorem pev_cheb : ∀ (n : ℕ) (θ : ℝ), pev (cheb n) (Real.cos θ) = Real.cos (n * θ)
  | 0, θ => by simp [cheb, pev]
  | 1, θ => by simp [cheb, pev]
  | n + 2, θ => by
    rw [cheb, pev_padd, pev, pev_psmul, pev_psmul, pev_cheb (n + 1), pev_cheb n]
    have e1 : ((n + 2 : ℕ) : ℝ) * θ = ((n + 1 : ℕ) : ℝ) * θ + θ := by push_cast; ring
    have e2 : (n : ℝ) * θ = ((n + 1 : ℕ) : ℝ) * θ - θ := by push_cast; ring
    rw [e1, e2, Real.cos_add, Real.cos_sub]
    push_cast; ring

/-- `Σ_{k<n} g k` as a list polynomial. -/
def mk (g : ℕ → List ℚ) : ℕ → List ℚ
  | 0 => []
  | n + 1 => padd (mk g n) (g n)

theorem pev_mk (g : ℕ → List ℚ) (x : ℝ) : ∀ n : ℕ,
    pev (mk g n) x = ∑ k ∈ Finset.range n, pev (g k) x
  | 0 => by simp [mk, pev]
  | n + 1 => by rw [mk, pev_padd, pev_mk g x n, Finset.sum_range_succ]

/-! ## The tangent bound and the cell checker -/

theorem rpow_le_tangent (nq dq : ℕ) (hq : nq ≤ dq) (hd : 0 < dq) (u w A B : ℝ) (hu : 0 ≤ u)
    (hw : 0 < w) (hA : (1 - (nq : ℝ) / dq) * w ^ nq ≤ A) (hB : (nq : ℝ) / dq ≤ B * w ^ (dq - nq)) :
    u ^ ((nq : ℝ) / dq) ≤ A + B * u := by
  set q : ℝ := (nq : ℝ) / dq with hqdef
  have hd' : (0 : ℝ) < dq := by exact_mod_cast hd
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := by
    rw [hqdef, div_le_one hd']; exact_mod_cast hq
  have hgm := Real.geom_mean_le_arith_mean2_weighted hq0 (by linarith : 0 ≤ 1 - q) hu
    (by positivity : 0 ≤ w ^ dq) (by ring)
  have hP : ((w ^ dq : ℝ)) ^ (1 - q) = w ^ (dq - nq) := by
    rw [← Real.rpow_natCast w dq, ← Real.rpow_mul hw.le]
    have : (dq : ℝ) * (1 - q) = ((dq - nq : ℕ) : ℝ) := by
      rw [Nat.cast_sub hq, hqdef]; field_simp
    rw [this, Real.rpow_natCast]
  rw [hP] at hgm
  have hP0 : 0 < w ^ (dq - nq) := by positivity
  have hsplit : w ^ dq = w ^ nq * w ^ (dq - nq) := by rw [← pow_add]; congr 1; omega
  rw [hsplit] at hgm
  have h1 := mul_le_mul_of_nonneg_right hA hP0.le
  have h2 := mul_le_mul_of_nonneg_right hB hu
  have h3 : u ^ q * w ^ (dq - nq) ≤ (A + B * u) * w ^ (dq - nq) := by nlinarith
  exact le_of_mul_le_mul_right h3 hP0

/-- One cell `[lo, hi]` with tangent data `w, A, B`. -/
def cellOK (PT Pψ : List ℚ) (nq dq : ℕ) (lo hi w A B : ℚ) : Bool :=
  decide (lo < hi) && decide (0 < w) && decide ((1 - (nq : ℚ) / dq) * w ^ nq ≤ A) &&
    decide ((nq : ℚ) / dq ≤ B * w ^ (dq - nq)) &&
    decide (0 ≤ lowbd ((hi - lo) / 2) (shift ((lo + hi) / 2) (addC (-A) (padd PT (psmul (-B) Pψ)))))

/-- Cells `(hi, w, A, B)`, consecutive from `lo` up to `1`. -/
def chk (PT Pψ : List ℚ) (nq dq : ℕ) : ℚ → List (ℚ × ℚ × ℚ × ℚ) → Bool
  | lo, [] => decide (1 ≤ lo)
  | lo, (hi, w, A, B) :: rest => cellOK PT Pψ nq dq lo hi w A B && chk PT Pψ nq dq hi rest

theorem cell_sound (PT Pψ : List ℚ) (nq dq : ℕ) (lo hi w A B : ℚ)
    (h : cellOK PT Pψ nq dq lo hi w A B = true) (hq : nq ≤ dq) (hd : 0 < dq)
    (c : ℝ) (hlo : (lo : ℝ) ≤ c) (hhi : c ≤ hi) (hu : 0 ≤ pev Pψ c) :
    pev Pψ c ^ ((nq : ℝ) / dq) ≤ pev PT c := by
  simp only [cellOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hlh, hw⟩, hA⟩, hB⟩, hF⟩ := h
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  have hA' : (1 - (nq : ℝ) / dq) * (w : ℝ) ^ nq ≤ A := by
    have := (Rat.cast_le (K := ℝ)).2 hA; push_cast at this; exact this
  have hB' : (nq : ℝ) / dq ≤ B * (w : ℝ) ^ (dq - nq) := by
    have := (Rat.cast_le (K := ℝ)).2 hB; push_cast at this; exact this
  have ht := rpow_le_tangent nq dq hq hd _ w A B hu hw' hA' hB'
  have hh : (0 : ℚ) ≤ (hi - lo) / 2 := by linarith
  have hx : |c - ((lo + hi) / 2 : ℚ)| ≤ (((hi - lo) / 2 : ℚ) : ℝ) := by
    rw [abs_le]; push_cast; constructor <;> linarith
  have hlow := lowbd_le _ hh _ hx (shift ((lo + hi) / 2) (addC (-A) (padd PT (psmul (-B) Pψ))))
  rw [pev_shift, add_sub_cancel, pev_addC, pev_padd, pev_psmul] at hlow
  have hF' : (0 : ℝ) ≤ lowbd ((hi - lo) / 2) (shift ((lo + hi) / 2) (addC (-A) (padd PT (psmul (-B) Pψ)))) := by
    exact_mod_cast hF
  push_cast at hlow
  linarith

theorem chk_sound_lt (PT Pψ : List ℚ) (nq dq : ℕ) (hq : nq ≤ dq) (hd : 0 < dq) :
    ∀ (cells : List (ℚ × ℚ × ℚ × ℚ)) (lo : ℚ), chk PT Pψ nq dq lo cells = true →
      ∀ c : ℝ, (lo : ℝ) < c → c ≤ 1 → 0 ≤ pev Pψ c → pev Pψ c ^ ((nq : ℝ) / dq) ≤ pev PT c
  | [], lo, h, c, hlo, h1, _ => by
    simp only [chk, decide_eq_true_eq] at h
    have : (1 : ℝ) ≤ lo := by exact_mod_cast h
    linarith
  | (hi, w, A, B) :: rest, lo, h, c, hlo, h1, hu => by
    simp only [chk, Bool.and_eq_true] at h
    rcases le_or_gt c hi with hc | hc
    · exact cell_sound PT Pψ nq dq lo hi w A B h.1 hq hd c hlo.le hc hu
    · exact chk_sound_lt PT Pψ nq dq hq hd rest hi h.2 c hc h1 hu

/-- **Soundness of the checker** on `[lo, 1]`, `lo < 1`. -/
theorem chk_sound (PT Pψ : List ℚ) (nq dq : ℕ) (hq : nq ≤ dq) (hd : 0 < dq)
    (cells : List (ℚ × ℚ × ℚ × ℚ)) (lo : ℚ) (hlo1 : lo < 1) (h : chk PT Pψ nq dq lo cells = true)
    (c : ℝ) (hlo : (lo : ℝ) ≤ c) (h1 : c ≤ 1) (hu : 0 ≤ pev Pψ c) :
    pev Pψ c ^ ((nq : ℝ) / dq) ≤ pev PT c := by
  rcases hlo.lt_or_eq with hlt | heq
  · exact chk_sound_lt PT Pψ nq dq hq hd cells lo h c hlt h1 hu
  · match cells, h with
    | [], h =>
      simp only [chk, decide_eq_true_eq] at h
      exact absurd h (not_le.2 hlo1)
    | (hi, w, A, B) :: rest, h =>
      simp only [chk, Bool.and_eq_true] at h
      have hlh : lo < hi := by
        have := h.1
        simp only [cellOK, Bool.and_eq_true, decide_eq_true_eq] at this
        exact this.1.1.1.1
      have : c ≤ hi := by rw [← heq]; exact_mod_cast hlh.le
      exact cell_sound PT Pψ nq dq lo hi w A B h.1 hq hd c hlo this hu

end M1D
end Palprimes
