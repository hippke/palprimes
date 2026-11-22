import Palprimes.TL1.Asymp
import Palprimes.Major1D.Data

/-! # TL¹ for the bases `b = 4, …, 9` through one-dimensional majorants

For `l = 1`, `Γ(x, y) = D_b(x + y)`, so a trigonometric polynomial `T(t) = Σ_{|v|<b} τ_v cos 2πvt`
with `T ≥ ψ_b^{p/2}` is a `BlockMaj b 1` with frequencies `(v, v)`. In the variable `c = cos 2πt`
both `T` and `ψ_b` are rational polynomials (`pev_cheb`), and `T(c) ≥ ψ_b(c)^q` on `[−1, 1]` is the
kernel-checked cell certificate of `Major1D/Data.lean` (`chk_sound`).
* `smMaj`: the block majorant from a certificate;
* `tl1_of_cert`: `tl1_eventually` with `θ = 0.2608`, `δ = 0.47`, conditions (ii), (iii) in exact
  exponent form (Nat inequalities, kernel-checked);
* `tl1_small`: TL¹ for `4 ≤ b ≤ 9`. -/

set_option linter.style.longLine false

open Finset Real

namespace Palprimes
namespace M1D

/-- Frequencies `(v, v)`, `v = k − (b − 1)`, `k < 2b − 1`. -/
def sS (b : ℕ) : Finset (ℤ × ℤ) :=
  (range (2 * b - 1)).image (fun k : ℕ => ((k : ℤ) - ((b : ℤ) - 1), (k : ℤ) - ((b : ℤ) - 1)))

/-- Coefficients `τ(v, ·) = c_{|v|} / 2^52`. -/
noncomputable def sTau (cs : List ℕ) (w : ℤ × ℤ) : ℝ := (tq cs w.1 : ℝ)

theorem sTau_nonneg (cs : List ℕ) (w : ℤ × ℤ) : 0 ≤ sTau cs w := by
  unfold sTau tq; push_cast; positivity

theorem cos_natAbs (v : ℤ) (θ : ℝ) : Real.cos ((v.natAbs : ℝ) * θ) = Real.cos ((v : ℝ) * θ) := by
  rw [Nat.cast_natAbs, Int.cast_abs]
  rcases abs_choice (v : ℝ) with h | h
  · rw [h]
  · rw [h, neg_mul, Real.cos_neg]

theorem cos_cheb (v : ℤ) (s : ℝ) :
    Real.cos (2 * π * ((v : ℝ) * s)) = pev (cheb v.natAbs) (Real.cos (2 * π * s)) := by
  rw [pev_cheb, cos_natAbs]; ring_nf

theorem Tval_eq (b : ℕ) (cs : List ℕ) (x y : ℝ) :
    Tval (sS b) (sTau cs) x y = pev (mkPT b cs) (Real.cos (2 * π * (x + y))) := by
  unfold Tval sS
  rw [Finset.sum_image (fun a _ c _ h => by
    have := congrArg Prod.fst h
    simp only at this
    exact_mod_cast (by linarith : (a : ℤ) = c))]
  unfold mkPT
  rw [pev_mk]
  apply Finset.sum_congr rfl; intro k _
  rw [pev_psmul, ← cos_cheb]
  unfold sTau
  congr 2; ring

theorem psiB_eq (b : ℕ) (t : ℝ) : psiB b t = pev (mkPsi b) (Real.cos (2 * π * t)) := by
  unfold psiB phiB mkPsi
  rw [div_pow, norm_sq_sum_range_ee, pev_psmul, pev_mk]
  simp_rw [pev_mk, ← cos_cheb]
  push_cast
  rw [div_eq_inv_mul, one_div]

/-- **The block majorant** of a cell certificate. -/
noncomputable def smMaj (b : ℕ) (hb : 2 ≤ b) (cs : List ℕ) (nq dq : ℕ) (hq : 0 < nq ∧ 2 * nq < dq)
    (cells : List (ℚ × ℚ × ℚ × ℚ)) (hchk : chk (mkPT b cs) (mkPsi b) nq dq (-1) cells = true) :
    BlockMaj b 1 where
  S := sS b
  τ := sTau cs
  p := 2 * nq / dq
  hp0 := by
    have : (0 : ℝ) < nq := by exact_mod_cast hq.1
    have : (0 : ℝ) < dq := by exact_mod_cast (by omega : 0 < dq)
    positivity
  hp1 := by
    have : (0 : ℝ) < dq := by exact_mod_cast (by omega : 0 < dq)
    rw [div_le_one this]; exact_mod_cast (by omega : 2 * nq ≤ dq)
  h00 := by
    unfold sS
    refine Finset.mem_image.2 ⟨b - 1, Finset.mem_range.2 (by omega), ?_⟩
    have : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by omega
    rw [this]; simp
  hS := by
    intro w hw
    unfold sS at hw
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hw
    rw [Finset.mem_range] at hk
    simp only [pow_one]
    constructor <;> (rw [abs_lt]; constructor <;> omega)
  hneg := by
    intro w hw
    unfold sS at hw ⊢
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hw
    rw [Finset.mem_range] at hk
    refine Finset.mem_image.2 ⟨2 * b - 2 - k, Finset.mem_range.2 (by omega), ?_⟩
    have : ((2 * b - 2 - k : ℕ) : ℤ) = 2 * (b : ℤ) - 2 - k := by omega
    rw [this, Prod.neg_mk]; congr 1 <;> ring
  hsym := by
    intro w _
    simp [sTau, tq, Int.natAbs_neg]
  hmaj := by
    intro x y
    have hG : Gam b 1 x y = Dfun b (x + y) := by simp [Gam]
    have hd : (0 : ℝ) < dq := by exact_mod_cast (by omega : 0 < dq)
    rw [hG, norm_Dfun b (by omega), Tval_eq, Real.sqrt_eq_rpow, ← Real.rpow_mul (psiB_nonneg b _)]
    have e : (1 / 2 : ℝ) * (2 * nq / dq) = (nq : ℝ) / dq := by field_simp
    have hu := psiB_nonneg b (x + y)
    rw [e, psiB_eq] at *
    exact chk_sound _ _ nq dq (by omega) (by omega) cells (-1) (by norm_num) hchk _
      (by push_cast; exact Real.neg_one_le_cos _) (Real.cos_le_one _) hu

theorem smMaj_t00 (b : ℕ) (hb : 2 ≤ b) (cs : List ℕ) (nq dq : ℕ) (hq : 0 < nq ∧ 2 * nq < dq)
    (cells : List (ℚ × ℚ × ℚ × ℚ)) (hchk : chk (mkPT b cs) (mkPsi b) nq dq (-1) cells = true)
    (c0 : ℕ) (hc0 : cs.getD 0 0 = c0) :
    (smMaj b hb cs nq dq hq cells hchk).t00 = (c0 : ℝ) / 2 ^ 52 := by
  change sTau cs (0, 0) = _
  unfold sTau tq
  simp only [Int.natAbs_zero, hc0]
  push_cast; ring

theorem smMaj_A (b : ℕ) (hb : 2 ≤ b) (cs : List ℕ) (nq dq : ℕ) (hq : 0 < nq ∧ 2 * nq < dq)
    (cells : List (ℚ × ℚ × ℚ × ℚ)) (hchk : chk (mkPT b cs) (mkPsi b) nq dq (-1) cells = true)
    (Anum : ℕ) (hA : qev (mkPT b cs) 1 = (Anum : ℚ) / 2 ^ 52) :
    (smMaj b hb cs nq dq hq cells hchk).A = (Anum : ℝ) / 2 ^ 52 := by
  change ∑ w ∈ sS b, |sTau cs w| = _
  have h := Tval_eq b cs 0 0
  simp only [Tval, mul_zero, add_zero, Real.cos_zero, mul_one] at h
  rw [Finset.sum_congr rfl (fun w _ => abs_of_nonneg (sTau_nonneg cs w)), h,
    show (1 : ℝ) = ((1 : ℚ) : ℝ) by simp, pev_cast, hA]
  push_cast; ring

/-- **TL¹ from a cell certificate** (`l = 1`, `θ = 0.2608`, `δ = 0.47`). Conditions (ii), (iii) at
`κ = ε = 0` in exponent form: `b^g t₀₀^D < r^s` and `A^E < r^k`, `r = 3b²/(2b²+1)`,
`g/D = 2θ`, `s/D = 2θ(1−p)/3`, `k/E = δ(1−p)/3`, as Nat inequalities. -/
theorem tl1_of_cert (b : ℕ) (hb : 2 ≤ b) (cs : List ℕ) (nq dq : ℕ) (hq : 0 < nq ∧ 2 * nq < dq)
    (cells : List (ℚ × ℚ × ℚ × ℚ)) (hchk : chk (mkPT b cs) (mkPsi b) nq dq (-1) cells = true)
    (c0 Anum D g s E k : ℕ) (hc0 : cs.getD 0 0 = c0) (hc0pos : 0 < c0) (hc01 : c0 ≤ 2 ^ 52)
    (hA : qev (mkPT b cs) 1 = (Anum : ℚ) / 2 ^ 52) (hA1 : 2 ^ 52 ≤ Anum)
    (hD0 : 0 < D) (hD : 625 * g = 326 * D) (hs : 1875 * dq * s = 326 * D * (dq - 2 * nq))
    (hii : b ^ g * c0 ^ D * (2 * b ^ 2 + 1) ^ s < (3 * b ^ 2) ^ s * 2 ^ (52 * D))
    (hE0 : 0 < E) (hE : 300 * dq * k = 47 * E * (dq - 2 * nq))
    (hiii : Anum ^ E * (2 * b ^ 2 + 1) ^ k < (3 * b ^ 2) ^ k * 2 ^ (52 * E)) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 ∧
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ R0 : ℕ, ((b : ℝ) ^ N) ^ (47 / 100 : ℝ) ≤ R0 →
      (R0 : ℝ) ≤ ((b : ℝ) ^ (2 * N + 1)) ^ (2608 / 10000 : ℝ) →
      ∀ Qs : Finset ℕ, (∀ q ∈ Qs, R0 ≤ q ∧ q ≤ 2 * R0 ∧ Nat.Coprime q b) → ∀ β : ℝ,
        ∑ q ∈ Qs, ∑ h ∈ redRes q, Fprod b N ((h : ℝ) / q + β) ≤ R0 * ((b : ℝ) ^ N) ^ (-κ) := by
  set M := smMaj b hb cs nq dq hq cells hchk with hM
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hb0 : (0 : ℝ) < b := by linarith
  have hLb : 0 < Real.log b := Real.log_pos hb1
  have hdq : (0 : ℝ) < dq := by exact_mod_cast (by omega : 0 < dq)
  have hMp : M.p = 2 * nq / dq := rfl
  have hp0 : 0 < M.p := M.hp0
  have hp1 : M.p ≤ 1 := M.hp1
  have ht00 := smMaj_t00 b hb cs nq dq hq cells hchk c0 hc0
  have hMA := smMaj_A b hb cs nq dq hq cells hchk Anum hA
  have hc0r : (0 : ℝ) < c0 := by exact_mod_cast hc0pos
  have hAr : (0 : ℝ) < Anum := by exact_mod_cast (by omega : 0 < Anum)
  set t0 : ℝ := (c0 : ℝ) / 2 ^ 52 with ht0def
  set A0 : ℝ := (Anum : ℝ) / 2 ^ 52 with hA0def
  have ht0pos : 0 < t0 := by positivity
  have ht01 : t0 ≤ 1 := by
    rw [ht0def, div_le_one (by positivity)]; exact_mod_cast hc01
  have hA01 : 1 ≤ A0 := by
    rw [hA0def, le_div_iff₀ (by positivity), one_mul]; exact_mod_cast hA1
  have hA0pos : 0 < A0 := by linarith
  have hthB : thetaB b = Real.log (3 * (b : ℝ) ^ 2 / (2 * (b : ℝ) ^ 2 + 1)) / Real.log b := by
    rw [thetaB, Real.logb]
  have hLr : Real.log (3 * (b : ℝ) ^ 2 / (2 * (b : ℝ) ^ 2 + 1)) =
      Real.log (3 * (b : ℝ) ^ 2) - Real.log (2 * (b : ℝ) ^ 2 + 1) :=
    Real.log_div (by positivity) (by positivity)
  have hpq : (1 : ℝ) - M.p = ((dq : ℝ) - 2 * nq) / dq := by rw [hMp]; field_simp
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD0
  have hEr : (0 : ℝ) < E := by exact_mod_cast hE0
  have hg' : (g : ℝ) = 2 * (2608 / 10000) * D := by
    have : ((625 * g : ℕ) : ℝ) = ((326 * D : ℕ) : ℝ) := by rw [hD]
    push_cast at this; linarith
  have hs' : (s : ℝ) = 2 * (2608 / 10000) * (1 - M.p) / 3 * D := by
    have : ((1875 * dq * s : ℕ) : ℝ) = ((326 * D * (dq - 2 * nq) : ℕ) : ℝ) := by rw [hs]
    push_cast [Nat.cast_sub (by omega : 2 * nq ≤ dq)] at this
    rw [hpq]; field_simp; linarith
  have hk' : (k : ℝ) = 47 / 100 * (1 - M.p) / 3 * E := by
    have : ((300 * dq * k : ℕ) : ℝ) = ((47 * E * (dq - 2 * nq) : ℕ) : ℝ) := by rw [hE]
    push_cast [Nat.cast_sub (by omega : 2 * nq ≤ dq)] at this
    rw [hpq]; field_simp; linarith
  have hl2 : Real.log ((2 : ℝ) ^ 52) = 52 * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
  -- (ii) in logarithmic form
  have hlii : 2 * (2608 / 10000) * Real.log b + Real.log t0 <
      2 * (2608 / 10000) * (1 - M.p) / 3 * Real.log (3 * (b : ℝ) ^ 2 / (2 * (b : ℝ) ^ 2 + 1)) := by
    have h : (b : ℝ) ^ g * (c0 : ℝ) ^ D * (2 * (b : ℝ) ^ 2 + 1) ^ s <
        (3 * (b : ℝ) ^ 2) ^ s * (2 : ℝ) ^ (52 * D) := by exact_mod_cast hii
    have hl := Real.log_lt_log (by positivity) h
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow,
      Real.log_pow, Real.log_pow, hg', hs'] at hl
    push_cast at hl
    rw [ht0def, Real.log_div (by positivity) (by positivity), hl2, hLr]
    suffices hX : (D : ℝ) * (2 * (2608 / 10000) * Real.log b + (Real.log c0 - 52 * Real.log 2) -
        2 * (2608 / 10000) * (1 - M.p) / 3 * (Real.log (3 * (b : ℝ) ^ 2) - Real.log (2 * (b : ℝ) ^ 2 + 1))) < D * 0 by
      have := lt_of_mul_lt_mul_left hX hDr.le
      linarith
    linarith
  -- (iii) in logarithmic form
  have hliii : Real.log A0 <
      47 / 100 * (1 - M.p) / 3 * Real.log (3 * (b : ℝ) ^ 2 / (2 * (b : ℝ) ^ 2 + 1)) := by
    have h : (Anum : ℝ) ^ E * (2 * (b : ℝ) ^ 2 + 1) ^ k <
        (3 * (b : ℝ) ^ 2) ^ k * (2 : ℝ) ^ (52 * E) := by exact_mod_cast hiii
    have hl := Real.log_lt_log (by positivity) h
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, hk'] at hl
    push_cast at hl
    rw [hA0def, Real.log_div (by positivity) (by positivity), hl2, hLr]
    suffices hX : (E : ℝ) * ((Real.log Anum - 52 * Real.log 2) -
        47 / 100 * (1 - M.p) / 3 * (Real.log (3 * (b : ℝ) ^ 2) - Real.log (2 * (b : ℝ) ^ 2 + 1))) < E * 0 by
      have := lt_of_mul_lt_mul_left hX hEr.le
      linarith
    linarith
  set ψ := -Real.logb b t0 with hψdef
  set lamA := Real.logb b A0 with hlamdef
  have hψ0 : 0 ≤ ψ := by
    have := Real.logb_nonpos hb1 ht0pos.le ht01; linarith
  have hlam0 : 0 ≤ lamA := Real.logb_nonneg hb1 hA01
  have hgap2 : 0 < ψ + 2 * (2608 / 10000) * thetaB b * (1 - M.p) / 3 - 2 * (2608 / 10000) := by
    have e : ψ + 2 * (2608 / 10000) * thetaB b * (1 - M.p) / 3 - 2 * (2608 / 10000) =
        (2 * (2608 / 10000) * (1 - M.p) / 3 * Real.log (3 * (b : ℝ) ^ 2 / (2 * (b : ℝ) ^ 2 + 1)) -
          (2 * (2608 / 10000) * Real.log b + Real.log t0)) / Real.log b := by
      rw [hthB, hψdef, Real.logb]; field_simp; ring
    rw [e]; apply div_pos _ hLb; linarith
  have hgap3 : 0 < 47 / 100 * thetaB b * (1 - M.p) / 3 - lamA := by
    have e : 47 / 100 * thetaB b * (1 - M.p) / 3 - lamA =
        (47 / 100 * (1 - M.p) / 3 * Real.log (3 * (b : ℝ) ^ 2 / (2 * (b : ℝ) ^ 2 + 1)) -
          Real.log A0) / Real.log b := by
      rw [hthB, hlamdef, Real.logb]; field_simp
    rw [e]; apply div_pos _ hLb; linarith
  set κ := min ((ψ + 2 * (2608 / 10000) * thetaB b * (1 - M.p) / 3 - 2 * (2608 / 10000)) / 4)
    ((47 / 100 * thetaB b * (1 - M.p) / 3 - lamA) / 6) with hκ
  have hκ0 : 0 < κ := lt_min (by linarith) (by linarith)
  have hκ1 := min_le_left ((ψ + 2 * (2608 / 10000) * thetaB b * (1 - M.p) / 3 - 2 * (2608 / 10000)) / 4)
    ((47 / 100 * thetaB b * (1 - M.p) / 3 - lamA) / 6)
  have hκ2 := min_le_right ((ψ + 2 * (2608 / 10000) * thetaB b * (1 - M.p) / 3 - 2 * (2608 / 10000)) / 4)
    ((47 / 100 * thetaB b * (1 - M.p) / 3 - lamA) / 6)
  rw [← hκ] at hκ1 hκ2
  have hθb := thetaB_pos b hb
  have hθb1 := thetaB_le_one b hb
  have hκle : κ ≤ 1 := by
    have h1 : thetaB b * (1 - M.p) ≤ 1 := by
      nlinarith [mul_le_mul_of_nonneg_right hθb1 (by linarith : (0 : ℝ) ≤ 1 - M.p)]
    have h2 : 0 ≤ thetaB b * (1 - M.p) := mul_nonneg hθb.le (by linarith)
    linarith
  refine ⟨κ, hκ0, hκle, ?_⟩
  apply tl1_eventually M hb le_rfl ψ lamA (2608 / 10000) (47 / 100) κ κ hψ0 hlam0 (by norm_num)
    (by norm_num) (by norm_num) hκ0 hκ0 hκle hp0.le
  · rw [ht00]; exact ht0pos.le
  · rw [ht00, Nat.cast_one, one_mul, hψdef, neg_neg, Real.rpow_logb hb0 hb1.ne' ht0pos]
  · rw [hMA, Nat.cast_one, one_mul, hlamdef, Real.rpow_logb hb0 hb1.ne' hA0pos]
  · linarith
  · linarith

end M1D

open M1D in
/-- **TL¹ for the bases `4 ≤ b ≤ 9`** at `θ = 0.2608`, `δ = 0.47` (same statement as
`tl1_ge_ten`), from the one-dimensional majorants of `Major1D/Data.lean`. -/
theorem tl1_small (b : ℕ) (hb4 : 4 ≤ b) (hb9 : b ≤ 9) : ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 ∧
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ R0 : ℕ, ((b : ℝ) ^ N) ^ (47 / 100 : ℝ) ≤ R0 →
      (R0 : ℝ) ≤ ((b : ℝ) ^ (2 * N + 1)) ^ (2608 / 10000 : ℝ) →
      ∀ Qs : Finset ℕ, (∀ q ∈ Qs, R0 ≤ q ∧ q ≤ 2 * R0 ∧ Nat.Coprime q b) → ∀ β : ℝ,
        ∑ q ∈ Qs, ∑ h ∈ redRes q, Fprod b N ((h : ℝ) / q + β) ≤ R0 * ((b : ℝ) ^ N) ^ (-κ) := by
  interval_cases b
  · exact tl1_of_cert 4 (by norm_num) cs4 49 100 (by norm_num) cells4 chk4
      2188159714910440 4508764286329902 46875 24450 163 15000 47
      rfl (by norm_num) (by norm_num) A4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by norm_num) (by norm_num) (by decide +kernel)
  · exact tl1_of_cert 5 (by norm_num) cs5 47 100 (by norm_num) cells5 chk5
      1953035007160506 4519807413965876 15625 8150 163 5000 47
      rfl (by norm_num) (by norm_num) A5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by norm_num) (by norm_num) (by decide +kernel)
  · exact tl1_of_cert 6 (by norm_num) cs6 23 50 (by norm_num) cells6 chk6
      1775680807211085 4525595413559303 46875 24450 652 3750 47
      rfl (by norm_num) (by norm_num) A6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by norm_num) (by norm_num) (by decide +kernel)
  · exact tl1_of_cert 7 (by norm_num) cs7 9 20 (by norm_num) cells7 chk7
      1637471435636414 4531395753848208 9375 4890 163 3000 47
      rfl (by norm_num) (by norm_num) A7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by norm_num) (by norm_num) (by decide +kernel)
  · exact tl1_of_cert 8 (by norm_num) cs8 11 25 (by norm_num) cells8 chk8
      1534944601438154 4537200419718910 15625 8150 326 2500 47
      rfl (by norm_num) (by norm_num) A8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by norm_num) (by norm_num) (by decide +kernel)
  · exact tl1_of_cert 9 (by norm_num) cs9 11 25 (by norm_num) cells9 chk9
      1420959258721672 4537328196579274 15625 8150 326 2500 47
      rfl (by norm_num) (by norm_num) A9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by norm_num) (by norm_num) (by decide +kernel)
end Palprimes
