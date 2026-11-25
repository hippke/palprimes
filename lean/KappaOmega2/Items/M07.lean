import KappaOmega2.Statements
import KappaOmega2.Items.M07_Exact

/-!
# M07. Greaves' Lemma 8: `|M₁ − M₂₃ − M*(y^U)| ≤ εV(y)` for `y ≥ y₀`

Proof (`M07_PLAN.md`): the exact identity `M₁ − M* = Σ_{δ ∈ 𝒟} φ(δ)γ(δ)/δ T⁺(y/δ, p(δ))` (`M07_Exact`), then
Lemma 7 at `Y = y/δ`, `s = log Y/log p(δ) ∈ (0, 2]`, with `y/δ ≥ y^{c₂}`, `c₂ = (1/2)(2/3)^{84}` (chain bound),
`V(√(y/δ)) ≤ (6/c₂)V(y)` and `Σ_{δ ∈ 𝒟} γ(δ)/δ ≤ V(y^{c₂/2})/V(y^U) ≤ 6/c₂` (Mertens, `VB_log_bounds`).
-/

set_option linter.style.longLine false
set_option linter.deprecated false
set_option maxRecDepth 100000

open Finset Real
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

namespace KappaOmega2.M07

open Palprimes Palprimes.Greaves Palprimes.MT
open Classical

theorem Wf_nonneg (t : ℝ) : 0 ≤ Wf t := by
  unfold Wf mm kSq UU W1
  split_ifs with h1 h2 h3
  · exact le_rfl
  · push Not at h1; exact le_min (by positivity) (by linarith)
  · push Not at h1 h2; linarith
  · norm_num

theorem Wf_le (t : ℝ) : Wf t ≤ W1 := by
  unfold Wf mm kSq UU W1
  split_ifs with h1 h2 h3
  · norm_num
  · exact (min_le_right _ _).trans (by linarith)
  · linarith
  · exact le_rfl

theorem log_prod_cast {E : Finset ℕ} (hE : ∀ p ∈ E, p.Prime) :
    Real.log ((∏ p ∈ E, p : ℕ) : ℝ) = ∑ p ∈ E, Real.log (p : ℝ) := by
  rw [Nat.cast_prod, Real.log_prod]
  intro p hp; exact_mod_cast (hE p hp).ne_zero

/-- Chain bound: if every nonempty `E' ⊆ E` of size in the class satisfies the Jurkat–Richert condition and the
class contains all sizes `1 … |E|`, then `log(Y/Π E) ≥ (2/3)^{|E|} log Y`. -/
theorem chain_bound : ∀ (E : Finset ℕ), (∀ p ∈ E, p.Prime) → ∀ (C : ℕ → Prop) (Y : ℝ), 1 ≤ Y →
    (∀ j, 1 ≤ j → j ≤ E.card → C j) → ChiG C Y E →
      (2 / 3 : ℝ) ^ E.card * Real.log Y ≤ Real.log Y - Real.log ((∏ p ∈ E, p : ℕ) : ℝ) := by
  intro E
  induction E using Finset.induction_on_max with
  | empty =>
    intro _ C Y hY _ _
    simp
  | insert M E' hM ih =>
    intro hE C Y hY hC hchi
    have hMp : M.Prime := hE M (mem_insert_self _ _)
    have hE' : ∀ p ∈ E', p.Prime := fun p hp => hE p (mem_insert_of_mem hp)
    have hME' : M ∉ E' := fun h => lt_irrefl M (hM M h)
    have hcard : (insert M E').card = E'.card + 1 := card_insert_of_notMem hME'
    obtain ⟨h1, h2⟩ := (chiG_insert C Y hE' hMp hM).1 hchi
    have hM3 : (M : ℝ) ^ 3 < Y := h1 (hC 1 le_rfl (by omega))
    have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hMp.two_le
    have hM0 : (0 : ℝ) < M := by linarith
    have hMM : (M : ℝ) ≤ (M : ℝ) ^ 3 := by
      have : (1 : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
      nlinarith
    have hMY : (M : ℝ) < Y := lt_of_le_of_lt hMM hM3
    have hYM : 1 ≤ Y / M := by rw [le_div_iff₀ hM0]; linarith
    have ih' := ih hE' (fun j => C (j + 1)) (Y / M) hYM (fun j hj1 hj2 => hC (j + 1) (by omega) (by omega)) h2
    have hlogM : 3 * Real.log M < Real.log Y := by
      have := Real.log_lt_log (by positivity) hM3
      rw [Real.log_pow, Nat.cast_ofNat] at this; exact this
    have hlogYM : Real.log (Y / M) = Real.log Y - Real.log M := Real.log_div (by linarith) hM0.ne'
    have hlogM0 : 0 ≤ Real.log M := Real.log_nonneg (by linarith)
    have hprod : Real.log ((∏ p ∈ insert M E', p : ℕ) : ℝ) = Real.log M + Real.log ((∏ p ∈ E', p : ℕ) : ℝ) := by
      rw [prod_insert hME', Nat.cast_mul, Real.log_mul (by exact_mod_cast hMp.ne_zero)
        (by exact_mod_cast (prod_pos_of_primes hE').ne')]
    rw [hcard, hprod, pow_succ]
    rw [hlogYM] at ih'
    have hk : (0 : ℝ) ≤ (2 / 3) ^ E'.card := by positivity
    have : (2 / 3 : ℝ) ^ E'.card * (2 / 3 * Real.log Y) ≤ (2 / 3) ^ E'.card * (Real.log Y - Real.log M) :=
      mul_le_mul_of_nonneg_left (by linarith) hk
    nlinarith

/-- The constant `c₂ = (1/2)(2/3)^{84}`. -/
noncomputable def c2 : ℝ := 1 / 2 * (2 / 3) ^ 84

theorem c2_pos : 0 < c2 := by unfold c2; positivity

theorem c2_le : c2 ≤ 4 / 103 := by unfold c2; norm_num

/-- Logarithmic facts on `Δ ∈ 𝒟` (`m` the smallest prime, `L = log(y/Π Δ)`): `c₂ log y ≤ L ≤ 2 log m`. -/
theorem Dsf_logs {y : ℝ} (hy : 1 < y) {Δ : Finset ℕ} (hΔS : Δ ⊆ primesBelow (y ^ UU)) (hΔ : Δ ∈ Dsf y (y ^ UU)) :
    c2 * Real.log y ≤ Real.log y - Real.log ((∏ p ∈ Δ, p : ℕ) : ℝ) ∧
      Real.log y - Real.log ((∏ p ∈ Δ, p : ℕ) : ℝ) ≤ 2 * Real.log ((∏ p ∈ Δ, p).minFac : ℝ) ∧
      ∀ p ∈ Δ, (∏ q ∈ Δ, q).minFac ≤ p := by
  have hΔp : ∀ p ∈ Δ, p.Prime := fun p hp => primesBelow_prime (hΔS hp)
  obtain ⟨hne, hc1, -, -, hle⟩ := (mem_Dsf_iff y _ hΔS).1 hΔ
  obtain ⟨-, -, -, hviol⟩ := Dsf_facts y _ hΔS hΔ
  obtain ⟨hm, hmin⟩ := minFac_prod hΔp hne
  obtain ⟨m, hmdef⟩ : ∃ m, (∏ p ∈ Δ, p).minFac = m := ⟨_, rfl⟩
  rw [hmdef] at hm hmin hc1 hviol ⊢
  have hcard' : (Δ.erase m).card + 1 = Δ.card := card_erase_add_one hm
  have hsplitN : (∏ p ∈ Δ, p) = m * ∏ p ∈ Δ.erase m, p := (mul_prod_erase Δ (fun p => p) hm).symm
  have hmq0 : ∀ q ∈ Δ.erase m, m < q := fun q hq => lt_of_le_of_ne (hmin q (mem_of_mem_erase hq)) (ne_of_mem_erase hq).symm
  obtain ⟨Δ', hΔ'⟩ : ∃ Δ', Δ.erase m = Δ' := ⟨_, rfl⟩
  rw [hΔ'] at hc1 hviol hcard' hsplitN hmq0
  have hEp : ∀ p ∈ Δ', p.Prime := fun p hp => hΔp p (mem_of_mem_erase (hΔ' ▸ hp))
  have hly : 0 < Real.log y := Real.log_pos hy
  have hmp := hΔp m hm
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hmp.two_le
  have hlm : 0 < Real.log m := Real.log_pos (by linarith)
  have hP' : (0 : ℝ) < ((∏ p ∈ Δ', p : ℕ) : ℝ) := by exact_mod_cast prod_pos_of_primes hEp
  have hsplit : ((∏ p ∈ Δ, p : ℕ) : ℝ) = m * ((∏ p ∈ Δ', p : ℕ) : ℝ) := by
    rw [hsplitN, Nat.cast_mul]
  have hlogΔ : Real.log ((∏ p ∈ Δ, p : ℕ) : ℝ) = Real.log m + Real.log ((∏ p ∈ Δ', p : ℕ) : ℝ) := by
    rw [hsplit, Real.log_mul (by linarith) hP'.ne']
  -- D1: `log y − log Π Δ' ≤ 3 log m`
  have hD1 : Real.log y - Real.log ((∏ p ∈ Δ', p : ℕ) : ℝ) ≤ 3 * Real.log m := by
    have h := Real.log_le_log (by positivity) hviol
    rw [Real.log_div (by linarith) hP'.ne', Real.log_pow, Nat.cast_ofNat] at h; linarith
  have hcardle : (Δ.card : ℝ) ≤ 103 / 2 := by rw [show (1 : ℝ) / mm = 103 / 2 by norm_num [mm]] at hle; exact hle
  refine ⟨?_, by rw [hlogΔ]; linarith, hmin⟩
  rcases Δ'.eq_empty_or_nonempty with he | hne'
  · -- `Δ = {m}`, `m < y^U`
    have hlogΔ' : Real.log ((∏ p ∈ Δ', p : ℕ) : ℝ) = 0 := by
      rw [he, prod_empty, Nat.cast_one, Real.log_one]
    have hmz : (m : ℝ) < y ^ UU := ((mem_primesBelow _ _).1 (hΔS hm)).2
    have hlmz : Real.log m < UU * Real.log y := by
      have := Real.log_lt_log (by linarith) hmz
      rwa [Real.log_rpow (by linarith)] at this
    rw [hlogΔ, hlogΔ']
    have := c2_le
    have hU : UU = 99 / 103 := rfl
    nlinarith
  · obtain ⟨hq, hqmin⟩ := minFac_prod hEp hne'
    have hfull := hc1 Δ' (subset_refl _) hne'
    obtain ⟨q, hqdef⟩ : ∃ q, (∏ p ∈ Δ', p).minFac = q := ⟨_, rfl⟩
    rw [hqdef] at hq hqmin hfull
    have hmq : m < q := hmq0 q hq
    have hcardΔ' : Δ'.card ≤ 50 := by
      have : (Δ.card : ℝ) < 52 := by linarith
      have : Δ.card < 52 := by exact_mod_cast this
      omega
    have hCchi : ∀ j, 1 ≤ j → j ≤ Δ'.card → Cchi j := by
      intro j _ hj
      right
      rw [show (1 : ℝ) / mm = 103 / 2 by norm_num [mm]]
      have : (j : ℝ) ≤ 50 := by exact_mod_cast hj.trans hcardΔ'
      linarith
    have hchain := chain_bound Δ' hEp Cchi y hy.le hCchi hc1
    -- the full set `Δ'` itself: `Π Δ' · q² < y`
    have hfull := hfull (hCchi _ (by have := hne'.card_pos; omega) le_rfl)
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (hEp q hq).two_le
    have hlogfull : Real.log ((∏ p ∈ Δ', p : ℕ) : ℝ) + 2 * Real.log q < Real.log y := by
      have h := Real.log_lt_log (by positivity) hfull
      rw [Real.log_mul hP'.ne' (by positivity), Real.log_pow, Nat.cast_ofNat] at h; linarith
    have hlmq : Real.log m < Real.log q := Real.log_lt_log (by linarith) (by exact_mod_cast hmq)
    have hpow : (2 / 3 : ℝ) ^ 84 ≤ (2 / 3) ^ Δ'.card := pow_le_pow_of_le_one (by norm_num) (by norm_num) (hcardΔ'.trans (by norm_num))
    rw [hlogΔ]
    unfold c2
    nlinarith

end KappaOmega2.M07

namespace KappaOmega2

open Palprimes Palprimes.Greaves Palprimes.MT KappaOmega2.M07
open Classical

set_option maxHeartbeats 2000000 in
theorem itemM07 : ItemM07 := by
  intro b hb h7 ε hε
  obtain ⟨x₀, hx₀1, hx₀⟩ := Palprimes.E1.VB_log_bounds b hb (η := 1 / 2) (by norm_num)
  have hκ := kappaB_pos b
  have hc2 := c2_pos
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 86 * W1 * (6 / c2) * (6 / c2) := ⟨_, rfl⟩
  have hK0 : 0 < K := by
    rw [hK]; have : 0 < 6 / c2 := div_pos (by norm_num) hc2
    have hW : (0 : ℝ) < W1 := by unfold W1; norm_num
    positivity
  obtain ⟨ε', hε'⟩ : ∃ ε' : ℝ, ε' = ε / (K + 1) := ⟨_, rfl⟩
  have hε'0 : 0 < ε' := by rw [hε']; positivity
  obtain ⟨y7, hy7⟩ := h7 ε' hε'0
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 2 / c2 * (|Real.log x₀| + |Real.log (max y7 1)| + 1) := ⟨_, rfl⟩
  refine ⟨Real.exp A, fun y hy => ?_⟩
  have hA1 : 1 ≤ A := by
    rw [hA]
    have : 2 / c2 ≥ 1 := by
      rw [ge_iff_le, le_div_iff₀ hc2]; have := c2_le; linarith
    have h0 : 1 ≤ |Real.log x₀| + |Real.log (max y7 1)| + 1 := by
      have := abs_nonneg (Real.log x₀); have := abs_nonneg (Real.log (max y7 1)); linarith
    exact one_le_mul_of_one_le_of_one_le this h0
  have hy0 : 0 < y := lt_of_lt_of_le (Real.exp_pos _) hy
  have hlyA : A ≤ Real.log y := by rw [← Real.log_exp A]; exact Real.log_le_log (Real.exp_pos _) hy
  have hly : 0 < Real.log y := by linarith
  have hy1 : 1 < y := by
    by_contra h; push Not at h
    have := Real.log_nonpos hy0.le h; linarith
  -- consequences of `log y ≥ A`
  have hbig : |Real.log x₀| + |Real.log (max y7 1)| + 1 ≤ c2 / 2 * Real.log y := by
    have : c2 / 2 * A = |Real.log x₀| + |Real.log (max y7 1)| + 1 := by rw [hA]; field_simp
    have := mul_le_mul_of_nonneg_left hlyA (by positivity : (0 : ℝ) ≤ c2 / 2)
    linarith
  have hlx0 : Real.log x₀ ≤ c2 / 2 * Real.log y := by
    have := le_abs_self (Real.log x₀); have := abs_nonneg (Real.log (max y7 1)); linarith
  have hly7 : Real.log (max y7 1) ≤ c2 / 2 * Real.log y := by
    have := le_abs_self (Real.log (max y7 1)); have := abs_nonneg (Real.log x₀); linarith
  have hx0pos : 0 < x₀ := by linarith
  -- `x ≥ x₀` from `log x ≥ c₂/2 log y`
  have hge_x0 : ∀ x : ℝ, 0 < x → c2 / 2 * Real.log y ≤ Real.log x → x₀ ≤ x := by
    intro x hx h
    have : Real.log x₀ ≤ Real.log x := le_trans hlx0 h
    exact (Real.log_le_log_iff hx0pos hx).1 this
  have hc2le := c2_le
  have hc2y : c2 / 2 * Real.log y ≤ c2 * Real.log y := by
    have := mul_pos hc2 hly; linarith
  have hyx0 : x₀ ≤ y := hge_x0 y hy0 (by
    have := mul_le_mul_of_nonneg_right (by linarith : c2 / 2 ≤ 1) hly.le; linarith)
  have hVy := hx₀ y hyx0
  have hz0 : 0 < y ^ UU := Real.rpow_pos_of_pos hy0 _
  have hlz : Real.log (y ^ UU) = UU * Real.log y := Real.log_rpow hy0 _
  have hzx0 : x₀ ≤ (y ^ UU) := hge_x0 (y ^ UU) hz0 (by
    rw [hlz]; exact mul_le_mul_of_nonneg_right (by unfold UU; linarith) hly.le)
  have hVz := hx₀ (y ^ UU) hzx0
  -- the per-term bound
  have hterm : ∀ Δ ∈ Dsf y (y ^ UU),
      |phiW W1 (wy y) (∏ p ∈ Δ, p) * rhoB b (∏ p ∈ Δ, p) / ((∏ p ∈ Δ, p : ℕ) : ℝ) *
          (Tpm b true (y / ((∏ p ∈ Δ, p : ℕ) : ℝ)) ((∏ p ∈ Δ, p).minFac) -
            Real.exp Real.eulerMascheroniConstant * VB b (Real.sqrt (y / ((∏ p ∈ Δ, p : ℕ) : ℝ))))| ≤
        86 * W1 * gD b Δ * (ε' * (6 / c2 * VB b y)) := by
    intro Δ hΔ
    have hΔS : Δ ⊆ primesBelow (y ^ UU) := by unfold Dsf at hΔ; exact mem_powerset.1 (mem_filter.1 hΔ).1
    have hΔp : ∀ p ∈ Δ, p.Prime := fun p hp => primesBelow_prime (hΔS hp)
    obtain ⟨hL1, hL2, -⟩ := Dsf_logs hy1 hΔS hΔ
    obtain ⟨hne, -, -, -, hle⟩ := (mem_Dsf_iff y _ hΔS).1 hΔ
    obtain ⟨hm, -⟩ := minFac_prod hΔp hne
    set m := (∏ p ∈ Δ, p).minFac
    set P : ℝ := ((∏ p ∈ Δ, p : ℕ) : ℝ) with hP
    have hP0 : 0 < P := by rw [hP]; exact_mod_cast prod_pos_of_primes hΔp
    set Y := y / P with hY
    have hY0 : 0 < Y := div_pos hy0 hP0
    have hlogY : Real.log Y = Real.log y - Real.log P := Real.log_div hy0.ne' hP0.ne'
    have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (hΔp m hm).two_le
    have hlm : 0 < Real.log m := Real.log_pos (by linarith)
    have hlY : 0 < Real.log Y := by rw [hlogY]; have := mul_pos hc2 hly; linarith
    -- Lemma 7 at `Y`, `s = log Y / log m`
    set s := Real.log Y / Real.log m with hs
    have hs0 : 0 < s := div_pos hlY hlm
    have hs3 : s ≤ 3 := by rw [hs, div_le_iff₀ hlm]; rw [hlogY]; linarith
    have hYs : Y ^ (1 / s) = m := by
      rw [Real.rpow_def_of_pos hY0, hs, one_div_div, mul_div_cancel₀ _ hlY.ne', Real.exp_log (by linarith)]
    have hY7 : y7 ≤ Y := by
      have h1 : Real.log (max y7 1) ≤ Real.log Y := by rw [hlogY]; linarith
      have h2 := (Real.log_le_log_iff (by positivity) hY0).1 h1
      exact le_trans (le_max_left _ _) h2
    have h7Y := hy7 Y hY7 s hs0 hs3
    rw [hYs] at h7Y
    -- `V(√Y) ≤ (6/c₂) V(y)`
    have hsq0 : 0 < Real.sqrt Y := Real.sqrt_pos.2 hY0
    have hlsq : Real.log (Real.sqrt Y) = Real.log Y / 2 := Real.log_sqrt hY0.le
    have hsqx0 : x₀ ≤ Real.sqrt Y := hge_x0 _ hsq0 (by rw [hlsq, hlogY]; linarith)
    have hVsq := hx₀ _ hsqx0
    have hlsq0 : 0 < Real.log (Real.sqrt Y) := by rw [hlsq]; linarith
    have hVsqle : VB b (Real.sqrt Y) ≤ 6 / c2 * VB b y := by
      have hV0 := Palprimes.E1.VB_pos' b (Real.sqrt Y)
      have h0 : c2 / 2 * Real.log y ≤ Real.log (Real.sqrt Y) := by rw [hlsq, hlogY]; linarith
      have e1 := mul_le_mul_of_nonneg_left h0 hV0.le
      have e2 := hVsq.2
      have e3 := hVy.1
      have e4 : VB b (Real.sqrt Y) * (c2 / 2) * Real.log y ≤ (3 * VB b y) * Real.log y := by
        have r1 : VB b (Real.sqrt Y) * (c2 / 2) * Real.log y = VB b (Real.sqrt Y) * (c2 / 2 * Real.log y) := by ring
        have r2 : (3 * VB b y) * Real.log y = 3 * (VB b y * Real.log y) := by ring
        rw [r1, r2]; linarith
      have e5 := le_of_mul_le_mul_right e4 hly
      rw [div_mul_eq_mul_div, le_div_iff₀ hc2]
      linarith
    -- `|φ| ≤ 86 W1`
    have hphi : |phiW W1 (wy y) (∏ p ∈ Δ, p)| ≤ 86 * W1 := by
      rw [phiW_prod _ hΔp]
      have hs0' : 0 ≤ ∑ p ∈ Δ, wy y p := sum_nonneg fun p _ => Wf_nonneg _
      have hs1 : ∑ p ∈ Δ, wy y p ≤ Δ.card * W1 := by
        have := sum_le_sum (s := Δ) (fun p _ => Wf_le (Real.log p / Real.log y))
        simpa [wy] using this
      have hc : (Δ.card : ℝ) ≤ 85 := by rw [show (1 : ℝ) / mm = 103 / 2 by norm_num [mm]] at hle; linarith
      have hW : (0 : ℝ) < W1 := by unfold W1; norm_num
      have := mul_le_mul_of_nonneg_right hc hW.le
      rw [abs_le]; constructor <;> linarith
    have hg := rho_div_prod b hΔp
    have hg0 : 0 ≤ gD b Δ := prod_nonneg fun p _ => gB_nonneg b p
    rw [mul_div_assoc, hg, abs_mul, abs_mul, abs_of_nonneg hg0]
    have hVsq0 := Palprimes.E1.VB_pos' b (Real.sqrt Y)
    calc |phiW W1 (wy y) (∏ p ∈ Δ, p)| * gD b Δ *
          |Tpm b true Y m - Real.exp Real.eulerMascheroniConstant * VB b (Real.sqrt Y)|
        ≤ 86 * W1 * gD b Δ * (ε' * VB b (Real.sqrt Y)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hphi hg0) h7Y (abs_nonneg _)
          have : (0 : ℝ) ≤ W1 := by unfold W1; norm_num
          positivity
      _ ≤ 86 * W1 * gD b Δ * (ε' * (6 / c2 * VB b y)) := by
          apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hVsqle hε'0.le)
          have : (0 : ℝ) ≤ W1 := by unfold W1; norm_num
          positivity
  -- `Σ_{Δ ∈ 𝒟} γ/δ ≤ 6/c₂`
  set w := Real.exp (c2 / 2 * Real.log y) with hw
  have hw0 : 0 < w := Real.exp_pos _
  have hlw : Real.log w = c2 / 2 * Real.log y := Real.log_exp _
  have hwx0 : x₀ ≤ w := hge_x0 w hw0 (by rw [hlw])
  have hVw := hx₀ w hwx0
  have hwz : w ≤ (y ^ UU) := by
    rw [← Real.exp_log hz0, hw]; apply Real.exp_le_exp.2; rw [hlz]
    exact mul_le_mul_of_nonneg_right (by unfold UU; linarith) hly.le
  set Q := (primesBelow (y ^ UU)).filter (fun p : ℕ => w ≤ (p : ℝ)) with hQ
  have hsumg : ∑ Δ ∈ Dsf y (y ^ UU), gD b Δ ≤ 6 / c2 := by
    have hsub : Dsf y (y ^ UU) ⊆ Q.powerset := by
      intro Δ hΔ
      have hΔS : Δ ⊆ primesBelow (y ^ UU) := by unfold Dsf at hΔ; exact mem_powerset.1 (mem_filter.1 hΔ).1
      have hΔp : ∀ p ∈ Δ, p.Prime := fun p hp => primesBelow_prime (hΔS hp)
      obtain ⟨hL1, hL2, hmin⟩ := Dsf_logs hy1 hΔS hΔ
      rw [mem_powerset]
      intro p hp
      rw [hQ, mem_filter]
      refine ⟨hΔS hp, ?_⟩
      have hm2 : (1 : ℝ) ≤ ((∏ q ∈ Δ, q).minFac : ℝ) := by
        have := (Nat.minFac_prime (show (∏ q ∈ Δ, q) ≠ 1 from by
          intro h1
          have := Finset.dvd_prod_of_mem (fun p => p) hp
          rw [h1] at this
          exact (hΔp p hp).ne_one (Nat.dvd_one.1 this))).two_le
        exact_mod_cast (by omega : 1 ≤ (∏ q ∈ Δ, q).minFac)
      have hlm : c2 / 2 * Real.log y ≤ Real.log ((∏ q ∈ Δ, q).minFac : ℝ) := by linarith
      have : w ≤ ((∏ q ∈ Δ, q).minFac : ℝ) := by
        rw [hw]; calc Real.exp (c2 / 2 * Real.log y) ≤ Real.exp (Real.log ((∏ q ∈ Δ, q).minFac : ℝ)) :=
              Real.exp_le_exp.2 hlm
          _ = _ := Real.exp_log (by linarith)
      exact le_trans this (by exact_mod_cast hmin p hp)
    have h1 : ∑ Δ ∈ Dsf y (y ^ UU), gD b Δ ≤ ∑ Δ ∈ Q.powerset, gD b Δ :=
      sum_le_sum_of_subset_of_nonneg hsub (fun Δ _ _ => prod_nonneg fun p _ => gB_nonneg b p)
    have h2 : ∑ Δ ∈ Q.powerset, gD b Δ = ∏ p ∈ Q, (1 + gB b p) := by
      unfold gD; rw [prod_one_add]
    have hSw : (primesBelow (y ^ UU)).filter (fun p : ℕ => ¬ w ≤ (p : ℝ)) = primesBelow w := by
      ext p; rw [mem_filter, mem_primesBelow, mem_primesBelow]; constructor
      · rintro ⟨⟨hp, _⟩, h⟩; exact ⟨hp, lt_of_not_ge h⟩
      · rintro ⟨hp, h⟩; exact ⟨⟨hp, lt_of_lt_of_le h hwz⟩, not_le.2 h⟩
    have hVsplit : VB b (y ^ UU) = (∏ p ∈ Q, (1 - gB b p)) * VB b w := by
      unfold VB
      rw [← hSw, hQ, prod_filter_mul_prod_filter_not]
    have hpm : (∏ p ∈ Q, (1 + gB b p)) * ∏ p ∈ Q, (1 - gB b p) ≤ 1 := by
      rw [← prod_mul_distrib]
      apply prod_le_one₀
      · intro p _
        have h1 := gB_nonneg b p
        have h2 := Palprimes.E1.gB_le_half' b p
        exact mul_nonneg (by linarith) (by linarith)
      · intro p _
        have h1 := gB_nonneg b p
        have r : (1 + gB b p) * (1 - gB b p) = 1 - gB b p ^ 2 := by ring
        rw [r]; linarith [sq_nonneg (gB b p)]
    have hQm0 : 0 < ∏ p ∈ Q, (1 - gB b p) := prod_pos fun p _ => by
      have := Palprimes.E1.gB_le_half' b p; linarith
    have hVz0 := Palprimes.E1.VB_pos' b (y ^ UU)
    have hVw0 := Palprimes.E1.VB_pos' b w
    have h3 : ∏ p ∈ Q, (1 + gB b p) ≤ VB b w / VB b (y ^ UU) := by
      rw [hVsplit, le_div_iff₀ (by positivity)]
      calc (∏ p ∈ Q, (1 + gB b p)) * ((∏ p ∈ Q, (1 - gB b p)) * VB b w)
          = ((∏ p ∈ Q, (1 + gB b p)) * ∏ p ∈ Q, (1 - gB b p)) * VB b w := by ring
        _ ≤ 1 * VB b w := mul_le_mul_of_nonneg_right hpm hVw0.le
        _ = VB b w := one_mul _
    have h4 : VB b w / VB b (y ^ UU) ≤ 6 / c2 := by
      rw [div_le_div_iff₀ hVz0 hc2]
      have e1 : VB b w * (c2 / 2 * Real.log y) ≤ (1 + 1 / 2) * kappaB b := by rw [← hlw]; exact hVw.2
      have e2 : (1 - 1 / 2) * kappaB b ≤ VB b (y ^ UU) * (UU * Real.log y) := by rw [← hlz]; exact hVz.1
      have hU : UU ≤ 1 := by unfold UU; norm_num
      have e3 : VB b (y ^ UU) * (UU * Real.log y) ≤ VB b (y ^ UU) * Real.log y := by
        apply mul_le_mul_of_nonneg_left _ hVz0.le
        have := mul_le_mul_of_nonneg_right hU hly.le; linarith
      have e4 : VB b w * (c2 / 2) * Real.log y ≤ (3 * VB b (y ^ UU)) * Real.log y := by
        have r1 : VB b w * (c2 / 2) * Real.log y = VB b w * (c2 / 2 * Real.log y) := by ring
        have r2 : (3 * VB b (y ^ UU)) * Real.log y = 3 * (VB b (y ^ UU) * Real.log y) := by ring
        rw [r1, r2]; linarith
      have e5 := le_of_mul_le_mul_right e4 hly
      linarith
    linarith
  -- assembly
  have hid : M1 b y - M23 b y - Mstar b y (y ^ UU) = ∑ δ ∈ Dset y (y ^ UU) mm,
      phiW W1 (wy y) δ * rhoB b δ / δ * (Tpm b true (y / δ) (δ.minFac) -
        Real.exp Real.eulerMascheroniConstant * VB b (Real.sqrt (y / δ))) := by
    have h := exact_identity b y
    rw [show M1 b y - M23 b y - Mstar b y (y ^ UU) = (M1 b y - Mstar b y (y ^ UU)) - M23 b y by ring, h]
    unfold M23
    rw [← sum_sub_distrib]
    apply sum_congr rfl; intro δ _; ring
  rw [hid, sum_Dset]
  have hVy0 := Palprimes.E1.VB_pos' b y
  calc |∑ Δ ∈ Dsf y (y ^ UU), phiW W1 (wy y) (∏ p ∈ Δ, p) * rhoB b (∏ p ∈ Δ, p) / ((∏ p ∈ Δ, p : ℕ) : ℝ) *
          (Tpm b true (y / ((∏ p ∈ Δ, p : ℕ) : ℝ)) ((∏ p ∈ Δ, p).minFac) -
            Real.exp Real.eulerMascheroniConstant * VB b (Real.sqrt (y / ((∏ p ∈ Δ, p : ℕ) : ℝ))))|
      ≤ ∑ Δ ∈ Dsf y (y ^ UU), 86 * W1 * gD b Δ * (ε' * (6 / c2 * VB b y)) :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)
    _ = 86 * W1 * (ε' * (6 / c2 * VB b y)) * ∑ Δ ∈ Dsf y (y ^ UU), gD b Δ := by
        rw [mul_sum]; apply sum_congr rfl; intro Δ _; ring
    _ ≤ 86 * W1 * (ε' * (6 / c2 * VB b y)) * (6 / c2) := by
        apply mul_le_mul_of_nonneg_left hsumg
        have : (0 : ℝ) ≤ W1 := by unfold W1; norm_num
        positivity
    _ = ε' * K * VB b y := by rw [hK]; ring
    _ ≤ ε * VB b y := by
        apply mul_le_mul_of_nonneg_right _ hVy0.le
        rw [hε', div_mul_eq_mul_div, div_le_iff₀ (by linarith), mul_add, mul_one]
        linarith

end KappaOmega2
