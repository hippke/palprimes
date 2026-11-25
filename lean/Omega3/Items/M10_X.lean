import Omega3.Items.M10_XB

/-!
# M10 helper: the terms with `(d₁, t) > 1` (`M10_PLAN.md` §4.1, §4.6)

`S_p` (the Lemma 9 replacement of `−H_p`), `X_p` (its part with `(d₁, t) > 1`), the regrouping `S_p − E_p = X_p`
(uses Lemma 10 for `p < y` only) and the crude bound `|X_p| ≤ 2K(y)³/p²`.
-/

set_option linter.style.longLine false

open Finset Real
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

namespace Omega3

open Palprimes Palprimes.Greaves

/-- `S_p` (§4.1). -/
noncomputable def Sp (b : ℕ) (y : ℝ) (p : ℕ) : ℝ :=
  open Classical in
  rhoB b p / p * ∑ d ∈ D1set y p, (μ d : ℝ) * rhoB b d / d * (if chiStarProp y mm d then 1 else 0) *
    (if chiMinusProp y (d * p) then 1 else 0) * Rpm b (y / (p * d)) p (decide (Even (ω d)))

/-- `X_p`: the part of `S_p` with `(d₁, t) > 1`. -/
noncomputable def Xd (b : ℕ) (y : ℝ) (p : ℕ) : ℝ :=
  open Classical in
  rhoB b p / p * ∑ d ∈ D1set y p, (μ d : ℝ) * rhoB b d / d * (if chiStarProp y mm d then 1 else 0) *
    (if chiMinusProp y (d * p) then 1 else 0) *
    ∑ t ∈ (S9 (y / (p * d)) p (decide (Even (ω d)))).filter (fun t : ℕ => ¬ Nat.Coprime d t),
      rhoB b t / t * sigmaP b (y / (p * d) / t)

/-- `Lemma10Stmt` restricted to `p < y` (the only case used; the frozen version is false at `n = 1`, `p ≥ y`). -/
def Lemma10LtStmt : Prop :=
  ∀ (y m : ℝ) (p n : ℕ), 0 < m → 0 < y → p.Prime → (p : ℝ) < y → Squarefree n → (∀ q ∈ n.primeFactors, p < q) →
    (∀ q ∈ n.primeFactors, (q : ℝ) < y) → Even (ω n) →
      bfun y m p n = if n = 1 then 1 else if (n : ℝ) * n.minFac < y / p then -chibar y m n else 0

theorem lemma10Lt_of (h : Lemma10Stmt) : Lemma10LtStmt :=
  fun y m p n hm hy hp hpy hn h1 h2 h3 => h y m p n hm hy hp hpy hn h1 h2 h3

namespace M10

open Classical

theorem rhoB_mul (b m n : ℕ) : rhoB b (m * n) = rhoB b m * rhoB b n := by
  unfold rhoB
  simp only [Nat.coprime_mul_iff_left]
  split_ifs <;> simp_all

theorem G_nonneg (b n : ℕ) : 0 ≤ rhoB b n / (n : ℝ) := by unfold rhoB; split_ifs <;> positivity

theorem G_le_inv (b n : ℕ) : rhoB b n / (n : ℝ) ≤ 1 / n := by
  unfold rhoB; split_ifs
  · exact le_rfl
  · rw [zero_div]; positivity

theorem G_prod (b : ℕ) {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime) :
    rhoB b (∏ p ∈ D, p) / ((∏ p ∈ D, p : ℕ) : ℝ) = ∏ q ∈ D, rhoB b q / q := by
  induction D using Finset.induction_on with
  | empty => simp [rhoB]
  | insert a D ha ih =>
    have hD' : ∀ p ∈ D, p.Prime := fun p hp => hD p (mem_insert_of_mem hp)
    have ha0 : (0 : ℝ) < a := by exact_mod_cast (hD a (mem_insert_self a D)).pos
    have hP0 : (0 : ℝ) < ((∏ p ∈ D, p : ℕ) : ℝ) := by exact_mod_cast prod_pos_of_primes hD'
    rw [prod_insert ha, prod_insert ha, rhoB_mul, ← ih hD']
    push_cast
    field_simp

theorem abs_fm_prod (b : ℕ) {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime) :
    |fm b (∏ p ∈ D, p)| = ∏ q ∈ D, rhoB b q / q := by
  unfold fm
  have hmu : |(μ (∏ p ∈ D, p) : ℝ)| = 1 := by
    rw [← Int.cast_abs, ArithmeticFunction.abs_moebius_eq_one_of_squarefree (SelbergPort.prod_primes_squarefree D hD),
      Int.cast_one]
  rw [mul_div_assoc, abs_mul, G_prod b hD, hmu, one_mul, abs_of_nonneg (prod_nonneg fun q _ => G_nonneg b q)]

theorem abs_Tpm_le (b : ℕ) (plus : Bool) (Y w : ℝ) :
    |Tpm b plus Y w| ≤ ∏ q ∈ primesBelow w, (1 + rhoB b q / q) := by
  rw [Tpm_set, prod_one_add]
  refine le_trans (abs_sum_le_sum_abs _ _) (sum_le_sum fun D hD => ?_)
  have hDp : ∀ p ∈ D, p.Prime := fun p hp => primes_PB w p (mem_powerset.1 hD hp)
  rw [abs_mul, abs_fm_prod b hDp]
  have : |(if ChiS plus Y D then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
  have h0 : 0 ≤ ∏ q ∈ D, rhoB b q / q := prod_nonneg fun q _ => G_nonneg b q
  nlinarith [abs_nonneg (if ChiS plus Y D then (1 : ℝ) else 0)]

theorem prodPB_le_Kp (b : ℕ) {w y : ℝ} (h : w ≤ y) : ∏ q ∈ primesBelow w, (1 + rhoB b q / q) ≤ Kp b y := by
  unfold Kp
  apply prod_le_prod_of_subset_of_one_le₀ (primesBelow_mono h)
  · intro q _; linarith [G_nonneg b q]
  · intro q _ _; linarith [G_nonneg b q]

theorem abs_sigma_le (b : ℕ) {u y : ℝ} (hu : 0 < u) (huy : u ≤ y) (hy : 1 ≤ y) : |sigmaP b u| ≤ Kp b y := by
  unfold sigmaP
  refine le_trans (abs_Tpm_le b true u _) (prodPB_le_Kp b ?_)
  rcases le_or_gt u 1 with h | h
  · exact le_trans (Real.rpow_le_one hu.le h (by norm_num)) hy
  · calc u ^ ((1 : ℝ) / 3) ≤ u ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h.le (by norm_num)
      _ = u := Real.rpow_one u
      _ ≤ y := huy

/-- `Σ_{D ⊆ S, r ∈ D} Π_D f = f(r) Π_{S∖r}(1 + f)`. -/
theorem sum_powerset_mem (S : Finset ℕ) {r : ℕ} (hr : r ∈ S) (f : ℕ → ℝ) :
    ∑ D ∈ S.powerset, (if r ∈ D then ∏ q ∈ D, f q else 0) = f r * ∏ q ∈ S.erase r, (1 + f q) := by
  have hS : S = insert r (S.erase r) := (insert_erase hr).symm
  have hnot : r ∉ S.erase r := notMem_erase r S
  rw [hS, sum_powerset_insert hnot]
  have h1 : ∑ D ∈ (S.erase r).powerset, (if r ∈ D then ∏ q ∈ D, f q else 0) = 0 := by
    apply sum_eq_zero; intro D hD
    rw [if_neg (fun h => hnot (mem_powerset.1 hD h))]
  rw [h1, zero_add, erase_insert hnot, prod_one_add, mul_sum]
  apply sum_congr rfl; intro D hD
  have hrD : r ∉ D := fun h => hnot (mem_powerset.1 hD h)
  rw [if_pos (mem_insert_self r D), prod_insert hrD]

/-- `Σ_{d | P(y), r | d} γ(d)/d ≤ γ(r)/r · K(y)` for `r ∈ P(y)`. -/
theorem sum_dvd_G_le (b : ℕ) (y : ℝ) {r : ℕ} (hr : r ∈ primesBelow y) :
    ∑ d ∈ (primorialLt y).divisors, (if r ∣ d then rhoB b d / (d : ℝ) else 0) ≤ rhoB b r / r * Kp b y := by
  unfold primorialLt
  rw [sum_divisors_primes (primesBelow y) (primes_PB y)]
  have hrp : r.Prime := primes_PB y r hr
  have e : ∀ D ∈ (primesBelow y).powerset, (if r ∣ ∏ p ∈ D, p then rhoB b (∏ p ∈ D, p) / ((∏ p ∈ D, p : ℕ) : ℝ) else 0) =
      (if r ∈ D then ∏ q ∈ D, rhoB b q / q else 0) := by
    intro D hD
    have hDp : ∀ p ∈ D, p.Prime := fun p hp => primes_PB y p (mem_powerset.1 hD hp)
    by_cases h : r ∈ D
    · rw [if_pos (Finset.dvd_prod_of_mem (fun q => q) h), if_pos h, G_prod b hDp]
    · rw [if_neg (not_dvd_prod_of_notMem hrp hDp h), if_neg h]
  rw [sum_congr rfl e, sum_powerset_mem _ hr]
  apply mul_le_mul_of_nonneg_left _ (G_nonneg b r)
  unfold Kp
  apply prod_le_prod_of_subset_of_one_le₀ (erase_subset r _)
  · intro q _; linarith [G_nonneg b q]
  · intro q _ _; linarith [G_nonneg b q]

theorem primorialLt_pos' (z : ℝ) : 0 < primorialLt z := by
  unfold primorialLt
  exact Finset.prod_pos (fun p hp => ((mem_primesBelow z p).1 hp).1.pos)

theorem mem_PB_of_dvd {z : ℝ} {p : ℕ} (hp : p.Prime) (h : p ∣ primorialLt z) : p ∈ primesBelow z := by
  unfold primorialLt at h
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 h
  have hq' := (mem_primesBelow z q).1 hq
  rwa [(Nat.prime_dvd_prime_iff_eq hp hq'.1).1 hpq]

theorem primorialLt_dvd {a c : ℝ} (h : a ≤ c) : primorialLt a ∣ primorialLt c := by
  unfold primorialLt; exact prod_dvd_prod_of_subset _ _ _ (primesBelow_mono h)

theorem divisors_primorial_mono {a c : ℝ} (h : a ≤ c) : (primorialLt a).divisors ⊆ (primorialLt c).divisors :=
  Nat.divisors_subset_of_dvd (primorialLt_pos' c).ne' (primorialLt_dvd h)

/-- §4.6: `|X_p| ≤ 2K(y)³/p²`. -/
theorem Xd_bound (b : ℕ) {y : ℝ} (hy : 16 ≤ y) {p : ℕ} (hp : p.Prime) :
    |Xd b y p| ≤ 2 * Kp b y ^ 3 / (p : ℝ) ^ 2 := by
  have hy1 : (1 : ℝ) ≤ y := by linarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hK0 := Kp_pos b y
  set K := Kp b y with hK
  set G : ℕ → ℝ := fun n => rhoB b n / (n : ℝ) with hG
  have hG0 : ∀ n, 0 ≤ G n := fun n => G_nonneg b n
  set Dy := (primorialLt y).divisors with hDy
  set R := (primesBelow y).filter (fun r : ℕ => p < r) with hR
  -- the pair sum
  set PS := ∑ d ∈ Dy, ∑ t ∈ Dy, ∑ r ∈ R, (if r ∣ d then G d else 0) * (if r ∣ t then G t else 0) with hPS
  have hPSb : PS ≤ K ^ 2 * (2 / ((p : ℝ) + 1)) := by
    have e1 : PS = ∑ r ∈ R, (∑ d ∈ Dy, (if r ∣ d then G d else 0)) * (∑ t ∈ Dy, (if r ∣ t then G t else 0)) := by
      calc PS = ∑ d ∈ Dy, ∑ r ∈ R, ∑ t ∈ Dy, (if r ∣ d then G d else 0) * (if r ∣ t then G t else 0) := by
            rw [hPS]; apply sum_congr rfl; intro d _; rw [sum_comm]
        _ = ∑ r ∈ R, ∑ d ∈ Dy, ∑ t ∈ Dy, (if r ∣ d then G d else 0) * (if r ∣ t then G t else 0) := sum_comm
        _ = _ := by apply sum_congr rfl; intro r _; rw [sum_mul_sum]
    rw [e1]
    calc ∑ r ∈ R, (∑ d ∈ Dy, (if r ∣ d then G d else 0)) * (∑ t ∈ Dy, (if r ∣ t then G t else 0))
        ≤ ∑ r ∈ R, (G r * K) * (G r * K) := by
          apply sum_le_sum; intro r hr
          have hr' : r ∈ primesBelow y := (mem_filter.1 hr).1
          have h1 := sum_dvd_G_le b y hr'
          have h0 : 0 ≤ ∑ d ∈ Dy, (if r ∣ d then G d else 0) := sum_nonneg fun d _ => by split_ifs <;> simp [hG0]
          exact mul_le_mul h1 h1 h0 (mul_nonneg (hG0 r) hK0.le)
      _ = K ^ 2 * ∑ r ∈ R, G r ^ 2 := by rw [mul_sum]; apply sum_congr rfl; intro r _; ring
      _ ≤ K ^ 2 * (2 / ((p : ℝ) + 1)) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg K)
          set n := ⌈y⌉₊ + 1 with hn
          have hsub : R ⊆ Ioo p n := by
            intro r hr
            rw [hR, mem_filter, mem_primesBelow] at hr
            rw [mem_Ioo]
            refine ⟨hr.2, ?_⟩
            have : (r : ℝ) < n := by rw [hn]; push_cast; linarith [Nat.le_ceil y, hr.1.2]
            exact_mod_cast this
          calc ∑ r ∈ R, G r ^ 2 ≤ ∑ r ∈ R, ((r : ℝ) ^ 2)⁻¹ := by
                apply sum_le_sum; intro r _
                have h1 := G_le_inv b r
                have h0 := hG0 r
                rw [← one_div, ← one_div_pow]
                exact pow_le_pow_left₀ h0 h1 2
            _ ≤ ∑ i ∈ Ioo p n, ((i : ℝ) ^ 2)⁻¹ := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
            _ ≤ 2 / ((p : ℝ) + 1) := sum_Ioo_inv_sq_le p n
  -- per-d bound
  have hper : ∀ d ∈ D1set y p,
      |(μ d : ℝ) * rhoB b d / d * (if chiStarProp y mm d then 1 else 0) * (if chiMinusProp y (d * p) then 1 else 0) *
        ∑ t ∈ (S9 (y / (p * d)) p (decide (Even (ω d)))).filter (fun t : ℕ => ¬ Nat.Coprime d t),
          rhoB b t / t * sigmaP b (y / (p * d) / t)| ≤
      K * ∑ t ∈ Dy, ∑ r ∈ R, (if r ∣ d then G d else 0) * (if r ∣ t then G t else 0) := by
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors (mem_filter.1 hd).1
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.pos
    have hpd : (1 : ℝ) ≤ p * d := by nlinarith
    set η := y / (p * d) with hη
    have hη0 : 0 < η := div_pos (by linarith) (by linarith)
    have hηy : η ≤ y := div_le_self (by linarith) hpd
    have hA : |(μ d : ℝ) * rhoB b d / d * (if chiStarProp y mm d then 1 else 0) *
        (if chiMinusProp y (d * p) then 1 else 0)| ≤ G d := by
      rw [abs_mul, abs_mul, mul_div_assoc, abs_mul]
      have h1 : |(μ d : ℝ)| ≤ 1 := by
        rw [← Int.cast_abs]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      have h2 : |(if chiStarProp y mm d then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
      have h3 : |(if chiMinusProp y (d * p) then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
      have hGd : |rhoB b d / (d : ℝ)| = G d := abs_of_nonneg (hG0 d)
      rw [hGd]
      have := hG0 d
      calc |(μ d : ℝ)| * G d * |(if chiStarProp y mm d then (1 : ℝ) else 0)| *
          |(if chiMinusProp y (d * p) then (1 : ℝ) else 0)| ≤ 1 * G d * 1 * 1 := by gcongr
        _ = G d := by ring
    have hT : |∑ t ∈ (S9 η p (decide (Even (ω d)))).filter (fun t : ℕ => ¬ Nat.Coprime d t),
        rhoB b t / t * sigmaP b (η / t)| ≤
        K * ∑ t ∈ Dy, ∑ r ∈ R, (if r ∣ d then 1 else 0) * (if r ∣ t then G t else 0) := by
      refine le_trans (abs_sum_le_sum_abs _ _) ?_
      rw [mul_sum]
      have hsub : (S9 η p (decide (Even (ω d)))).filter (fun t : ℕ => ¬ Nat.Coprime d t) ⊆ Dy := by
        intro t ht
        exact divisors_primorial_mono hηy (mem_filter.1 (mem_filter.1 ht).1).1
      refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ => mul_nonneg hK0.le
        (sum_nonneg fun r _ => by split_ifs <;> simp [hG0])))
      apply sum_le_sum; intro t ht
      have ht1 := mem_filter.1 ht
      have ht2 := mem_filter.1 ht1.1
      have ht0 : 0 < t := Nat.pos_of_mem_divisors ht2.1
      have ht1' : (1 : ℝ) ≤ t := by exact_mod_cast ht0
      obtain ⟨r, hr, hrd, hrt⟩ := Nat.Prime.not_coprime_iff_dvd.1 ht1.2
      have hrR : r ∈ R := by
        rw [hR, mem_filter]
        refine ⟨primesBelow_mono hηy (mem_PB_of_dvd hr (hrt.trans (Nat.dvd_of_mem_divisors ht2.1))), ?_⟩
        have := ht2.2.1 r (Nat.mem_primeFactors.2 ⟨hr, hrt, ht0.ne'⟩)
        exact_mod_cast this
      have hsig : |sigmaP b (η / t)| ≤ K :=
        abs_sigma_le b (div_pos hη0 (by linarith)) (le_trans (div_le_self hη0.le ht1') hηy) (by linarith)
      rw [abs_mul, abs_of_nonneg (hG0 t)]
      calc G t * |sigmaP b (η / t)| ≤ K * G t := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hsig (hG0 t)
        _ ≤ K * ∑ r ∈ R, (if r ∣ d then 1 else 0) * (if r ∣ t then G t else 0) := by
            apply mul_le_mul_of_nonneg_left _ hK0.le
            have := single_le_sum (f := fun r => (if r ∣ d then (1 : ℝ) else 0) * (if r ∣ t then G t else 0))
              (fun r _ => by split_ifs <;> simp [hG0]) hrR
            simp only [if_pos hrd, if_pos hrt, one_mul] at this
            exact this
    rw [abs_mul]
    calc _ ≤ G d * (K * ∑ t ∈ Dy, ∑ r ∈ R, (if r ∣ d then 1 else 0) * (if r ∣ t then G t else 0)) :=
          mul_le_mul hA hT (abs_nonneg _) (hG0 d)
      _ = K * ∑ t ∈ Dy, ∑ r ∈ R, (if r ∣ d then G d else 0) * (if r ∣ t then G t else 0) := by
          rw [mul_left_comm, mul_sum]; congr 1; apply sum_congr rfl; intro t _
          rw [mul_sum]; apply sum_congr rfl; intro r _
          split_ifs <;> ring
  have hX : |Xd b y p| ≤ G p * (K * PS) := by
    unfold Xd
    rw [abs_mul]
    have hGp : |rhoB b p / (p : ℝ)| = G p := abs_of_nonneg (hG0 p)
    rw [hGp]
    apply mul_le_mul_of_nonneg_left _ (hG0 p)
    refine le_trans (abs_sum_le_sum_abs _ _) (le_trans (sum_le_sum hper) ?_)
    rw [hPS, mul_sum]
    apply sum_le_sum_of_subset_of_nonneg
    · intro d hd
      exact divisors_primorial_mono (Real.rpow_le_self_of_one_le hy1 (by norm_num [UU])) (mem_filter.1 hd).1
    · intro d _ _
      exact mul_nonneg hK0.le (sum_nonneg fun t _ => sum_nonneg fun r _ =>
        mul_nonneg (by split_ifs <;> simp [hG0]) (by split_ifs <;> simp [hG0]))
  have hPS0 : 0 ≤ PS := by
    rw [hPS]
    exact sum_nonneg fun d _ => sum_nonneg fun t _ => sum_nonneg fun r _ =>
      mul_nonneg (by split_ifs <;> simp [hG0]) (by split_ifs <;> simp [hG0])
  calc |Xd b y p| ≤ G p * (K * PS) := hX
    _ ≤ (1 / p) * (K * (K ^ 2 * (2 / ((p : ℝ) + 1)))) := by
        apply mul_le_mul (G_le_inv b p) _ (mul_nonneg hK0.le hPS0) (by positivity)
        exact mul_le_mul_of_nonneg_left hPSb hK0.le
    _ = 2 * K ^ 3 / ((p : ℝ) * ((p : ℝ) + 1)) := by field_simp
    _ ≤ 2 * K ^ 3 / (p : ℝ) ^ 2 := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith

end M10

end Omega3
