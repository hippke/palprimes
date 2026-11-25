import Omega3.Statements
import Palprimes.Sieve.SelbergSum

namespace Omega3

open Finset Palprimes
open scoped ArithmeticFunction.Moebius

set_option linter.style.longLine false

/-! Item S09 -/

lemma s09_gS_nonneg (b n : ℕ) : 0 ≤ gS b n := by
  unfold gS
  split_ifs
  · positivity
  · exact le_rfl

lemma s09_gS_pos (b n : ℕ) (h : Squarefree n ∧ Nat.Coprime n (bigB b)) : gS b n = 1 / (n.totient : ℝ) := by
  unfold gS; rw [if_pos h]

lemma s09_gS_zero (b n : ℕ) (h : ¬ (Squarefree n ∧ Nat.Coprime n (bigB b))) : gS b n = 0 := by
  unfold gS; rw [if_neg h]

lemma s09_sum_div_totient (d : ℕ) (hd : Squarefree d) :
    ∑ l ∈ d.divisors, (1 : ℝ) / (l.totient : ℝ) = (d : ℝ) / (d.totient : ℝ) := by
  have hP : ∀ p ∈ d.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have h1 := sum_rpow_div_totient d.primeFactors hP 0
  rw [Nat.prod_primeFactors_of_squarefree hd] at h1
  simp only [Real.rpow_zero] at h1
  rw [h1]
  have h2 := inv_mul_euler_eq d hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.ne_zero.bot_lt
  have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.2 hd.ne_zero.bot_lt
  have h3 : ∏ p ∈ d.primeFactors, (1 + 1 / ((p : ℝ) - 1)) =
      ∏ p ∈ d.primeFactors.filter Nat.Prime, (1 - (1 : ℝ) / p)⁻¹ := by
    rw [Finset.filter_true_of_mem hP]
    apply Finset.prod_congr rfl
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    have : (p : ℝ) - 1 ≠ 0 := by linarith
    have : (p : ℝ) ≠ 0 := by linarith
    field_simp
    ring
  rw [h3]
  have : ∏ p ∈ d.primeFactors.filter Nat.Prime, (1 - (1 : ℝ) / p)⁻¹ = (d : ℝ) / d.totient := by
    have := h2
    field_simp at this ⊢
    linarith
  exact this

lemma s09_GS_nonneg (b : ℕ) (z : ℝ) : 0 ≤ GS b z :=
  Finset.sum_nonneg (fun n _ => s09_gS_nonneg b n)

lemma s09_sel (b d : ℕ) (z : ℝ) :
    (d : ℝ) * ∑ k ∈ (ltSet z).filter (fun k => d ∣ k), gS b k ≤ GS b z := by
  classical
  by_cases hd : Squarefree d ∧ Nat.Coprime d (bigB b)
  swap
  · have : ∑ k ∈ (ltSet z).filter (fun k => d ∣ k), gS b k = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.mem_filter] at hk
      apply s09_gS_zero
      rintro ⟨h1, h2⟩
      exact hd ⟨h1.squarefree_of_dvd hk.2, Nat.Coprime.coprime_dvd_left hk.2 h2⟩
    rw [this, mul_zero]; exact s09_GS_nonneg b z
  obtain ⟨hdsq, hdB⟩ := hd
  have hd0 : 0 < d := hdsq.ne_zero.bot_lt
  set M : Finset ℕ := (range ⌈z⌉₊).filter (fun m => 1 ≤ m ∧ ((d * m : ℕ) : ℝ) < z ∧ Squarefree m ∧
    Nat.Coprime m d ∧ Nat.Coprime m (bigB b)) with hM
  -- the filter equals the image of M
  have hsub : (M.image (fun m => d * m)) ⊆ (ltSet z).filter (fun k => d ∣ k) := by
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨m, hm, rfl⟩ := hk
    rw [hM, Finset.mem_filter, Finset.mem_range] at hm
    rw [Finset.mem_filter]
    refine ⟨?_, dvd_mul_right _ _⟩
    unfold ltSet
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.lt_ceil.2 hm.2.2.1, Nat.mul_pos hd0 hm.2.1, hm.2.2.1⟩
  have hzero : ∀ k ∈ (ltSet z).filter (fun k => d ∣ k), k ∉ M.image (fun m => d * m) → gS b k = 0 := by
    intro k hk hnot
    apply s09_gS_zero
    rintro ⟨h1, h2⟩
    apply hnot
    rw [Finset.mem_filter] at hk
    obtain ⟨c, rfl⟩ := hk.2
    have hk1 := hk.1
    unfold ltSet at hk1
    rw [Finset.mem_filter, Finset.mem_range] at hk1
    rw [Finset.mem_image]
    refine ⟨c, ?_, rfl⟩
    rw [hM, Finset.mem_filter, Finset.mem_range]
    have hc0 : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; simp at hk1)
    have hsq := (Nat.squarefree_mul_iff.1 h1)
    refine ⟨lt_of_le_of_lt (Nat.le_mul_of_pos_left c hd0) hk1.1, hc0, hk1.2.2, hsq.2.2, hsq.1.symm,
      Nat.Coprime.coprime_dvd_left (dvd_mul_left c d) h2⟩
  have hsum1 : ∑ k ∈ (ltSet z).filter (fun k => d ∣ k), gS b k = ∑ k ∈ M.image (fun m => d * m), gS b k :=
    (Finset.sum_subset hsub hzero).symm
  have hinj : Set.InjOn (fun m => d * m) (M : Set ℕ) := fun a _ c _ h => Nat.eq_of_mul_eq_mul_left hd0 h
  rw [hsum1, Finset.sum_image hinj]
  -- gS (d m) = 1 / (φ d φ m)
  have hgdm : ∀ m ∈ M, gS b (d * m) = 1 / (d.totient : ℝ) * (1 / (m.totient : ℝ)) := by
    intro m hm
    rw [hM, Finset.mem_filter] at hm
    obtain ⟨_, _, _, hsq, hcop, hB⟩ := hm
    rw [s09_gS_pos b _ ⟨Nat.squarefree_mul_iff.2 ⟨hcop.symm, hdsq, hsq⟩, Nat.Coprime.mul_left hdB hB⟩,
      Nat.totient_mul hcop.symm]
    push_cast; rw [one_div_mul_one_div]
  rw [Finset.sum_congr rfl hgdm, ← Finset.mul_sum]
  -- the lower bound for GS through pairs (l, m)
  have hpairs : ∑ p ∈ d.divisors ×ˢ M, gS b (p.1 * p.2) ≤ GS b z := by
    unfold GS
    have himg : ((d.divisors ×ˢ M).image (fun p => p.1 * p.2)) ⊆ ltSet z := by
      intro k hk
      rw [Finset.mem_image] at hk
      obtain ⟨⟨l, m⟩, hp, rfl⟩ := hk
      rw [Finset.mem_product, Nat.mem_divisors] at hp
      have hm := hp.2
      rw [hM, Finset.mem_filter, Finset.mem_range] at hm
      have hl1 : 0 < l := Nat.pos_of_dvd_of_pos hp.1.1 hd0
      have hlm : l * m ≤ d * m := Nat.mul_le_mul_right m (Nat.le_of_dvd hd0 hp.1.1)
      have hlz : ((l * m : ℕ) : ℝ) < z := lt_of_le_of_lt (by exact_mod_cast hlm) hm.2.2.1
      unfold ltSet
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_ceil.2 hlz, Nat.mul_pos hl1 hm.2.1, hlz⟩
    have hinj2 : Set.InjOn (fun p : ℕ × ℕ => p.1 * p.2) ((d.divisors ×ˢ M : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
      rintro ⟨l, m⟩ hp ⟨l', m'⟩ hp' h
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Nat.mem_divisors] at hp hp'
      have hm := hp.2; have hm' := hp'.2
      rw [hM, Finset.mem_filter] at hm hm'
      simp only at h
      have e1 : l = l' := by
        have g1 : Nat.gcd (l * m) d = l := by
          rw [Nat.Coprime.gcd_mul_right_cancel l hm.2.2.2.2.1]
          exact Nat.gcd_eq_left hp.1.1
        have g2 : Nat.gcd (l' * m') d = l' := by
          rw [Nat.Coprime.gcd_mul_right_cancel l' hm'.2.2.2.2.1]
          exact Nat.gcd_eq_left hp'.1.1
        rw [← g1, ← g2, h]
      subst e1
      have hl0 : 0 < l := Nat.pos_of_dvd_of_pos hp.1.1 hd0
      have : m = m' := Nat.eq_of_mul_eq_mul_left hl0 h
      rw [this]
    calc ∑ p ∈ d.divisors ×ˢ M, gS b (p.1 * p.2)
        = ∑ k ∈ (d.divisors ×ˢ M).image (fun p => p.1 * p.2), gS b k :=
          (Finset.sum_image hinj2).symm
      _ ≤ ∑ k ∈ ltSet z, gS b k :=
          Finset.sum_le_sum_of_subset_of_nonneg himg (fun n _ _ => s09_gS_nonneg b n)
  have hpairs' : ∑ p ∈ d.divisors ×ˢ M, gS b (p.1 * p.2) =
      (d : ℝ) / (d.totient : ℝ) * ∑ m ∈ M, 1 / (m.totient : ℝ) := by
    rw [← s09_sum_div_totient d hdsq, Finset.sum_mul, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro l hl
    rw [Nat.mem_divisors] at hl
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [hM, Finset.mem_filter] at hm
    obtain ⟨_, _, _, hsq, hcop, hB⟩ := hm
    have hlsq : Squarefree l := hdsq.squarefree_of_dvd hl.1
    have hlB : Nat.Coprime l (bigB b) := Nat.Coprime.coprime_dvd_left hl.1 hdB
    have hlm : Nat.Coprime l m := Nat.Coprime.coprime_dvd_left hl.1 hcop.symm
    rw [s09_gS_pos b _ ⟨Nat.squarefree_mul_iff.2 ⟨hlm, hlsq, hsq⟩, Nat.Coprime.mul_left hlB hB⟩,
      Nat.totient_mul hlm]
    push_cast; rw [one_div_mul_one_div]
  calc (d : ℝ) * (1 / (d.totient : ℝ) * ∑ m ∈ M, 1 / (m.totient : ℝ))
      = (d : ℝ) / (d.totient : ℝ) * ∑ m ∈ M, 1 / (m.totient : ℝ) := by ring
    _ ≤ GS b z := by rw [← hpairs']; exact hpairs

/-! ### Step functions -/

lemma s09_foldl (u : ℝ) (l : List (ℚ × ℚ)) (acc : ℝ) :
    l.foldl (fun acc pr => if (pr.1 : ℝ) ≤ u then (pr.2 : ℝ) else acc) acc = acc ∨
      ∃ pr ∈ l, (pr.1 : ℝ) ≤ u ∧
        l.foldl (fun acc pr => if (pr.1 : ℝ) ≤ u then (pr.2 : ℝ) else acc) acc = (pr.2 : ℝ) := by
  induction l generalizing acc with
  | nil => left; rfl
  | cons a l ih =>
    simp only [List.foldl_cons]
    rcases ih (if (a.1 : ℝ) ≤ u then (a.2 : ℝ) else acc) with h | ⟨pr, hpr, h1, h2⟩
    · by_cases ha : (a.1 : ℝ) ≤ u
      · right; exact ⟨a, List.mem_cons_self, ha, by rw [h]; simp [ha]⟩
      · left; rw [h]; simp [ha]
    · right; exact ⟨pr, List.mem_cons_of_mem _ hpr, h1, h2⟩

lemma s09_eval_cases (e : StepFn) (u : ℝ) :
    StepFn.eval e u = 0 ∨ ∃ pr ∈ e, (pr.1 : ℝ) ≤ u ∧ StepFn.eval e u = (pr.2 : ℝ) := by
  unfold StepFn.eval
  exact s09_foldl u e 0

noncomputable def s09Mv (e : StepFn) : ℝ := (e.map (fun pr => |(pr.2 : ℝ)|)).sum

noncomputable def s09u0 (e : StepFn) : ℝ := (e.map (fun pr => (pr.1 : ℝ))).foldr min 1

lemma s09_u0_pos (e : StepFn) (he : StepOK e) : 0 < s09u0 e := by
  unfold s09u0
  have : ∀ l : List (ℚ × ℚ), (∀ pr ∈ l, 0 < pr.1) → 0 < (l.map (fun pr => (pr.1 : ℝ))).foldr min 1 := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons a l ih =>
      intro h
      simp only [List.map_cons, List.foldr_cons]
      exact lt_min (by exact_mod_cast h a List.mem_cons_self) (ih (fun pr hpr => h pr (List.mem_cons_of_mem _ hpr)))
  exact this e (fun pr hpr => (he.2 pr hpr).1)

lemma s09_u0_le (e : StepFn) (pr : ℚ × ℚ) (hpr : pr ∈ e) : s09u0 e ≤ (pr.1 : ℝ) := by
  unfold s09u0
  have : ∀ l : List (ℚ × ℚ), pr ∈ l → (l.map (fun pr => (pr.1 : ℝ))).foldr min 1 ≤ (pr.1 : ℝ) := by
    intro l
    induction l with
    | nil => intro h; simp at h
    | cons a l ih =>
      intro h
      simp only [List.map_cons, List.foldr_cons]
      rcases List.mem_cons.1 h with rfl | h'
      · exact min_le_left _ _
      · exact le_trans (min_le_right _ _) (ih h')
  exact this e hpr

lemma s09_Mv_nonneg (e : StepFn) : 0 ≤ s09Mv e :=
  List.sum_nonneg (by intro x hx; obtain ⟨pr, _, rfl⟩ := List.mem_map.1 hx; exact abs_nonneg _)

lemma s09_eval_abs (e : StepFn) (u : ℝ) : |StepFn.eval e u| ≤ s09Mv e := by
  rcases s09_eval_cases e u with h | ⟨pr, hpr, _, h⟩
  · rw [h]; simpa using s09_Mv_nonneg e
  · rw [h]
    unfold s09Mv
    apply List.single_le_sum (l := e.map (fun pr => |(pr.2 : ℝ)|))
    · intro x hx; obtain ⟨pr, _, rfl⟩ := List.mem_map.1 hx; exact abs_nonneg _
    · exact List.mem_map.2 ⟨pr, hpr, rfl⟩

lemma s09_eval_ne (e : StepFn) (he : StepOK e) (u : ℝ) (h : StepFn.eval e u ≠ 0) : s09u0 e ≤ u := by
  rcases s09_eval_cases e u with h0 | ⟨pr, hpr, h1, _⟩
  · exact absurd h0 h
  · exact le_trans (s09_u0_le e pr hpr) h1

lemma s09_GS_ge_one (b : ℕ) (z : ℝ) (hz : 1 < z) : 1 ≤ GS b z := by
  unfold GS
  have h1 : (1 : ℕ) ∈ ltSet z := by
    unfold ltSet
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_ceil.2 (by simpa using hz), le_rfl, by simpa using hz⟩
  have : gS b 1 = 1 := by
    rw [s09_gS_pos b 1 ⟨squarefree_one, Nat.coprime_one_left _⟩]; simp
  calc (1 : ℝ) = gS b 1 := this.symm
    _ ≤ ∑ n ∈ ltSet z, gS b n :=
      Finset.single_le_sum (f := gS b) (fun n _ => s09_gS_nonneg b n) h1

lemma s09_etaK (b : ℕ) (e : StepFn) (he : StepOK e) (x : ℝ) (hx : 1 < x) (k : ℕ)
    (hk : k ∈ ltSet (Real.sqrt x)) :
    |etaK b e x k| ≤ s09Mv e / (s09u0 e * GS b (Real.sqrt x)) := by
  classical
  set z := Real.sqrt x with hzdef
  have hz : 1 < z := by rw [hzdef]; exact Real.lt_sqrt_of_sq_lt (by linarith)
  have hG := s09_GS_ge_one b z hz
  set G := GS b z with hGdef
  have hGpos : 0 < G := by linarith
  have hu0 := s09_u0_pos e he
  have hMv := s09_Mv_nonneg e
  have hLz : 0 < Real.log z := Real.log_pos hz
  unfold ltSet at hk
  rw [Finset.mem_filter, Finset.mem_range] at hk
  have hk1 : 1 ≤ k := hk.2.1
  have hkz : (k : ℝ) < z := hk.2.2
  set Q := k.primeFactors.filter (fun q => etaQ b e x q ≠ 0) with hQ
  have hetaK : etaK b e x k = ∑ q ∈ Q, etaQ b e x q := by
    unfold etaK
    rw [hQ, Finset.sum_filter_ne_zero]
  have hQb : ∀ q ∈ Q, |etaQ b e x q| ≤ s09Mv e / G := by
    intro q _
    unfold etaQ
    rw [abs_div, abs_of_pos hGpos]
    exact div_le_div_of_nonneg_right (s09_eval_abs e _) hGpos.le
  have hQcard : s09u0 e * (Q.card : ℝ) < 1 := by
    have hq : ∀ q ∈ Q, z ^ (s09u0 e) ≤ (q : ℝ) := by
      intro q hq
      rw [hQ, Finset.mem_filter] at hq
      have hqp := Nat.prime_of_mem_primeFactors hq.1
      have hne : StepFn.eval e (Real.log q / Real.log (Real.sqrt x)) ≠ 0 := by
        intro h0; apply hq.2; unfold etaQ; rw [h0]; simp
      have hle := s09_eval_ne e he _ hne
      rw [← hzdef] at hle
      rw [le_div_iff₀ hLz] at hle
      rw [Real.rpow_def_of_pos (by linarith)]
      have hqpos : (0 : ℝ) < q := by exact_mod_cast hqp.pos
      calc Real.exp (Real.log z * s09u0 e) ≤ Real.exp (Real.log q) := Real.exp_le_exp.2 (by linarith)
        _ = q := Real.exp_log hqpos
    have hprod : ∏ q ∈ Q, q ∣ k := by
      apply Finset.prod_primes_dvd
      · intro q hq
        exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hq).1).prime
      · intro q hq
        exact Nat.dvd_of_mem_primeFactors (Finset.mem_filter.1 hq).1
    have hle : ((∏ q ∈ Q, q : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.le_of_dvd (by omega) hprod
    have h2 : (z ^ (s09u0 e)) ^ Q.card ≤ ((∏ q ∈ Q, q : ℕ) : ℝ) := by
      rw [Nat.cast_prod, ← Finset.prod_const]
      exact Finset.prod_le_prod₀ (fun _ _ => by positivity) hq
    have h3 : z ^ (s09u0 e * Q.card) < z ^ (1 : ℝ) := by
      rw [Real.rpow_one, Real.rpow_mul (by linarith), Real.rpow_natCast]
      linarith
    exact (Real.rpow_lt_rpow_left_iff hz).1 h3
  rw [hetaK]
  calc |∑ q ∈ Q, etaQ b e x q| ≤ ∑ q ∈ Q, |etaQ b e x q| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ Q, s09Mv e / G := Finset.sum_le_sum hQb
    _ = (Q.card : ℝ) * (s09Mv e / G) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (1 / s09u0 e) * (s09Mv e / G) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [le_div_iff₀ hu0]; linarith
    _ = s09Mv e / (s09u0 e * G) := by field_simp

lemma s09_nu_abs (b : ℕ) (e : StepFn) (he : StepOK e) (x : ℝ) (hx : 1 < x) :
    |nuA b e x| ≤ (1 + s09Mv e / s09u0 e) / GS b (Real.sqrt x) := by
  set z := Real.sqrt x with hzdef
  have hz : 1 < z := by rw [hzdef]; exact Real.lt_sqrt_of_sq_lt (by linarith)
  have hG := s09_GS_ge_one b z hz
  have hGpos : 0 < GS b z := by linarith
  have hu0 := s09_u0_pos e he
  have hMv := s09_Mv_nonneg e
  unfold nuA
  rw [← hzdef]
  rw [abs_div, abs_of_pos hGpos]
  apply div_le_div_of_nonneg_right _ hGpos.le
  have hS : |∑ k ∈ ltSet z, gS b k * etaK b e x k| ≤ s09Mv e / s09u0 e := by
    calc |∑ k ∈ ltSet z, gS b k * etaK b e x k| ≤ ∑ k ∈ ltSet z, |gS b k * etaK b e x k| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ ltSet z, gS b k * (s09Mv e / (s09u0 e * GS b z)) := by
          apply Finset.sum_le_sum
          intro k hk
          rw [abs_mul, abs_of_nonneg (s09_gS_nonneg b k)]
          exact mul_le_mul_of_nonneg_left (s09_etaK b e he x hx k hk) (s09_gS_nonneg b k)
      _ = s09Mv e / s09u0 e := by
          rw [← Finset.sum_mul]
          show GS b z * _ = _
          field_simp
  calc |1 + ∑ k ∈ ltSet z, gS b k * etaK b e x k| ≤ |(1 : ℝ)| + |∑ k ∈ ltSet z, gS b k * etaK b e x k| :=
        abs_add_le _ _
    _ ≤ 1 + s09Mv e / s09u0 e := by rw [abs_one]; linarith

lemma s09_lam_bound (b : ℕ) (e : StepFn) (he : StepOK e) (x : ℝ) (hx : 1 < x) (d : ℕ) :
    |lamA b e x d| ≤ 1 + 2 * (s09Mv e / s09u0 e) := by
  classical
  set z := Real.sqrt x with hzdef
  have hz : 1 < z := by rw [hzdef]; exact Real.lt_sqrt_of_sq_lt (by linarith)
  have hG := s09_GS_ge_one b z hz
  have hGpos : 0 < GS b z := by linarith
  have hu0 := s09_u0_pos e he
  have hMv := s09_Mv_nonneg e
  have hR : 0 ≤ s09Mv e / s09u0 e := by positivity
  unfold lamA
  rw [← hzdef]
  by_cases hc : Nat.Coprime d (bigB b)
  swap
  · rw [if_neg hc]; simp; linarith
  rw [if_pos hc]
  have hnu := s09_nu_abs b e he x hx
  rw [← hzdef] at hnu
  set F := (ltSet z).filter (fun k => d ∣ k) with hF
  have hterm : ∀ k ∈ F, |(μ (k / d) : ℝ) * ykA b e x k| ≤ gS b k * ((1 + 2 * (s09Mv e / s09u0 e)) / GS b z) := by
    intro k hk
    rw [hF, Finset.mem_filter] at hk
    have hη := s09_etaK b e he x hx k hk.1
    rw [← hzdef] at hη
    unfold ykA
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (s09_gS_nonneg b k)]
    have h1 : |(μ (k / d) : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have h2 : |(μ k : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have h3 : |nuA b e x - etaK b e x k| ≤ (1 + 2 * (s09Mv e / s09u0 e)) / GS b z := by
      calc |nuA b e x - etaK b e x k| ≤ |nuA b e x| + |etaK b e x k| := abs_sub _ _
        _ ≤ (1 + s09Mv e / s09u0 e) / GS b z + s09Mv e / s09u0 e / GS b z := by
            apply add_le_add hnu
            calc |etaK b e x k| ≤ s09Mv e / (s09u0 e * GS b z) := hη
              _ = s09Mv e / s09u0 e / GS b z := by rw [div_div]
        _ = (1 + 2 * (s09Mv e / s09u0 e)) / GS b z := by ring
    have h4 : 0 ≤ gS b k := s09_gS_nonneg b k
    calc |(μ (k / d) : ℝ)| * (|(μ k : ℝ)| * gS b k * |nuA b e x - etaK b e x k|)
        ≤ 1 * (1 * gS b k * ((1 + 2 * (s09Mv e / s09u0 e)) / GS b z)) := by
          apply mul_le_mul h1 _ (by positivity) (by norm_num)
          apply mul_le_mul _ h3 (abs_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_right h2 h4
      _ = _ := by ring
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg d)]
  calc (d : ℝ) * |∑ k ∈ F, (μ (k / d) : ℝ) * ykA b e x k|
      ≤ (d : ℝ) * ∑ k ∈ F, gS b k * ((1 + 2 * (s09Mv e / s09u0 e)) / GS b z) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
    _ = ((d : ℝ) * ∑ k ∈ F, gS b k) * ((1 + 2 * (s09Mv e / s09u0 e)) / GS b z) := by
        rw [← Finset.sum_mul]; ring
    _ ≤ GS b z * ((1 + 2 * (s09Mv e / s09u0 e)) / GS b z) := by
        apply mul_le_mul_of_nonneg_right (s09_sel b d z) (by positivity)
    _ = _ := by field_simp

lemma s09_lam1 (b : ℕ) (e : StepFn) (x : ℝ) (hx : 1 < x) : lamA b e x 1 = 1 := by
  classical
  set z := Real.sqrt x with hzdef
  have hz : 1 < z := by rw [hzdef]; exact Real.lt_sqrt_of_sq_lt (by linarith)
  have hG := s09_GS_ge_one b z hz
  have hGpos : 0 < GS b z := by linarith
  unfold lamA
  rw [← hzdef, if_pos (Nat.coprime_one_left _)]
  have hfil : (ltSet z).filter (fun k => 1 ∣ k) = ltSet z := Finset.filter_true_of_mem (fun k _ => one_dvd k)
  rw [hfil]
  have e1 : ∀ k ∈ ltSet z, (μ (k / 1) : ℝ) * ykA b e x k = gS b k * (nuA b e x - etaK b e x k) := by
    intro k _
    unfold ykA
    rw [Nat.div_one, ← mul_assoc, ← mul_assoc]
    by_cases hg : Squarefree k ∧ Nat.Coprime k (bigB b)
    · have : (μ k : ℝ) * (μ k : ℝ) = 1 := by
        have := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hg.1
        have h2 : ((μ k : ℤ) : ℝ) ^ 2 = 1 := by exact_mod_cast this
        nlinarith
      rw [this, one_mul]
    · rw [s09_gS_zero b k hg]; ring
  rw [Nat.cast_one, one_mul, Finset.sum_congr rfl e1]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hnu : nuA b e x = (1 + ∑ k ∈ ltSet z, gS b k * etaK b e x k) / GS b z := rfl
  rw [hnu]
  show GS b z * ((1 + ∑ k ∈ ltSet z, gS b k * etaK b e x k) / GS b z) - _ = 1
  field_simp
  ring

lemma s09_supp (b : ℕ) (e : StepFn) (x : ℝ) (d : ℕ) (h : lamA b e x d ≠ 0) :
    Squarefree d ∧ 1 ≤ d ∧ (d : ℝ) < Real.sqrt x := by
  classical
  unfold lamA at h
  by_cases hc : Nat.Coprime d (bigB b)
  swap
  · rw [if_neg hc] at h; exact absurd rfl h
  rw [if_pos hc] at h
  have h2 : ∑ k ∈ (ltSet (Real.sqrt x)).filter (fun k => d ∣ k), (μ (k / d) : ℝ) * ykA b e x k ≠ 0 := by
    intro h0; apply h; rw [h0, mul_zero]
  obtain ⟨k, hk, hk0⟩ := Finset.exists_ne_zero_of_sum_ne_zero h2
  rw [Finset.mem_filter] at hk
  have hμ : (μ k : ℝ) ≠ 0 := by
    intro h0; apply hk0; unfold ykA; rw [h0]; ring
  have hsq : Squarefree k := ArithmeticFunction.moebius_ne_zero_iff_squarefree.1 (by exact_mod_cast hμ)
  have hk1 := hk.1
  unfold ltSet at hk1
  rw [Finset.mem_filter, Finset.mem_range] at hk1
  have hdk : d ≤ k := Nat.le_of_dvd (by omega) hk.2
  refine ⟨hsq.squarefree_of_dvd hk.2, ?_, lt_of_le_of_lt (by exact_mod_cast hdk) hk1.2.2⟩
  rcases Nat.eq_zero_or_pos d with h0 | h0
  · subst h0; simp at hk; omega
  · exact h0

theorem itemS09 : ItemS09 := by
  intro b hb etas hetas
  refine ⟨(etas.map (fun e => 1 + 2 * (s09Mv e / s09u0 e))).sum, 4, ?_⟩
  intro x hx e he
  have hx1 : 1 < x := by linarith
  refine ⟨s09_lam1 b e x hx1, fun d => ?_, fun d hd => s09_supp b e x d hd⟩
  refine le_trans (s09_lam_bound b e (hetas e he) x hx1 d) ?_
  apply List.single_le_sum (l := etas.map (fun e => 1 + 2 * (s09Mv e / s09u0 e)))
  · intro y hy
    obtain ⟨e', he', rfl⟩ := List.mem_map.1 hy
    have := s09_Mv_nonneg e'
    have := s09_u0_pos e' (hetas e' he')
    positivity
  · exact List.mem_map.2 ⟨e, he, rfl⟩

end Omega3




