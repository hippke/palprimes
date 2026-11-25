import Omega3.Statements
import Palprimes.Sieve.SelbergSum

/-! # M02 helpers (copied from S08, renamed), part G: `G(w) = β log w + O(1)` for the Selberg sum `GS b w`. -/

namespace Omega3

open Finset Palprimes

set_option linter.style.longLine false

lemma m02_gS_nonneg (b n : ℕ) : 0 ≤ gS b n := by
  unfold gS
  split_ifs
  · positivity
  · exact le_rfl

lemma m02_GS_nonneg (b : ℕ) (z : ℝ) : 0 ≤ GS b z :=
  Finset.sum_nonneg (fun n _ => m02_gS_nonneg b n)

lemma m02_mem_ltSet (z : ℝ) (n : ℕ) : n ∈ ltSet z ↔ 1 ≤ n ∧ (n : ℝ) < z := by
  unfold ltSet
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · intro h; exact h.2
  · intro h; exact ⟨Nat.lt_ceil.2 h.2, h⟩

lemma m02_ltSet_mono {z z' : ℝ} (h : z ≤ z') : ltSet z ⊆ ltSet z' := by
  intro n hn
  rw [m02_mem_ltSet] at hn ⊢
  exact ⟨hn.1, lt_of_lt_of_le hn.2 h⟩

lemma m02_GS_mono (b : ℕ) {z z' : ℝ} (h : z ≤ z') : GS b z ≤ GS b z' :=
  Finset.sum_le_sum_of_subset_of_nonneg (m02_ltSet_mono h) (fun n _ _ => m02_gS_nonneg b n)

lemma m02_ltSet_empty {z : ℝ} (hz : z ≤ 1) : ltSet z = ∅ := by
  ext n
  rw [m02_mem_ltSet]
  simp only [Finset.notMem_empty, iff_false, not_and, not_lt]
  intro h
  have : (1 : ℝ) ≤ n := by exact_mod_cast h
  linarith

lemma m02_GS_le_one {z : ℝ} (b : ℕ) (hz : z ≤ 1) : GS b z = 0 := by
  unfold GS; rw [m02_ltSet_empty hz]; simp

lemma m02_bigB_ne_zero (b : ℕ) (hb : 2 ≤ b) : bigB b ≠ 0 := by
  unfold bigB
  have : b < b ^ 3 := by
    calc b = b ^ 1 := (pow_one b).symm
      _ < b ^ 3 := Nat.pow_lt_pow_right (by omega) (by omega)
  omega

/-- Lower bound (M03 argument): `H_B(K) ≤ G(z)` for `K < z`. -/
lemma m02_HB_le (b : ℕ) (hb : 2 ≤ b) (K : ℕ) (z : ℝ) (hKz : (K : ℝ) < z) :
    HB (bigB b).primeFactors K ≤ GS b z := by
  classical
  have hB0 : bigB b ≠ 0 := m02_bigB_ne_zero b hb
  set Pset : Finset ℕ := (range (K + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ bigB b) with hPset
  have hP : ∀ p ∈ Pset, p.Prime := fun p hp => (Finset.mem_filter.1 hp).2.1
  have h1 : HB (bigB b).primeFactors K ≤
      ∑ n ∈ (Icc 1 K).filter (fun n => n ∈ Nat.factoredNumbers Pset), (1 : ℝ) / n := by
    unfold HB
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro m hm
      rw [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
      refine ⟨hm.1, ?_⟩
      rw [Nat.mem_factoredNumbers]
      refine ⟨by omega, fun p hp' => ?_⟩
      have hp := Nat.prime_of_mem_primeFactorsList hp'
      have hpm := Nat.dvd_of_mem_primeFactorsList hp'
      rw [hPset, Finset.mem_filter, Finset.mem_range]
      refine ⟨by have := Nat.le_of_dvd (by omega) hpm; omega, hp, fun hpB => ?_⟩
      exact hm.2 p (Nat.mem_primeFactors.2 ⟨hp, hpB, hB0⟩) hpm
    · intro m _ _; positivity
  have h2 := factored_le_selbergS Pset hP K ((K : ℝ) ^ 2) le_rfl
  have hPsq : Squarefree (∏ p ∈ Pset, p) := SelbergPort.prod_primes_squarefree Pset hP
  have hPcop : Nat.Coprime (∏ p ∈ Pset, p) (bigB b) := by
    apply Nat.Coprime.prod_left
    intro p hp
    have := (Finset.mem_filter.1 hp).2
    exact (Nat.Prime.coprime_iff_not_dvd this.1).2 this.2
  have h3 : ∑ l ∈ (∏ p ∈ Pset, p).divisors with (((l : ℕ) : ℝ) ^ 2 ≤ (K : ℝ) ^ 2), (1 : ℝ) / (Nat.totient l) ≤
      GS b z := by
    have hterm : ∀ l ∈ (∏ p ∈ Pset, p).divisors.filter (fun l : ℕ => (((l : ℕ) : ℝ) ^ 2 ≤ (K : ℝ) ^ 2)),
        (1 : ℝ) / (Nat.totient l) = gS b l := by
      intro l hl
      rw [Finset.mem_filter, Nat.mem_divisors] at hl
      unfold gS
      rw [if_pos ⟨hPsq.squarefree_of_dvd hl.1.1, Nat.Coprime.coprime_dvd_left hl.1.1 hPcop⟩]
    rw [Finset.sum_congr rfl hterm]
    unfold GS
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro l hl
      rw [Finset.mem_filter, Nat.mem_divisors] at hl
      rw [m02_mem_ltSet]
      refine ⟨Nat.pos_of_dvd_of_pos hl.1.1 (Nat.pos_of_ne_zero hl.1.2), ?_⟩
      have : (l : ℝ) ≤ K := by
        have h0 : (0 : ℝ) ≤ l := Nat.cast_nonneg _
        have h0' : (0 : ℝ) ≤ K := Nat.cast_nonneg _
        nlinarith [hl.2]
      linarith
    · intro n _ _; exact m02_gS_nonneg b n
  linarith

/-! ### Upper bound -/

/-- `k ↦ (√k)⁻¹` as a monoid hom. -/
noncomputable def m02isq : ℕ →* ℝ where
  toFun n := (Real.sqrt n)⁻¹
  map_one' := by simp
  map_mul' m n := by push_cast; rw [Real.sqrt_mul (Nat.cast_nonneg _), mul_inv]

/-- `k ↦ 1/k` as a monoid hom. -/
noncomputable def m02inv : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by simp
  map_mul' m n := by push_cast; rw [mul_inv]

/-- `J(n) = Π_{p | n} 1/(√p − 1)`. -/
noncomputable def m02J (n : ℕ) : ℝ := ∏ p ∈ n.primeFactors, 1 / (Real.sqrt p - 1)

lemma m02_sqrt_gt_one (p : ℕ) (hp : p.Prime) : 1 < Real.sqrt p := by
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)

/-- One squarefree `n`: `1/φ(n) ≤ (1/n) Σ_{k ∈ F(n), nk < w} 1/k + w^{−1/2} J(n)`. -/
lemma m02_inv_totient_le (n : ℕ) (hn : Squarefree n) (w : ℝ) (hw : 0 < w) :
    (1 : ℝ) / n.totient ≤
      (1 / (n : ℝ)) * ∑ k ∈ (range ⌈w⌉₊).filter (fun k => k ∈ Nat.factoredNumbers n.primeFactors ∧ ((n * k : ℕ) : ℝ) < w),
        (1 : ℝ) / k + (Real.sqrt w)⁻¹ * m02J n := by
  classical
  set t := n.primeFactors with ht
  have hn0 : n ≠ 0 := hn.ne_zero
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have htP : t.filter Nat.Prime = t := Finset.filter_true_of_mem (fun p hp => Nat.prime_of_mem_primeFactors hp)
  -- Euler products
  have H1 := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := m02inv) (fun {p} hp => by
      have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      simp only [m02inv, MonoidHom.coe_mk, OneHom.coe_mk, norm_inv, Real.norm_natCast]
      exact inv_lt_one_of_one_lt₀ this) t).2
  have H2 := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := m02isq) (fun {p} hp => by
      have := m02_sqrt_gt_one p hp
      simp only [m02isq, MonoidHom.coe_mk, OneHom.coe_mk, norm_inv, Real.norm_eq_abs,
        abs_of_pos (by linarith : (0 : ℝ) < Real.sqrt p)]
      exact inv_lt_one_of_one_lt₀ this) t).2
  rw [htP] at H1 H2
  set S := (range ⌈w⌉₊).subtype (fun k => k ∈ Nat.factoredNumbers t) with hS
  set g1 : Nat.factoredNumbers t → ℝ := fun m => if ((n * (m : ℕ) : ℕ) : ℝ) < w then (1 : ℝ) / (m : ℕ) else 0 with hg1
  have Hg1 : HasSum g1 (∑ m ∈ S, g1 m) := by
    apply hasSum_sum_of_ne_finset_zero
    intro m hm
    simp only [hg1]
    rw [if_neg]
    intro hlt
    apply hm
    rw [hS, Finset.mem_subtype, Finset.mem_range]
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero hn0
    have h2 : ((m : ℕ) : ℝ) < w := by
      have : ((m : ℕ) : ℝ) ≤ ((n * (m : ℕ) : ℕ) : ℝ) := by
        push_cast; nlinarith [(Nat.cast_nonneg (m : ℕ) : (0 : ℝ) ≤ (m : ℕ))]
      linarith
    exact Nat.lt_ceil.2 h2
  set c := Real.sqrt (n / w) with hc
  have Hg2 := H2.mul_left c
  have Hle := hasSum_le (f := fun m : Nat.factoredNumbers t => m02inv m)
    (g := fun m => g1 m + c * m02isq m) (fun m => by
      simp only [hg1, m02inv, m02isq, MonoidHom.coe_mk, OneHom.coe_mk]
      have hm0 : ((m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast m.2.1
      have hmpos : (0 : ℝ) < (m : ℕ) := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hm0)
      split_ifs with hlt
      · have : 0 ≤ c * (Real.sqrt ((m : ℕ) : ℝ))⁻¹ := by positivity
        rw [one_div]; linarith
      · push_neg at hlt
        push_cast at hlt
        -- `1/m ≤ √(n/w) / √m` since `nm ≥ w`
        have hsm : 0 < Real.sqrt ((m : ℕ) : ℝ) := Real.sqrt_pos.2 hmpos
        have key : 1 ≤ c * Real.sqrt ((m : ℕ) : ℝ) := by
          rw [hc, ← Real.sqrt_mul (by positivity)]
          rw [show (1 : ℝ) = Real.sqrt 1 by simp]
          apply Real.sqrt_le_sqrt
          rw [div_mul_eq_mul_div, le_div_iff₀ hw]; linarith
        have e : (((m : ℕ) : ℝ))⁻¹ = (Real.sqrt ((m : ℕ) : ℝ))⁻¹ * (Real.sqrt ((m : ℕ) : ℝ))⁻¹ := by
          rw [← mul_inv, Real.mul_self_sqrt hmpos.le]
        have h3 : (Real.sqrt ((m : ℕ) : ℝ))⁻¹ ≤ c := by
          rw [inv_le_iff_one_le_mul₀ hsm]; linarith
        have : (((m : ℕ) : ℝ))⁻¹ ≤ c * (Real.sqrt ((m : ℕ) : ℝ))⁻¹ := by
          rw [e]; exact mul_le_mul_of_nonneg_right h3 (by positivity)
        linarith) H1 (Hg1.add Hg2)
  -- convert
  have hfin : ∑ m ∈ S, g1 m = ∑ k ∈ (range ⌈w⌉₊).filter (fun k => k ∈ Nat.factoredNumbers t ∧ ((n * k : ℕ) : ℝ) < w),
      (1 : ℝ) / k := by
    rw [hS, Finset.sum_subtype_eq_sum_filter (f := fun k : ℕ => if ((n * k : ℕ) : ℝ) < w then (1 : ℝ) / k else 0)]
    rw [Finset.sum_filter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    by_cases h1 : k ∈ Nat.factoredNumbers t <;> by_cases h2 : ((n * k : ℕ) : ℝ) < w <;> simp [h1, h2]
  rw [hfin] at Hle
  have he := inv_mul_euler_eq n hn
  rw [Finset.filter_true_of_mem (fun p hp => Nat.prime_of_mem_primeFactors hp)] at he
  have hprod2 : (1 / (n : ℝ)) * (c * ∏ p ∈ t, (1 - m02isq p)⁻¹) = (Real.sqrt w)⁻¹ * m02J n := by
    have hsn : Real.sqrt (n : ℝ) = ∏ p ∈ t, Real.sqrt p := by
      have := map_prod m02isq (fun p => p) t
      simp only [m02isq, MonoidHom.coe_mk, OneHom.coe_mk] at this
      rw [Nat.prod_primeFactors_of_squarefree hn] at this
      push_cast at this
      rw [Finset.prod_inv_distrib] at this
      exact inv_injective this
    have hsn0 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
    have hc' : c = Real.sqrt n / Real.sqrt w := by rw [hc, Real.sqrt_div' _ hw.le]
    rw [hc']
    unfold m02J
    rw [← ht]
    have hsq : (1 / (n : ℝ)) = (Real.sqrt n)⁻¹ * (Real.sqrt n)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt hnpos.le, one_div]
    have : (1 / (n : ℝ)) * (Real.sqrt n / Real.sqrt w * ∏ p ∈ t, (1 - m02isq p)⁻¹) =
        (Real.sqrt w)⁻¹ * ((Real.sqrt n)⁻¹ * ∏ p ∈ t, (1 - m02isq p)⁻¹) := by
      rw [hsq]; field_simp
    rw [this, hsn, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    have hp1 := m02_sqrt_gt_one p (Nat.prime_of_mem_primeFactors hp)
    simp only [m02isq, MonoidHom.coe_mk, OneHom.coe_mk]
    have h0 : Real.sqrt (p : ℝ) - 1 ≠ 0 := by linarith
    have h0' : Real.sqrt (p : ℝ) ≠ 0 := by linarith
    field_simp
  calc (1 : ℝ) / n.totient = (1 / (n : ℝ)) * ∏ p ∈ t, (1 - m02inv p)⁻¹ := by
        rw [← he, ← ht]; simp [m02inv, one_div]
    _ ≤ (1 / (n : ℝ)) * (∑ k ∈ (range ⌈w⌉₊).filter (fun k => k ∈ Nat.factoredNumbers t ∧ ((n * k : ℕ) : ℝ) < w),
          (1 : ℝ) / k + c * ∏ p ∈ t, (1 - m02isq p)⁻¹) := mul_le_mul_of_nonneg_left Hle (by positivity)
    _ = _ := by rw [mul_add, hprod2]

lemma m02_isq_prod (n : ℕ) (hn : Squarefree n) :
    (Real.sqrt (n : ℝ))⁻¹ = ∏ p ∈ n.primeFactors, (Real.sqrt (p : ℝ))⁻¹ := by
  have := map_prod m02isq (fun p => p) n.primeFactors
  simp only [m02isq, MonoidHom.coe_mk, OneHom.coe_mk] at this
  rw [Nat.prod_primeFactors_of_squarefree hn] at this
  simpa using this

lemma m02_primeFactors_mul (n k : ℕ) (hn : Squarefree n) (hk : k ∈ Nat.factoredNumbers n.primeFactors) :
    (n * k).primeFactors = n.primeFactors := by
  rw [Nat.primeFactors_mul hn.ne_zero hk.1]
  exact Finset.union_eq_left.2 (Nat.primeFactors_subset_of_mem_factoredNumbers hk)

/-- Part A: the pairs `(n, k)` with `nk < w` inject into `m ≤ K` coprime to `B`. -/
lemma m02_partA (b : ℕ) (hb : 2 ≤ b) (w : ℝ) :
    ∑ n ∈ (ltSet w).filter (fun n => Squarefree n ∧ Nat.Coprime n (bigB b)),
      (1 / (n : ℝ)) * ∑ k ∈ (range ⌈w⌉₊).filter (fun k => k ∈ Nat.factoredNumbers n.primeFactors ∧ ((n * k : ℕ) : ℝ) < w),
        (1 : ℝ) / k ≤ HB (bigB b).primeFactors (⌈w⌉₊ - 1) := by
  classical
  set N := (ltSet w).filter (fun n => Squarefree n ∧ Nat.Coprime n (bigB b)) with hN
  set T : ℕ → Finset ℕ := fun n => (range ⌈w⌉₊).filter (fun k => k ∈ Nat.factoredNumbers n.primeFactors ∧ ((n * k : ℕ) : ℝ) < w) with hT
  have e1 : ∀ n ∈ N, (1 / (n : ℝ)) * ∑ k ∈ T n, (1 : ℝ) / k = ∑ k ∈ T n, (1 : ℝ) / ((n * k : ℕ) : ℝ) := by
    intro n _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    push_cast; rw [one_div_mul_one_div]
  rw [Finset.sum_congr rfl e1, Finset.sum_sigma']
  have hinj : Set.InjOn (fun x : (_ : ℕ) × ℕ => x.1 * x.2) (N.sigma T : Set ((_ : ℕ) × ℕ)) := by
    rintro ⟨n, k⟩ hx ⟨n', k'⟩ hx' h
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, hN, hT, Finset.mem_filter] at hx hx'
    simp only at h
    have hn := hx.1.2.1
    have hn' := hx'.1.2.1
    have h1 : n.primeFactors = n'.primeFactors := by
      rw [← m02_primeFactors_mul n k hn hx.2.2.1, ← m02_primeFactors_mul n' k' hn' hx'.2.2.1, h]
    have h2 : n = n' := by
      rw [← Nat.prod_primeFactors_of_squarefree hn, ← Nat.prod_primeFactors_of_squarefree hn', h1]
    subst h2
    have hn0 : 0 < n := Nat.pos_of_ne_zero hn.ne_zero
    have h3 : k = k' := Nat.eq_of_mul_eq_mul_left hn0 h
    subst h3; rfl
  rw [← Finset.sum_image (f := fun m : ℕ => (1 : ℝ) / (m : ℝ)) hinj]
  unfold HB
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨⟨n, k⟩, hx, rfl⟩ := hm
    simp only [Finset.mem_sigma, hN, hT, Finset.mem_filter] at hx
    obtain ⟨⟨hnl, hnsq, hncop⟩, _, hkF, hlt⟩ := hx
    rw [m02_mem_ltSet] at hnl
    rw [Finset.mem_filter, Finset.mem_Icc]
    have hk0 : k ≠ 0 := hkF.1
    refine ⟨⟨Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hnsq.ne_zero hk0), ?_⟩, ?_⟩
    · have := Nat.lt_ceil.2 hlt
      dsimp only
      omega
    · intro q hq hqd
      dsimp only at hqd
      have hqp := Nat.prime_of_mem_primeFactors hq
      have hqB := Nat.dvd_of_mem_primeFactors hq
      have hqn : q ∣ n := by
        rcases (Nat.Prime.dvd_mul hqp).1 hqd with h | h
        · exact h
        · have : q ∈ k.primeFactors := Nat.mem_primeFactors.2 ⟨hqp, h, hk0⟩
          exact Nat.dvd_of_mem_primeFactors (Nat.primeFactors_subset_of_mem_factoredNumbers hkF this)
      exact (Nat.Prime.coprime_iff_not_dvd hqp).1 (Nat.Coprime.coprime_dvd_left hqn hncop) hqB
  · intro m _ _; positivity

lemma m02_sum_isqrt (M : ℕ) : ∑ j ∈ Icc 1 M, (Real.sqrt (j : ℝ))⁻¹ ≤ 2 * Real.sqrt M := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    set a := Real.sqrt (M : ℝ)
    set c := Real.sqrt ((M + 1 : ℕ) : ℝ)
    have ha : 0 ≤ a := Real.sqrt_nonneg _
    have hc2 : c ^ 2 = a ^ 2 + 1 := by
      rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]; push_cast; ring
    have hc : 0 < c := Real.sqrt_pos.2 (by positivity)
    have hac : 2 * a * c ≤ 2 * a ^ 2 + 1 := by nlinarith [sq_nonneg (c - a)]
    have : c⁻¹ ≤ 2 * c - 2 * a := by
      rw [inv_le_iff_one_le_mul₀' hc]; nlinarith
    linarith

lemma m02_sum_dvd (d K : ℕ) (hd : 0 < d) (f : ℕ → ℝ) :
    ∑ m ∈ (Icc 1 K).filter (fun m => d ∣ m), f m = ∑ j ∈ Icc 1 (K / d), f (d * j) := by
  symm
  apply Finset.sum_nbij' (fun j => d * j) (fun m => m / d)
  · intro j hj
    simp only [mem_Icc] at hj
    simp only [mem_filter, mem_Icc]
    refine ⟨⟨by nlinarith, ?_⟩, dvd_mul_right d j⟩
    calc d * j ≤ d * (K / d) := Nat.mul_le_mul_left d hj.2
      _ ≤ K := Nat.mul_div_le K d
  · intro m hm
    simp only [mem_filter, mem_Icc] at hm
    simp only [mem_Icc]
    obtain ⟨⟨h1, h2⟩, k, rfl⟩ := hm
    rw [Nat.mul_div_cancel_left k hd]
    have h3 : d * k / d ≤ K / d := Nat.div_le_div_right h2
    rw [Nat.mul_div_cancel_left k hd] at h3
    refine ⟨?_, h3⟩
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at h1
    · exact h
  · intro j _; exact Nat.mul_div_cancel_left j hd
  · intro m hm
    simp only [mem_filter] at hm
    exact Nat.mul_div_cancel' hm.2
  · intro j _; rfl

/-- `Σ_{n < w, d | n} n^{−1/2} ≤ 2√w/d`. -/
lemma m02_sum_isqrt_dvd (d : ℕ) (hd : 0 < d) (w : ℝ) (hw : 0 < w) (S : Finset ℕ)
    (hS : ∀ n ∈ S, 1 ≤ n ∧ (n : ℝ) < w ∧ d ∣ n) :
    ∑ n ∈ S, (Real.sqrt (n : ℝ))⁻¹ ≤ 2 * Real.sqrt w / d := by
  classical
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : ∑ n ∈ S, (Real.sqrt (n : ℝ))⁻¹ ≤ ∑ n ∈ (Icc 1 ⌊w⌋₊).filter (fun m => d ∣ m), (Real.sqrt (n : ℝ))⁻¹ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      obtain ⟨h1, h2, h3⟩ := hS n hn
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨h1, Nat.le_floor h2.le⟩, h3⟩
    · intro n _ _; positivity
  rw [m02_sum_dvd d _ hd] at h1
  have h2 : ∑ j ∈ Icc 1 (⌊w⌋₊ / d), (Real.sqrt ((d * j : ℕ) : ℝ))⁻¹ =
      (Real.sqrt d)⁻¹ * ∑ j ∈ Icc 1 (⌊w⌋₊ / d), (Real.sqrt (j : ℝ))⁻¹ := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
    push_cast; rw [Real.sqrt_mul (Nat.cast_nonneg _), mul_inv]
  rw [h2] at h1
  have h3 := m02_sum_isqrt (⌊w⌋₊ / d)
  have h4 : Real.sqrt ((⌊w⌋₊ / d : ℕ) : ℝ) ≤ Real.sqrt w / Real.sqrt d := by
    rw [← Real.sqrt_div' _ hd'.le]
    apply Real.sqrt_le_sqrt
    rw [le_div_iff₀ hd']
    have : ((⌊w⌋₊ / d : ℕ) : ℝ) * d ≤ ⌊w⌋₊ := by exact_mod_cast Nat.div_mul_le_self _ _
    linarith [Nat.floor_le hw.le]
  have hsd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hd'
  have h5 : (Real.sqrt d)⁻¹ * (2 * (Real.sqrt w / Real.sqrt d)) = 2 * Real.sqrt w / d := by
    rw [show (2 * Real.sqrt w / d) = 2 * Real.sqrt w / (Real.sqrt d * Real.sqrt d) by
      rw [Real.mul_self_sqrt hd'.le]]
    field_simp
  calc _ ≤ _ := h1
    _ ≤ (Real.sqrt d)⁻¹ * (2 * (Real.sqrt w / Real.sqrt d)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
    _ = _ := h5

/-- The constant `S = Σ n^{−3/2}`. -/
noncomputable def m02S32 : ℝ := ∑' n : ℕ, ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹

lemma m02_jp (p : ℕ) (hp : p.Prime) : 1 / (Real.sqrt p - 1) / p ≤ 4 * ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hs := m02_sqrt_gt_one p hp
  have hs43 : 4 / 3 ≤ Real.sqrt p := by
    rw [show (4 / 3 : ℝ) = Real.sqrt (16 / 9) by
      rw [show (16 / 9 : ℝ) = (4 / 3) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hp0 : (0 : ℝ) < p := by linarith
  have e : (p : ℝ) ^ (3 / 2 : ℝ) = p * Real.sqrt p := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hp0, Real.rpow_one, Real.sqrt_eq_rpow]
  rw [e]
  have h1 : 0 < Real.sqrt p - 1 := by linarith
  rw [div_div, one_div, ← one_div, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

lemma m02_sum_jp (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∑ p ∈ P, 1 / (Real.sqrt p - 1) / p ≤ 4 * m02S32 := by
  have hsum : Summable (fun n : ℕ => ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    Real.summable_nat_rpow_inv.2 (by norm_num)
  calc ∑ p ∈ P, 1 / (Real.sqrt p - 1) / p ≤ ∑ p ∈ P, 4 * ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹ :=
        Finset.sum_le_sum (fun p hp => m02_jp p (hP p hp))
    _ = 4 * ∑ p ∈ P, ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by rw [Finset.mul_sum]
    _ ≤ 4 * m02S32 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact hsum.sum_le_tsum P (fun n _ => by positivity)

/-- Part B: `Σ_{n < w squarefree} J(n) ≤ 2√w exp(4S)`. -/
lemma m02_partB (w : ℝ) (hw : 0 < w) :
    ∑ n ∈ (ltSet w).filter Squarefree, m02J n ≤ 2 * Real.sqrt w * Real.exp (4 * m02S32) := by
  classical
  set N := (ltSet w).filter Squarefree with hN
  set Pw := (range ⌈w⌉₊).filter Nat.Prime with hPw
  set j : ℕ → ℝ := fun p => 1 / (Real.sqrt p - 1) with hj
  have hJ : ∀ n ∈ N, m02J n = (Real.sqrt (n : ℝ))⁻¹ * ∑ t ∈ n.primeFactors.powerset, ∏ p ∈ t, j p := by
    intro n hn
    rw [hN, Finset.mem_filter] at hn
    rw [m02_isq_prod n hn.2, ← Finset.prod_one_add, ← Finset.prod_mul_distrib]
    unfold m02J
    apply Finset.prod_congr rfl
    intro p hp
    have h1 := m02_sqrt_gt_one p (Nat.prime_of_mem_primeFactors hp)
    simp only [hj]
    have : Real.sqrt (p : ℝ) - 1 ≠ 0 := by linarith
    have : Real.sqrt (p : ℝ) ≠ 0 := by linarith
    field_simp
    ring
  rw [Finset.sum_congr rfl hJ]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm' (t' := Pw.powerset) (s' := fun t => N.filter (fun n => t ⊆ n.primeFactors))]
  swap
  · intro n t
    simp only [Finset.mem_powerset, Finset.mem_filter, hN, hPw]
    constructor
    · rintro ⟨⟨hn, hsq⟩, ht⟩
      refine ⟨⟨⟨hn, hsq⟩, ht⟩, fun p hp => ?_⟩
      have hpf := ht hp
      rw [Finset.mem_filter, Finset.mem_range]
      have hpn : p ≤ n := Nat.le_of_mem_primeFactors hpf
      rw [m02_mem_ltSet] at hn
      have : (p : ℝ) < w := lt_of_le_of_lt (by exact_mod_cast hpn) hn.2
      exact ⟨Nat.lt_ceil.2 this, Nat.prime_of_mem_primeFactors hpf⟩
    · rintro ⟨⟨⟨hn, hsq⟩, ht⟩, _⟩
      exact ⟨⟨hn, hsq⟩, ht⟩
  have hb : ∀ t ∈ Pw.powerset, ∑ n ∈ N.filter (fun n => t ⊆ n.primeFactors), (Real.sqrt (n : ℝ))⁻¹ * ∏ p ∈ t, j p ≤
      2 * Real.sqrt w * ∏ p ∈ t, (j p / p) := by
    intro t ht
    rw [Finset.mem_powerset] at ht
    have htP : ∀ p ∈ t, p.Prime := fun p hp => (Finset.mem_filter.1 (ht hp)).2
    set d := ∏ p ∈ t, p with hd
    have hd0 : 0 < d := Finset.prod_pos (fun p hp => (htP p hp).pos)
    rw [← Finset.sum_mul]
    have hs := m02_sum_isqrt_dvd d hd0 w hw (N.filter (fun n => t ⊆ n.primeFactors)) (by
      intro n hn
      simp only [hN, Finset.mem_filter] at hn
      rw [m02_mem_ltSet] at hn
      refine ⟨hn.1.1.1, hn.1.1.2, ?_⟩
      exact (Greaves.subset_primeFactors_iff t htP n (by have := hn.1.1.1; omega)).1 hn.2)
    have hjt : 0 ≤ ∏ p ∈ t, j p := Finset.prod_nonneg (fun p hp => by
      have := m02_sqrt_gt_one p (htP p hp); simp only [hj]; apply div_nonneg zero_le_one; linarith)
    calc (∑ n ∈ N.filter (fun n => t ⊆ n.primeFactors), (Real.sqrt (n : ℝ))⁻¹) * ∏ p ∈ t, j p
        ≤ 2 * Real.sqrt w / d * ∏ p ∈ t, j p := mul_le_mul_of_nonneg_right hs hjt
      _ = 2 * Real.sqrt w * ∏ p ∈ t, (j p / p) := by
        rw [Finset.prod_div_distrib (s := t) (f := j) (g := fun p : ℕ => (p : ℝ)), hd, Nat.cast_prod]; ring
  calc _ ≤ ∑ t ∈ Pw.powerset, 2 * Real.sqrt w * ∏ p ∈ t, (j p / p) := Finset.sum_le_sum hb
    _ = 2 * Real.sqrt w * ∏ p ∈ Pw, (1 + j p / p) := by rw [← Finset.mul_sum, Finset.prod_one_add]
    _ ≤ 2 * Real.sqrt w * Real.exp (∑ p ∈ Pw, j p / p) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [Real.exp_sum]
        apply Finset.prod_le_prod₀
        · intro p hp
          have := m02_sqrt_gt_one p (Finset.mem_filter.1 hp).2
          have : 0 ≤ j p / p := by simp only [hj]; apply div_nonneg (div_nonneg zero_le_one (by linarith)) (Nat.cast_nonneg _)
          linarith
        · intro p _
          have := Real.add_one_le_exp (j p / p); linarith
    _ ≤ 2 * Real.sqrt w * Real.exp (4 * m02S32) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.exp_le_exp.2 (m02_sum_jp Pw (fun p hp => (Finset.mem_filter.1 hp).2))

lemma m02_J_nonneg (n : ℕ) : 0 ≤ m02J n := by
  unfold m02J
  apply Finset.prod_nonneg
  intro p hp
  have := m02_sqrt_gt_one p (Nat.prime_of_mem_primeFactors hp)
  apply div_nonneg zero_le_one; linarith

/-- Upper bound: `G(w) ≤ H_B(⌈w⌉ − 1) + 2 exp(4S)`. -/
lemma m02_GS_upper (b : ℕ) (hb : 2 ≤ b) (w : ℝ) (hw : 0 < w) :
    GS b w ≤ HB (bigB b).primeFactors (⌈w⌉₊ - 1) + 2 * Real.exp (4 * m02S32) := by
  classical
  set N := (ltSet w).filter (fun n => Squarefree n ∧ Nat.Coprime n (bigB b)) with hN
  set R : ℕ → ℝ := fun n => (1 / (n : ℝ)) * ∑ k ∈ (range ⌈w⌉₊).filter
      (fun k => k ∈ Nat.factoredNumbers n.primeFactors ∧ ((n * k : ℕ) : ℝ) < w), (1 : ℝ) / k with hR
  have h1 : GS b w ≤ ∑ n ∈ N, (R n + (Real.sqrt w)⁻¹ * m02J n) := by
    unfold GS
    rw [hN, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro n _
    unfold gS
    split_ifs with h
    · exact m02_inv_totient_le n h.1 w hw
    · exact le_rfl
  rw [Finset.sum_add_distrib] at h1
  have hA := m02_partA b hb w
  have hB : ∑ n ∈ N, (Real.sqrt w)⁻¹ * m02J n ≤ 2 * Real.exp (4 * m02S32) := by
    rw [← Finset.mul_sum]
    have hsub : ∑ n ∈ N, m02J n ≤ ∑ n ∈ (ltSet w).filter Squarefree, m02J n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        rw [hN, Finset.mem_filter] at hn
        rw [Finset.mem_filter]; exact ⟨hn.1, hn.2.1⟩
      · intro n _ _; exact m02_J_nonneg n
    have hP := m02_partB w hw
    have hsw : 0 < Real.sqrt w := Real.sqrt_pos.2 hw
    calc (Real.sqrt w)⁻¹ * ∑ n ∈ N, m02J n ≤ (Real.sqrt w)⁻¹ * (2 * Real.sqrt w * Real.exp (4 * m02S32)) :=
          mul_le_mul_of_nonneg_left (le_trans hsub hP) (by positivity)
      _ = 2 * Real.exp (4 * m02S32) := by field_simp
  linarith

/-- `β = Π_{p | B}(1 − 1/p)`. -/
noncomputable def m02beta (b : ℕ) : ℝ := ∏ q ∈ (bigB b).primeFactors, (1 - 1 / (q : ℝ))

lemma m02_beta_pos (b : ℕ) : 0 < m02beta b := by
  unfold m02beta
  apply Finset.prod_pos
  intro q hq
  have : (2 : ℝ) ≤ q := by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).two_le
  rw [sub_pos, div_lt_one (by linarith)]; linarith

lemma m02_beta_le_one (b : ℕ) : m02beta b ≤ 1 := by
  unfold m02beta
  apply Finset.prod_le_one₀
  · intro q hq
    have : (2 : ℝ) ≤ q := by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).two_le
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  · intro q hq
    have : (0 : ℝ) ≤ 1 / q := by positivity
    linarith

/-- **G asymptotics**: `|G(w) − β log w| ≤ C` for `w ≥ 1`. -/
theorem m02_G_asymp (b : ℕ) (hb : 2 ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℝ, 1 ≤ w → |GS b w - m02beta b * Real.log w| ≤ C := by
  set s := (bigB b).primeFactors with hs
  have hsP : ∀ q ∈ s, q.Prime := fun q hq => Nat.prime_of_mem_primeFactors hq
  set C1 : ℝ := 2 ^ (#s) * (2 + 2 * Real.log (∏ q ∈ s, q : ℕ)) with hC1
  have hC1 : 0 ≤ C1 := by
    have : 0 ≤ Real.log (∏ q ∈ s, q : ℕ) := Real.log_natCast_nonneg _
    positivity
  set E := 2 * Real.exp (4 * m02S32) with hE
  have hE0 : 0 ≤ E := by positivity
  have hβ := m02_beta_pos b
  have hβ1 := m02_beta_le_one b
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- the case `w ≥ 2`
  have main : ∀ w : ℝ, 2 ≤ w → |GS b w - m02beta b * Real.log w| ≤ C1 + E + Real.log 2 := by
    intro w hw
    set K := ⌈w⌉₊ - 1 with hK
    have hc1 : (⌈w⌉₊ : ℝ) < w + 1 := Nat.ceil_lt_add_one (by linarith)
    have hc2 : w ≤ (⌈w⌉₊ : ℝ) := Nat.le_ceil w
    have hc3 : 2 ≤ ⌈w⌉₊ := by
      have : (2 : ℝ) ≤ ⌈w⌉₊ := le_trans hw hc2
      exact_mod_cast this
    have hK1 : 1 ≤ K := by omega
    have hKr : (K : ℝ) = (⌈w⌉₊ : ℝ) - 1 := by rw [hK, Nat.cast_sub (by omega)]; simp
    have hKw : (K : ℝ) < w := by linarith
    have hKw2 : w / 2 ≤ (K : ℝ) := by linarith
    have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
    have hlogK : Real.log K ≤ Real.log w := Real.log_le_log hK0 hKw.le
    have hlogK2 : Real.log w - Real.log 2 ≤ Real.log K := by
      rw [← Real.log_div (by linarith) (by norm_num)]
      exact Real.log_le_log (by linarith) hKw2
    have happ := HB_approx s hsP K hK1
    rw [abs_le] at happ
    have hlo := m02_HB_le b hb K w hKw
    have hup := m02_GS_upper b hb w (by linarith)
    have hβdef : m02beta b = ∏ q ∈ s, (1 - 1 / (q : ℝ)) := rfl
    rw [← hβdef] at happ
    rw [abs_le]
    constructor
    · nlinarith
    · nlinarith
  refine ⟨C1 + E + 2 * Real.log 2 + C1 + E, by positivity, fun w hw => ?_⟩
  rcases le_or_gt 2 w with h2 | h2
  · have := main w h2; linarith
  · have hG0 := m02_GS_nonneg b w
    have hG2 : GS b w ≤ GS b 2 := m02_GS_mono b h2.le
    have hm2 := main 2 le_rfl
    rw [abs_le] at hm2
    have hlw : 0 ≤ Real.log w := Real.log_nonneg hw
    have hlw2 : Real.log w ≤ Real.log 2 := Real.log_le_log (by linarith) h2.le
    rw [abs_le]
    constructor
    · nlinarith
    · nlinarith

end Omega3
