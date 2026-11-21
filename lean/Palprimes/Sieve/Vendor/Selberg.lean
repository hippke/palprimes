import Mathlib

/-!
# Selberg's Λ² upper-bound sieve, ported from PrimeNumberTheoremAnd
(https://github.com/AlexKontorovich/PrimeNumberTheoremAnd, commit a4fb698)
(`Mathlib/NumberTheory/Sieve/{AuxResults,Basic,Selberg}.lean`, Arend Mellendijk, Apache 2.0),
on top of mathlib's `Mathlib/NumberTheory/SelbergSieve.lean` (`BoundingSieve`, `SelbergSieve`).

Main results:
* `Palprimes.SelbergPort.selberg_bound_simple` : the general simple Selberg bound.
* `Palprimes.selberg_concrete` : the bound for density `1/d`, unit weights, arbitrary finite
  support and an arbitrary finite set of primes.
-/

noncomputable section

open scoped BigOperators Classical ArithmeticFunction.Moebius ArithmeticFunction.omega
  ArithmeticFunction.zeta

open Finset Real Nat ArithmeticFunction BoundingSieve

namespace Palprimes

namespace SelbergPort

/-! ### Auxiliary results (from `AuxResults.lean` and `Basic.lean`) -/

theorem sum_over_dvd_ite {α : Type _} [Ring α] {P : ℕ} (hP : P ≠ 0) {n : ℕ} (hn : n ∣ P)
    {f : ℕ → α} : ∑ d ∈ n.divisors, f d = ∑ d ∈ P.divisors, if d ∣ n then f d else 0 := by
  rw [← Finset.sum_filter, Nat.divisors_filter_dvd_of_dvd hP hn]

theorem moebius_inv_dvd_lower_bound (l m : ℕ) (hm : Squarefree m) :
    (∑ d ∈ m.divisors, if l ∣ d then (μ d:ℤ) else 0) = if l = m then (μ l:ℤ) else 0 := by
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm.ne_zero
  revert hm
  revert m
  apply (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq_on
    {n | Squarefree n} (fun _ _ => Squarefree.squarefree_of_dvd)).mpr
  intro m hm_pos hm
  rw [sum_divisorsAntidiagonal' (f:= fun x y => μ x • if l=y then μ l else 0)]
  by_cases hl : l ∣ m
  · rw [ite_eq_left hl, sum_eq_single l]
    · have hmul : m / l * l = m := Nat.div_mul_cancel hl
      rw [ite_eq_left rfl, smul_eq_mul, ← isMultiplicative_moebius.map_mul_of_coprime,
        hmul]
      apply coprime_of_squarefree_mul; rw [hmul]; exact hm
    · intro d _ hdl; rw [ite_eq_right hdl.symm, smul_zero]
    · intro h; rw [mem_divisors] at h; exfalso; exact h ⟨hl, (Nat.ne_of_lt hm_pos).symm⟩
  · rw [ite_eq_right hl, sum_eq_zero]; intro d hd
    rw [ite_eq_right, smul_zero]
    by_contra h; rw [← h] at hd; exact hl (dvd_of_mem_divisors hd)

theorem moebius_inv_dvd_lower_bound' {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then μ d else 0) = if l = m then μ l else 0 := by
  rw [← moebius_inv_dvd_lower_bound _ _ (Squarefree.squarefree_of_dvd hm hP),
    sum_over_dvd_ite hP.ne_zero hm]
  simp_rw [ite_and, ← sum_filter, filter_comm]

theorem moebius_inv_dvd_lower_bound_real {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then (μ d : ℝ) else 0) =
      if l = m then (μ l : ℝ) else 0 := by
  norm_cast
  apply moebius_inv_dvd_lower_bound' hP l m hm

private theorem lambdaSquared_eq_zero_of_support_wlog {w : ℕ → ℝ} {y : ℝ}
    (hw : ∀ (d : ℕ), ¬d ^ 2 ≤ y → w d = 0)
    {d : ℕ} (hd : ¬↑d ≤ y) (d1 : ℕ) (d2 : ℕ) (h : d = Nat.lcm d1 d2) (hle : d1 ≤ d2) :
    w d1 * w d2 = 0 := by
  rw [hw d2, mul_zero]
  by_contra hyp; apply hd
  apply le_trans _ hyp
  norm_cast
  calc _ ≤ (d1.lcm d2) := by rw [h]
      _ ≤ (d1*d2) := Nat.div_le_self _ _
      _ ≤ _       := ?_
  · rw [sq]; gcongr

theorem lambdaSquared_eq_zero_of_support (w : ℕ → ℝ) (y : ℝ)
    (hw : ∀ d : ℕ, ¬d ^ 2 ≤ y → w d = 0) (d : ℕ) (hd : ¬d ≤ y) :
    lambdaSquared w d = 0 := by
  dsimp only [lambdaSquared]
  by_cases hy : 0 ≤ y
  swap
  · push Not at hd hy
    have : ∀ d' : ℕ, w d' = 0 := by
      intro d'; apply hw
      have : (0:ℝ) ≤ (d') ^ 2 := by positivity
      linarith
    apply sum_eq_zero; intro d1 _
    apply sum_eq_zero; intro d2 _
    rw [this d1, this d2]
    simp only [mul_zero, ite_self]
  apply sum_eq_zero; intro d1 _
  apply sum_eq_zero; intro d2 _
  split_ifs with h
  swap
  · rfl
  rcases Nat.le_or_le d1 d2 with hle | hle
  · apply lambdaSquared_eq_zero_of_support_wlog hw hd d1 d2 h hle
  · rw [mul_comm]
    apply lambdaSquared_eq_zero_of_support_wlog hw hd d2 d1
      (Nat.lcm_comm d1 d2 ▸ h) hle

/-! ### The Selberg sieve (from `Selberg.lean`) -/

set_option quotPrecheck false

variable (s : SelbergSieve)
local notation3 "ν" => BoundingSieve.nu (self := SelbergSieve.toBoundingSieve (self := s))
local notation3 "P" => BoundingSieve.prodPrimes (self := SelbergSieve.toBoundingSieve (self := s))
local notation3 "X" => BoundingSieve.totalMass (self := SelbergSieve.toBoundingSieve (self := s))
local notation3 "R" => BoundingSieve.rem (s := SelbergSieve.toBoundingSieve (self := s))
local notation3 "g" => BoundingSieve.selbergTerms (s := SelbergSieve.toBoundingSieve (self := s))
local notation3 "y" => SelbergSieve.level (self := s)

def selbergBoundingSum : ℝ :=
  ∑ l ∈ divisors P, if l ^ 2 ≤ y then g l else 0

local notation3 "S" => Palprimes.SelbergPort.selbergBoundingSum s

theorem selbergBoundingSum_pos : 0 < S := by
  dsimp only [selbergBoundingSum]
  rw [← sum_filter]
  apply sum_pos
  · intro l hl
    rw [mem_filter, mem_divisors] at hl
    exact selbergTerms_pos hl.1.1
  · simp_rw [Finset.Nonempty, mem_filter]; use 1
    constructor
    · apply one_mem_divisors.mpr prodPrimes_ne_zero
    rw [cast_one, one_pow]
    exact s.one_le_level

theorem selbergBoundingSum_ne_zero : S ≠ 0 :=
  _root_.ne_of_gt (selbergBoundingSum_pos s)

theorem selbergBoundingSum_nonneg : 0 ≤ S := _root_.le_of_lt (selbergBoundingSum_pos s)

def selbergWeights : ℕ → ℝ := fun d =>
  if d ∣ P then
    (ν d)⁻¹ * g d * μ d * S⁻¹ *
      ∑ m ∈ divisors P, if (d * m) ^ 2 ≤ y ∧ m.Coprime d then g m else 0
  else 0

local notation3 "γ" => Palprimes.SelbergPort.selbergWeights s

theorem selbergWeights_eq_zero_of_not_dvd {d : ℕ} (hd : ¬ d ∣ P) : γ d = 0 := by
  rw [selbergWeights, ite_eq_right hd]

theorem selbergWeights_eq_zero (d : ℕ) (hd : ¬d ^ 2 ≤ y) : γ d = 0 := by
  dsimp only [selbergWeights]
  split_ifs with h
  · rw [mul_eq_zero_of_right _]
    apply Finset.sum_eq_zero
    refine fun m hm => ite_eq_right ?_
    intro hyp
    have : (d^2:ℝ) ≤ (d*m)^2 := by
      norm_cast
      refine Nat.pow_le_pow_left ?_ 2
      exact Nat.le_mul_of_pos_right _ (Nat.pos_of_mem_divisors hm)
    linarith [hyp.1]
  · rfl

theorem selbergWeights_mul_mu_nonneg (d : ℕ) (hdP : d ∣ P) : 0 ≤ γ d * μ d := by
  dsimp only [selbergWeights]
  rw [ite_eq_left hdP, mul_assoc]
  trans ((μ d :ℝ)^2 * (ν d)⁻¹ * g d * S⁻¹ * ∑ m ∈ divisors P,
          if (d * m) ^ 2 ≤ y ∧ Coprime m d then g m else 0)
  swap
  · apply le_of_eq; ring
  refine mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_) ?_
  · apply sq_nonneg
  · exact inv_nonneg.mpr (le_of_lt <| nu_pos_of_dvd_prodPrimes hdP)
  · exact le_of_lt <| selbergTerms_pos hdP
  · exact selbergBoundingSum_nonneg s
  apply sum_nonneg; intro m hm
  split_ifs with h
  · exact le_of_lt <| selbergTerms_pos (dvd_of_mem_divisors hm)
  · rfl

omit s in
theorem sum_mul_subst (k n : ℕ) {f : ℕ → ℝ} (h : ∀ l, l ∣ n → ¬ k ∣ l → f l = 0) :
      ∑ l ∈ n.divisors, f l
    = ∑ m ∈ n.divisors, if k*m ∣ n then f (k*m) else 0 := by
  by_cases hn: n = 0
  · simp [hn]
  by_cases hkn : k ∣ n
  swap
  · rw [sum_eq_zero, sum_eq_zero]
    · rintro m _
      rw [ite_eq_right]
      rintro h
      apply hkn
      exact (Nat.dvd_mul_right k m).trans h
    · intro l hl; apply h l (dvd_of_mem_divisors hl)
      apply fun hkl => hkn <| hkl.trans (dvd_of_mem_divisors hl)
  trans (∑ l ∈ n.divisors, ∑ m ∈ n.divisors, if l=k*m then f l else 0)
  · rw [sum_congr rfl]; intro l hl
    by_cases hkl : k ∣ l
    swap
    · rw [h l (dvd_of_mem_divisors hl) hkl, sum_eq_zero]
      intro m _; rw [ite_id]
    rw [sum_eq_single (l/k)]
    · rw [ite_eq_left]; rw [Nat.mul_div_cancel' hkl]
    · intro m _ hmlk
      apply ite_eq_right; revert hmlk; contrapose; intro hlkm
      rw [hlkm, mul_comm, Nat.mul_div_cancel]
      apply Nat.pos_of_dvd_of_pos hkn (Nat.pos_of_ne_zero hn)
    · contrapose!; intro _
      rw [mem_divisors]
      exact ⟨Trans.trans (Nat.div_dvd_of_dvd hkl) (dvd_of_mem_divisors hl), hn⟩
  · rw [sum_comm, sum_congr rfl]; intro m _
    split_ifs with hdvd
    · rw [sum_ite_eq_of_mem']
      simp only [mem_divisors, hdvd, ne_eq, hn, not_false_eq_true, and_self]
    · apply sum_eq_zero; intro l hl
      apply ite_eq_right
      rintro rfl
      simp only [mem_divisors, ne_eq] at hl
      exact hdvd hl.1

theorem selbergWeights_eq_dvds_sum (d : ℕ) :
    ν d * γ d =
      S⁻¹ * μ d *
        ∑ l ∈ divisors P, if d ∣ l ∧ l ^ 2 ≤ y then g l else 0 := by
  by_cases h_dvd : d ∣ P
  swap
  · dsimp only [selbergWeights]; rw [ite_eq_right h_dvd]
    rw [sum_eq_zero]
    · ring
    intro l hl; rw [mem_divisors] at hl
    rw [ite_eq_right]; push Not; intro h
    exfalso; exact h_dvd (dvd_trans h hl.left)
  dsimp only [selbergWeights]
  rw [ite_eq_left h_dvd]
  repeat rw [mul_sum]
  apply symm
  rw [sum_mul_subst d P]
  · apply sum_congr rfl
    intro m hm
    rw [mul_ite_zero, ← ite_and, mul_ite_zero, mul_ite_zero]
    apply if_ctx_congr _ _ fun _ => rfl
    · rw [coprime_comm]
      constructor
      · intro h
        push_cast at h
        exact ⟨h.2.2, coprime_of_squarefree_mul
          <| Squarefree.squarefree_of_dvd h.1 s.prodPrimes_squarefree⟩
      · intro h
        push_cast
        exact ⟨ Coprime.mul_dvd_of_dvd_of_dvd h.2 h_dvd (dvd_of_mem_divisors hm),
          Nat.dvd_mul_right d m, h.1⟩
    · intro h
      trans ((ν d)⁻¹ * (ν d) * g d * μ d / S * g m)
      · rw [inv_mul_cancel₀ (nu_ne_zero h_dvd),
          selbergTerms_isMultiplicative.map_mul_of_coprime <| coprime_comm.mp h.2]
        ring
      ring
  · intro l _ hdl
    rw [ite_eq_right, mul_zero]
    push Not; intro h; contradiction

theorem selbergWeights_diagonalisation (l : ℕ) (hl : l ∈ divisors P) :
    (∑ d ∈ divisors P, if l ∣ d then ν d * γ d else 0) =
      if l ^ 2 ≤ y then g l * μ l * S⁻¹ else 0 := by
  calc
    (∑ d ∈ divisors P, if l ∣ d then ν d * γ d else 0) =
        ∑ d ∈ divisors P, ∑ k ∈ divisors P,
          if l ∣ d ∧ d ∣ k ∧ k ^ 2 ≤ y then g k * S⁻¹ * (μ d:ℝ) else 0 := by
      apply sum_congr rfl; intro d _
      rw [selbergWeights_eq_dvds_sum, ← boole_mul, mul_sum, mul_sum]
      apply sum_congr rfl; intro k _
      rw [mul_ite_zero, ite_zero_mul_ite_zero]
      apply if_ctx_congr Iff.rfl _ (fun _ => rfl)
      intro _; ring
    _ = ∑ k ∈ divisors P, if k ^ 2 ≤ y then
            (∑ d ∈ divisors P, if l ∣ d ∧ d ∣ k then (μ d:ℝ) else 0) * g k * S⁻¹
          else 0 := by
      rw [sum_comm]; apply sum_congr rfl; intro k _
      apply symm
      rw [← boole_mul, sum_mul, sum_mul, mul_sum, sum_congr rfl]
      intro d _
      rw [ite_zero_mul, ite_zero_mul, ite_zero_mul, one_mul, ← ite_and]
      apply if_ctx_congr _ _ (fun _ => rfl)
      · tauto
      intro _; ring
    _ = if l ^ 2 ≤ y then g l * μ l * S⁻¹ else 0 := by
      rw [← sum_ite_eq_of_mem' (divisors P) l
        (fun _ => if l^2 ≤ y then g l * μ l * S⁻¹ else 0) hl]
      apply sum_congr rfl; intro k hk
      rw [moebius_inv_dvd_lower_bound_real s.prodPrimes_squarefree l _ (dvd_of_mem_divisors hk),
        ← ite_and, ite_zero_mul, ite_zero_mul, ← ite_and]
      apply if_ctx_congr _ _ fun _ => rfl
      · rw [and_comm, eq_comm]; apply and_congr_right
        intro heq; rw [heq]
      · intro h; rw [h.1]; ring

def selbergMuPlus : ℕ → ℝ :=
  lambdaSquared γ

local notation3 "μ⁺" => Palprimes.SelbergPort.selbergMuPlus s

theorem weight_one_of_selberg : γ 1 = 1 := by
  dsimp only [selbergWeights]
  rw [ite_eq_left (one_dvd P), s.nu_mult.left, selbergTerms_isMultiplicative.map_one]
  simp only [inv_one, mul_one, isUnit_one, IsUnit.squarefree, moebius_apply_of_squarefree,
    cardFactors_one, _root_.pow_zero, Int.cast_one, selbergBoundingSum, one_mul,
    coprime_one_right_eq_true, and_true, cast_one]
  rw [inv_mul_cancel₀]
  exact selbergBoundingSum_ne_zero s

theorem selbergμPlus_eq_zero (d : ℕ) (hd : ¬d ≤ y) : μ⁺ d = 0 := by
  apply lambdaSquared_eq_zero_of_support _ y _ d hd
  apply selbergWeights_eq_zero s

theorem selberg_isUpperMoebius : IsUpperMoebius μ⁺ :=
  upperMoebius_lambdaSquared γ (weight_one_of_selberg s)

theorem selberg_bound_simple_mainSum :
    mainSum (s := s.toBoundingSieve) μ⁺ = S⁻¹ := by
  rw [selbergMuPlus, mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  trans (∑ l ∈ divisors P, (if l ^ 2 ≤ y then g l * (S⁻¹) ^ 2 else 0))
  · apply sum_congr rfl; intro l hl
    rw [selbergWeights_diagonalisation s l hl, ite_pow, zero_pow two_ne_zero, mul_ite_zero]
    apply if_congr Iff.rfl _ rfl
    trans ((g l)⁻¹ * g l * g l * (μ l:ℝ)^2  * (S⁻¹) ^ 2)
    · ring
    norm_cast; rw [moebius_sq_eq_one_of_squarefree <| squarefree_of_mem_divisors_prodPrimes hl]
    rw [inv_mul_cancel₀ <| _root_.ne_of_gt <| selbergTerms_pos <| dvd_of_mem_divisors hl]
    push_cast
    ring
  simp_rw [← ite_zero_mul]
  rw [← sum_mul]
  change S * _ = _
  rw [sq, ← mul_assoc, mul_inv_cancel₀ (selbergBoundingSum_ne_zero s), one_mul]

omit s in
theorem eq_gcd_mul_of_dvd_of_coprime {k d m : ℕ} (hkd : k ∣ d) (hmd : Coprime m d)
    (hk : k ≠ 0) : k = d.gcd (k*m) := by
  obtain ⟨r, hr⟩ := hkd
  have hrdvd : r ∣ d := by use k; rw [mul_comm]; exact hr
  apply symm; rw [hr, Nat.gcd_mul_left, mul_eq_left₀ hk, Nat.gcd_comm]
  apply Coprime.coprime_dvd_right hrdvd hmd

private theorem helper {k m d : ℕ} (hkd : k ∣ d) (hk : k ∈ divisors P) (hm : m ∈ divisors P) :
    k * m ∣ P ∧ k = Nat.gcd d (k * m) ∧ (k * m) ^ 2 ≤ y ↔
    (k * m) ^ 2 ≤ y ∧ Coprime m d := by
  constructor
  · intro h
    constructor
    · exact h.2.2
    · obtain ⟨r, hr⟩ := hkd
      rw [hr, Nat.gcd_mul_left, eq_comm, mul_eq_left₀ (by rintro rfl; simp at hk ⊢)] at h
      rw [hr, coprime_comm]; apply Coprime.mul_left
      · apply coprime_of_squarefree_mul <|
          Squarefree.squarefree_of_dvd h.1 s.prodPrimes_squarefree
      · exact h.2.1
  · intro h
    constructor
    · apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      · rw [coprime_comm]; exact Coprime.coprime_dvd_right hkd h.2
      · exact dvd_of_mem_divisors hk
      · exact dvd_of_mem_divisors hm
    constructor
    · exact eq_gcd_mul_of_dvd_of_coprime hkd h.2 (by rintro rfl; simp at hk ⊢)
    · exact h.1

theorem selbergBoundingSum_ge {d : ℕ} (hdP : d ∣ P) :
    S ≥ γ d * ↑(μ d) * S := by
  calc
  _ = (∑ k ∈ divisors P, ∑ l ∈ divisors P, if k = d.gcd l ∧ l ^ 2 ≤ y then g l else 0) := by
    dsimp only [selbergBoundingSum]
    rw [sum_comm, sum_congr rfl]; intro l _
    simp_rw [ite_and]
    rw [sum_ite_eq_of_mem']
    · rw [mem_divisors]
      exact ⟨(Nat.gcd_dvd_left d l).trans (hdP), prodPrimes_ne_zero⟩
  _ = (∑ k ∈ divisors P,
          if k ∣ d then
            g k * ∑ m ∈ divisors P, if (k * m) ^ 2 ≤ y ∧ m.Coprime d then g m else 0
          else 0) := by
    apply sum_congr rfl; intro k hk
    rw [mul_sum]
    split_ifs with hkd
    swap
    · rw [sum_eq_zero]; intro l _
      rw [ite_eq_right]
      push Not; intro h; exfalso
      rw [h] at hkd
      exact hkd <| Nat.gcd_dvd_left d l
    rw [sum_mul_subst k P, sum_congr rfl]
    · intro m hm
      rw [mul_ite_zero, ← ite_and]
      apply if_ctx_congr _ _ fun _ => rfl
      · exact_mod_cast helper s hkd hk hm
      · intro h
        apply selbergTerms_isMultiplicative.map_mul_of_coprime
        rw [gcd_comm]; apply h.2.coprime_dvd_right hkd
    · intro l _ hkl; apply ite_eq_right
      push Not; intro h; exfalso
      rw [h] at hkl; exact hkl (Nat.gcd_dvd_right d l)
  _ ≥ (∑ k ∈ divisors P, if k ∣ d
          then g k * ∑ m ∈ divisors P, if (d * m) ^ 2 ≤ y ∧ m.Coprime d then g m else 0
          else 0 ) := by
    apply sum_le_sum; intro k _
    split_ifs with hkd
    swap
    · rfl
    apply mul_le_mul le_rfl _ _ (le_of_lt <| selbergTerms_pos <| hkd.trans hdP)
    · apply sum_le_sum; intro m hm
      split_ifs with h h' h'
      · rfl
      · exfalso; apply h'
        refine ⟨?_, h.2⟩
        · trans ((d*m)^2:ℝ)
          · norm_cast; gcongr
            refine Nat.le_of_dvd ?_ hkd
            apply Nat.pos_of_ne_zero; apply ne_zero_of_dvd_ne_zero prodPrimes_ne_zero hdP
          exact_mod_cast h.1
      · refine le_of_lt <| selbergTerms_pos <| dvd_of_mem_divisors hm
      · rfl
    apply sum_nonneg; intro m hm
    split_ifs
    · apply le_of_lt <| selbergTerms_pos <| dvd_of_mem_divisors hm
    · rfl
  _ = _ := by
    conv => enter [1, 2, k]; rw [← ite_zero_mul]
    rw [← sum_mul, sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv hdP]
    trans (S * S⁻¹ * (μ d:ℝ)^2 * (ν d)⁻¹ * g d * (∑ m ∈ divisors P, if (d*m) ^ 2 ≤ y ∧
      Coprime m d then g m else 0))
    · rw [mul_inv_cancel₀, ← Int.cast_pow, moebius_sq_eq_one_of_squarefree]
      · push_cast; ring
      · exact Squarefree.squarefree_of_dvd hdP s.prodPrimes_squarefree
      · exact selbergBoundingSum_ne_zero s
    dsimp only [selbergWeights]; rw [ite_eq_left hdP]
    ring

theorem selberg_bound_weights (d : ℕ) : |γ d| ≤ 1 := by
  by_cases hdP : d ∣ P
  swap
  · rw [selbergWeights_eq_zero_of_not_dvd s hdP]; simp only [zero_le_one, abs_zero]
  have : 1*S ≥ γ d * ↑(μ d) * S := by
    rw [one_mul]
    exact selbergBoundingSum_ge s hdP
  replace this : γ d * μ d ≤ 1 := by
    apply le_of_mul_le_mul_of_pos_right this (selbergBoundingSum_pos s)
  convert this using 1
  rw [← abs_of_nonneg <| selbergWeights_mul_mu_nonneg s d hdP,
    abs_mul, ← Int.cast_abs, abs_moebius_eq_one_of_squarefree <|
    (s.prodPrimes_squarefree.squarefree_of_dvd hdP), Int.cast_one, mul_one]

theorem selberg_bound_muPlus (n : ℕ) (hn : n ∈ divisors P) :
    |μ⁺ n| ≤ (3:ℝ) ^ ω n := by
  let f : ℕ → ℕ → ℝ := fun x z : ℕ => if n = x.lcm z then 1 else 0
  dsimp only [selbergMuPlus, lambdaSquared]
  calc
    |∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, if n = d1.lcm d2 then γ d1 * γ d2 else 0| ≤
        ∑ d1 ∈ n.divisors, |∑ d2 ∈ n.divisors, if n = d1.lcm d2 then γ d1 * γ d2 else 0| := ?_
    _ ≤ ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, |if n = d1.lcm d2 then γ d1 * γ d2 else 0| := ?_
    _ ≤ ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, f d1 d2 := ?_
    _ = (n.divisors ×ˢ n.divisors).sum fun p => f p.fst p.snd := ?_
    _ = Finset.card ((n.divisors ×ˢ n.divisors).filter
          fun p : ℕ × ℕ => n = p.fst.lcm p.snd) := ?_
    _ = (3:ℕ) ^ ω n := ?_
    _ = (3:ℝ) ^ ω n := ?_
  · apply abs_sum_le_sum_abs
  · gcongr; apply abs_sum_le_sum_abs
  · gcongr with d1 _ d2
    rw [apply_ite abs, abs_zero, abs_mul]
    simp only [f]
    by_cases h : n = d1.lcm d2
    · rw [ite_eq_left h, ite_eq_left h]
      exact (mul_le_of_le_one_left (abs_nonneg <| γ d2) (selberg_bound_weights s d1)).trans
        (selberg_bound_weights s d2)
    rw [ite_eq_right h, ite_eq_right h]
  · rw [← Finset.sum_product']
  · rw [← sum_filter, Finset.sum_const, smul_one_eq_cast]
  · norm_cast
    simp [← card_pair_lcm_eq (squarefree_of_mem_divisors_prodPrimes hn), eq_comm]
  norm_num

theorem selberg_bound_simple_errSum :
    errSum (s := s.toBoundingSieve) μ⁺ ≤
      ∑ d ∈ divisors P, if (d : ℝ) ≤ y then (3:ℝ) ^ ω d * |R d| else 0 := by
  dsimp only [errSum]
  gcongr with d hd
  split_ifs with h
  · apply mul_le_mul _ le_rfl (abs_nonneg <| R d) (pow_nonneg _ <| ω d)
    · apply selberg_bound_muPlus s d hd
    · norm_num
  · rw [selbergμPlus_eq_zero s d h, abs_zero, zero_mul]

/-- The simple form of Selberg's upper-bound sieve. -/
theorem selberg_bound_simple :
    siftedSum (s := s.toBoundingSieve) ≤
      X / S +
        ∑ d ∈ divisors P, if (d : ℝ) ≤ y then (3:ℝ) ^ ω d * |R d| else 0 := by
  calc
    siftedSum (s := s.toBoundingSieve) ≤ X * mainSum (s := s.toBoundingSieve) μ⁺ +
        errSum (s := s.toBoundingSieve) μ⁺ :=
      siftedSum_le_mainSum_errSum_of_upperMoebius _ (selberg_isUpperMoebius s)
    _ ≤ _ := ?_
  gcongr
  · rw [selberg_bound_simple_mainSum, div_eq_mul_inv]
  · apply selberg_bound_simple_errSum

end SelbergPort

/-! ### The concrete sieve: unit weights, density `1/d` -/

namespace SelbergPort

theorem prod_primes_squarefree (Pset : Finset ℕ) (h : ∀ p ∈ Pset, p.Prime) :
    Squarefree (∏ p ∈ Pset, p) := by
  refine Iff.mpr Nat.squarefree_iff_prime_squarefree ?_
  intro p hp; by_contra h_dvd
  by_cases hps : p ∈ Pset
  · rw [← Finset.mul_prod_erase (a:=p) (h := hps), mul_dvd_mul_iff_left (Nat.Prime.ne_zero hp)]
      at h_dvd
    obtain ⟨q, hq⟩ := hp.prime.exists_mem_finset_dvd h_dvd
    rw [Finset.mem_erase] at hq
    exact hq.1.1 <| symm <| (Nat.prime_dvd_prime_iff_eq hp (h q hq.1.2)).mp hq.2
  · have : p ∣ ∏ p ∈ Pset, p := Trans.trans (dvd_mul_right p p) h_dvd
    obtain ⟨q, hq⟩ := hp.prime.exists_mem_finset_dvd this
    have heq : p = q := by
      rw [← Nat.prime_dvd_prime_iff_eq hp (h q hq.1)]
      exact hq.2
    rw [heq] at hps; exact hps hq.1

/-- The density function `ν d = 1/d`. -/
def nuInv : ArithmeticFunction ℝ := (ζ : ArithmeticFunction ℝ).pdiv ArithmeticFunction.id

theorem nuInv_apply {d : ℕ} (hd : d ≠ 0) : nuInv d = 1 / (d : ℝ) := by
  simp [nuInv, ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.zeta_apply, hd]

theorem nuInv_zero : nuInv 0 = 0 := by simp

theorem nuInv_mult : nuInv.IsMultiplicative := by
  unfold nuInv; arith_mult

/-- The Selberg sieve with support `E`, unit weights, total mass `X`, sifting primes `Pset`,
density `1/d` and level `y`. -/
def concreteSieve (E : Finset ℕ) (Pset : Finset ℕ) (hP : ∀ p ∈ Pset, p.Prime)
    (X : ℝ) (y : ℝ) (hy : 1 ≤ y) : SelbergSieve where
  support := E
  prodPrimes := ∏ p ∈ Pset, p
  prodPrimes_squarefree := prod_primes_squarefree Pset hP
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := X
  nu := nuInv
  nu_mult := nuInv_mult
  nu_pos_of_prime := fun p hp _ => by
    rw [nuInv_apply hp.ne_zero]; have := hp.pos; positivity
  nu_lt_one_of_prime := fun p hp _ => by
    rw [nuInv_apply hp.ne_zero, one_div]
    apply inv_lt_one_of_one_lt₀
    exact_mod_cast hp.one_lt
  level := y
  one_le_level := hy

theorem totient_eq_prod_of_squarefree {l : ℕ} (hl : Squarefree l) :
    (Nat.totient l : ℝ) = ∏ p ∈ l.primeFactors, ((p : ℝ) - 1) := by
  have h := Nat.totient_mul_prod_primeFactors l
  rw [Nat.prod_primeFactors_of_squarefree hl] at h
  have hl0 : l ≠ 0 := hl.ne_zero
  have h' : Nat.totient l = ∏ p ∈ l.primeFactors, (p - 1) := by
    rw [mul_comm] at h
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hl0) h
  rw [h', Nat.cast_prod]
  apply prod_congr rfl
  intro p hp
  have : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_lt.le
  rw [Nat.cast_sub this, Nat.cast_one]

theorem selbergTerms_concrete (E Pset : Finset ℕ) (hP : ∀ p ∈ Pset, p.Prime) (X y : ℝ)
    (hy : 1 ≤ y) {l : ℕ} (hl : Squarefree l) :
    BoundingSieve.selbergTerms (s := (concreteSieve E Pset hP X y hy).toBoundingSieve) l =
      1 / (Nat.totient l : ℝ) := by
  rw [selbergTerms_apply, totient_eq_prod_of_squarefree hl]
  change nuInv l * ∏ p ∈ l.primeFactors, (1 - nuInv p)⁻¹ = _
  rw [nuInv_apply hl.ne_zero]
  have hl' : (l : ℝ) = ∏ p ∈ l.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hl]
  rw [hl', one_div, ← prod_inv_distrib, ← prod_mul_distrib, one_div,
    ← prod_inv_distrib]
  apply prod_congr rfl
  intro p hp
  have hp' := Nat.prime_of_mem_primeFactors hp
  rw [nuInv_apply hp'.ne_zero]
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp'.one_lt
  have h0 : (p : ℝ) ≠ 0 := by positivity
  have h2 : (p : ℝ) - 1 ≠ 0 := by linarith
  field_simp

end SelbergPort

open Finset in
/-- Selberg's Λ² upper bound with density `1/d`, for an arbitrary finite set and prime set. -/
theorem selberg_concrete (E : Finset ℕ) (Pset : Finset ℕ) (hP : ∀ p ∈ Pset, p.Prime)
    (X : ℝ) (y : ℝ) (hy : 1 ≤ y) :
    (#(E.filter (fun n => ∀ p ∈ Pset, ¬ p ∣ n)) : ℝ) ≤
      X / (∑ l ∈ (∏ p ∈ Pset, p).divisors with (((l : ℕ) : ℝ) ^ 2 ≤ y), (1 : ℝ) / (Nat.totient l)) +
      ∑ d ∈ (∏ p ∈ Pset, p).divisors with (((d : ℕ) : ℝ) ≤ y),
        (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors d) *
          |(#(E.filter (d ∣ ·)) : ℝ) - X / d| := by
  set s := SelbergPort.concreteSieve E Pset hP X y hy with hs
  have h := SelbergPort.selberg_bound_simple s
  have hsift : siftedSum (s := s.toBoundingSieve) =
      (#(E.filter (fun n => ∀ p ∈ Pset, ¬ p ∣ n)) : ℝ) := by
    rw [siftedSum, card_eq_sum_ones, Nat.cast_sum, sum_filter]
    apply sum_congr rfl
    intro n _
    change (if Nat.Coprime (∏ p ∈ Pset, p) n then (1:ℝ) else 0) = _
    have : Nat.Coprime (∏ p ∈ Pset, p) n ↔ ∀ p ∈ Pset, ¬ p ∣ n := by
      rw [Nat.coprime_prod_left_iff]
      exact forall₂_congr fun p hp => (hP p hp).coprime_iff_not_dvd
    simp only [this, Nat.cast_one]
  have hS : SelbergPort.selbergBoundingSum s =
      ∑ l ∈ (∏ p ∈ Pset, p).divisors with (((l : ℕ) : ℝ) ^ 2 ≤ y), (1 : ℝ) / (Nat.totient l) := by
    rw [SelbergPort.selbergBoundingSum, sum_filter]
    apply sum_congr rfl
    intro l hl
    change (if (l : ℝ) ^ 2 ≤ y then _ else 0) = _
    rw [SelbergPort.selbergTerms_concrete E Pset hP X y hy
      (squarefree_of_mem_divisors_prodPrimes hl)]
  have hR : ∑ d ∈ divisors (∏ p ∈ Pset, p), (if (d : ℝ) ≤ y then
      (3:ℝ) ^ ω d * |BoundingSieve.rem (s := s.toBoundingSieve) d| else 0) =
      ∑ d ∈ (∏ p ∈ Pset, p).divisors with (((d : ℕ) : ℝ) ≤ y),
        (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors d) *
          |(#(E.filter (d ∣ ·)) : ℝ) - X / d| := by
    rw [sum_filter]
    apply sum_congr rfl
    intro d hd
    have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
    have hrem : BoundingSieve.rem (s := s.toBoundingSieve) d =
        (#(E.filter (d ∣ ·)) : ℝ) - X / d := by
      rw [BoundingSieve.rem, BoundingSieve.multSum]
      change (∑ n ∈ E, if d ∣ n then (1:ℝ) else 0) - SelbergPort.nuInv d * X = _
      rw [SelbergPort.nuInv_apply hd0, ← sum_filter, sum_const, nsmul_eq_mul, mul_one]
      ring
    rw [hrem]
  rw [← hsift, ← hS, ← hR]
  exact h

end Palprimes
