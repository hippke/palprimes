import KappaOmega2.Statements
import KappaOmega2.Items.S02_Base

/-!
# S02 with the missing hypothesis `m ≤ 1`: Greaves' Lemma 2 identity for squarefree `A ∣ P(z)`

`ItemS02` as frozen is false for `m > 1` (`S02_Neg.lean`). With `m ≤ 1` added (the route has `m = 1/85`) the identity
holds; `S02_fixed : ItemS02fix` below. Plan in `S02_PLAN.md`.
-/

namespace KappaOmega2

open Finset Palprimes Palprimes.Greaves
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

set_option linter.style.longLine false

/-- Proposed corrected S02: `ItemS02` plus `m ≤ 1`. -/
def ItemS02fix : Prop :=
  ∀ (y z m W1' : ℝ) (w : ℕ → ℝ) (A : ℕ), 0 < m → m ≤ 1 → 1 < y → z ≤ y → Squarefree A →
    (∀ p ∈ A.primeFactors, (p : ℝ) < z) →
    SigmaG y z W1' w A = Sig1 y z m W1' w A + Sig2 y z m W1' w A + Sig3 y z m W1' w A + Sig4 y z m W1' w A

lemma S02F_cop (A δ : ℕ) (hδ0 : δ ≠ 0) : ∀ t ∈ (radLt A (δ.minFac : ℝ)).divisors, Nat.Coprime t δ := by
  intro t ht
  have hC0 : radLt A (δ.minFac : ℝ) ≠ 0 := (S02_rad_sqf A _).ne_zero
  have ht0 : t ≠ 0 := by rintro rfl; exact hC0 (Nat.eq_zero_of_zero_dvd (Nat.dvd_of_mem_divisors ht))
  rw [← Nat.disjoint_primeFactors ht0 hδ0, Finset.disjoint_left]
  intro q hqt hqδ
  have hqC := Nat.primeFactors_mono (Nat.dvd_of_mem_divisors ht) hC0 hqt
  rw [S02_rad_pf, Finset.mem_filter] at hqC
  have h1 : q < δ.minFac := by exact_mod_cast hqC.2
  have h2 := Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hqδ).two_le (Nat.dvd_of_mem_primeFactors hqδ)
  omega

/-- Step A: `Σ₁ = Λ{A} − Σ_{δ ∣ A, δ ≠ 1} μ(δ)χ̄(δ) I(δ)`. -/
lemma S02F_sig1 (y m W1' : ℝ) (w : ℕ → ℝ) (A : ℕ) (hA : Squarefree A) :
    ∑ d ∈ A.divisors, (μ d : ℝ) * chi y m d * phiW W1' w d =
      LamA A W1' w - ∑ δ ∈ A.divisors.filter (· ≠ 1), (μ δ : ℝ) * chibar y m δ * innerS W1' w A δ := by
  have hA0 : A ≠ 0 := hA.ne_zero
  have h1 : ∀ d ∈ A.divisors, (μ d : ℝ) * chi y m d * phiW W1' w d =
      (μ d : ℝ) * phiW W1' w d - ((μ d : ℝ) * phiW W1' w d) * ∑ δ ∈ S02heads d, chibar y m δ := by
    intro d hd
    rw [S02_chi_tel y m d (hA.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd))]
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, S02_sum_muphi W1' w A hA,
    S02_swap A hA (fun d => (μ d : ℝ) * phiW W1' w d) (chibar y m)]
  congr 1
  apply Finset.sum_congr rfl
  intro δ hδ
  rw [Finset.mem_filter, Nat.mem_divisors] at hδ
  have hδ0 : δ ≠ 0 := by rintro rfl; exact hA0 (Nat.eq_zero_of_zero_dvd hδ.1.1)
  unfold innerS
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (S02F_cop A δ hδ0 t ht)]
  push_cast
  ring

lemma S02F_omega_zero (δ : ℕ) (hδ0 : δ ≠ 0) : ω δ = 0 ↔ δ = 1 := by
  rw [ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors, Finset.card_eq_zero,
    Nat.primeFactors_eq_empty]
  constructor
  · rintro (h | h)
    · exact absurd h hδ0
    · exact h
  · intro h; exact Or.inr h

/-- Step B: split of the `δ`-sum by `ν(δ)`. -/
lemma S02F_split (y m W1' : ℝ) (w : ℕ → ℝ) (A : ℕ) (hA : Squarefree A) :
    ∑ δ ∈ A.divisors.filter (· ≠ 1), (μ δ : ℝ) * chibar y m δ * innerS W1' w A δ =
      (∑ p ∈ A.primeFactors, -(chibar y m p * innerS W1' w A p)) +
      (∑ δ ∈ A.divisors.filter (fun δ : ℕ => Odd (ω δ) ∧ 3 ≤ ω δ ∧ (ω δ : ℝ) ≤ 1 / m),
          (μ δ : ℝ) * chibar y m δ * innerS W1' w A δ) +
      (∑ δ ∈ A.divisors.filter (fun δ : ℕ => Even (ω δ) ∧ 2 ≤ ω δ),
          (μ δ : ℝ) * chibar y m δ * innerS W1' w A δ) := by
  classical
  have hA0 : A ≠ 0 := hA.ne_zero
  set F : ℕ → ℝ := fun δ => (μ δ : ℝ) * chibar y m δ * innerS W1' w A δ with hF
  set S := A.divisors.filter (· ≠ 1) with hS
  rw [← Finset.sum_filter_add_sum_filter_not S (fun δ => ω δ = 1)]
  have hP : S.filter (fun δ => ω δ = 1) = A.primeFactors := by
    ext δ
    rw [hS, Finset.mem_filter, Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨⟨hδA, -⟩, hδ1⟩, hω⟩
      have hδsq := hA.squarefree_of_dvd hδA
      rw [ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors] at hω
      obtain ⟨p, hp⟩ := Finset.card_eq_one.1 hω
      have hpδ : δ = p := by
        have := Nat.prod_primeFactors_of_squarefree hδsq
        rw [hp] at this; simpa using this.symm
      have hpp : p.Prime := by
        have : p ∈ δ.primeFactors := by rw [hp]; simp
        exact Nat.prime_of_mem_primeFactors this
      exact Nat.mem_primeFactors.2 ⟨by rw [hpδ]; exact hpp, hδA, hA0⟩
    · intro hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      exact ⟨⟨⟨Nat.dvd_of_mem_primeFactors hp, hA0⟩, hpp.ne_one⟩,
        ArithmeticFunction.cardDistinctFactors_apply_prime hpp⟩
  rw [hP]
  have hpart1 : ∑ p ∈ A.primeFactors, F p = ∑ p ∈ A.primeFactors, -(chibar y m p * innerS W1' w A p) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [hF]; simp only
    rw [ArithmeticFunction.moebius_apply_prime (Nat.prime_of_mem_primeFactors hp)]
    push_cast; ring
  rw [hpart1, add_assoc]
  congr 1
  set S' := S.filter (fun δ => ¬ ω δ = 1) with hS'
  rw [← Finset.sum_filter_add_sum_filter_not S' (fun δ => Even (ω δ))]
  have hE : S'.filter (fun δ => Even (ω δ)) = A.divisors.filter (fun δ : ℕ => Even (ω δ) ∧ 2 ≤ ω δ) := by
    ext δ
    rw [hS', hS]
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨⟨⟨hδA, -⟩, hδ1⟩, hω1⟩, he⟩
      have hδ0 : δ ≠ 0 := by rintro rfl; exact hA0 (Nat.eq_zero_of_zero_dvd hδA)
      have hω0 : ω δ ≠ 0 := fun h => hδ1 ((S02F_omega_zero δ hδ0).1 h)
      exact ⟨⟨hδA, hA0⟩, he, by omega⟩
    · rintro ⟨⟨hδA, -⟩, he, h2⟩
      have hδ0 : δ ≠ 0 := by rintro rfl; exact hA0 (Nat.eq_zero_of_zero_dvd hδA)
      refine ⟨⟨⟨⟨hδA, hA0⟩, ?_⟩, by omega⟩, he⟩
      intro h1; rw [h1] at h2; simp at h2
  rw [hE, add_comm]
  congr 1
  set S'' := S'.filter (fun δ => ¬ Even (ω δ)) with hS''
  rw [← Finset.sum_filter_add_sum_filter_not S'' (fun δ => (ω δ : ℝ) ≤ 1 / m)]
  have hO : S''.filter (fun δ => (ω δ : ℝ) ≤ 1 / m) =
      A.divisors.filter (fun δ : ℕ => Odd (ω δ) ∧ 3 ≤ ω δ ∧ (ω δ : ℝ) ≤ 1 / m) := by
    ext δ
    rw [hS'', hS', hS]
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨⟨⟨⟨hδA, -⟩, hδ1⟩, hω1⟩, he⟩, hl⟩
      have hδ0 : δ ≠ 0 := by rintro rfl; exact hA0 (Nat.eq_zero_of_zero_dvd hδA)
      have hω0 : ω δ ≠ 0 := fun h => hδ1 ((S02F_omega_zero δ hδ0).1 h)
      have ho : Odd (ω δ) := Nat.not_even_iff_odd.mp he
      obtain ⟨k, hk⟩ := ho
      exact ⟨⟨hδA, hA0⟩, ⟨k, hk⟩, by omega, hl⟩
    · rintro ⟨⟨hδA, -⟩, ho, h3, hl⟩
      refine ⟨⟨⟨⟨⟨hδA, hA0⟩, ?_⟩, by omega⟩, Nat.not_even_iff_odd.mpr ho⟩, hl⟩
      intro h1; rw [h1] at h3; simp at h3
  rw [hO]
  have hZ : ∑ δ ∈ S''.filter (fun δ => ¬ (ω δ : ℝ) ≤ 1 / m), F δ = 0 := by
    apply Finset.sum_eq_zero
    intro δ hδ
    rw [hS'', hS', hS] at hδ
    simp only [Finset.mem_filter, Nat.mem_divisors] at hδ
    obtain ⟨⟨⟨⟨⟨hδA, -⟩, hδ1⟩, -⟩, he⟩, hl⟩ := hδ
    rw [hF]; simp only
    rw [S02_chibar_zero y m δ (hA.squarefree_of_dvd hδA) hδ1 he hl]; ring
  rw [hZ, add_zero]

/-- The `val` form as a sum. -/
lemma S02F_val_sum (c : ℝ) (w : ℕ → ℝ) (P : Finset ℕ) :
    S02val c w P = c * (if P = ∅ then 1 else 0) + ∑ q ∈ P, w q * (if P = {q} then 1 else 0) := by
  classical
  unfold S02val
  by_cases h0 : P = ∅
  · subst h0; simp
  · rw [if_neg h0, if_neg h0, mul_zero, zero_add]
    by_cases h1 : P.card = 1
    · obtain ⟨q, hq⟩ := Finset.card_eq_one.1 h1
      subst hq; simp
    · rw [if_neg h1]
      symm
      apply Finset.sum_eq_zero
      intro q _
      rw [if_neg]; · ring
      intro he; rw [he] at h1; simp at h1

/-- The indicator count of the least prime of `P` in `[s, ∞)`. -/
lemma S02F_count (P : Finset ℕ) (s : ℝ) :
    ∑ q ∈ P.filter (fun q : ℕ => s ≤ (q : ℝ)), (if ∀ r ∈ P, q ≤ r then (1 : ℝ) else 0) =
      (if ∀ r ∈ P, s ≤ (r : ℝ) then 1 else 0) - (if P = ∅ then 1 else 0) := by
  classical
  by_cases h0 : P = ∅
  · subst h0; simp
  · have hne : P.Nonempty := Finset.nonempty_iff_ne_empty.mpr h0
    set r₀ := P.min' hne with hr₀
    have hr₀P : r₀ ∈ P := Finset.min'_mem P hne
    have hiff : ∀ q ∈ P, (∀ r ∈ P, q ≤ r) ↔ q = r₀ := by
      intro q hq
      constructor
      · intro h; exact le_antisymm (h r₀ hr₀P) (Finset.min'_le P q hq)
      · rintro rfl r hr; exact Finset.min'_le P r hr
    have hcongr : ∀ q ∈ P.filter (fun q : ℕ => s ≤ (q : ℝ)),
        (if ∀ r ∈ P, q ≤ r then (1 : ℝ) else 0) = if q = r₀ then 1 else 0 := by
      intro q hq
      rw [Finset.mem_filter] at hq
      by_cases h : q = r₀
      · rw [if_pos ((hiff q hq.1).2 h), if_pos h]
      · rw [if_neg (fun h' => h ((hiff q hq.1).1 h')), if_neg h]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq', if_neg h0, sub_zero]
    have hs : (∀ r ∈ P, s ≤ (r : ℝ)) ↔ s ≤ (r₀ : ℝ) := by
      constructor
      · intro h; exact h r₀ hr₀P
      · intro h r hr
        have : (r₀ : ℝ) ≤ r := by exact_mod_cast Finset.min'_le P r hr
        linarith
    have h1 : (r₀ ∈ P.filter (fun q : ℕ => s ≤ (q : ℝ))) ↔ s ≤ (r₀ : ℝ) := by
      rw [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hr₀P, h⟩⟩
    split_ifs with ha hb hb
    · rfl
    · exact absurd (hs.2 (h1.1 ha)) hb
    · exact absurd (h1.2 (hs.1 hb)) ha
    · rfl

/-- Step E for one prime `p ∣ A`. -/
lemma S02F_perp (y m W1' : ℝ) (w : ℕ → ℝ) (A p : ℕ) (hm0 : 0 < m) (hm : m ≤ 1) (hy : 1 < y)
    (hA : Squarefree A) (hp : p ∈ A.primeFactors) :
    -(∑ q ∈ (primesBelow (p : ℝ)).filter (fun q : ℕ => q ∣ A ∧ y ≤ (q : ℝ) ^ 2 * p),
        ((W1' - w p) * Ssv (A / (p * q)) q - w q * Ssv (A / (p * q)) p)) =
      chibar y m p * innerS W1' w A p +
        -(chibar y m p) * (phiW W1' w p * Ssv (A / p) (Real.sqrt (y / p)) +
          ∑ q ∈ (A / p).primeFactors.filter (fun q : ℕ => q < p ∧ (q : ℝ) ^ 2 * p < y),
            w q * Ssv (A / (p * q)) p) := by
  classical
  have hA0 : A ≠ 0 := hA.ne_zero
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpA := Nat.dvd_of_mem_primeFactors hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  set a := A / p with ha
  have hAa : A = p * a := (Nat.mul_div_cancel' hpA).symm
  have ha0 : a ≠ 0 := by intro h; rw [h, mul_zero] at hAa; exact hA0 hAa
  have hasq : Squarefree a := hA.squarefree_of_dvd (Nat.div_dvd_of_dvd hpA)
  have hpna : ¬ p ∣ a := by
    intro hd
    have : p * p ∣ A := by rw [hAa]; exact Nat.mul_dvd_mul_left p hd
    exact hpp.one_lt.ne' (Nat.isUnit_iff.mp (hA _ this))
  set PC := a.primeFactors.filter (fun q : ℕ => q < p) with hPC
  have hphi : phiW W1' w p = W1' - w p := by
    unfold phiW; rw [Nat.Prime.primeFactors hpp, Finset.sum_singleton]
  -- the inner sum is val of PC
  have hI : innerS W1' w A p = S02val (phiW W1' w p) w PC := by
    rw [S02_inner W1' w A p hpp.ne_zero, S02_rad_pf, Nat.Prime.minFac_eq hpp]
    congr 1
    ext q
    rw [hPC, Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨hq, hlt⟩
      have hqlt : q < p := by exact_mod_cast hlt
      have hqp := Nat.prime_of_mem_primeFactors hq
      have hqa : q ∣ a := by
        have hcop : Nat.Coprime q p := (Nat.coprime_primes hqp hpp).2 (by omega)
        exact hcop.dvd_of_dvd_mul_left (hAa ▸ Nat.dvd_of_mem_primeFactors hq)
      exact ⟨Nat.mem_primeFactors.2 ⟨hqp, hqa, ha0⟩, hqlt⟩
    · rintro ⟨hq, hlt⟩
      refine ⟨Nat.primeFactors_mono (Nat.div_dvd_of_dvd hpA) hA0 hq, by exact_mod_cast hlt⟩
  -- primes of a are ≠ p
  have hane : ∀ r ∈ a.primeFactors, r ≠ p := by
    intro r hr hrp; rw [hrp] at hr; exact hpna (Nat.dvd_of_mem_primeFactors hr)
  -- (a/q).primeFactors = a.primeFactors.erase q
  have herase : ∀ q ∈ a.primeFactors, (A / (p * q)).primeFactors = a.primeFactors.erase q := by
    intro q hq
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hqa := Nat.dvd_of_mem_primeFactors hq
    rw [← Nat.div_div_eq_div_mul, ← ha]
    have haq : a = q * (a / q) := (Nat.mul_div_cancel' hqa).symm
    have haq0 : a / q ≠ 0 := by intro h; rw [h, mul_zero] at haq; exact ha0 haq
    have hqn : ¬ q ∣ a / q := by
      intro hd
      have : q * q ∣ a := by rw [haq]; exact Nat.mul_dvd_mul_left q hd
      exact hqp.one_lt.ne' (Nat.isUnit_iff.mp (hasq _ this))
    have hpf : a.primeFactors = insert q (a / q).primeFactors := by
      conv_lhs => rw [haq]
      rw [Nat.primeFactors_mul hqp.ne_zero haq0, Nat.Prime.primeFactors hqp]; rfl
    rw [hpf, Finset.erase_insert]
    intro hmem; exact hqn (Nat.dvd_of_mem_primeFactors hmem)
  -- S facts
  have hS1 : ∀ t : ℝ, t ≤ p → Ssv a t = if ∀ r ∈ PC, t ≤ (r : ℝ) then 1 else 0 := by
    intro t ht
    unfold Ssv
    congr 1
    apply propext
    constructor
    · intro h r hr; exact h r (Finset.mem_filter.1 hr).1
    · intro h r hr
      by_cases hrp : r < p
      · exact h r (Finset.mem_filter.2 ⟨hr, hrp⟩)
      · have : (p : ℝ) ≤ r := by exact_mod_cast not_lt.1 hrp
        linarith
  have hS2 : ∀ q ∈ PC, Ssv (A / (p * q)) p = if PC = {q} then 1 else 0 := by
    intro q hq
    have hqa := (Finset.mem_filter.1 hq).1
    unfold Ssv
    rw [herase q hqa]
    congr 1
    apply propext
    constructor
    · intro h
      apply Finset.eq_singleton_iff_unique_mem.2 ⟨hq, _⟩
      intro r hr
      by_contra hne
      have := h r (Finset.mem_erase.2 ⟨hne, (Finset.mem_filter.1 hr).1⟩)
      have h2 : r < p := (Finset.mem_filter.1 hr).2
      have : (r : ℝ) < p := by exact_mod_cast h2
      linarith
    · intro h r hr
      obtain ⟨hrq, hra⟩ := Finset.mem_erase.1 hr
      by_cases hrp : r < p
      · have : r ∈ PC := Finset.mem_filter.2 ⟨hra, hrp⟩
        rw [h, Finset.mem_singleton] at this; exact absurd this hrq
      · exact_mod_cast not_lt.1 hrp
  have hS3 : ∀ q ∈ PC, Ssv (A / (p * q)) q = if ∀ r ∈ PC, q ≤ r then 1 else 0 := by
    intro q hq
    have hqa := (Finset.mem_filter.1 hq).1
    have hqp' := (Finset.mem_filter.1 hq).2
    unfold Ssv
    rw [herase q hqa]
    congr 1
    apply propext
    constructor
    · intro h r hr
      by_cases hrq : r = q
      · rw [hrq]
      · exact_mod_cast h r (Finset.mem_erase.2 ⟨hrq, (Finset.mem_filter.1 hr).1⟩)
    · intro h r hr
      obtain ⟨hrq, hra⟩ := Finset.mem_erase.1 hr
      by_cases hrp : r < p
      · exact_mod_cast h r (Finset.mem_filter.2 ⟨hra, hrp⟩)
      · have : q ≤ r := by omega
        exact_mod_cast this
  have hsqrt_iff : ∀ q : ℕ, ((q : ℝ) < Real.sqrt (y / p) ↔ (q : ℝ) ^ 2 * p < y) := by
    intro q
    rw [Real.lt_sqrt (by positivity), lt_div_iff₀ hpR]
  -- the set R_p of Λ₂
  have hR : (primesBelow (p : ℝ)).filter (fun q : ℕ => q ∣ A ∧ y ≤ (q : ℝ) ^ 2 * p) =
      PC.filter (fun q : ℕ => Real.sqrt (y / p) ≤ (q : ℝ)) := by
    ext q
    rw [Finset.mem_filter, Finset.mem_filter, hPC, Finset.mem_filter, mem_primesBelow]
    constructor
    · rintro ⟨⟨hqp, hqlt⟩, hqA, hyq⟩
      have hqlt' : q < p := by exact_mod_cast hqlt
      have hcop : Nat.Coprime q p := (Nat.coprime_primes hqp hpp).2 (by omega)
      have hqa : q ∣ a := hcop.dvd_of_dvd_mul_left (hAa ▸ hqA)
      refine ⟨⟨Nat.mem_primeFactors.2 ⟨hqp, hqa, ha0⟩, hqlt'⟩, ?_⟩
      exact not_lt.1 (fun h => absurd ((hsqrt_iff q).1 h) (not_lt.2 hyq))
    · rintro ⟨⟨hqa, hqlt⟩, hsq⟩
      refine ⟨⟨Nat.prime_of_mem_primeFactors hqa, by exact_mod_cast hqlt⟩,
        (Nat.dvd_of_mem_primeFactors hqa).trans (Nat.div_dvd_of_dvd hpA), ?_⟩
      exact not_lt.1 (fun h => absurd ((hsqrt_iff q).2 h) (not_lt.2 hsq))
  have hQS : (A / p).primeFactors.filter (fun q : ℕ => q < p ∧ (q : ℝ) ^ 2 * p < y) =
      PC.filter (fun q : ℕ => ¬ Real.sqrt (y / p) ≤ (q : ℝ)) := by
    ext q
    rw [Finset.mem_filter, Finset.mem_filter, hPC, Finset.mem_filter, ← ha, not_le, hsqrt_iff]
    tauto
  rw [hR, hQS, hI]
  -- case split on χ̄(p)
  rw [S02_chibar_prime y m hm0 hm p hpp]
  by_cases hy3 : y ≤ (p : ℝ) ^ 3
  · rw [if_pos hy3]
    have hsle : Real.sqrt (y / p) ≤ p := by
      have : y / p ≤ (p : ℝ) ^ 2 := by rw [div_le_iff₀ hpR]; nlinarith
      calc Real.sqrt (y / p) ≤ Real.sqrt ((p : ℝ) ^ 2) := Real.sqrt_le_sqrt this
        _ = p := Real.sqrt_sq hpR.le
    have hS1' : Ssv (A / p) (Real.sqrt (y / p)) = _ := hS1 _ hsle
    first | rw [hS1'] | rw [hS1 _ hsle]
    set s := Real.sqrt (y / p) with hs
    -- rewrite the S-terms on the sets
    have e1 : ∑ q ∈ PC.filter (fun q : ℕ => s ≤ (q : ℝ)),
        ((W1' - w p) * Ssv (A / (p * q)) q - w q * Ssv (A / (p * q)) p) =
        (W1' - w p) * ∑ q ∈ PC.filter (fun q : ℕ => s ≤ (q : ℝ)), (if ∀ r ∈ PC, q ≤ r then (1 : ℝ) else 0) -
          ∑ q ∈ PC.filter (fun q : ℕ => s ≤ (q : ℝ)), w q * (if PC = {q} then 1 else 0) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro q hq
      have hqPC := (Finset.mem_filter.1 hq).1
      rw [hS3 q hqPC, hS2 q hqPC]
    have e2 : ∑ q ∈ PC.filter (fun q : ℕ => ¬ s ≤ (q : ℝ)), w q * Ssv (A / (p * q)) p =
        ∑ q ∈ PC.filter (fun q : ℕ => ¬ s ≤ (q : ℝ)), w q * (if PC = {q} then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [hS2 q (Finset.mem_filter.1 hq).1]
    rw [e1, e2, S02F_count, S02F_val_sum, hphi]
    rw [← Finset.sum_filter_add_sum_filter_not PC (fun q : ℕ => s ≤ (q : ℝ))]
    ring
  · rw [if_neg hy3]
    have hempty : PC.filter (fun q : ℕ => Real.sqrt (y / p) ≤ (q : ℝ)) = ∅ := by
      apply Finset.filter_false_of_mem
      intro q hq hsq
      have hqlt : (q : ℝ) < p := by exact_mod_cast (Finset.mem_filter.1 hq).2
      have h1 : y / p ≤ (q : ℝ) ^ 2 := by
        rw [← Real.sq_sqrt (by positivity : (0 : ℝ) ≤ y / p)]
        exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq 2
      rw [div_le_iff₀ hpR] at h1
      have : (q : ℝ) ^ 2 * p < (p : ℝ) ^ 3 := by
        have h0 : (0 : ℝ) ≤ q := by positivity
        have hq2 : (q : ℝ) ^ 2 < (p : ℝ) ^ 2 := by nlinarith
        have := mul_lt_mul_of_pos_right hq2 hpR
        calc (q : ℝ) ^ 2 * p < (p : ℝ) ^ 2 * p := this
          _ = (p : ℝ) ^ 3 := by ring
      exact hy3 (by linarith)
    rw [hempty]; simp

theorem S02_fixed : ItemS02fix := by
  classical
  intro y z m W1' w A hm0 hm hy _ hA hz
  have hrad := S02_rad_self A z hA hz
  have hA0 : A ≠ 0 := hA.ne_zero
  unfold SigmaG Sig1 Sig2 Sig3 Sig4
  rw [hrad, S02F_sig1 y m W1' w A hA, S02F_split y m W1' w A hA]
  unfold Lam2
  have hpb : (primesBelow z).filter (· ∣ A) = A.primeFactors := by
    ext p
    rw [Finset.mem_filter, mem_primesBelow, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hp, -⟩, hpA⟩; exact ⟨hp, hpA, hA0⟩
    · rintro ⟨hp, hpA, -⟩
      exact ⟨⟨hp, hz p (Nat.mem_primeFactors.2 ⟨hp, hpA, hA0⟩)⟩, hpA⟩
  rw [hpb]
  have hper := fun p (hp : p ∈ A.primeFactors) => S02F_perp y m W1' w A p hm0 hm hy hA hp
  have key := Finset.sum_congr rfl (fun p hp => hper p hp)
  rw [Finset.sum_neg_distrib, Finset.sum_add_distrib] at key
  have hP : ∑ p ∈ A.primeFactors, -(chibar y m p * innerS W1' w A p) =
      -∑ p ∈ A.primeFactors, chibar y m p * innerS W1' w A p := by rw [Finset.sum_neg_distrib]
  rw [hP]
  linarith

end KappaOmega2
