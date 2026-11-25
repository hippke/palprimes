import Omega3.Items.M10_Regroup
import Omega3.Items.M10_P2

/-!
# M10 helper: the Lemma 9 errors (`M10_PLAN.md` §4.4, §4.5)

`−H_p = γ(p)/p Σ_{d₁} A(d₁) T^{ε(d₁)}(y/(pd₁), p)` (P2), `|T − R| ≤ ε V(p)` by the uniform Lemma 9 (`Lemma9UStmt`),
`Σ_{d₁} |A(d₁)| ≤ V(p)/V(y^U)`, and `Σ_{y^m < p} γ(p)/p V(p) ≤ V(y^m) ≤ 86 V(y)` (telescoping, Mertens).
-/

set_option linter.style.longLine false

open Finset Real
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

namespace Omega3

open Palprimes Palprimes.Greaves

/-- Lemma 9, uniform in `s = log η / log ζ ≤ S` (HR's Reduction Lemma is uniform for bounded `s`; for `+` and
`η ≤ ζ³` it is an exact identity). -/
def Lemma9UStmt (b : ℕ) : Prop :=
  ∀ S ε : ℝ, 0 < ε → ∃ ζ₀ : ℝ, ∀ ζ ≥ ζ₀, ∀ η : ℝ, 0 < η → ∀ plus : Bool, (plus = false → ζ ^ 2 < η) →
    η ≤ ζ ^ S → |Tpm b plus η ζ - Rpm b η ζ plus| ≤ ε * MT.VB b ζ

/-- The weight `A(d₁) = μ(d₁)γ(d₁)/d₁ χ*_y(d₁) χ⁻_y(d₁p)`. -/
noncomputable def Ad (b : ℕ) (y : ℝ) (p d : ℕ) : ℝ :=
  open Classical in
  (μ d : ℝ) * rhoB b d / d * (if chiStarProp y mm d then 1 else 0) * (if chiMinusProp y (d * p) then 1 else 0)

namespace M10

open Classical

theorem fm_prod (b : ℕ) {E : Finset ℕ} (hE : ∀ q ∈ E, q.Prime) :
    fm b (∏ q ∈ E, q) = ∏ q ∈ E, (-(rhoB b q / q)) := by
  induction E using Finset.induction_on with
  | empty => simp [fm, rhoB]
  | insert a E ha ih =>
    have hE' : ∀ q ∈ E, q.Prime := fun q hq => hE q (mem_insert_of_mem hq)
    rw [fm_insert b (hE a (mem_insert_self a E)) hE' ha, ih hE', prod_insert ha]

end M10

/-- P2 (Greaves p. 92/94): `−H_p = γ(p)/p Σ_{d₁} A(d₁) T^{ε(d₁)}(y/(pd₁), p)`. -/
theorem negHp_factor (b : ℕ) {y : ℝ} (hy : 1 ≤ y) {p : ℕ} (hp : p.Prime) (hpz : (p : ℝ) < y ^ UU) :
    -Hp b y p = rhoB b p / p * ∑ d ∈ D1set y p, Ad b y p d * Tpm b (decide (Even (ω d))) (y / (p * d)) p := by
  classical
  set z := y ^ UU with hz
  set S' := (primesBelow z).filter (fun q : ℕ => p < q) with hS'
  have hpPB : p ∈ primesBelow z := (mem_primesBelow z p).2 ⟨hp, hpz⟩
  set T : Finset ℕ → ℝ := fun E => M10.fm b (∏ q ∈ E, q) * (if chiMinusProp y (∏ q ∈ E, q) then 1 else 0) *
    (if chiStarProp y mm (d1of (∏ q ∈ E, q) p) then 1 else 0) with hT
  -- LHS in set form
  have hL : Hp b y p = ∑ E ∈ (primesBelow z).powerset.filter (fun E => p ∈ E), T E := by
    unfold Hp
    rw [sum_filter, sum_filter]
    unfold primorialLt
    rw [sum_divisors_primes (primesBelow z) (M10.primes_PB z)]
    apply sum_congr rfl; intro E hE
    have hEp : ∀ q ∈ E, q.Prime := fun q hq => M10.primes_PB z q (mem_powerset.1 hE hq)
    have hiff : p ∣ ∏ q ∈ E, q ↔ p ∈ E := by
      constructor
      · intro h
        obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 h
        rwa [(Nat.prime_dvd_prime_iff_eq hp (hEp q hq)).1 hpq]
      · intro h; exact Finset.dvd_prod_of_mem (fun q => q) h
    by_cases h : p ∈ E
    · rw [if_pos (hiff.2 h), if_pos h, hT]; simp only [M10.fm]
    · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]
  -- RHS in set form
  have hR : ∑ d ∈ D1set y p, Ad b y p d * Tpm b (decide (Even (ω d))) (y / (p * d)) p =
      ∑ D₁ ∈ S'.powerset, Ad b y p (∏ q ∈ D₁, q) *
        Tpm b (decide (Even D₁.card)) (y / (p * ((∏ q ∈ D₁, q : ℕ) : ℝ))) p := by
    unfold D1set
    rw [sum_filter]
    unfold primorialLt
    rw [sum_divisors_primes (primesBelow z) (M10.primes_PB z)]
    rw [M10.sum_powerset_of_support (filter_subset (fun q : ℕ => p < q) (primesBelow z))]
    rotate_left
    · intro E hE hne q hq
      rw [mem_filter]
      refine ⟨hE hq, ?_⟩
      by_contra hlt
      apply hne
      have hEp : ∀ q ∈ E, q.Prime := fun q hq => M10.primes_PB z q (hE hq)
      rw [if_neg]
      rw [Nat.primeFactors_prod hEp]
      exact fun h => hlt (h q hq)
    · apply sum_congr rfl; intro E hE
      have hES : E ⊆ S' := mem_powerset.1 hE
      have hEp : ∀ q ∈ E, q.Prime := fun q hq => M10.primes_PB z q (mem_filter.1 (hES hq)).1
      have hgt : ∀ q ∈ (∏ q ∈ E, q).primeFactors, p < q := by
        rw [Nat.primeFactors_prod hEp]; exact fun q hq => (mem_filter.1 (hES hq)).2
      rw [if_pos hgt, M10.omega_prod hEp]
  rw [hL, hR, ← sum_neg_distrib, mul_sum]
  simp_rw [M10.Tpm_set, mul_sum]
  rw [← sum_product']
  symm
  apply Finset.sum_nbij' (fun x : Finset ℕ × Finset ℕ => x.1 ∪ insert p x.2)
    (fun E => (E.filter (fun q : ℕ => p < q), E.filter (fun q : ℕ => q < p)))
  · intro x hx
    rw [mem_product, mem_powerset, mem_powerset] at hx
    rw [mem_filter, mem_powerset]
    refine ⟨?_, mem_union_right _ (mem_insert_self _ _)⟩
    intro q hq
    rcases mem_union.1 hq with h | h
    · exact (mem_filter.1 (hx.1 h)).1
    · rcases mem_insert.1 h with rfl | h
      · exact hpPB
      · exact M10.primesBelow_mono hpz.le (hx.2 h)
  · intro E hE
    rw [mem_filter, mem_powerset] at hE
    rw [mem_product, mem_powerset, mem_powerset]
    constructor
    · intro q hq; rw [mem_filter] at hq ⊢; exact ⟨hE.1 hq.1, hq.2⟩
    · intro q hq; rw [mem_filter] at hq
      rw [mem_primesBelow]
      exact ⟨M10.primes_PB z q (hE.1 hq.1), by exact_mod_cast hq.2⟩
  · intro x hx
    rw [mem_product, mem_powerset, mem_powerset] at hx
    have h₁ : ∀ q ∈ x.1, p < q := fun q hq => (mem_filter.1 (hx.1 hq)).2
    have h₂ : ∀ q ∈ x.2, q < p := fun q hq => by
      have := ((mem_primesBelow _ q).1 (hx.2 hq)).2; exact_mod_cast this
    ext1
    · ext q; simp only [mem_filter, mem_union, mem_insert]
      constructor
      · rintro ⟨h | rfl | h, hlt⟩
        · exact h
        · exact absurd hlt (lt_irrefl _)
        · exact absurd hlt (lt_asymm (h₂ q h))
      · intro h; exact ⟨Or.inl h, h₁ q h⟩
    · ext q; simp only [mem_filter, mem_union, mem_insert]
      constructor
      · rintro ⟨h | rfl | h, hlt⟩
        · exact absurd hlt (lt_asymm (h₁ q h))
        · exact absurd hlt (lt_irrefl _)
        · exact h
      · intro h; exact ⟨Or.inr (Or.inr h), h₂ q h⟩
  · intro E hE
    rw [mem_filter] at hE
    ext q; simp only [mem_filter, mem_union, mem_insert]
    constructor
    · rintro (⟨h, _⟩ | rfl | ⟨h, _⟩)
      · exact h
      · exact hE.2
      · exact h
    · intro h
      rcases lt_trichotomy p q with hlt | heq | hgt
      · exact Or.inl ⟨h, hlt⟩
      · exact Or.inr (Or.inl heq.symm)
      · exact Or.inr (Or.inr ⟨h, hgt⟩)
  · intro x hx
    rw [mem_product, mem_powerset, mem_powerset] at hx
    obtain ⟨D₁, D₂⟩ := x
    simp only at hx ⊢
    have hD₁p : ∀ q ∈ D₁, q.Prime := fun q hq => M10.primes_PB z q (mem_filter.1 (hx.1 hq)).1
    have hD₂p : ∀ q ∈ D₂, q.Prime := fun q hq => M10.primes_PB _ q (hx.2 hq)
    have h₁ : ∀ q ∈ D₁, p < q := fun q hq => (mem_filter.1 (hx.1 hq)).2
    have h₂ : ∀ q ∈ D₂, q < p := fun q hq => by
      have := ((mem_primesBelow _ q).1 (hx.2 hq)).2; exact_mod_cast this
    have hpD₁ : p ∉ D₁ := fun h => lt_irrefl p (h₁ p h)
    have hpD₂ : p ∉ D₂ := fun h => lt_irrefl p (h₂ p h)
    have hdisj : Disjoint D₁ (insert p D₂) := by
      rw [disjoint_left]; intro q hq hq'
      rcases mem_insert.1 hq' with rfl | hq'
      · exact hpD₁ hq
      · exact lt_asymm (h₁ q hq) (h₂ q hq')
    have hall : ∀ q ∈ D₁ ∪ insert p D₂, q.Prime := by
      intro q hq; rcases mem_union.1 hq with hq | hq
      · exact hD₁p q hq
      · rcases mem_insert.1 hq with rfl | hq
        · exact hp
        · exact hD₂p q hq
    have hfm : M10.fm b (∏ q ∈ D₁ ∪ insert p D₂, q) =
        M10.fm b (∏ q ∈ D₁, q) * (-(rhoB b p / p)) * M10.fm b (∏ q ∈ D₂, q) := by
      rw [M10.fm_prod b hall, M10.fm_prod b hD₁p, M10.fm_prod b hD₂p, prod_union hdisj, prod_insert hpD₂]; ring
    have hd1 : d1of (∏ q ∈ D₁ ∪ insert p D₂, q) p = ∏ q ∈ D₁, q := by
      unfold d1of
      rw [Nat.primeFactors_prod hall]
      congr 1
      ext q; simp only [mem_filter, mem_union, mem_insert]
      constructor
      · rintro ⟨h | rfl | h, hlt⟩
        · exact h
        · exact absurd hlt (lt_irrefl _)
        · exact absurd hlt (lt_asymm (h₂ q h))
      · intro h; exact ⟨Or.inl h, h₁ q h⟩
    have hP2 := M10.P2 (Y := y) hp hD₁p hD₂p h₁ h₂
    have hcm := M10.chiMinus_iff y hall
    have hA : ∀ hq : True, chiMinusProp y ((∏ q ∈ D₁, q) * p) ↔ M10.ChiS false y (insert p D₁) := by
      intro _
      have hallA : ∀ q ∈ insert p D₁, q.Prime := by
        intro q hq; rcases mem_insert.1 hq with rfl | hq
        · exact hp
        · exact hD₁p q hq
      rw [← M10.chiMinus_iff y hallA, prod_insert hpD₁, mul_comm]
    have hA' := hA trivial
    rw [hT]
    dsimp only
    rw [hfm, hd1]
    unfold Ad
    have hfm1 : (μ (∏ q ∈ D₁, q) : ℝ) * rhoB b (∏ q ∈ D₁, q) / ((∏ q ∈ D₁, q : ℕ) : ℝ) = M10.fm b (∏ q ∈ D₁, q) := rfl
    rw [hfm1]
    by_cases c1 : chiStarProp y mm (∏ q ∈ D₁, q)
    · by_cases c2 : M10.ChiS false y (insert p D₁)
      · by_cases c3 : M10.ChiS (decide (Even D₁.card)) (y / (p * ((∏ q ∈ D₁, q : ℕ) : ℝ))) D₂
        · rw [if_pos c1, if_pos (hA'.2 c2), if_pos c3, if_pos (hcm.2 (hP2.2 ⟨c2, c3⟩))]; ring
        · rw [if_pos c1, if_pos (hA'.2 c2), if_neg c3, if_neg (fun h => c3 (hP2.1 (hcm.1 h)).2)]; ring
      · rw [if_pos c1, if_neg (fun h => c2 (hA'.1 h)), if_neg (fun h => c2 (hP2.1 (hcm.1 h)).1)]; ring
    · rw [if_neg c1]; ring

namespace M10

open Classical

theorem abs_Ad_le (b : ℕ) (y : ℝ) (p d : ℕ) : |Ad b y p d| ≤ rhoB b d / (d : ℝ) := by
  unfold Ad
  rw [abs_mul, abs_mul, mul_div_assoc, abs_mul]
  have h1 : |(μ d : ℝ)| ≤ 1 := by rw [← Int.cast_abs]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have h2 : |(if chiStarProp y mm d then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
  have h3 : |(if chiMinusProp y (d * p) then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
  have hG := G_nonneg b d
  rw [abs_of_nonneg hG]
  calc |(μ d : ℝ)| * (rhoB b d / d) * |(if chiStarProp y mm d then (1 : ℝ) else 0)| *
      |(if chiMinusProp y (d * p) then (1 : ℝ) else 0)| ≤ 1 * (rhoB b d / d) * 1 * 1 := by gcongr
    _ = rhoB b d / d := by ring

/-- `Σ_{d₁} |A(d₁)| ≤ V(p)/V(y^U)`. -/
theorem sum_abs_Ad_le (b : ℕ) {y : ℝ} {p : ℕ} (hp : p.Prime) (hpz : (p : ℝ) < y ^ UU) :
    ∑ d ∈ D1set y p, |Ad b y p d| ≤ MT.VB b p / MT.VB b (y ^ UU) := by
  set z := y ^ UU with hz
  set S' := (primesBelow z).filter (fun q : ℕ => p < q) with hS'
  set S'' := (primesBelow z).filter (fun q : ℕ => ¬ p < q) with hS''
  have hsum : ∑ d ∈ D1set y p, rhoB b d / (d : ℝ) = ∏ q ∈ S', (1 + rhoB b q / q) := by
    unfold D1set
    rw [sum_filter]
    unfold primorialLt
    rw [sum_divisors_primes (primesBelow z) (primes_PB z), prod_one_add]
    have e : ∀ D ∈ (primesBelow z).powerset, (if ∀ q ∈ (∏ p ∈ D, p).primeFactors, p < q then
        rhoB b (∏ p ∈ D, p) / ((∏ p ∈ D, p : ℕ) : ℝ) else 0) =
        (if ∀ q ∈ D, p < q then ∏ q ∈ D, rhoB b q / q else 0) := by
      intro D hD
      have hDp : ∀ q ∈ D, q.Prime := fun q hq => primes_PB z q (mem_powerset.1 hD hq)
      rw [Nat.primeFactors_prod hDp, G_prod b hDp]
    rw [sum_congr rfl e]
    rw [sum_powerset_of_support (filter_subset _ _) _ (fun E _ hE => by
      intro q hq
      by_contra hqn
      apply hE
      rw [if_neg]
      intro h
      exact hqn (mem_filter.2 ⟨‹E ⊆ primesBelow z› hq, h q hq⟩))]
    apply sum_congr rfl; intro D hD
    rw [if_pos (fun q hq => (mem_filter.1 (mem_powerset.1 hD hq)).2)]
  have hgB : ∀ q ∈ primesBelow z, rhoB b q / (q : ℝ) = MT.gB b q := fun q hq => rhoB_div_eq_gB b (primes_PB z q hq)
  have hP1 : (∏ q ∈ S', (1 + rhoB b q / q)) * (∏ q ∈ S', (1 - MT.gB b q)) ≤ 1 := by
    rw [← prod_mul_distrib]
    apply prod_le_one₀
    · intro q hq
      rw [hgB q (mem_filter.1 hq).1]
      have := MT.gB_nonneg b q; have := E1.gB_le_half' b q; nlinarith
    · intro q hq
      rw [hgB q (mem_filter.1 hq).1]
      have := MT.gB_nonneg b q; nlinarith
  have hsplit : MT.VB b z = (∏ q ∈ S', (1 - MT.gB b q)) * ∏ q ∈ S'', (1 - MT.gB b q) := by
    unfold MT.VB; rw [hS', hS'', prod_filter_mul_prod_filter_not]
  have hS''le : ∏ q ∈ S'', (1 - MT.gB b q) ≤ MT.VB b p := by
    unfold MT.VB
    apply prod_le_prod_of_subset_of_le_one₀
    · intro q hq
      rw [mem_primesBelow] at hq
      rw [hS'', mem_filter, mem_primesBelow]
      refine ⟨⟨hq.1, lt_trans hq.2 hpz⟩, ?_⟩
      have : q < p := by exact_mod_cast hq.2
      omega
    · intro q _; have := E1.gB_le_half' b q; linarith
    · intro q _ _; have := MT.gB_nonneg b q; linarith
  have hpos' : 0 < ∏ q ∈ S', (1 - MT.gB b q) := prod_pos fun q _ => by have := E1.gB_le_half' b q; linarith
  have hVz : 0 < MT.VB b z := E1.VB_pos' b z
  have hpos'' : 0 < ∏ q ∈ S'', (1 - MT.gB b q) := prod_pos fun q _ => by have := E1.gB_le_half' b q; linarith
  calc ∑ d ∈ D1set y p, |Ad b y p d| ≤ ∑ d ∈ D1set y p, rhoB b d / (d : ℝ) := sum_le_sum fun d _ => abs_Ad_le b y p d
    _ = ∏ q ∈ S', (1 + rhoB b q / q) := hsum
    _ ≤ 1 / ∏ q ∈ S', (1 - MT.gB b q) := by rw [le_div_iff₀ hpos']; exact hP1
    _ = (∏ q ∈ S'', (1 - MT.gB b q)) / MT.VB b z := by
        rw [hsplit, div_mul_eq_div_div_swap, div_self hpos''.ne']
    _ ≤ MT.VB b p / MT.VB b z := div_le_div_of_nonneg_right hS''le hVz.le

end M10

theorem Sp_eq (b : ℕ) (y : ℝ) (p : ℕ) :
    Sp b y p = rhoB b p / p * ∑ d ∈ D1set y p, Ad b y p d * Rpm b (y / (p * d)) p (decide (Even (ω d))) := rfl

/-- §4.5: the Lemma 9 errors, from the uniform Lemma 9. -/
theorem L_bound_of (b : ℕ) (hb : 2 ≤ b) (h9U : Lemma9UStmt b) (ε : ℝ) (hε : 0 < ε) :
    ∃ y₀ : ℝ, ∀ y ≥ y₀, ∑ p ∈ (primesBelow (y ^ ((1 : ℝ) / 4))).filter (fun p : ℕ => y ^ mm < (p : ℝ)),
      wy y p * |-Hp b y p - Sp b y p| ≤ ε * MT.VB b y := by
  classical
  set ε' := ε / 7396 with hε'
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨ζ₀, hζ⟩ := h9U 85 ε' hε'0
  have hm0 : (0 : ℝ) < mm := by norm_num [mm]
  obtain ⟨y₁, hy₁, hrat⟩ := E1.VB_ratio_mul b hb mm hm0 (by norm_num [mm]) 1 one_pos
  set ζ₁ := max ζ₀ 1 with hζ₁
  refine ⟨max (max 16 y₁) (ζ₁ ^ (85 : ℝ)), fun y hy => ?_⟩
  have hy16 : (16 : ℝ) ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have hyy₁ : y₁ ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
  have hyζ : ζ₁ ^ (85 : ℝ) ≤ y := le_trans (le_max_right _ _) hy
  have hy1 : (1 : ℝ) < y := by linarith
  have hy0 : (0 : ℝ) < y := by linarith
  have hζ1 : (1 : ℝ) ≤ ζ₁ := le_max_right _ _
  -- y^m ≥ ζ₁
  have hym : ζ₁ ≤ y ^ mm := by
    have := Real.rpow_le_rpow (by positivity) hyζ (by norm_num [mm] : (0 : ℝ) ≤ mm)
    rwa [← Real.rpow_mul (by linarith), show (85 : ℝ) * mm = 1 by norm_num [mm], Real.rpow_one] at this
  -- V(y^m) ≤ 86 V(y)
  have hVy := E1.VB_pos' b y
  have hlogym : Real.log (y ^ mm) = mm * Real.log y := Real.log_rpow hy0 mm
  have hVm : MT.VB b (y ^ mm) ≤ 86 * MT.VB b y := by
    have h := hrat y hyy₁ (y ^ mm) le_rfl (Real.rpow_le_self_of_one_le hy1.le (by norm_num [mm]))
    have hl : Real.log y / Real.log (y ^ mm) = 85 := by
      rw [hlogym]; field_simp [(Real.log_pos hy1).ne']; norm_num [mm]
    rw [hl] at h
    have := (abs_le.1 h).2
    linarith
  set z := y ^ UU with hz
  have hzy : z ≤ y := Real.rpow_le_self_of_one_le hy1.le (by norm_num [UU])
  have hVz : MT.VB b y ≤ MT.VB b z := E1.VB_anti b hzy
  have hVz0 : 0 < MT.VB b z := E1.VB_pos' b z
  set F := (primesBelow (y ^ ((1 : ℝ) / 4))).filter (fun p : ℕ => y ^ mm < (p : ℝ)) with hF
  -- per-p bound
  have hper : ∀ p ∈ F, |-Hp b y p - Sp b y p| ≤ ε' * (MT.VB b (y ^ mm) / MT.VB b z) * (MT.gB b p * MT.VB b p) := by
    intro p hpF
    rw [hF, mem_filter, mem_primesBelow] at hpF
    obtain ⟨⟨hp, hp4⟩, hpm⟩ := hpF
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hpz : (p : ℝ) < z := lt_of_lt_of_le hp4 (Real.rpow_le_rpow_of_exponent_le hy1.le (by norm_num [UU]))
    have hpζ : ζ₀ ≤ p := le_trans (le_max_left _ _) (le_trans hym hpm.le)
    have hp85 : y < (p : ℝ) ^ (85 : ℝ) := by
      have := Real.rpow_lt_rpow (by positivity) hpm (by norm_num : (0 : ℝ) < 85)
      rwa [← Real.rpow_mul hy0.le, show mm * 85 = 1 by norm_num [mm], Real.rpow_one] at this
    rw [negHp_factor b hy1.le hp hpz, Sp_eq, ← mul_sub, ← sum_sub_distrib, abs_mul,
      abs_of_nonneg (M10.G_nonneg b p), M10.rhoB_div_eq_gB b hp]
    have hgp := MT.gB_nonneg b p
    have hterm : ∀ d ∈ D1set y p, |Ad b y p d * Tpm b (decide (Even (ω d))) (y / (p * d)) p -
        Ad b y p d * Rpm b (y / (p * d)) p (decide (Even (ω d)))| ≤ |Ad b y p d| * (ε' * MT.VB b p) := by
      intro d hd
      rw [← mul_sub, abs_mul]
      by_cases hA : Ad b y p d = 0
      · rw [hA]; simp
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have hd0 : 0 < d := Nat.pos_of_mem_divisors (mem_filter.1 hd).1
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
      have hη0 : 0 < y / (p * d) := by positivity
      have hχ : chiMinusProp y (d * p) := by
        by_contra h; apply hA; unfold Ad; rw [if_neg h, mul_zero]
      apply hζ p hpζ _ hη0
      · intro hpl
        -- ν(d) odd: χ⁻_y(d p) with h = d p
        have hodd : ¬ Even (ω d) := by
          intro he; simp [he] at hpl
        have hdlt : ∀ q ∈ d.primeFactors, p < q := (mem_filter.1 hd).2
        have hpd : Nat.Coprime p d := (Nat.Prime.coprime_iff_not_dvd hp).2 (fun h =>
          lt_irrefl p (hdlt p (Nat.mem_primeFactors.2 ⟨hp, h, hd0.ne'⟩)))
        have hev : Even (ω (d * p)) := by
          rw [mul_comm, ArithmeticFunction.cardDistinctFactors_mul hpd, ArithmeticFunction.cardDistinctFactors_apply_prime hp]
          exact (Nat.not_even_iff_odd.1 hodd).one_add
        have hne : d * p ≠ 1 := fun h => hp.one_lt.ne' (Nat.eq_one_of_dvd_one ⟨d, by rw [mul_comm]; exact h.symm⟩)
        have h1 := hχ (d * p) (Nat.mem_divisors_self _ (Nat.mul_ne_zero hd0.ne' hp.ne_zero)) hne hev
        rw [M10.minFac_mul_prime_below hp hd0.ne' hdlt] at h1
        rw [lt_div_iff₀ (by positivity)]
        push_cast at h1
        nlinarith
      · calc y / (p * d) ≤ y := div_le_self hy0.le (by nlinarith)
          _ ≤ (p : ℝ) ^ (85 : ℝ) := hp85.le
    calc MT.gB b p * |∑ d ∈ D1set y p, (Ad b y p d * Tpm b (decide (Even (ω d))) (y / (p * d)) p -
          Ad b y p d * Rpm b (y / (p * d)) p (decide (Even (ω d))))|
        ≤ MT.gB b p * ∑ d ∈ D1set y p, |Ad b y p d| * (ε' * MT.VB b p) :=
          mul_le_mul_of_nonneg_left (le_trans (abs_sum_le_sum_abs _ _) (sum_le_sum hterm)) hgp
      _ = MT.gB b p * (ε' * MT.VB b p) * ∑ d ∈ D1set y p, |Ad b y p d| := by rw [← sum_mul]; ring
      _ ≤ MT.gB b p * (ε' * MT.VB b p) * (MT.VB b p / MT.VB b z) :=
          mul_le_mul_of_nonneg_left (M10.sum_abs_Ad_le b hp hpz) (by have := E1.VB_pos' b p; positivity)
      _ ≤ MT.gB b p * (ε' * MT.VB b p) * (MT.VB b (y ^ mm) / MT.VB b z) := by
          apply mul_le_mul_of_nonneg_left _ (by have := E1.VB_pos' b p; positivity)
          exact div_le_div_of_nonneg_right (E1.VB_anti b hpm.le) hVz0.le
      _ = ε' * (MT.VB b (y ^ mm) / MT.VB b z) * (MT.gB b p * MT.VB b p) := by ring
  -- sum over p
  have htel : ∑ p ∈ F, MT.gB b p * MT.VB b p ≤ MT.VB b (y ^ mm) := by
    have hsub : F ⊆ E1.primesIco (y ^ mm) (y ^ ((1 : ℝ) / 4)) := by
      intro p hp
      rw [hF, mem_filter, mem_primesBelow] at hp
      rw [E1.mem_primesIco]
      exact ⟨hp.1.1, hp.2.le, hp.1.2⟩
    have hle : y ^ mm ≤ y ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow_of_exponent_le hy1.le (by norm_num [mm])
    calc ∑ p ∈ F, MT.gB b p * MT.VB b p ≤ ∑ p ∈ E1.primesIco (y ^ mm) (y ^ ((1 : ℝ) / 4)), MT.gB b p * MT.VB b p :=
          sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => mul_nonneg (MT.gB_nonneg b p) (E1.VB_pos' b p).le)
      _ = MT.VB b (y ^ mm) - MT.VB b (y ^ ((1 : ℝ) / 4)) := E1.telescope b hle
      _ ≤ MT.VB b (y ^ mm) := by linarith [E1.VB_pos' b (y ^ ((1 : ℝ) / 4))]
  have hR0 : 0 ≤ ε' * (MT.VB b (y ^ mm) / MT.VB b z) := by
    have := E1.VB_pos' b (y ^ mm); positivity
  calc ∑ p ∈ F, wy y p * |-Hp b y p - Sp b y p|
      ≤ ∑ p ∈ F, ε' * (MT.VB b (y ^ mm) / MT.VB b z) * (MT.gB b p * MT.VB b p) := by
        apply sum_le_sum; intro p hp
        have hw0 := M10.wy_nonneg y p
        have hw1 : wy y p ≤ 1 := M10.Wf_le_one _
        calc wy y p * |-Hp b y p - Sp b y p| ≤ 1 * |-Hp b y p - Sp b y p| :=
              mul_le_mul_of_nonneg_right hw1 (abs_nonneg _)
          _ ≤ _ := by rw [one_mul]; exact hper p hp
    _ = ε' * (MT.VB b (y ^ mm) / MT.VB b z) * ∑ p ∈ F, MT.gB b p * MT.VB b p := by rw [mul_sum]
    _ ≤ ε' * (MT.VB b (y ^ mm) / MT.VB b z) * MT.VB b (y ^ mm) := mul_le_mul_of_nonneg_left htel hR0
    _ ≤ ε' * (86 * MT.VB b y / MT.VB b y) * (86 * MT.VB b y) := by
        have h1 : MT.VB b (y ^ mm) / MT.VB b z ≤ 86 * MT.VB b y / MT.VB b y := by
          calc MT.VB b (y ^ mm) / MT.VB b z ≤ 86 * MT.VB b y / MT.VB b z := div_le_div_of_nonneg_right hVm hVz0.le
            _ ≤ 86 * MT.VB b y / MT.VB b y := div_le_div_of_nonneg_left (by positivity) hVy hVz
        have := E1.VB_pos' b (y ^ mm)
        apply mul_le_mul (mul_le_mul_of_nonneg_left h1 hε'0.le) hVm this.le (by positivity)
    _ = ε * MT.VB b y := by rw [hε']; field_simp; ring

end Omega3
