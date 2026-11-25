import Omega3.Statements

/-!
# S02 as frozen is false for `m > 1` (counterexample `y = 10`, `z = 4`, `m = 2`, `W(1) = 1`, `w = 0`, `A = 6`)

For `m > 1` no divisor `h` with odd `ν(h)` is constrained in `χ_y` (since `ν(h) ≥ 1 > 1/m`), so `χ̄_y(p) = 0` for primes
and `Σ₂ = Σ₃ = 0`, while `Λ₂` does not depend on `m`. At `A = 6 = 3·2`, `y = 10 ≤ 2²·3`: `Σ(A) = Λ − Λ₂ = 0 − 1 = −1`,
but `Σ₁ + Σ₂ + Σ₃ + Σ₄ = −1 + 0 + 0 + 1 = 0`. See `reports/S02_STATEMENT.md`.
-/

namespace Omega3

open Finset Palprimes Palprimes.Greaves
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

set_option linter.style.longLine false

lemma S02N_pf6 : (6 : ℕ).primeFactors = {2, 3} := by
  rw [show (6 : ℕ) = 2 * 3 by rfl, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]; rfl

lemma S02N_mu6 : μ 6 = 1 := by
  rw [show (6 : ℕ) = 2 * 3 by rfl, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num), ArithmeticFunction.moebius_apply_prime (by norm_num)]; rfl

lemma S02N_om6 : ω 6 = 2 := by
  rw [ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors, S02N_pf6]; rfl

lemma S02N_div6 : (6 : ℕ).divisors = {1, 2, 3, 6} := by decide

lemma S02N_rad : radLt 6 4 = 6 := by
  classical
  unfold radLt
  rw [S02N_pf6]
  rw [Finset.filter_true_of_mem (by intro p hp; simp at hp; rcases hp with rfl | rfl <;> norm_num)]
  rfl

lemma S02N_rad2 : radLt 6 2 = 1 := by
  classical
  unfold radLt
  rw [S02N_pf6]
  rw [Finset.filter_false_of_mem (by intro p hp; simp at hp; rcases hp with rfl | rfl <;> norm_num)]
  rfl

lemma S02N_pb4 : primesBelow 4 = {2, 3} := by
  ext p; rw [mem_primesBelow]; constructor
  · rintro ⟨hp, hlt⟩
    have : p < 4 := by exact_mod_cast hlt
    interval_cases p <;> simp_all <;> norm_num at hp
  · intro h; simp at h; rcases h with rfl | rfl <;> norm_num

lemma S02N_pb3 : primesBelow 3 = {2} := by
  ext p; rw [mem_primesBelow]; constructor
  · rintro ⟨hp, hlt⟩
    have : p < 3 := by exact_mod_cast hlt
    interval_cases p <;> simp_all <;> norm_num at hp
  · intro h; simp at h; subst h; norm_num

lemma S02N_pb2 : primesBelow 2 = ∅ := by
  ext p; rw [mem_primesBelow]; simp only [Finset.notMem_empty, iff_false, not_and]
  intro hp hlt
  have : p < 2 := by exact_mod_cast hlt
  exact absurd hp.two_le (by omega)

lemma S02N_chi1 : chi 10 2 1 = 1 := by
  classical
  unfold chi; rw [if_pos]
  intro h hh hne
  simp at hh; exact absurd hh hne

lemma S02N_chip (p : ℕ) (hp : p.Prime) : chi 10 2 p = 1 := by
  classical
  unfold chi; rw [if_pos]
  intro h hh hne hcond
  rw [Nat.Prime.divisors hp] at hh
  simp at hh
  rcases hh with rfl | rfl
  · exact absurd rfl hne
  · rw [ArithmeticFunction.cardDistinctFactors_apply_prime hp] at hcond
    norm_num at hcond

lemma S02N_chi6 : chi 10 2 6 = 0 := by
  classical
  unfold chi; rw [if_neg]
  intro hc
  have := hc 6 (by rw [S02N_div6]; simp) (by norm_num) (Or.inl (by rw [S02N_om6]; decide))
  rw [show (6 : ℕ).minFac = 2 by decide] at this
  norm_num at this

lemma S02N_chibarp (p : ℕ) (hp : p.Prime) : chibar 10 2 p = 0 := by
  unfold chibar
  rw [if_neg hp.ne_one, Nat.Prime.minFac_eq hp, Nat.div_self hp.pos, S02N_chi1, S02N_chip p hp]; ring

lemma S02N_chibar6 : chibar 10 2 6 = 1 := by
  unfold chibar
  rw [if_neg (by norm_num), show (6 : ℕ).minFac = 2 by decide, show (6 : ℕ) / 2 = 3 by rfl,
    S02N_chip 3 (by norm_num), S02N_chi6]; ring

/-- The S02 statement as frozen before 2026-11-24 21:52 (without `m ≤ 1`). -/
def ItemS02old : Prop :=
  ∀ (y z m W1' : ℝ) (w : ℕ → ℝ) (A : ℕ), 0 < m → 1 < y → z ≤ y → Squarefree A →
    (∀ p ∈ A.primeFactors, (p : ℝ) < z) →
    SigmaG y z W1' w A = Sig1 y z m W1' w A + Sig2 y z m W1' w A + Sig3 y z m W1' w A + Sig4 y z m W1' w A

theorem S02_not : ¬ ItemS02old := by
  classical
  intro h
  have hsq : Squarefree (6 : ℕ) := by
    rw [show (6 : ℕ) = 2 * 3 by rfl]
    exact (Nat.squarefree_mul (by norm_num)).2 ⟨(show Nat.Prime 2 by norm_num).prime.squarefree, (show Nat.Prime 3 by norm_num).prime.squarefree⟩
  have H := h 10 4 2 1 (fun _ => 0) 6 (by norm_num) (by norm_num) (by norm_num) hsq
    (by rw [S02N_pf6]; intro p hp; simp at hp; rcases hp with rfl | rfl <;> norm_num)
  have hL : SigmaG 10 4 1 (fun _ => 0) 6 = -1 := by
    unfold SigmaG LamA Lam2
    rw [S02N_rad, if_neg (by norm_num), if_neg (by norm_num), S02N_pb4]
    have hf : ({2, 3} : Finset ℕ).filter (· ∣ 6) = {2, 3} := by decide
    rw [hf, Finset.sum_pair (by norm_num)]
    simp only [Nat.cast_ofNat]
    rw [S02N_pb2, S02N_pb3]
    simp only [Finset.filter_empty, Finset.sum_empty, zero_add]
    have hf2 : ({2} : Finset ℕ).filter (fun p2 : ℕ => p2 ∣ 6 ∧ (10 : ℝ) ≤ (p2 : ℝ) ^ 2 * 3) = {2} := by
      rw [Finset.filter_singleton, if_pos (by norm_num)]
    rw [hf2, Finset.sum_singleton]
    have hS : Ssv (6 / (3 * 2)) ((2 : ℕ) : ℝ) = 1 := by
      unfold Ssv; rw [if_pos]; intro p hp; simp at hp
    rw [hS]; norm_num
  have h1 : Sig1 10 4 2 1 (fun _ => 0) 6 = -1 := by
    unfold Sig1 phiW
    rw [S02N_rad, S02N_div6]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    rw [S02N_chi1, S02N_chip 2 (by norm_num), S02N_chip 3 (by norm_num), S02N_chi6, S02N_mu6,
      ArithmeticFunction.moebius_apply_prime (show Nat.Prime 2 by norm_num),
      ArithmeticFunction.moebius_apply_prime (show Nat.Prime 3 by norm_num)]
    simp
  have h2 : Sig2 10 4 2 1 (fun _ => 0) 6 = 0 := by
    unfold Sig2
    rw [S02N_rad, S02N_pf6, Finset.sum_pair (by norm_num), S02N_chibarp 2 (by norm_num),
      S02N_chibarp 3 (by norm_num)]
    simp
  have h3 : Sig3 10 4 2 1 (fun _ => 0) 6 = 0 := by
    unfold Sig3
    rw [Finset.filter_false_of_mem]
    · simp
    · intro δ _ hδ
      obtain ⟨_, h3, h4⟩ := hδ
      have : (3 : ℝ) ≤ (ω δ : ℝ) := by exact_mod_cast h3
      norm_num at h4; linarith
  have h4 : Sig4 10 4 2 1 (fun _ => 0) 6 = 1 := by
    unfold Sig4
    rw [S02N_rad, S02N_div6]
    have hf : ({1, 2, 3, 6} : Finset ℕ).filter (fun δ : ℕ => Even (ω δ) ∧ 2 ≤ ω δ) = {6} := by
      ext δ
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hδ, he, h2⟩
        rcases hδ with rfl | rfl | rfl | rfl
        · simp at h2
        · rw [ArithmeticFunction.cardDistinctFactors_apply_prime (by norm_num)] at h2; omega
        · rw [ArithmeticFunction.cardDistinctFactors_apply_prime (by norm_num)] at h2; omega
        · rfl
      · rintro rfl
        refine ⟨by simp, ?_, ?_⟩ <;> rw [S02N_om6]; decide
    rw [hf, Finset.sum_singleton, S02N_mu6, S02N_chibar6]
    unfold innerS phiW
    rw [show (6 : ℕ).minFac = 2 by decide]
    rw [show ((2 : ℕ) : ℝ) = 2 by norm_num, S02N_rad2]
    simp
  rw [hL, h1, h2, h3, h4] at H
  norm_num at H

end Omega3
