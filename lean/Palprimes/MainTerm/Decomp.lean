import Palprimes.MainTerm.Chains
import Palprimes.MainTerm.VB
import Palprimes.Omega4.Skeleton

/-! # The main term `MT` in Greaves' form (4.2)

`MT P b y = Gw gB w false y L w(1)` and, by `Gw_eq`, `MT = w(1) S^-(y) − Σ_{p<y} w(p) C(p)` with the
chain form of `C(p)`. -/

set_option linter.style.longLine false

open Finset Real

namespace Palprimes.MT

open Palprimes.Greaves

theorem prod_gB (b : ℕ) (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime) :
    ∏ q ∈ T, gB b q = if Nat.Coprime (∏ q ∈ T, q) (Palprimes.bigB b) then 1 / ((∏ q ∈ T, q : ℕ) : ℝ) else 0 := by
  classical
  have h1 : ∀ q ∈ T, gB b q = if Nat.Coprime q (Palprimes.bigB b) then 1 / (q : ℝ) else 0 := by
    intro q hq; unfold gB
    by_cases hc : Nat.Coprime q (Palprimes.bigB b)
    · rw [if_pos ⟨hT q hq, hc⟩, if_pos hc]
    · rw [if_neg (fun h => hc h.2), if_neg hc]
  rw [Finset.prod_congr rfl h1, Finset.prod_ite_zero]
  by_cases hc : ∀ i ∈ T, Nat.Coprime i (Palprimes.bigB b)
  · rw [if_pos hc, if_pos (Nat.coprime_prod_left_iff.2 hc)]
    push_cast; rw [Finset.prod_div_distrib, Finset.prod_const_one]
  · rw [if_neg hc, if_neg (fun h => hc (Nat.coprime_prod_left_iff.1 h))]

/-- **`MT` in `Gw` form.** -/
theorem MT_eq_Gw (P : WPar) (b : ℕ) (y : ℝ) :
    MT P b y = Gw (gB b) (P.wn y) false y (toDec (primesBelow y)) (P.wn y 1) := by
  classical
  rw [Gw_eq_sum, MT]
  apply Finset.sum_congr rfl
  intro T hT
  have hTp : ∀ q ∈ T, q.Prime := fun q hq => ((mem_primesBelow y q).1 (Finset.mem_powerset.1 hT hq)).1
  rw [← prod_gB b T hTp]
  unfold term gwTerm
  split_ifs <;> ring

theorem primesBelow_filter_lt (y : ℝ) (p : ℕ) (hp : (p : ℝ) < y) :
    (primesBelow y).filter (fun q => q < p) = primesBelow p := by
  ext q
  simp only [mem_filter, mem_primesBelow]
  constructor
  · rintro ⟨⟨hq, _⟩, hqp⟩; exact ⟨hq, by exact_mod_cast hqp⟩
  · rintro ⟨hq, hqp⟩
    have : q < p := by exact_mod_cast hqp
    exact ⟨⟨hq, by linarith⟩, this⟩

/-- **Greaves (4.2), exact.** -/
theorem MT_decomp (P : WPar) (b : ℕ) (y : ℝ) :
    MT P b y = P.wn y 1 * Sg (gB b) false y (toDec (primesBelow y)) -
      ∑ p ∈ primesBelow y, P.wn y p *
        CS (gB b) p (fun σ z => Sg (gB b) σ z (toDec (primesBelow p))) false y
          (toDec ((primesBelow y).filter (fun q => p < q))) := by
  classical
  have hnd : (toDec (primesBelow y)).Nodup := Finset.sort_nodup _ _
  rw [MT_eq_Gw, Gw_eq (gB b) (P.wn y) _ hnd, sum_toDec]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  have hpy : (p : ℝ) < y := ((mem_primesBelow y p).1 hp).2
  rw [toDec_split (primesBelow y) p hp, Cg_eq_CS (gB b) p _ _ ?_, primesBelow_filter_lt y p hpy]
  intro hmem
  rw [mem_toDec, mem_filter] at hmem
  exact lt_irrefl p hmem.2

/-! ## Large primes -/

theorem Sg_true_skip (g : ℕ → ℝ) (z : ℝ) : ∀ (l1 l2 : List ℕ), (∀ q ∈ l1, z < (q : ℝ) ^ 3) →
    Sg g true z (l1 ++ l2) = Sg g true z l2 := by
  intro l1
  induction l1 with
  | nil => intro l2 _; rfl
  | cons q l1 ih =>
    intro l2 h
    have hq : ¬ headOK true z q := fun h' => absurd h' (not_le.2 (h q (by simp)))
    simp only [List.cons_append, Sg, if_neg hq, sub_zero]
    exact ih l2 (fun q' hq' => h q' (List.mem_cons_of_mem q hq'))

/-- `Sg false z (l1 ++ l2) = Sg false z l2 − Σ_{P∈l1} g P · Sg true (z/P) (rest after P)`. -/
theorem Sg_false_append (g : ℕ → ℝ) (z : ℝ) : ∀ (l1 l2 : List ℕ),
    Sg g false z (l1 ++ l2) = Sg g false z l2 - sumTails (fun P rest => g P * Sg g true (z / P) (rest ++ l2)) l1 := by
  intro l1
  induction l1 with
  | nil => intro l2; simp [sumTails]
  | cons P l1 ih =>
    intro l2
    simp only [List.cons_append, Sg, sumTails]
    rw [if_pos (show headOK false z P from trivial), ih l2]
    simp only [Bool.not_false]; ring

/-- For `p` above `y^{1/2}` only the single-prime chain survives. -/
theorem CS_big (g : ℕ → ℝ) (p : ℕ) (leaf : Bool → ℝ → ℝ) (y : ℝ) (hy : 0 < y) (hp : 0 < p)
    (hpy : y < (p : ℝ) ^ 2) : ∀ (pre : List ℕ), (∀ q ∈ pre, (p : ℝ) < q) →
    CS g p leaf false y pre = -(g p * leaf true (y / p)) := by
  have hplus : ∀ (Q : ℕ), (p : ℝ) ≤ Q → ∀ (pre : List ℕ), (∀ q ∈ pre, (p : ℝ) < q) →
      CS g p leaf true (y / Q) pre = 0 := by
    intro Q hQ pre
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
    have hQ0 : (0 : ℝ) < Q := by linarith
    have hbad : ∀ q : ℕ, (p : ℝ) ≤ q → ¬ headOK true (y / Q) q := by
      intro q hq h
      have h1 : (q : ℝ) ^ 3 ≤ y / Q := h
      have h2 : (p : ℝ) ^ 3 ≤ (q : ℝ) ^ 3 := pow_le_pow_left₀ hp0.le hq 3
      have h3 : y / Q < (p : ℝ) := by
        rw [div_lt_iff₀ hQ0]; nlinarith
      have h4 : (p : ℝ) ≤ (p : ℝ) ^ 3 := by
        have : (1 : ℝ) ≤ p := by exact_mod_cast hp
        nlinarith
      linarith
    induction pre with
    | nil => intro _; simp only [CS, if_neg (hbad p le_rfl), neg_zero]
    | cons P pre ih =>
      intro h
      simp only [CS, if_neg (hbad P (h P (by simp)).le), sub_zero]
      exact ih (fun q hq => h q (List.mem_cons_of_mem P hq))
  intro pre
  induction pre with
  | nil => intro _; simp only [CS, if_pos (show headOK false y p from trivial)]; rfl
  | cons P pre ih =>
    intro h
    simp only [CS, if_pos (show headOK false y P from trivial), Bool.not_false]
    rw [ih (fun q hq => h q (List.mem_cons_of_mem P hq)),
      hplus P (h P (by simp)).le pre (fun q hq => h q (List.mem_cons_of_mem P hq))]
    simp

end Palprimes.MT
