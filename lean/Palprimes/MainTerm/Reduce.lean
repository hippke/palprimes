import Palprimes.MainTerm.Decomp
import Palprimes.MainTerm.E1

/-! # The main term reduced to `S^-(y, 2)`, a sum over large primes, and chains

`MT_reduce`: with `S = primes < y`, `sm = {p ∈ S : p² < y}`, `bg = S \ sm`,
`MT = w(1) S^-(y,2) + Σ_{P∈bg} (w(P) − w(1)) g(P) Sg⁺(y/P, primes < P)
      + Σ_{p∈sm} Σ_{T ⊆ S_{>p}} w(p) csTerm(T)`. -/

set_option linter.style.longLine false

open Finset Real

namespace Palprimes.MT

open Palprimes.Greaves

theorem toDec_filter_split (P : ℕ → Prop) [DecidablePred P] : ∀ (S : Finset ℕ),
    (∀ a ∈ S, ∀ c ∈ S, P c → ¬ P a → a < c) →
    toDec S = toDec (S.filter P) ++ toDec (S.filter (fun q => ¬ P q)) := by
  intro S
  induction S using Finset.induction_on_max with
  | empty => intro _; simp [toDec_empty]
  | insert M S hM ih =>
    intro hP
    have hP' : ∀ a ∈ S, ∀ c ∈ S, P c → ¬ P a → a < c := fun a ha c hc =>
      hP a (Finset.mem_insert_of_mem ha) c (Finset.mem_insert_of_mem hc)
    by_cases hPM : P M
    · rw [Finset.filter_insert, if_pos hPM, Finset.filter_insert, if_neg (not_not.2 hPM),
        toDec_insert_max M S hM, toDec_insert_max M _ (fun x hx => hM x (Finset.mem_of_mem_filter x hx)),
        ih hP', List.cons_append]
    · have hnone : ∀ c ∈ S, ¬ P c := by
        intro c hc hPc
        have := hP M (Finset.mem_insert_self M S) c (Finset.mem_insert_of_mem hc) hPc hPM
        exact lt_irrefl _ (lt_trans this (hM c hc))
      have h1 : (insert M S).filter P = ∅ := by
        rw [Finset.filter_insert, if_neg hPM, Finset.filter_eq_empty_iff]
        exact hnone
      have h2 : (insert M S).filter (fun q => ¬ P q) = insert M S := by
        rw [Finset.filter_eq_self]
        intro c hc
        rcases Finset.mem_insert.1 hc with rfl | hc
        · exact hPM
        · exact hnone c hc
      rw [h1, h2, toDec_empty, List.nil_append]

theorem sumTails_toDec (f : ℕ → List ℕ → ℝ) : ∀ (S : Finset ℕ),
    sumTails f (toDec S) = ∑ P ∈ S, f P (toDec (S.filter (· < P))) := by
  intro S
  induction S using Finset.induction_on_max with
  | empty => simp [toDec_empty, sumTails]
  | insert M S hM ih =>
    have hMS : M ∉ S := fun h => lt_irrefl M (hM M h)
    rw [toDec_insert_max M S hM, sumTails, ih, Finset.sum_insert hMS]
    have e1 : (insert M S).filter (· < M) = S := by
      ext q; simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨rfl | hq, h⟩
        · exact absurd h (lt_irrefl _)
        · exact hq
      · intro hq; exact ⟨Or.inr hq, hM q hq⟩
    rw [e1]
    congr 1
    apply Finset.sum_congr rfl
    intro P hP
    rw [Finset.filter_insert, if_neg (not_lt.2 (hM P hP).le)]

/-- `CS_big` with `y ≤ p²`. -/
theorem CS_big' (g : ℕ → ℝ) (p : ℕ) (leaf : Bool → ℝ → ℝ) (y : ℝ) (hy : 0 < y) (hp : 2 ≤ p)
    (hpy : y ≤ (p : ℝ) ^ 2) : ∀ (pre : List ℕ), (∀ q ∈ pre, (p : ℝ) < q) →
    CS g p leaf false y pre = -(g p * leaf true (y / p)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hplus : ∀ (Q : ℕ), (p : ℝ) ≤ Q → ∀ (pre : List ℕ), (∀ q ∈ pre, (p : ℝ) < q) →
      CS g p leaf true (y / Q) pre = 0 := by
    intro Q hQ pre
    have hQ0 : (0 : ℝ) < Q := by linarith
    have hbad : ∀ q : ℕ, (p : ℝ) ≤ q → ¬ headOK true (y / Q) q := by
      intro q hq h
      have h1 : (q : ℝ) ^ 3 ≤ y / Q := h
      have h2 : (p : ℝ) ^ 3 ≤ (q : ℝ) ^ 3 := pow_le_pow_left₀ hp0.le hq 3
      have h3 : y / Q ≤ (p : ℝ) := by
        rw [div_le_iff₀ hQ0]; nlinarith
      have h4 : (p : ℝ) < (p : ℝ) ^ 3 := by nlinarith
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

/-- The small primes `p² < y`. -/
noncomputable def smP (y : ℝ) : Finset ℕ := (primesBelow y).filter (fun q => (q : ℝ) ^ 2 < y)
/-- The large primes `p² ≥ y`. -/
noncomputable def bgP (y : ℝ) : Finset ℕ := (primesBelow y).filter (fun q => ¬ (q : ℝ) ^ 2 < y)

theorem smP_eq (y : ℝ) (hy : 0 < y) : smP y = primesBelow (y ^ (1 / (2 : ℝ))) := by
  ext q
  simp only [smP, mem_filter, mem_primesBelow]
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hs : (0 : ℝ) ≤ y ^ (1 / (2 : ℝ)) := Real.rpow_nonneg hy.le _
  have hsq : (y ^ (1 / (2 : ℝ))) ^ 2 = y := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le]; norm_num
  have key : (q : ℝ) ^ 2 < y ↔ (q : ℝ) < y ^ (1 / (2 : ℝ)) := by
    have := pow_lt_pow_iff_left₀ hq0 hs two_ne_zero; rw [hsq] at this; exact this
  constructor
  · rintro ⟨⟨hp, _⟩, h⟩; exact ⟨hp, key.1 h⟩
  · rintro ⟨hp, h⟩
    refine ⟨⟨hp, ?_⟩, key.2 h⟩
    have h1 : (1 : ℝ) ≤ q := by exact_mod_cast hp.one_lt.le
    nlinarith [key.2 h]

theorem split_order (y : ℝ) : ∀ a ∈ primesBelow y, ∀ c ∈ primesBelow y,
    (fun q : ℕ => ¬ (q : ℝ) ^ 2 < y) c → ¬ (fun q : ℕ => ¬ (q : ℝ) ^ 2 < y) a → a < c := by
  intro a _ c _ hc ha
  simp only [not_not, not_lt] at hc ha
  have : (a : ℝ) ^ 2 < (c : ℝ) ^ 2 := by linarith
  exact_mod_cast lt_of_pow_lt_pow_left₀ 2 (Nat.cast_nonneg c) this

/-- Primes below a large prime `P` in decreasing order, split at `√y`. -/
theorem toDec_below_big (y : ℝ) (P : ℕ) (hP : P ∈ bgP y) :
    toDec ((bgP y).filter (· < P)) ++ toDec (smP y) = toDec (primesBelow P) := by
  classical
  have hPS : P ∈ primesBelow y := (mem_filter.1 hP).1
  have hPy : (P : ℝ) < y := ((mem_primesBelow y P).1 hPS).2
  have hP2 : y ≤ (P : ℝ) ^ 2 := not_lt.1 (mem_filter.1 hP).2
  rw [← primesBelow_filter_lt y P hPy]
  rw [toDec_filter_split (fun q : ℕ => ¬ (q : ℝ) ^ 2 < y) _ (fun a ha c hc => split_order y a
    (mem_filter.1 ha).1 c (mem_filter.1 hc).1)]
  congr 2
  · unfold bgP; rw [Finset.filter_filter, Finset.filter_filter]
    apply Finset.filter_congr; intro q _; tauto
  · unfold smP; rw [Finset.filter_filter]
    apply Finset.filter_congr; intro q _
    constructor
    · intro h3
      refine ⟨?_, not_not.2 h3⟩
      have : (q : ℝ) ^ 2 < (P : ℝ) ^ 2 := by linarith
      exact_mod_cast lt_of_pow_lt_pow_left₀ 2 (Nat.cast_nonneg P) this
    · rintro ⟨_, h3⟩; exact not_not.1 h3

/-- The `S⁺` leaf of a large prime. -/
noncomputable def bigLeaf (b : ℕ) (y : ℝ) (P : ℕ) : ℝ := Sg (gB b) true (y / P) (toDec (primesBelow P))

/-- **Reduction of the main term.** -/
theorem MT_reduce (P : WPar) (b : ℕ) (y : ℝ) (hy : 1 < y) :
    MT P b y = P.wn y 1 * Sminus b y 2 +
      ∑ Q ∈ bgP y, (P.wn y Q - P.wn y 1) * gB b Q * bigLeaf b y Q +
      ∑ p ∈ smP y, ∑ T ∈ ((primesBelow y).filter (fun q => p < q)).powerset,
        P.wn y p * csTerm (gB b) p (fun σ z => Sg (gB b) σ z (toDec (primesBelow p))) false y T := by
  classical
  have hy0 : 0 < y := by linarith
  rw [MT_decomp]
  -- first term
  have hS : toDec (primesBelow y) = toDec (bgP y) ++ toDec (smP y) :=
    toDec_filter_split (fun q : ℕ => ¬ (q : ℝ) ^ 2 < y) _ (split_order y) |>.trans (by
      congr 2; unfold smP; ext q; simp)
  have h1 : Sg (gB b) false y (toDec (primesBelow y)) = Sminus b y 2 -
      ∑ Q ∈ bgP y, gB b Q * bigLeaf b y Q := by
    rw [hS, Sg_false_append, sumTails_toDec]
    unfold Sminus
    rw [← smP_eq y hy0]
    congr 1
    apply Finset.sum_congr rfl
    intro Q hQ
    unfold bigLeaf
    rw [toDec_below_big y Q hQ]
  -- chains
  have hsplit : ∑ p ∈ primesBelow y, P.wn y p *
      CS (gB b) p (fun σ z => Sg (gB b) σ z (toDec (primesBelow p))) false y
        (toDec ((primesBelow y).filter (fun q => p < q))) =
      ∑ p ∈ bgP y, P.wn y p * (-(gB b p * bigLeaf b y p)) +
      ∑ p ∈ smP y, P.wn y p * (-∑ T ∈ ((primesBelow y).filter (fun q => p < q)).powerset,
        csTerm (gB b) p (fun σ z => Sg (gB b) σ z (toDec (primesBelow p))) false y T) := by
    rw [← Finset.sum_filter_add_sum_filter_not (primesBelow y) (fun q : ℕ => ¬ (q : ℝ) ^ 2 < y)]
    congr 1
    · apply Finset.sum_congr rfl
      intro p hp
      have hpS := (mem_filter.1 hp).1
      have hpp := ((mem_primesBelow y p).1 hpS).1
      have hp2 : y ≤ (p : ℝ) ^ 2 := not_lt.1 (mem_filter.1 hp).2
      rw [CS_big' (gB b) p _ y hy0 hpp.two_le hp2]
      · rfl
      · intro q hq
        rw [mem_toDec, mem_filter] at hq
        exact_mod_cast hq.2
    · have e : (primesBelow y).filter (fun q : ℕ => ¬ ¬ (q : ℝ) ^ 2 < y) = smP y := by
        unfold smP; ext q; simp
      rw [e]
      apply Finset.sum_congr rfl
      intro p _
      rw [CS_eq_sum]
  rw [h1, hsplit]
  simp only [Finset.mul_sum, Finset.sum_neg_distrib, mul_neg]
  have e2 : ∑ Q ∈ bgP y, (P.wn y Q - P.wn y 1) * gB b Q * bigLeaf b y Q =
      ∑ Q ∈ bgP y, P.wn y Q * (gB b Q * bigLeaf b y Q) - ∑ Q ∈ bgP y, P.wn y 1 * (gB b Q * bigLeaf b y Q) := by
    rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro Q _; ring
  rw [e2, mul_sub, Finset.mul_sum]
  ring

end Palprimes.MT
