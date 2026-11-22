import Palprimes.Greaves.Subsets

/-! # Greaves Lemma 3.1 for a single integer `a`

`Aset a y` = primes of `a` below `y`; `Sig a = G(-)(y, Aset a y, w 1)` is Greaves' `Σ_ℬ(A, w)`.
`nu a Y` = Greaves' `ν_{y,U}(a)` with `Y = y^U`: primes below `Y` once, primes `≥ Y` with multiplicity.
`lemma31`: `Sig a ≤ w(q_a) · [ν(a) ≤ R]` (Greaves (3.15), (3.16)). -/

set_option linter.style.longLine false

open Finset Real

namespace Palprimes.Greaves

/-- Primes of `a` below `y`. -/
noncomputable def Aset (a : ℕ) (y : ℝ) : Finset ℕ :=
  open Classical in a.primeFactors.filter (fun p : ℕ => (p : ℝ) < y)

/-- Greaves' `ν_{y,U}(a)` with `Y = y^U`. -/
noncomputable def nu (a : ℕ) (Y : ℝ) : ℕ :=
  open Classical in
  #(a.primeFactors.filter (fun p : ℕ => (p : ℝ) < Y)) +
    ∑ p ∈ a.primeFactors.filter (fun p : ℕ => Y ≤ (p : ℝ)), a.factorization p

theorem toDec_pairwise (S : Finset ℕ) : (toDec S).Pairwise (· > ·) := by
  have h := (Finset.pairwise_sort S (· ≥ ·)).and (Finset.sort_nodup S (· ≥ ·))
  exact h.imp (fun h => lt_of_le_of_ne h.1 h.2.symm)

theorem mem_toDec (S : Finset ℕ) (p : ℕ) : p ∈ toDec S ↔ p ∈ S := Finset.mem_sort _

theorem sum_toDec (S : Finset ℕ) (f : ℕ → ℝ) : ((toDec S).map f).sum = ∑ p ∈ S, f p := by
  rw [← Finset.sum_map_toList]
  exact List.Perm.sum_eq (List.Perm.map f (Finset.sort_perm_toList S _))

/-- **The counting step**: `Σ_{p∈S, p<Y} (U − log p/log y) < U − V` and `a < y^g`, `g ≤ V + RU`
give `ν(a) ≤ R`. -/
theorem nu_le (a : ℕ) (ha : 1 ≤ a) (y U V g : ℝ) (R : ℕ) (hy : 1 < y) (hU0 : 0 < U) (hU1 : U ≤ 1)
    (hag : (a : ℝ) < y ^ g) (hg : g ≤ V + R * U)
    (hS : ∑ p ∈ (Aset a y).filter (fun p : ℕ => (p : ℝ) < y ^ U), (U - Real.log p / Real.log y) < U - V) :
    nu a (y ^ U) ≤ R := by
  classical
  have hL : 0 < Real.log y := Real.log_pos hy
  set Y := y ^ U with hYdef
  have hY1 : 1 ≤ Y := Real.one_le_rpow hy.le hU0.le
  have hYy : Y ≤ y := by
    calc Y ≤ y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hy.le hU1
      _ = y := Real.rpow_one y
  set t : ℕ → ℝ := fun p => Real.log p / Real.log y with ht
  have ht0 : ∀ p : ℕ, 1 ≤ p → 0 ≤ t p := fun p hp =>
    div_nonneg (Real.log_nonneg (by exact_mod_cast hp)) hL.le
  set P := a.primeFactors with hP
  set Ps := P.filter (fun p : ℕ => (p : ℝ) < Y) with hPs
  set Pb := P.filter (fun p : ℕ => Y ≤ (p : ℝ)) with hPb
  -- log a / log y = Σ v_p t_p
  have hloga : Real.log a / Real.log y = ∑ p ∈ P, (a.factorization p : ℝ) * t p := by
    rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization, Finset.sum_div]
    apply Finset.sum_congr rfl; intro p _; simp only [ht]; ring
  have hlt : Real.log a / Real.log y < g := by
    rw [div_lt_iff₀ hL]
    have := Real.log_lt_log (by exact_mod_cast ha) hag
    rw [Real.log_rpow (by linarith)] at this; linarith
  -- small primes are in `Aset`
  have hPsA : Ps = (Aset a y).filter (fun p : ℕ => (p : ℝ) < Y) := by
    ext p; simp only [hPs, Aset, mem_filter]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, lt_of_lt_of_le h2 hYy⟩, h2⟩
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
  -- the split of `Σ v_p t_p`
  have hsplit : ∑ p ∈ P, (a.factorization p : ℝ) * t p =
      ∑ p ∈ Ps, (a.factorization p : ℝ) * t p + ∑ p ∈ Pb, (a.factorization p : ℝ) * t p := by
    rw [hPs, hPb, ← Finset.sum_filter_add_sum_filter_not P (fun p : ℕ => (p : ℝ) < Y)]
    congr 1
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext p; simp [not_lt]
  have hPpos : ∀ p ∈ P, 1 ≤ a.factorization p ∧ 1 ≤ p := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    exact ⟨(Nat.Prime.factorization_pos_of_dvd hpp (by omega) (Nat.dvd_of_mem_primeFactors hp)),
      hpp.one_lt.le⟩
  have hsmall : ∑ p ∈ Ps, t p ≤ ∑ p ∈ Ps, (a.factorization p : ℝ) * t p := by
    apply Finset.sum_le_sum; intro p hp
    have h := hPpos p (Finset.mem_of_mem_filter p hp)
    have : (1 : ℝ) ≤ a.factorization p := by exact_mod_cast h.1
    have := ht0 p h.2
    nlinarith
  -- big primes contribute `v_p (U − t_p) ≤ 0`
  have hbig : ∑ p ∈ Pb, (a.factorization p : ℝ) * U ≤ ∑ p ∈ Pb, (a.factorization p : ℝ) * t p := by
    apply Finset.sum_le_sum; intro p hp
    have hpY : Y ≤ (p : ℝ) := (Finset.mem_filter.1 hp).2
    have hUt : U ≤ t p := by
      simp only [ht]
      rw [le_div_iff₀ hL]
      have h1 : Real.log Y ≤ Real.log p := Real.log_le_log (by linarith) hpY
      rw [hYdef, Real.log_rpow (by linarith)] at h1
      linarith
    exact mul_le_mul_of_nonneg_left hUt (by positivity)
  -- assemble: `U ν − Σ_{counted} t < U − V`
  have hnu : (nu a Y : ℝ) * U < U - V + g := by
    have e : (nu a Y : ℝ) * U = ∑ p ∈ Ps, U + ∑ p ∈ Pb, (a.factorization p : ℝ) * U := by
      simp only [nu, hPs, hPb]
      push_cast
      rw [Finset.sum_const, nsmul_eq_mul, add_mul, Finset.sum_mul]
    have hS' : ∑ p ∈ Ps, (U - t p) < U - V := by rw [hPsA]; exact hS
    rw [Finset.sum_sub_distrib] at hS'
    rw [e]
    have := hsplit
    linarith
  have hR : (nu a Y : ℝ) < R + 1 := by
    have h1 : (nu a Y : ℝ) * U < (R + 1) * U := by nlinarith
    exact lt_of_mul_lt_mul_right h1 hU0.le
  have : (nu a Y) < R + 1 := by exact_mod_cast hR
  omega

theorem mem_Aset (a : ℕ) (y : ℝ) (p : ℕ) : p ∈ Aset a y ↔ p ∈ a.primeFactors ∧ (p : ℝ) < y := by
  classical
  simp [Aset]

/-- The least element of `Aset a y` is the least prime factor of `a`. -/
theorem minFac_eq_of_min (a : ℕ) (y : ℝ) (m : ℕ) (hm : m ∈ Aset a y) (hmin : ∀ p ∈ Aset a y, m ≤ p) :
    a.minFac = m := by
  rw [mem_Aset] at hm
  obtain ⟨hmP, hmy⟩ := hm
  have hmp : m.Prime := Nat.prime_of_mem_primeFactors hmP
  have hmd : m ∣ a := Nat.dvd_of_mem_primeFactors hmP
  have ha0 : a ≠ 0 := (Nat.mem_primeFactors.1 hmP).2.2
  have ha1 : a ≠ 1 := by rintro rfl; exact hmp.one_lt.ne' (Nat.eq_one_of_dvd_one hmd)
  have h1 : a.minFac ≤ m := Nat.minFac_le_of_dvd hmp.two_le hmd
  have hq : a.minFac.Prime := Nat.minFac_prime ha1
  have hqS : a.minFac ∈ Aset a y := by
    rw [mem_Aset]
    refine ⟨Nat.mem_primeFactors.2 ⟨hq, Nat.minFac_dvd a, ha0⟩, ?_⟩
    have : (a.minFac : ℝ) ≤ m := by exact_mod_cast h1
    linarith
  exact le_antisymm h1 (hmin _ hqS)

theorem list_two_decomp (L : List ℕ) (hL : 2 ≤ L.length) : ∃ pre Q2 Q1, L = pre ++ [Q2, Q1] := by
  match h : L.reverse with
  | [] => simp at h; subst h; simp at hL
  | [x] => have := congrArg List.length h; simp at this; omega
  | Q1 :: Q2 :: rest =>
    refine ⟨rest.reverse, Q2, Q1, ?_⟩
    have := congrArg List.reverse h
    rw [List.reverse_reverse] at this
    rw [this]; simp

/-- **The key step**: positivity of `Σ_ℬ` gives `Σ_{p∈A} (w1 − w p) < w1` and `Σ_ℬ ≤ w(q_a)`. -/
theorem key31 (w : ℕ → ℝ) (y : ℝ) (a : ℕ) (ha1 : 1 ≤ a) (hw0 : ∀ p, 0 ≤ w p) (hwle : ∀ p, w p ≤ w 1)
    (hbig : ∀ p : ℕ, p.Prime → y ≤ p → w p = w 1)
    (hHyp : HypTop w y (toDec (Aset a y)) (w 1)) (hpos : 0 < G w false y (toDec (Aset a y)) (w 1)) :
    ∑ p ∈ Aset a y, (w 1 - w p) < w 1 ∧ G w false y (toDec (Aset a y)) (w 1) ≤ w a.minFac := by
  classical
  set S := Aset a y with hS
  set L := toDec S with hL
  have hmem : ∀ p, p ∈ L ↔ p ∈ S := fun p => mem_toDec S p
  have hsumL : (L.map (fun p => w 1 - w p)).sum = ∑ p ∈ S, (w 1 - w p) := sum_toDec S _
  match hlen : L with
  | [] =>
    have hS0 : S = ∅ := Finset.eq_empty_iff_forall_notMem.2 (fun p hp => by simpa using (hmem p).2 hp)
    have hG : G w false y [] (w 1) = w 1 := rfl
    rw [hG] at hpos ⊢
    refine ⟨by rw [hS0]; simpa using hpos, ?_⟩
    by_cases ha : a = 1
    · rw [ha, Nat.minFac_one]
    · have hq := Nat.minFac_prime ha
      by_cases hqy : (a.minFac : ℝ) < y
      · exfalso
        have ha0 : a ≠ 0 := by omega
        have : a.minFac ∈ S := by
          rw [hS, mem_Aset]; exact ⟨Nat.mem_primeFactors.2 ⟨hq, Nat.minFac_dvd a, ha0⟩, hqy⟩
        rw [hS0] at this; simp at this
      · push Not at hqy; rw [hbig _ hq hqy]
  | [p] =>
    have hG : G w false y [p] (w 1) = w p := by
      simp only [G]; rw [if_pos (show headOK false y p from trivial)]; simp [G]
    rw [hG] at hpos ⊢
    have hS1 : S = {p} := by
      ext q; rw [← hmem q]; simp
    refine ⟨by rw [hS1]; simp; linarith, ?_⟩
    have hpS : p ∈ S := by rw [hS1]; simp
    rw [minFac_eq_of_min a y p hpS (fun q hq => by rw [← hS, hS1] at hq; simp at hq; omega)]
  | Q :: R :: rest =>
    obtain ⟨pre, Q2, Q1, hdec⟩ := list_two_decomp (Q :: R :: rest) (by simp)
    rw [hdec] at hpos hHyp hsumL ⊢
    have hsort : (pre ++ [Q2, Q1]).Pairwise (· > ·) := by
      have := toDec_pairwise S; rw [← hL, hdec] at this; exact this
    have hQ1S : Q1 ∈ S := by rw [← hmem, hdec]; simp
    have hQ1pos : 0 < Q1 := by
      have := (mem_Aset a y Q1).1 hQ1S
      exact (Nat.prime_of_mem_primeFactors this.1).pos
    have hwc : ∀ q ∈ pre ++ [Q2, Q1], w q ≤ w 1 := fun q _ => hwle q
    obtain ⟨_, hGle⟩ := G_pos_two w hw0 y pre Q2 Q1 (w 1) hsort hQ1pos hwc hHyp hpos
    have hsplit : ((pre ++ [Q2, Q1]).map (fun q => w 1 - w q)).sum =
        ((pre ++ [Q2]).map (fun q => w 1 - w q)).sum + (w 1 - w Q1) := by
      simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil]; ring
    have hnn : 0 ≤ ((pre ++ [Q2]).map (fun q => w 1 - w q)).sum := by
      apply List.sum_nonneg; intro x hx; rw [List.mem_map] at hx
      obtain ⟨q, _, rfl⟩ := hx; linarith [hwle q]
    refine ⟨by rw [← hsumL]; linarith, ?_⟩
    have hmin : ∀ q ∈ S, Q1 ≤ q := by
      intro q hq
      rw [← hmem, hdec] at hq
      rcases List.mem_append.1 hq with h | h
      · have := (List.pairwise_append.1 hsort).2.2 q h Q1 (by simp); omega
      · simp at h
        rcases h with rfl | rfl
        · have := (List.pairwise_append.1 hsort).2.1; simp at this; omega
        · exact le_rfl
    rw [minFac_eq_of_min a y Q1 hQ1S hmin]
    linarith

/-- **Greaves Lemma 3.1**: `Σ_ℬ(A, w) ≤ w(q_a) · [ν_{y,U}(a) ≤ R]`. -/
theorem lemma31 (w : ℕ → ℝ) (y U V g : ℝ) (R : ℕ) (a : ℕ) (ha : 1 ≤ a) (hy : 1 < y)
    (hU0 : 0 < U) (hU1 : U ≤ 1) (hag : (a : ℝ) < y ^ g) (hg : g ≤ V + R * U)
    (hw0 : ∀ p, 0 ≤ w p) (hwle : ∀ p, w p ≤ w 1) (hw1 : w 1 = U - V)
    (h311 : ∀ p : ℕ, p.Prime → (p : ℝ) < y ^ U → 0 < w p → w p ≤ Real.log p / Real.log y - V)
    (hbig : ∀ p : ℕ, p.Prime → y ≤ p → w p = w 1)
    (hHyp : HypTop w y (toDec (Aset a y)) (w 1)) :
    G w false y (toDec (Aset a y)) (w 1) ≤ if nu a (y ^ U) ≤ R then w a.minFac else 0 := by
  classical
  by_cases hpos : 0 < G w false y (toDec (Aset a y)) (w 1)
  · obtain ⟨hsum, hle⟩ := key31 w y a ha hw0 hwle hbig hHyp hpos
    have hnu : nu a (y ^ U) ≤ R := by
      apply nu_le a ha y U V g R hy hU0 hU1 hag hg
      -- `Σ_{p∈S, p<Y} (U − t_p) ≤ Σ_{p∈S} (w1 − w p) < w1 = U − V`
      have hterm : ∀ p ∈ (Aset a y).filter (fun p : ℕ => (p : ℝ) < y ^ U),
          U - Real.log p / Real.log y ≤ w 1 - w p := by
        intro p hp
        have hpS : p ∈ Aset a y := Finset.mem_of_mem_filter p hp
        have hpY : (p : ℝ) < y ^ U := (Finset.mem_filter.1 hp).2
        have hpp : p.Prime := Nat.prime_of_mem_primeFactors ((mem_Aset a y p).1 hpS).1
        have hwp : 0 < w p := by
          by_contra hle0
          push Not at hle0
          have hwp0 : w p = 0 := le_antisymm hle0 (hw0 p)
          have : w 1 - w p ≤ ∑ q ∈ Aset a y, (w 1 - w q) :=
            Finset.single_le_sum (f := fun q => w 1 - w q) (fun q _ => by linarith [hwle q]) hpS
          rw [hwp0] at this; linarith
        have := h311 p hpp hpY hwp
        rw [hw1]; linarith
      calc ∑ p ∈ (Aset a y).filter (fun p : ℕ => (p : ℝ) < y ^ U), (U - Real.log p / Real.log y)
          ≤ ∑ p ∈ (Aset a y).filter (fun p : ℕ => (p : ℝ) < y ^ U), (w 1 - w p) :=
            Finset.sum_le_sum hterm
        _ ≤ ∑ p ∈ Aset a y, (w 1 - w p) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun q _ _ => by linarith [hwle q])
        _ < w 1 := hsum
        _ = U - V := hw1
    rw [if_pos hnu]; exact hle
  · push Not at hpos
    split_ifs
    · linarith [hw0 a.minFac]
    · exact hpos

end Palprimes.Greaves
