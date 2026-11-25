import Omega3.Items.M12_Data

/-!
# M12 helper: specifications of the list functions of `M12_Data`
-/

set_option linter.style.longLine false

open Finset

namespace Omega3.M12

/-- Table lookup with defaults. -/
def tabF (tab : List (List ℕ)) (k j : ℕ) : ℕ := (tab.getD k []).getD j 0

lemma TT_pos : 0 < TT := by unfold TT; positivity

lemma cdiv_zero_left {b : ℕ} (hb : 0 < b) : cdiv 0 b = 0 := by
  unfold cdiv; rw [zero_add]; exact Nat.div_eq_of_lt (by omega)

lemma getD_nil' (j : ℕ) : ([] : List ℕ).getD j 0 = 0 := by simp

lemma getD_tail (l : List ℕ) (j : ℕ) : l.tail.getD j 0 = l.getD (j + 1) 0 := by
  cases l <;> simp

lemma headD_eq (l : List ℕ) : l.headD 0 = l.getD 0 0 := by
  cases l <;> simp

lemma getD_zadd : ∀ (a b : List ℕ) (j : ℕ), (zadd a b).getD j 0 = a.getD j 0 + b.getD j 0
  | [], l, j => by simp [zadd]
  | a :: t, l, j => by
    cases j with
    | zero => cases l <;> simp [zadd]
    | succ j => simp only [zadd, List.getD_cons_succ]; rw [getD_zadd t l.tail j, getD_tail]

lemma getD_fuse (w : ℕ) : ∀ (n : ℕ) (acc row : List ℕ) (j : ℕ),
    (fuse w n acc row).getD j 0 = acc.getD j 0 +
      (if j < n then cdiv (w * max (row.getD j 0) (row.getD (j + 1) 0)) TT else 0)
  | 0, acc, row, j => by simp [fuse]
  | n + 1, acc, [], j => by
    simp only [fuse, getD_nil', max_self, mul_zero, cdiv_zero_left TT_pos, ite_self, add_zero]
  | n + 1, acc, a :: t, j => by
    cases j with
    | zero => simp only [fuse, List.getD_cons_zero, headD_eq, List.getD_cons_succ, if_pos (Nat.succ_pos n)]
    | succ j =>
      simp only [fuse, List.getD_cons_succ]
      rw [getD_fuse w n acc.tail t j, getD_tail]
      by_cases h : j < n
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]

lemma getD_prefixGen {α : Type} (f : List ℕ → α → List ℕ) (c : α → ℕ → ℕ)
    (hf : ∀ acc a j, (f acc a).getD j 0 = acc.getD j 0 + c a j) (d : α) :
    ∀ (as : List α) (acc : List ℕ) (t : ℕ), t ≤ as.length → ∀ j,
      ((prefixGen f acc as).getD t []).getD j 0 = acc.getD j 0 + ∑ u ∈ range t, c (as.getD u d) j
  | [], acc, t, ht, j => by
    simp only [List.length_nil, Nat.le_zero] at ht
    subst ht; simp [prefixGen]
  | a :: as, acc, 0, _, j => by simp [prefixGen]
  | a :: as, acc, t + 1, ht, j => by
    simp only [prefixGen, List.getD_cons_succ]
    rw [getD_prefixGen f c hf d as (f acc a) t (by simpa using ht) j, hf, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

lemma getD_addB (yd yu : ℕ) : ∀ (acc : List ℕ) (xs : List (ℕ × ℕ)) (j : ℕ),
    (addB yd yu acc xs).getD j 0 = acc.getD j 0 +
      (if j < xs.length then bterm (xs.getD j (0, 0)).1 (xs.getD j (0, 0)).2 yd yu else 0)
  | acc, [], j => by simp [addB]
  | acc, p :: ps, j => by
    cases j with
    | zero => cases acc <;> simp [addB]
    | succ j =>
      simp only [addB, List.getD_cons_succ, List.length_cons]
      rw [getD_addB yd yu acc.tail ps j, getD_tail]
      by_cases h : j < ps.length
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]

lemma getD_map_range {α : Type} (n : ℕ) (f : ℕ → α) (d : α) (j : ℕ) :
    ((List.range n).map f).getD j d = if j < n then f j else d := by
  by_cases h : j < n
  · rw [if_pos h, List.getD_eq_getElem (hn := by simpa using h)]
    simp
  · rw [if_neg h, List.getD_eq_default (hn := by simp; omega)]

lemma getD_drop (l : List ℕ) (s j : ℕ) : (l.drop s).getD j 0 = l.getD (s + j) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

lemma getD_drop' {α : Type} (l : List α) (d : α) (s j : ℕ) : (l.drop s).getD j d = l.getD (s + j) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

lemma getD_zip {α β : Type} (l₁ : List α) (l₂ : List β) (d₁ : α) (d₂ : β) (j : ℕ) (h₁ : j < l₁.length) (h₂ : j < l₂.length) :
    (List.zip l₁ l₂).getD j (d₁, d₂) = (l₁.getD j d₁, l₂.getD j d₂) := by
  rw [List.getD_eq_getElem (hn := by simp; omega), List.getD_eq_getElem (hn := h₁), List.getD_eq_getElem (hn := h₂)]
  simp

/-! ## The base table -/

lemma length_xdat (g : Grid) : (xdat g).length = g.N := by simp [xdat]

lemma getD_xdat (g : Grid) {j : ℕ} (hj : j < g.N) : (xdat g).getD j (0, 0) = (X1up g j, TOP g j) := by
  unfold xdat; rw [getD_map_range, if_pos hj]

/-- The base table entry as a sum over cells. -/
lemma tab1_spec (g : Grid) {k : ℕ} (hk : k ≤ g.SY) (hc : g.S3 ≤ CUT g k) (hc' : CUT g k ≤ g.SH) (j : ℕ) :
    tabF (tab1 g) k j = ∑ u ∈ range (CUT g k - g.S3),
      (if j < g.N then bterm (X1up g j) (TOP g j) (YDN g (g.S3 + u)) (YUP g (g.S3 + u + 1)) else 0) := by
  unfold tabF tab1
  rw [getD_map_range, if_pos (by omega)]
  unfold baseAcc
  rw [getD_prefixGen _ (fun σ j => if j < (xdat g).length then bterm ((xdat g).getD j (0, 0)).1 ((xdat g).getD j (0, 0)).2 (YDN g σ) (YUP g (σ + 1)) else 0)
    (fun acc σ j => getD_addB _ _ acc _ j) 0 _ [] _ (by simp; omega) j]
  simp only [getD_nil', zero_add]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hu' : u < g.SH - g.S3 := by simp at hu; omega
  rw [getD_map_range, if_pos hu', length_xdat]
  split_ifs with hj
  · rw [getD_xdat g hj]
  · rfl

/-! ## The step -/

lemma length_sdat (g : Grid) : (sdat g).length = g.SY := by simp [sdat]

lemma getD_sdat (g : Grid) {σ : ℕ} (h : σ < g.SY) : (sdat g).getD σ (0, 0, 0) = (σ / g.M, wt g σ, JL g σ) := by
  unfold sdat; rw [getD_map_range, if_pos h]

lemma SMT_le (g : Grid) (k : ℕ) : SMT g k ≤ g.SY := by
  unfold SMT
  split_ifs
  · have : ∀ p s f, findFirst p s f ≤ s + f := by
      intro p s f
      induction f generalizing s with
      | zero => simp [findFirst]
      | succ f ih => unfold findFirst; split_ifs <;> [omega; (have := ih (s + 1); omega)]
    simpa using this (gleY g k) 0 g.SY
  · exact le_rfl

lemma step_spec (g : Grid) (tab : List (List ℕ)) (htab : g.SY + 1 ≤ tab.length) {k : ℕ} (hk : k ≤ g.SY) (j : ℕ) :
    tabF (step g tab) k j = ∑ σ ∈ range (SMT g k),
      (if j < JL g σ then cdiv (wt g σ * max (tabF tab (σ + 1) (σ / g.M + j)) (tabF tab (σ + 1) (σ / g.M + j + 1))) TT else 0) := by
  unfold tabF step
  simp only
  rw [getD_map_range, if_pos (by omega)]
  have hlen : (List.zip (sdat g) (tab.drop 1)).length = g.SY := by
    simp [length_sdat]; omega
  rw [getD_prefixGen stepF (fun it j => if j < it.1.2.2 then cdiv (it.1.2.1 * max ((it.2.drop it.1.1).getD j 0) ((it.2.drop it.1.1).getD (j + 1) 0)) TT else 0)
    (fun acc it j => getD_fuse _ _ acc _ j) ((0, 0, 0), []) _ [] _ (by rw [hlen]; exact SMT_le g k) j]
  simp only [getD_nil', zero_add]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  have hσ' : σ < g.SY := lt_of_lt_of_le (Finset.mem_range.mp hσ) (SMT_le g k)
  rw [getD_zip _ _ _ _ _ (by rw [length_sdat]; exact hσ') (by simp; omega), getD_sdat g hσ']
  simp only [getD_drop, getD_drop']
  rw [Nat.add_comm 1 σ]
  rfl

lemma length_step (g : Grid) (tab : List (List ℕ)) : (step g tab).length = g.SY + 1 := by
  simp [step]

lemma length_tab1 (g : Grid) : (tab1 g).length = g.SY + 1 := by
  simp [tab1]

/-! ## The level runs -/

lemma run_spec (g : Grid) : ∀ (n : ℕ) (tab : List (List ℕ)) (acc : List ℕ) (j : ℕ),
    (run g n tab acc).getD j 0 = acc.getD j 0 + ∑ k ∈ range n, tabF ((step g)^[2 * k + 1] tab) g.SY j
  | 0, tab, acc, j => by simp [run]
  | n + 1, tab, acc, j => by
    simp only [run]
    rw [run_spec g n _ _ j, getD_zadd, Finset.sum_range_succ']
    have e : ∀ k, (step g)^[2 * k + 1] (step g (step g tab)) = (step g)^[2 * (k + 1) + 1] tab := by
      intro k
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, Function.iterate_add_apply]
      rfl
    simp only [e]
    unfold tabF
    simp only [mul_zero, zero_add, Function.iterate_one]
    ring

end Omega3.M12
