import Mathlib

/-! # Greaves 1982, §2–§3: Brun's identity for the weighted Rosser sum (list form)

Lists are strictly decreasing lists of primes (`P :: l`, `P` the largest).
* `RosOK σ z ℓ`: Rosser's conditions, `σ = false` the lower-bound set (conditions at even
  positions, `p_{2i}^3 p_{2i-1}⋯p_1 ≤ z`), `σ = true` the upper-bound set (odd positions);
* `G σ z ℓ c = Σ_{s ⊆ ℓ, RosOK σ z s} (-1)^{|s|} (c - Σ_{p∈s} w p)` by recursion on the largest prime;
* `Lam ℓ c` the same sum without restriction (Greaves (2.1), `Λ{A, c}`);
* `D = Lam - G`: Brun's boundary terms. `D_false_nonneg`: they are `≥ 0` under Greaves' (3.8). -/

set_option linter.style.longLine false

open Finset

namespace Palprimes.Greaves

variable (w : ℕ → ℝ)

/-- The Rosser condition for the head prime in state `σ`. -/
def headOK : Bool → ℝ → ℕ → Prop
  | false, _, _ => True
  | true, z, P => (P : ℝ) ^ 3 ≤ z

noncomputable instance (σ : Bool) (z : ℝ) (P : ℕ) : Decidable (headOK σ z P) := Classical.dec _

/-- Rosser's conditions on a decreasing list. -/
def RosOK : Bool → ℝ → List ℕ → Prop
  | _, _, [] => True
  | σ, z, P :: l => headOK σ z P ∧ RosOK (!σ) (z / P) l

/-- `Λ{ℓ, c} = Σ_{s ⊆ ℓ} (-1)^{|s|} (c - Σ_s w)`. -/
noncomputable def Lam : List ℕ → ℝ → ℝ
  | [], c => c
  | P :: l, c => Lam l c - Lam l (c - w P)

/-- The Rosser-restricted weighted sum. -/
noncomputable def G : Bool → ℝ → List ℕ → ℝ → ℝ
  | _, _, [], c => c
  | σ, z, P :: l, c => G σ z l c - (if headOK σ z P then G (!σ) (z / P) l (c - w P) else 0)

/-- Brun's boundary sum. -/
noncomputable def D (σ : Bool) (z : ℝ) (ℓ : List ℕ) (c : ℝ) : ℝ := Lam w ℓ c - G w σ z ℓ c

/-! ## `Λ` in closed form (Greaves Lemma 2.1 with `l = 1`) -/

theorem Lam_nil (c : ℝ) : Lam w [] c = c := rfl

theorem Lam_single (p : ℕ) (c : ℝ) : Lam w [p] c = w p := by simp [Lam]

theorem Lam_long (P Q : ℕ) (l : List ℕ) (c : ℝ) : Lam w (P :: Q :: l) c = 0 := by
  induction l generalizing P Q c with
  | nil => simp [Lam]
  | cons R l ih =>
    show Lam w (Q :: R :: l) c - Lam w (Q :: R :: l) (c - w P) = 0
    rw [ih Q R c, ih Q R (c - w P), sub_self]

/-- `Λ ≥ 0` when `c ≥ 0` and `w ≥ 0`. -/
theorem Lam_nonneg (hw : ∀ p, 0 ≤ w p) (ℓ : List ℕ) (c : ℝ) (hc : 0 ≤ c) : 0 ≤ Lam w ℓ c := by
  match ℓ with
  | [] => exact hc
  | [p] => rw [Lam_single]; exact hw p
  | P :: Q :: l => rw [Lam_long]

/-! ## The recursions for `D` -/

theorem D_nil (σ : Bool) (z c : ℝ) : D w σ z [] c = 0 := by simp [D, Lam, G]

theorem D_cons (σ : Bool) (z : ℝ) (P : ℕ) (l : List ℕ) (c : ℝ) :
    D w σ z (P :: l) c = D w σ z l c -
      (if headOK σ z P then D w (!σ) (z / P) l (c - w P) else Lam w l (c - w P)) := by
  classical
  simp only [D, Lam, G]
  split_ifs <;> ring

theorem D_false_cons (z : ℝ) (P : ℕ) (l : List ℕ) (c : ℝ) :
    D w false z (P :: l) c = D w false z l c - D w true (z / P) l (c - w P) := by
  rw [D_cons, if_pos (show headOK false z P from trivial)]; rfl

theorem D_true_cons (z : ℝ) (P : ℕ) (l : List ℕ) (c : ℝ) :
    D w true z (P :: l) c = D w true z l c -
      (if (P : ℝ) ^ 3 ≤ z then D w false (z / P) l (c - w P) else Lam w l (c - w P)) := by
  rw [D_cons]
  by_cases h : (P : ℝ) ^ 3 ≤ z
  · rw [if_pos (show headOK true z P from h), if_pos h]; rfl
  · rw [if_neg (show ¬ headOK true z P from h), if_neg h]

/-! ## Unrolled forms over the suffixes `P :: l` of `ℓ` -/

/-- Sum of `f P l` over all decompositions `ℓ = pre ++ P :: l`. -/
def sumTails (f : ℕ → List ℕ → ℝ) : List ℕ → ℝ
  | [] => 0
  | P :: l => f P l + sumTails f l

theorem D_false_eq (z : ℝ) (ℓ : List ℕ) (c : ℝ) :
    D w false z ℓ c = sumTails (fun P l => -D w true (z / P) l (c - w P)) ℓ := by
  induction ℓ with
  | nil => simp [D_nil, sumTails]
  | cons P l ih => rw [D_false_cons, ih, sumTails]; ring

theorem D_true_eq (z : ℝ) (ℓ : List ℕ) (c : ℝ) :
    D w true z ℓ c = sumTails (fun P l => -(if (P : ℝ) ^ 3 ≤ z then D w false (z / P) l (c - w P)
      else Lam w l (c - w P))) ℓ := by
  induction ℓ with
  | nil => simp [D_nil, sumTails]
  | cons P l ih => rw [D_true_cons, ih, sumTails]; ring

/-- The two-step expansion: `D(-) = Σ_{P > P'} ([P'^3 ≤ z/P] D(-)(z/PP') + [P'^3 > z/P] Λ)`. -/
theorem D_false_two (z : ℝ) (ℓ : List ℕ) (c : ℝ) :
    D w false z ℓ c = sumTails (fun P l => sumTails (fun P' l' =>
      if (P' : ℝ) ^ 3 ≤ z / P then D w false (z / P / P') l' (c - w P - w P')
      else Lam w l' (c - w P - w P')) l) ℓ := by
  rw [D_false_eq]
  congr 1; funext P l
  rw [D_true_eq]
  induction l with
  | nil => simp [sumTails]
  | cons Q l ih =>
    simp only [sumTails] at ih ⊢
    rw [neg_add, ih, neg_neg]

theorem sumTails_nonneg (f : ℕ → List ℕ → ℝ) (ℓ : List ℕ) (h : ∀ P l, 0 ≤ f P l) :
    0 ≤ sumTails f ℓ := by
  induction ℓ with
  | nil => simp [sumTails]
  | cons P l ih => simp only [sumTails]; linarith [h P l]

theorem sumTails_mono (f g : ℕ → List ℕ → ℝ) (ℓ : List ℕ) (h : ∀ P l, f P l ≤ g P l) :
    sumTails f ℓ ≤ sumTails g ℓ := by
  induction ℓ with
  | nil => simp [sumTails]
  | cons P l ih => simp only [sumTails]; linarith [h P l]

/-! ## Nonnegativity of the boundary terms under (3.8)

`Hyp z ℓ c`: every pair-chain `p₁ > p₂ > ⋯ > p_{2k}` taken from `ℓ` whose first `2k-2` entries satisfy
Rosser's conditions relative to `z` has `c - Σ w(p_i) ≥ 0`. We encode chains recursively. -/

/-- `Hyp z ℓ c`: (3.8) for chains from `ℓ`, relative to level `z` and budget `c`. -/
def Hyp : ℝ → List ℕ → ℝ → Prop
  | z, ℓ, c => ∀ P l, (∃ pre, ℓ = pre ++ P :: l) → ∀ P' l', (∃ pre', l = pre' ++ P' :: l') →
      0 ≤ c - w P - w P' ∧ ((P' : ℝ) ^ 3 ≤ z / P → Hyp (z / P / P') l' (c - w P - w P'))
  termination_by _ ℓ _ => ℓ.length
  decreasing_by
    obtain ⟨pre, rfl⟩ := ‹∃ pre, ℓ = pre ++ P :: l›
    obtain ⟨pre', rfl⟩ := ‹∃ pre', l = pre' ++ P' :: l'›
    simp; omega

theorem sumTails_nonneg' (f : ℕ → List ℕ → ℝ) (ℓ : List ℕ)
    (h : ∀ P l, (∃ pre, ℓ = pre ++ P :: l) → 0 ≤ f P l) : 0 ≤ sumTails f ℓ := by
  induction ℓ with
  | nil => simp [sumTails]
  | cons P l ih =>
    simp only [sumTails]
    have h1 := h P l ⟨[], rfl⟩
    have h2 := ih (fun Q m ⟨pre, hpre⟩ => h Q m ⟨P :: pre, by rw [hpre]; rfl⟩)
    linarith

theorem sumTails_mono' (f g : ℕ → List ℕ → ℝ) (ℓ : List ℕ)
    (h : ∀ P l, (∃ pre, ℓ = pre ++ P :: l) → f P l ≤ g P l) : sumTails f ℓ ≤ sumTails g ℓ := by
  induction ℓ with
  | nil => simp [sumTails]
  | cons P l ih =>
    simp only [sumTails]
    have h1 := h P l ⟨[], rfl⟩
    have h2 := ih (fun Q m ⟨pre, hpre⟩ => h Q m ⟨P :: pre, by rw [hpre]; rfl⟩)
    linarith

theorem length_lt_of_tail {ℓ l : List ℕ} {P : ℕ} (h : ∃ pre, ℓ = pre ++ P :: l) : l.length < ℓ.length := by
  obtain ⟨pre, rfl⟩ := h; simp; omega

/-- **Boundary terms are nonnegative** under (3.8) (`Hyp`) and `w ≥ 0`. -/
theorem D_false_nonneg (hw : ∀ p, 0 ≤ w p) : ∀ (n : ℕ) (z : ℝ) (ℓ : List ℕ) (c : ℝ), ℓ.length ≤ n →
    Hyp w z ℓ c → 0 ≤ D w false z ℓ c := by
  intro n
  induction n with
  | zero =>
    intro z ℓ c hn _
    have : ℓ = [] := List.length_eq_zero_iff.1 (by omega)
    rw [this]; simp [D_nil]
  | succ n ih =>
    intro z ℓ c hn hH
    rw [D_false_two]
    apply sumTails_nonneg'
    intro P l hPl
    apply sumTails_nonneg'
    intro P' l' hPl'
    rw [Hyp] at hH
    obtain ⟨hc, hrec⟩ := hH P l hPl P' l' hPl'
    split_ifs with hcond
    · have hlen : l'.length ≤ n := by
        have h1 := length_lt_of_tail hPl
        have h2 := length_lt_of_tail hPl'
        omega
      exact ih _ _ _ hlen (hrec hcond)
    · exact Lam_nonneg w hw _ _ hc

/-- (3.8) at the top level: only the chains through a pair `P > P'` with `P'^3 ≤ z/P` (`j ≥ 2`). -/
def HypTop (z : ℝ) (ℓ : List ℕ) (c : ℝ) : Prop :=
  ∀ (P : ℕ) (l : List ℕ), (∃ pre, ℓ = pre ++ P :: l) → ∀ (P' : ℕ) (l' : List ℕ), (∃ pre', l = pre' ++ P' :: l') →
    (P' : ℝ) ^ 3 ≤ z / P → Hyp w (z / P / P') l' (c - w P - w P')

/-- The first-level boundary terms `J₁` (pairs `P > P'` with `P'^3 P > z`). -/
noncomputable def J1 (z : ℝ) (ℓ : List ℕ) (c : ℝ) : ℝ :=
  sumTails (fun P l => sumTails (fun P' l' =>
    if (P' : ℝ) ^ 3 ≤ z / P then 0 else Lam w l' (c - w P - w P')) l) ℓ

/-- **Greaves (3.18)**: `G(-) ≤ Λ − J₁`. -/
theorem G_false_le (hw : ∀ p, 0 ≤ w p) (z : ℝ) (ℓ : List ℕ) (c : ℝ) (hH : HypTop w z ℓ c) :
    G w false z ℓ c ≤ Lam w ℓ c - J1 w z ℓ c := by
  have hD : J1 w z ℓ c ≤ D w false z ℓ c := by
    rw [D_false_two, J1]
    apply sumTails_mono'
    intro P l hPl
    apply sumTails_mono'
    intro P' l' hPl'
    split_ifs with hcond
    · exact D_false_nonneg w hw _ _ _ _ le_rfl (hH P l hPl P' l' hPl' hcond)
    · exact le_rfl
  unfold D at hD
  linarith

/-! ## Lemma 3.1: evaluation of `J₁` and the pairing argument -/

theorem sumTails_append_two (f : ℕ → List ℕ → ℝ) (hf : ∀ P l, 2 ≤ l.length → f P l = 0)
    (m : List ℕ) (a b : ℕ) : sumTails f (m ++ [a, b]) = f a [b] + f b [] := by
  induction m with
  | nil => simp [sumTails]
  | cons P m ih =>
    show f P (m ++ [a, b]) + sumTails f (m ++ [a, b]) = _
    rw [ih, hf P _ (by simp)]; ring

theorem Lam_long' (l : List ℕ) (hl : 2 ≤ l.length) (c : ℝ) : Lam w l c = 0 := by
  match l, hl with
  | P :: Q :: l, _ => exact Lam_long w P Q l c

theorem sum_map_const_nat (m : List ℕ) (a : ℝ) : (m.map (fun _ : ℕ => a)).sum = m.length * a := by
  induction m with
  | nil => simp
  | cons x m ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; push_cast; ring

/-- `J₁` for `ℓ = pre ++ [Q₂, Q₁]`. -/
theorem J1_eval (z : ℝ) (pre : List ℕ) (Q2 Q1 : ℕ) (c : ℝ) :
    J1 w z (pre ++ [Q2, Q1]) c =
      ((pre ++ [Q2]).map (fun P : ℕ => if (Q1 : ℝ) ^ 3 ≤ z / P then 0 else c - w P - w Q1)).sum +
      (pre.map (fun P : ℕ => if (Q2 : ℝ) ^ 3 ≤ z / P then 0 else w Q1)).sum := by
  have hinner : ∀ (P : ℕ) (m : List ℕ), sumTails (fun P' l' =>
      if (P' : ℝ) ^ 3 ≤ z / P then 0 else Lam w l' (c - w P - w P')) (m ++ [Q2, Q1]) =
      (if (Q2 : ℝ) ^ 3 ≤ z / P then 0 else w Q1) + (if (Q1 : ℝ) ^ 3 ≤ z / P then 0 else c - w P - w Q1) := by
    intro P m
    rw [sumTails_append_two _ (fun P' l hl => by split_ifs <;> simp [Lam_long' w l hl])]
    simp [Lam_single, Lam_nil]
  unfold J1
  induction pre with
  | nil =>
    simp [sumTails, Lam_nil]
  | cons P pre ih =>
    show sumTails _ (pre ++ [Q2, Q1]) + sumTails _ (pre ++ [Q2, Q1]) = _
    rw [hinner P pre, ih]
    simp only [List.cons_append, List.map_cons, List.sum_cons]
    ring

/-- **Lemma 3.1 (list form).** For a strictly decreasing list `ℓ` with at least two primes, if the
Rosser sum is positive then `Q₁³Q₂ > z` and `G ≤ c − Σ_{p∈ℓ} (c − w p)`. -/
theorem G_pos_two (hw : ∀ p, 0 ≤ w p) (z : ℝ) (pre : List ℕ) (Q2 Q1 : ℕ) (c : ℝ)
    (hsort : (pre ++ [Q2, Q1]).Pairwise (· > ·)) (hQ1 : 0 < Q1)
    (hwc : ∀ p ∈ pre ++ [Q2, Q1], w p ≤ c)
    (hH : HypTop w z (pre ++ [Q2, Q1]) c) (hpos : 0 < G w false z (pre ++ [Q2, Q1]) c) :
    z < (Q1 : ℝ) ^ 3 * Q2 ∧
      G w false z (pre ++ [Q2, Q1]) c ≤ c - ((pre ++ [Q2, Q1]).map (fun p => c - w p)).sum := by
  have hG := G_false_le w hw z _ c hH
  rw [Lam_long' w _ (by simp), J1_eval] at hG
  -- order facts
  have hpw := List.pairwise_append.1 hsort
  have hQ21 : Q1 < Q2 := by
    have := hpw.2.1; simp at this; omega
  have hpre : ∀ P ∈ pre, Q2 < P := by
    intro P hP; have := hpw.2.2 P hP Q2 (by simp); omega
  have hQ2pos : (0 : ℝ) < Q2 := by exact_mod_cast (by omega : 0 < Q2)
  have hQ1pos : (0 : ℝ) < Q1 := by exact_mod_cast hQ1
  by_cases hcase : (Q1 : ℝ) ^ 3 ≤ z / Q2
  · -- then `G ≤ 0`
    exfalso
    -- `J₁ ≥ Σ_{P∈pre, Q₁³P>z} (c − w P) ≥ 0`
    have hT : 0 ≤ ((pre ++ [Q2]).map (fun P : ℕ => if (Q1 : ℝ) ^ 3 ≤ z / P then 0 else c - w P - w Q1)).sum +
        (pre.map (fun P : ℕ => if (Q2 : ℝ) ^ 3 ≤ z / P then 0 else w Q1)).sum := by
      rw [List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, if_pos hcase, add_zero]
      rw [← List.sum_map_add]
      apply List.sum_nonneg
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨P, hP, rfl⟩ := hx
      have hPQ := hpre P hP
      have hPpos : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
      split_ifs with h1 h2
      · simp
      · simp; exact hw Q1
      · exfalso
        apply h1
        have h3 : (Q1 : ℝ) ^ 3 < (Q2 : ℝ) ^ 3 := by
          have : (Q1 : ℝ) < Q2 := by exact_mod_cast hQ21
          exact pow_lt_pow_left₀ this hQ1pos.le (by norm_num)
        linarith
      · have := hwc P (by simp [hP]); linarith
    linarith
  · -- `Q₁³Q₂ > z`: all pairs qualify
    have hz : z < (Q1 : ℝ) ^ 3 * Q2 := by
      push Not at hcase; rwa [div_lt_iff₀ hQ2pos] at hcase
    refine ⟨hz, ?_⟩
    have hall1 : ∀ P ∈ pre ++ [Q2], ¬ (Q1 : ℝ) ^ 3 ≤ z / P := by
      intro P hP
      have hPQ : Q2 ≤ P := by
        rcases List.mem_append.1 hP with h | h
        · exact (hpre P h).le
        · simp at h; omega
      have hPpos : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
      rw [div_eq_mul_inv, not_le]
      rw [← div_eq_mul_inv, div_lt_iff₀ hPpos]
      have : (Q2 : ℝ) ≤ P := by exact_mod_cast hPQ
      nlinarith [pow_pos hQ1pos 3]
    have hall2 : ∀ P ∈ pre, ¬ (Q2 : ℝ) ^ 3 ≤ z / P := by
      intro P hP
      have hPQ := hpre P hP
      have hPpos : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
      rw [not_le, div_lt_iff₀ hPpos]
      have h1 : (Q1 : ℝ) ^ 3 ≤ (Q2 : ℝ) ^ 3 := by
        have : (Q1 : ℝ) ≤ Q2 := by exact_mod_cast hQ21.le
        exact pow_le_pow_left₀ hQ1pos.le this 3
      have h2 : (Q2 : ℝ) ≤ P := by exact_mod_cast hPQ.le
      nlinarith [pow_pos hQ1pos 3]
    have e1 : ((pre ++ [Q2]).map (fun P : ℕ => if (Q1 : ℝ) ^ 3 ≤ z / P then 0 else c - w P - w Q1)).sum =
        ((pre ++ [Q2]).map (fun P : ℕ => c - w P - w Q1)).sum := by
      congr 1; apply List.map_congr_left; intro P hP; rw [if_neg (hall1 P hP)]
    have e2 : (pre.map (fun P : ℕ => if (Q2 : ℝ) ^ 3 ≤ z / P then 0 else w Q1)).sum =
        (pre.map (fun _ : ℕ => w Q1)).sum := by
      congr 1; apply List.map_congr_left; intro P hP; rw [if_neg (hall2 P hP)]
    rw [e1, e2] at hG
    have e3 : ((pre ++ [Q2]).map (fun P : ℕ => c - w P - w Q1)).sum =
        ((pre ++ [Q2]).map (fun P : ℕ => c - w P)).sum - (pre.length + 1) * w Q1 := by
      simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil]
      have : ∀ m : List ℕ, (m.map (fun P : ℕ => c - w P - w Q1)).sum = (m.map (fun P : ℕ => c - w P)).sum -
          m.length * w Q1 := by
        intro m; induction m with
        | nil => simp
        | cons x m ihm => simp only [List.map_cons, List.sum_cons, List.length_cons, ihm]; push_cast; ring
      rw [this]; ring
    have e4 : (pre.map (fun _ : ℕ => w Q1)).sum = pre.length * w Q1 := by
      exact sum_map_const_nat pre (w Q1)
    have e5 : ((pre ++ [Q2, Q1]).map (fun p => c - w p)).sum =
        ((pre ++ [Q2]).map (fun P : ℕ => c - w P)).sum + (c - w Q1) := by
      simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil]; ring
    rw [e3, e4] at hG
    rw [e5]
    linarith

end Palprimes.Greaves
