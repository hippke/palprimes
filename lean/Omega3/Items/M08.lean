import Omega3.Statements
import Omega3.Items.M08_Comb

/-!
# M08: Greaves' Lemma 9 (Halberstam–Richert Reduction Lemma)

Proof plan in `Omega3/Items/M08_PLAN.md`. The exact recursions (I1), (I2), (R1), (R2) are in `M08_Comb`;
here the tree of differences `Δ = T − R` is summed (Step 6) with node errors from the crude bound `|T| ≤ 1/V`
and from Palprimes' Rosser asymptotics at `s = 2` (`f(2) = 0`). The hypothesis `Lemma7Stmt` is not used.
-/

set_option linter.style.longLine false

open Finset Real Filter

namespace Omega3.M08

open Palprimes Palprimes.Greaves Palprimes.MT Palprimes.E1

/-- Summing the children: `Σ_{p ∈ P} g(p)|c(p)| ≤ η (V(w) − V(Y))/V(Y)` if `P ⊆ [w, Y)` and
`|c(p)| ≤ η V(p)/V(Y/p)`. -/
theorem sum_children (b : ℕ) {w Y η : ℝ} (hwY : w ≤ Y) (hY : 0 < Y) (hη : 0 ≤ η) (P : Finset ℕ)
    (hP : P ⊆ primesIco w Y) (c : ℕ → ℝ) (hc : ∀ p ∈ P, |c p| ≤ η * VB b p / VB b (Y / p)) :
    ∑ p ∈ P, gB b p * |c p| ≤ η * (VB b w - VB b Y) / VB b Y := by
  have hVY := VB_pos' b Y
  have h1 : ∀ p ∈ P, gB b p * |c p| ≤ η / VB b Y * (gB b p * VB b p) := by
    intro p hp
    have hpp := ((mem_primesIco w Y p).1 (hP hp)).1
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
    have hVp := VB_pos' b (Y / p)
    have hanti : VB b Y ≤ VB b (Y / p) := VB_anti b (div_le_self hY.le hp1)
    have h2 : η * VB b p / VB b (Y / p) ≤ η * VB b p / VB b Y :=
      div_le_div_of_nonneg_left (mul_nonneg hη (VB_pos' b p).le) hVY hanti
    have hg := gB_nonneg b p
    calc gB b p * |c p| ≤ gB b p * (η * VB b p / VB b Y) :=
          mul_le_mul_of_nonneg_left (le_trans (hc p hp) h2) hg
      _ = η / VB b Y * (gB b p * VB b p) := by ring
  have h3 : ∑ p ∈ P, gB b p * VB b p ≤ VB b w - VB b Y := by
    rw [← telescope b hwY]
    exact sum_le_sum_of_subset_of_nonneg hP (fun p _ _ => mul_nonneg (gB_nonneg b p) (VB_pos' b p).le)
  calc ∑ p ∈ P, gB b p * |c p| ≤ ∑ p ∈ P, η / VB b Y * (gB b p * VB b p) := sum_le_sum h1
    _ = η / VB b Y * ∑ p ∈ P, gB b p * VB b p := by rw [mul_sum]
    _ ≤ η / VB b Y * (VB b w - VB b Y) := mul_le_mul_of_nonneg_left h3 (div_nonneg hη hVY.le)
    _ = η * (VB b w - VB b Y) / VB b Y := by ring

/-- The terms with `p = w` (at most one prime). -/
theorem deg_bound {w η₁ : ℝ} (hη₁ : 0 ≤ η₁) (D : Finset ℕ) (hD : ∀ p ∈ D, (p : ℝ) = w) (f : ℕ → ℝ)
    (hf : ∀ p ∈ D, |f p| ≤ η₁) : |∑ p ∈ D, f p| ≤ η₁ := by
  have hcard : D.card ≤ 1 := by
    rw [card_le_one]
    intro a ha c hc
    have := (hD a ha).trans (hD c hc).symm
    exact_mod_cast this
  calc |∑ p ∈ D, f p| ≤ ∑ p ∈ D, |f p| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ D, η₁ := sum_le_sum hf
    _ = D.card * η₁ := by rw [sum_const, nsmul_eq_mul]
    _ ≤ 1 * η₁ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hη₁
    _ = η₁ := one_mul η₁

/-- Splitting `w ≤ p` into `w < p` and `p = w`. -/
theorem split_le (A : Finset ℕ) (w : ℝ) (f : ℕ → ℝ) :
    ∑ p ∈ A.filter (fun p : ℕ => w ≤ (p : ℝ)), f p =
      ∑ p ∈ A.filter (fun p : ℕ => w < (p : ℝ)), f p +
        ∑ p ∈ (A.filter (fun p : ℕ => w ≤ (p : ℝ))).filter (fun p : ℕ => ¬ w < (p : ℝ)), f p := by
  rw [← sum_filter_add_sum_filter_not (A.filter (fun p : ℕ => w ≤ (p : ℝ))) (fun p : ℕ => w < (p : ℝ)) f,
    filter_filter]
  congr 2
  ext p
  simp only [mem_filter]
  constructor
  · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩; exact ⟨h1, h3.le, h3⟩

theorem mem_deg {A : Finset ℕ} {w : ℝ} {p : ℕ}
    (hp : p ∈ (A.filter (fun p : ℕ => w ≤ (p : ℝ))).filter (fun p : ℕ => ¬ w < (p : ℝ))) :
    p ∈ A ∧ (p : ℝ) = w := by
  simp only [mem_filter, not_lt] at hp
  exact ⟨hp.1.1, le_antisymm hp.2 hp.1.2⟩

/-- **Step 6**: the tree bound `|T^σ(Y, w) − R^σ(Y, w)| ≤ (η₁ + η₂) V(w)/V(Y)`. -/
theorem tree_bound (b : ℕ) {y W₀ η₁ η₂ : ℝ} (hW₀ : 1 ≤ W₀) (hη₁ : 0 ≤ η₁) (hη₂ : 0 ≤ η₂)
    (H1 : ∀ p : ℕ, p.Prime → W₀ ≤ p → (p : ℝ) < y → ∀ (σ : Bool) (Y' : ℝ), gB b p * |Tpm b σ Y' p| ≤ η₁)
    (H2 : ∀ Y' : ℝ, W₀ ^ 2 ≤ Y' → Y' ≤ y → |Tpm b false Y' (Real.sqrt Y')| ≤ η₂) :
    ∀ n : ℕ, ∀ (σ : Bool) (Y w : ℝ), 0 < Y → Y < 2 ^ n → Y ≤ y → W₀ ≤ w → w ≤ Y →
      (σ = false → w ≤ Real.sqrt Y) →
        |Tpm b σ Y w - R b σ Y w| ≤ (η₁ + η₂) * VB b w / VB b Y := by
  intro n
  induction n with
  | zero =>
    intro σ Y w _ hY1 _ hw hwY _
    simp at hY1; linarith
  | succ n ih =>
    intro σ Y w hY hYn hYy hw hwY hsq
    have hVY := VB_pos' b Y
    have hη : 0 ≤ η₁ + η₂ := by linarith
    have hVw := VB_pos' b w
    have hVwY : VB b Y ≤ VB b w := VB_anti b hwY
    -- the child bound, used for both signs
    have child : ∀ (τ : Bool) (p : ℕ), p.Prime → w < (p : ℝ) → (p : ℝ) ≤ Y / p →
        (τ = false → (p : ℝ) ≤ Real.sqrt (Y / p)) →
        |Tpm b τ (Y / p) p - R b τ (Y / p) p| ≤ (η₁ + η₂) * VB b p / VB b (Y / p) := by
      intro τ p hp hwp hpY hτ
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      have hp0 : (0 : ℝ) < p := by linarith
      apply ih τ (Y / p) p (div_pos hY hp0)
      · rw [div_lt_iff₀ hp0]
        have : (2 : ℝ) ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
        have h2n : (0 : ℝ) < 2 ^ n := by positivity
        nlinarith
      · exact le_trans (div_le_self hY.le (by linarith)) hYy
      · linarith
      · exact hpY
      · exact hτ
    cases σ with
    | true =>
      rw [I1 b hY w, R1 b hY w, split_le]
      set A := primesBelow (Y ^ ((1 : ℝ) / 3)) with hA
      have hmemA : ∀ p ∈ A, p.Prime ∧ (p : ℝ) ^ 3 < Y := by
        intro p hp
        have := (mem_primesBelow _ p).1 hp
        exact ⟨this.1, (lt_cbrt_iff hY.le (Nat.cast_nonneg p)).1 this.2⟩
      have hpy : ∀ p ∈ A, (p : ℝ) < Y := by
        intro p hp
        obtain ⟨hpp, h3⟩ := hmemA p hp
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
        have : (p : ℝ) ^ 1 ≤ (p : ℝ) ^ 3 := pow_le_pow_right₀ hp1 (by norm_num)
        rw [pow_one] at this; linarith
      set D := (A.filter (fun p : ℕ => w ≤ (p : ℝ))).filter (fun p : ℕ => ¬ w < (p : ℝ)) with hD
      set P := A.filter (fun p : ℕ => w < (p : ℝ)) with hP
      have hdeg : |∑ p ∈ D, gB b p * Tpm b false (Y / p) p| ≤ η₁ := by
        apply deg_bound hη₁ D (fun p hp => (mem_deg hp).2)
        intro p hp
        obtain ⟨hpA, hpw⟩ := mem_deg hp
        rw [abs_mul, abs_of_nonneg (gB_nonneg b p)]
        exact H1 p (hmemA p hpA).1 (by rw [hpw]; exact hw) (lt_of_lt_of_le (hpy p hpA) hYy) false (Y / p)
      have hPI : P ⊆ primesIco w Y := by
        intro p hp
        rw [hP, mem_filter] at hp
        rw [mem_primesIco]
        exact ⟨(hmemA p hp.1).1, hp.2.le, hpy p hp.1⟩
      have hch : ∀ p ∈ P, |Tpm b false (Y / p) p - R b false (Y / p) p| ≤
          (η₁ + η₂) * VB b p / VB b (Y / p) := by
        intro p hp
        rw [hP, mem_filter] at hp
        obtain ⟨hpp, h3⟩ := hmemA p hp.1
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
        have hpY : (p : ℝ) ^ 2 ≤ Y / p := by
          rw [le_div_iff₀ hp0]; nlinarith
        apply child false p hpp hp.2
        · rw [le_div_iff₀ hp0]
          have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
          nlinarith
        · intro _; exact Real.le_sqrt_of_sq_le hpY
      have hsum := sum_children b hwY hY hη P hPI _ hch
      have e : sigmaP b Y + (∑ p ∈ P, gB b p * Tpm b false (Y / p) p +
            ∑ p ∈ D, gB b p * Tpm b false (Y / p) p) -
          (sigmaP b Y + ∑ p ∈ P, gB b p * R b false (Y / p) p) =
          ∑ p ∈ D, gB b p * Tpm b false (Y / p) p +
            ∑ p ∈ P, gB b p * (Tpm b false (Y / p) p - R b false (Y / p) p) := by
        rw [show ∑ p ∈ P, gB b p * (Tpm b false (Y / p) p - R b false (Y / p) p) =
          ∑ p ∈ P, gB b p * Tpm b false (Y / p) p - ∑ p ∈ P, gB b p * R b false (Y / p) p by
            rw [← sum_sub_distrib]; exact sum_congr rfl (fun p _ => by ring)]
        ring
      rw [e]
      have habs : |∑ p ∈ P, gB b p * (Tpm b false (Y / p) p - R b false (Y / p) p)| ≤
          ∑ p ∈ P, gB b p * |Tpm b false (Y / p) p - R b false (Y / p) p| := by
        refine le_trans (abs_sum_le_sum_abs _ _) (le_of_eq (sum_congr rfl fun p _ => ?_))
        rw [abs_mul, abs_of_nonneg (gB_nonneg b p)]
      have hfin : η₁ + (η₁ + η₂) * (VB b w - VB b Y) / VB b Y ≤ (η₁ + η₂) * VB b w / VB b Y := by
        rw [mul_sub, sub_div, mul_div_assoc (η₁ + η₂) (VB b Y), div_self hVY.ne']
        linarith
      calc _ ≤ |∑ p ∈ D, gB b p * Tpm b false (Y / p) p| +
            |∑ p ∈ P, gB b p * (Tpm b false (Y / p) p - R b false (Y / p) p)| := abs_add_le _ _
        _ ≤ η₁ + (η₁ + η₂) * (VB b w - VB b Y) / VB b Y := add_le_add hdeg (le_trans habs hsum)
        _ ≤ _ := hfin
    | false =>
      have hwsq := hsq rfl
      rw [I2 b Y hwsq, R2 b hY w, split_le]
      set A := primesBelow (Real.sqrt Y) with hA
      have hmemA : ∀ p ∈ A, p.Prime ∧ (p : ℝ) ^ 2 < Y := by
        intro p hp
        have := (mem_primesBelow _ p).1 hp
        exact ⟨this.1, (Real.lt_sqrt (Nat.cast_nonneg p)).1 this.2⟩
      have hpy : ∀ p ∈ A, (p : ℝ) < Y := by
        intro p hp
        obtain ⟨hpp, h3⟩ := hmemA p hp
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
        have : (p : ℝ) ^ 1 ≤ (p : ℝ) ^ 2 := pow_le_pow_right₀ hp1 (by norm_num)
        rw [pow_one] at this; linarith
      set D := (A.filter (fun p : ℕ => w ≤ (p : ℝ))).filter (fun p : ℕ => ¬ w < (p : ℝ)) with hD
      set P := A.filter (fun p : ℕ => w < (p : ℝ)) with hP
      have hleaf : |Tpm b false Y (Real.sqrt Y)| ≤ η₂ := by
        apply H2 Y _ hYy
        have h0 : (0 : ℝ) ≤ W₀ := by linarith
        have : W₀ ≤ Real.sqrt Y := le_trans hw hwsq
        calc W₀ ^ 2 ≤ Real.sqrt Y ^ 2 := pow_le_pow_left₀ h0 this 2
          _ = Y := Real.sq_sqrt hY.le
      have hdeg : |∑ p ∈ D, gB b p * Tpm b true (Y / p) p| ≤ η₁ := by
        apply deg_bound hη₁ D (fun p hp => (mem_deg hp).2)
        intro p hp
        obtain ⟨hpA, hpw⟩ := mem_deg hp
        rw [abs_mul, abs_of_nonneg (gB_nonneg b p)]
        exact H1 p (hmemA p hpA).1 (by rw [hpw]; exact hw) (lt_of_lt_of_le (hpy p hpA) hYy) true (Y / p)
      have hPI : P ⊆ primesIco w Y := by
        intro p hp
        rw [hP, mem_filter] at hp
        rw [mem_primesIco]
        exact ⟨(hmemA p hp.1).1, hp.2.le, hpy p hp.1⟩
      have hch : ∀ p ∈ P, |Tpm b true (Y / p) p - R b true (Y / p) p| ≤
          (η₁ + η₂) * VB b p / VB b (Y / p) := by
        intro p hp
        rw [hP, mem_filter] at hp
        obtain ⟨hpp, h2⟩ := hmemA p hp.1
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
        apply child true p hpp hp.2
        · rw [le_div_iff₀ hp0]; nlinarith
        · intro h; exact absurd h (by simp)
      have hsum := sum_children b hwY hY hη P hPI _ hch
      have e : Tpm b false Y (Real.sqrt Y) + (∑ p ∈ P, gB b p * Tpm b true (Y / p) p +
            ∑ p ∈ D, gB b p * Tpm b true (Y / p) p) -
          ∑ p ∈ P, gB b p * R b true (Y / p) p =
          (Tpm b false Y (Real.sqrt Y) + ∑ p ∈ D, gB b p * Tpm b true (Y / p) p) +
            ∑ p ∈ P, gB b p * (Tpm b true (Y / p) p - R b true (Y / p) p) := by
        rw [show ∑ p ∈ P, gB b p * (Tpm b true (Y / p) p - R b true (Y / p) p) =
          ∑ p ∈ P, gB b p * Tpm b true (Y / p) p - ∑ p ∈ P, gB b p * R b true (Y / p) p by
            rw [← sum_sub_distrib]; exact sum_congr rfl (fun p _ => by ring)]
        ring
      rw [e]
      have habs : |∑ p ∈ P, gB b p * (Tpm b true (Y / p) p - R b true (Y / p) p)| ≤
          ∑ p ∈ P, gB b p * |Tpm b true (Y / p) p - R b true (Y / p) p| := by
        refine le_trans (abs_sum_le_sum_abs _ _) (le_of_eq (sum_congr rfl fun p _ => ?_))
        rw [abs_mul, abs_of_nonneg (gB_nonneg b p)]
      have hfin : (η₂ + η₁) + (η₁ + η₂) * (VB b w - VB b Y) / VB b Y ≤ (η₁ + η₂) * VB b w / VB b Y := by
        rw [mul_sub, sub_div, mul_div_assoc (η₁ + η₂) (VB b Y), div_self hVY.ne']
        linarith
      calc _ ≤ |Tpm b false Y (Real.sqrt Y) + ∑ p ∈ D, gB b p * Tpm b true (Y / p) p| +
            |∑ p ∈ P, gB b p * (Tpm b true (Y / p) p - R b true (Y / p) p)| := abs_add_le _ _
        _ ≤ (η₂ + η₁) + (η₁ + η₂) * (VB b w - VB b Y) / VB b Y :=
            add_le_add (le_trans (abs_add_le _ _) (add_le_add hleaf hdeg)) (le_trans habs hsum)
        _ ≤ _ := hfin

/-! ## Analytic inputs for the root -/

theorem leaf_small (b : ℕ) {y W₀ ε' z₀ : ℝ} (hW4 : 4 ≤ W₀) (hWz : |z₀| + 1 ≤ W₀ ^ 2) (hy1 : 1 ≤ y)
    (hhalf : VB b (W₀ / 2) ≤ 6 * VB b W₀) (hε' : 0 < ε')
    (hz₀ : ∀ z : ℝ, z₀ ≤ z → |Sminus b z 2| ≤ ε' * VB b (Real.sqrt z)) :
    ∀ Y' : ℝ, W₀ ^ 2 ≤ Y' → Y' ≤ y →
      |Tpm b false Y' (Real.sqrt Y')| ≤ 6 * ε' * VB b W₀ + 2 / (W₀ * VB b y) := by
  intro Y' hY' hY'y
  have hW16 : (16 : ℝ) ≤ W₀ ^ 2 := by nlinarith
  have hW0 : 0 < W₀ := by linarith
  have hL := leaf_bound b (by linarith : (2 : ℝ) ≤ Y')
  set z : ℝ := (⌈Y'⌉₊ : ℝ) - 1 with hz
  have hz1 : Y' - 1 ≤ z := by rw [hz]; linarith [Nat.le_ceil Y']
  have hz2 : z < Y' := by rw [hz]; linarith [Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ Y')]
  have hzz₀ : z₀ ≤ z := by linarith [le_abs_self z₀]
  have hR := hz₀ z hzz₀
  have hsz : W₀ / 2 ≤ Real.sqrt z := by
    apply Real.le_sqrt_of_sq_le
    have : (W₀ / 2) ^ 2 = W₀ ^ 2 / 4 := by ring
    linarith
  have hszy : Real.sqrt z ≤ y := by
    have hyy : y ≤ y ^ 2 := le_self_pow₀ hy1 (by norm_num)
    calc Real.sqrt z ≤ Real.sqrt y := Real.sqrt_le_sqrt (by linarith)
      _ ≤ Real.sqrt (y ^ 2) := Real.sqrt_le_sqrt hyy
      _ = y := Real.sqrt_sq (by linarith)
  have hVy := VB_pos' b y
  have hVz1 : VB b (Real.sqrt z) ≤ 6 * VB b W₀ := le_trans (VB_anti b hsz) hhalf
  have hVz2 : VB b y ≤ VB b (Real.sqrt z) := VB_anti b hszy
  have hA : |Sminus b z 2| ≤ 6 * ε' * VB b W₀ := by
    calc |Sminus b z 2| ≤ ε' * VB b (Real.sqrt z) := hR
      _ ≤ ε' * (6 * VB b W₀) := mul_le_mul_of_nonneg_left hVz1 hε'.le
      _ = 6 * ε' * VB b W₀ := by ring
  have hB : 1 / (Real.sqrt z * VB b (Real.sqrt z)) ≤ 2 / (W₀ * VB b y) := by
    rw [show (2 : ℝ) / (W₀ * VB b y) = 1 / (W₀ / 2 * VB b y) by field_simp]
    exact one_div_le_one_div_of_le (by positivity) (mul_le_mul hsz hVz2 hVy.le (Real.sqrt_nonneg _))
  linarith

theorem ratio_le (b : ℕ) {y W₀ s κ : ℝ} (hs0 : 0 < s) (hL0 : 0 < Real.log W₀)
    (hlogW : Real.log y = s * Real.log W₀)
    (h1 : VB b W₀ * Real.log W₀ ≤ (1 + 1 / 2) * κ) (h2 : (1 - 1 / 2) * κ ≤ VB b y * Real.log y) :
    VB b W₀ ≤ 3 * s * VB b y := by
  rw [hlogW] at h2
  have h3 : VB b W₀ * Real.log W₀ * s ≤ (3 * s * VB b y * Real.log W₀) * s := by
    have : (1 + 1 / 2) * κ * s ≤ 3 * s * ((1 - 1 / 2) * κ) := by ring_nf; rfl
    have h4 : 3 * s * ((1 - 1 / 2) * κ) ≤ 3 * s * (VB b y * (s * Real.log W₀)) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h5 : VB b W₀ * Real.log W₀ * s ≤ (1 + 1 / 2) * κ * s := mul_le_mul_of_nonneg_right h1 hs0.le
    calc VB b W₀ * Real.log W₀ * s ≤ 3 * s * (VB b y * (s * Real.log W₀)) := by linarith
      _ = (3 * s * VB b y * Real.log W₀) * s := by ring
  exact le_of_mul_le_mul_right (le_of_mul_le_mul_right h3 hs0) hL0

theorem half_le (b : ℕ) {W₀ κ : ℝ} (hW4 : 4 ≤ W₀) (hL0 : 0 < Real.log W₀)
    (h1 : VB b (W₀ / 2) * Real.log (W₀ / 2) ≤ (1 + 1 / 2) * κ) (h2 : (1 - 1 / 2) * κ ≤ VB b W₀ * Real.log W₀) :
    VB b (W₀ / 2) ≤ 6 * VB b W₀ := by
  have hW0 : 0 < W₀ := by linarith
  have hl2 : Real.log W₀ / 2 ≤ Real.log (W₀ / 2) := by
    rw [Real.log_div hW0.ne' (by norm_num)]
    have : Real.log 4 ≤ Real.log W₀ := Real.log_le_log (by norm_num) hW4
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith
  have hV2 := VB_pos' b (W₀ / 2)
  have h3 : VB b (W₀ / 2) * (Real.log W₀ / 2) ≤ VB b (W₀ / 2) * Real.log (W₀ / 2) :=
    mul_le_mul_of_nonneg_left hl2 hV2.le
  have : VB b (W₀ / 2) * Real.log W₀ ≤ 6 * VB b W₀ * Real.log W₀ := by linarith
  exact le_of_mul_le_mul_right this hL0

theorem small_le (b : ℕ) {y W₀ s κ ε δ : ℝ} (hs0 : 0 < s) (hκ0 : 0 < κ) (hε : 0 < ε) (hW0 : 0 < W₀)
    (hδ : δ = ε * κ ^ 2 / (24 * s ^ 2)) (hlogW : Real.log y = s * Real.log W₀)
    (h1 : (1 - 1 / 2) * κ ≤ VB b y * Real.log y) (h2 : Real.log W₀ ^ 2 / (1 * W₀ + 0) < δ) :
    6 < ε * W₀ * VB b y ^ 2 := by
  rw [hlogW] at h1
  have hk : 0 ≤ (1 - 1 / 2) * κ := by positivity
  have h1sq : ((1 - 1 / 2) * κ) ^ 2 ≤ (VB b y * (s * Real.log W₀)) ^ 2 := pow_le_pow_left₀ hk h1 2
  simp only [one_mul, add_zero] at h2
  rw [div_lt_iff₀ hW0] at h2
  have hVy := VB_pos' b y
  have h3 : (VB b y * (s * Real.log W₀)) ^ 2 < VB b y ^ 2 * s ^ 2 * (δ * W₀) := by
    have : (VB b y * (s * Real.log W₀)) ^ 2 = VB b y ^ 2 * s ^ 2 * Real.log W₀ ^ 2 := by ring
    rw [this]
    exact mul_lt_mul_of_pos_left h2 (by positivity)
  have h4 : VB b y ^ 2 * s ^ 2 * (δ * W₀) = (ε * W₀ * VB b y ^ 2) * (κ ^ 2 / 24) := by
    rw [hδ]; field_simp
  have h5 : 6 * (κ ^ 2 / 24) = ((1 - 1 / 2) * κ) ^ 2 := by ring
  have hκ2 : 0 < κ ^ 2 / 24 := by positivity
  have h6 : 6 * (κ ^ 2 / 24) < (ε * W₀ * VB b y ^ 2) * (κ ^ 2 / 24) := by linarith
  exact lt_of_mul_lt_mul_right h6 hκ2.le

end Omega3.M08

namespace Omega3

open Palprimes Palprimes.Greaves Palprimes.MT Palprimes.E1 Omega3.M08

theorem itemM08 : ItemM08 := by
  intro b hb _h7 s hs plus hplus ε hε
  have hs0 : 0 < s := by linarith
  set κ := kappaB b with hκ
  have hκ0 : 0 < κ := kappaB_pos b
  obtain ⟨x₀, hx₀1, hx₀⟩ := VB_log_bounds b hb (by norm_num : (0 : ℝ) < 1 / 2)
  set ε' := ε / (36 * s) with hε'
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨z₀, hz₀⟩ := rosserAsymp_of_two_le b hb ε' hε'0
  have hz₀' : ∀ z : ℝ, z₀ ≤ z → |Sminus b z 2| ≤ ε' * VB b (Real.sqrt z) := by
    intro z hz
    have hR := (hz₀ z hz).2 2 le_rfl (by norm_num)
    rwa [fjr_le_two le_rfl, mul_zero, sub_zero, ← Real.sqrt_eq_rpow] at hR
  have hlim := tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  set δ := ε * κ ^ 2 / (24 * s ^ 2) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨U₀, hU₀⟩ := eventually_atTop.1 ((tendsto_order.1 hlim).2 δ hδ0)
  set U := max (max 4 (2 * x₀)) (max (Real.sqrt (|z₀| + 1)) U₀) with hU
  have hU4 : 4 ≤ U := le_trans (le_max_left _ _) (le_max_left _ _)
  have hU0 : 0 ≤ U := by linarith
  refine ⟨U ^ s, fun y hy => ?_⟩
  set W₀ := y ^ (1 / s) with hW₀
  have hy1 : 1 ≤ y := le_trans (Real.one_le_rpow (by linarith) hs0.le) hy
  have hy0 : 0 < y := by linarith
  have hWU : U ≤ W₀ := by
    have : (U ^ s) ^ (1 / s) ≤ y ^ (1 / s) := Real.rpow_le_rpow (by positivity) hy (by positivity)
    rwa [← Real.rpow_mul hU0, mul_one_div_cancel hs0.ne', Real.rpow_one] at this
  have hW4 : 4 ≤ W₀ := le_trans hU4 hWU
  have hWx : 2 * x₀ ≤ W₀ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hWU
  have hWz : Real.sqrt (|z₀| + 1) ≤ W₀ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hWU
  have hWU₀ : U₀ ≤ W₀ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hWU
  have hWz2 : |z₀| + 1 ≤ W₀ ^ 2 := by
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hWz 2
    rwa [Real.sq_sqrt (by positivity)] at this
  have hWy : W₀ ≤ y := by
    have := Real.rpow_le_rpow_of_exponent_le hy1 (show 1 / s ≤ 1 by rw [div_le_one hs0]; linarith)
    rwa [Real.rpow_one] at this
  have hW0 : 0 < W₀ := by linarith
  have hlogW : Real.log y = s * Real.log W₀ := by
    rw [hW₀, Real.log_rpow hy0]; field_simp
  have hL0 : 0 < Real.log W₀ := Real.log_pos (by linarith)
  have hVy := VB_pos' b y
  have hVW := VB_pos' b W₀
  have hx₀W : x₀ ≤ W₀ := by linarith
  have hx₀y : x₀ ≤ y := le_trans hx₀W hWy
  have hMy := hx₀ y hx₀y
  have hMW := hx₀ W₀ hx₀W
  have hratio : VB b W₀ ≤ 3 * s * VB b y := ratio_le b hs0 hL0 hlogW hMW.2 hMy.1
  have hhalf : VB b (W₀ / 2) ≤ 6 * VB b W₀ :=
    half_le b hW4 hL0 (hx₀ (W₀ / 2) (by linarith)).2 hMW.1
  have hsmall : 6 < ε * W₀ * VB b y ^ 2 := small_le b hs0 hκ0 hε hW0 hδ hlogW hMy.1 (hU₀ W₀ hWU₀)
  -- node errors
  set η₁ := 1 / (W₀ * VB b y) with hη₁
  set η₂ := 6 * ε' * VB b W₀ + 2 / (W₀ * VB b y) with hη₂
  have hη₁0 : 0 ≤ η₁ := by positivity
  have hη₂0 : 0 ≤ η₂ := by positivity
  have H1 : ∀ p : ℕ, p.Prime → W₀ ≤ p → (p : ℝ) < y → ∀ (σ : Bool) (Y' : ℝ),
      gB b p * |Tpm b σ Y' p| ≤ η₁ := by
    intro p hp hWp hpy σ Y'
    have hg : gB b p ≤ 1 / W₀ := by
      unfold gB; split_ifs
      · exact one_div_le_one_div_of_le hW0 hWp
      · positivity
    have hT : |Tpm b σ Y' p| ≤ 1 / VB b y :=
      le_trans (abs_Tpm_le b σ Y' p) (one_div_le_one_div_of_le hVy (VB_anti b hpy.le))
    calc gB b p * |Tpm b σ Y' p| ≤ (1 / W₀) * (1 / VB b y) :=
          mul_le_mul hg hT (abs_nonneg _) (by positivity)
      _ = η₁ := by rw [hη₁, one_div_mul_one_div]
  have H2 := leaf_small b hW4 hWz2 hy1 hhalf hε'0 hz₀'
  -- the root of the tree
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt y (by norm_num : (1 : ℝ) < 2)
  have hroot := tree_bound b (by linarith : (1 : ℝ) ≤ W₀) hη₁0 hη₂0 H1 H2 n plus y W₀ hy0 hn le_rfl le_rfl hWy
    (by
      intro hpf
      have hs2 := hplus hpf
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hy1 (by rw [div_le_div_iff₀ hs0 (by norm_num)]; linarith))
  rw [T9sum_eq_R]
  have hηy : η₁ + η₂ ≤ ε * VB b y := by
    have e1 : 6 * ε' * VB b W₀ ≤ ε / 2 * VB b y := by
      have : 6 * ε' * VB b W₀ ≤ 6 * ε' * (3 * s * VB b y) := mul_le_mul_of_nonneg_left hratio (by positivity)
      have e : 6 * ε' * (3 * s * VB b y) = ε / 2 * VB b y := by rw [hε']; field_simp; ring
      linarith
    have e2 : 3 / (W₀ * VB b y) ≤ ε / 2 * VB b y := by
      rw [div_le_iff₀ (by positivity)]
      have : ε / 2 * VB b y * (W₀ * VB b y) = (ε * W₀ * VB b y ^ 2) / 2 := by ring
      rw [this]; linarith
    have e3 : η₁ + η₂ = 6 * ε' * VB b W₀ + 3 / (W₀ * VB b y) := by
      rw [hη₁, hη₂]; ring
    linarith
  calc |Tpm b plus y W₀ - R b plus y W₀| ≤ (η₁ + η₂) * VB b W₀ / VB b y := hroot
    _ ≤ ε * VB b y * VB b W₀ / VB b y := by
        apply div_le_div_of_nonneg_right _ hVy.le
        exact mul_le_mul_of_nonneg_right hηy hVW.le
    _ = ε * VB b W₀ := by field_simp

end Omega3
