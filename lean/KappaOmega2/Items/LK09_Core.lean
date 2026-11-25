import KappaOmega2.StatementsK
import KappaOmega2.LemmaR
import Palprimes.ExpSum.Collision

/-!
# LK09_Core: `g_J²` as a trigonometric polynomial with injective frequencies (shared by LK09 and QK03)

For `j < m`, `g_J(α) = P(γ) · M_W(b^j γ)` with `γ = b^{m−j} α` and `P(γ) = Π_{i<j} G_g(c'_i γ)`,
`c'_i = b^i + b^{ℓ+2j−1−i}`. Writing `M_W = G_{g'}` for the uniform weight `g' = 1/W` on `[0, W)`, squaring gives
`g_J(α)² = Σ_{(f, s)} w(f, s) e(V(f, s) γ)` with `V(f, s) = Σ_i f_i c'_i + s b^j`, `f_i ≤ 2b − 2`, `s ≤ 2W − 2`.
The frequencies are injective (`KappaOmega2.lemmaE`), `V < 2 W b^{2j}`, and `Σ w² = m_w(4)^j m_M(4)`.
-/

namespace KappaOmega2

namespace LK09

open Finset Palprimes

set_option linter.style.longLine false

/-- `(g ∗ g)(s)`, the inner sum of `mw4`. -/
noncomputable def cc (b : ℕ) (g : ℕ → ℝ) (s : ℕ) : ℝ :=
  ∑ i ∈ range (s + 1), if i < b ∧ s - i < b then g i * g (s - i) else 0

lemma mw4_eq (b : ℕ) (g : ℕ → ℝ) : mw4 b g = ∑ s ∈ range (2 * b - 1), cc b g s ^ 2 := rfl

lemma conv_fiber (b : ℕ) (g : ℕ → ℝ) (s : ℕ) :
    ∑ p ∈ (range b ×ˢ range b).filter (fun p : ℕ × ℕ => p.1 + p.2 = s), g p.1 * g p.2 = cc b g s := by
  unfold cc
  rw [← Finset.sum_filter]
  apply Finset.sum_nbij' (fun p => p.1) (fun i => (i, s - i))
  · intro p hp
    simp only [mem_filter, mem_product, mem_range] at hp ⊢
    omega
  · intro i hi
    simp only [mem_filter, mem_product, mem_range] at hi ⊢
    omega
  · intro p hp
    simp only [mem_filter, mem_product, mem_range] at hp
    ext
    · rfl
    · simp only; omega
  · intro i _; rfl
  · intro p hp
    simp only [mem_filter, mem_product, mem_range] at hp
    congr 2; omega

lemma Gsq (b : ℕ) (hb : 1 ≤ b) (g : ℕ → ℝ) (t : ℝ) :
    Gg b g t ^ 2 = ∑ s : Fin (2 * b - 1), (cc b g s : ℂ) * ee ((s : ℕ) * t) := by
  unfold Gg
  rw [sq, Finset.sum_mul_sum, ← Finset.sum_product']
  have hterm : ∀ p ∈ range b ×ˢ range b, ((g p.1 : ℂ) * ee (p.1 * t)) * ((g p.2 : ℂ) * ee (p.2 * t)) =
      ((g p.1 * g p.2 : ℝ) : ℂ) * ee (((p.1 + p.2 : ℕ) : ℝ) * t) := by
    intro p _
    rw [show (((p.1 + p.2 : ℕ) : ℝ) * t) = (p.1 : ℝ) * t + (p.2 : ℝ) * t by push_cast; ring, ee_add]
    push_cast; ring
  rw [Finset.sum_congr rfl hterm]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : ℕ × ℕ => p.1 + p.2) (t := range (2 * b - 1))
    (fun p hp => by simp only [mem_product, mem_range] at hp; simp only [mem_range]; omega)]
  rw [← Fin.sum_univ_eq_sum_range (fun s => ∑ p ∈ (range b ×ˢ range b).filter (fun p : ℕ × ℕ => p.1 + p.2 = s),
      ((g p.1 * g p.2 : ℝ) : ℂ) * ee (((p.1 + p.2 : ℕ) : ℝ) * t))]
  apply Finset.sum_congr rfl
  intro s _
  rw [← conv_fiber b g s]
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hps := (Finset.mem_filter.1 hp).2
  rw [← hps]; push_cast; ring

/-! ### The middle block as a digit sum -/

lemma Mmid_eq (W : ℕ) (β : ℝ) : Mmid W β = Gg W (fun _ => 1 / (W : ℝ)) β := by
  unfold Mmid Gg
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  push_cast
  ring

lemma cnt_card (W s : ℕ) :
    ((range (s + 1)).filter (fun i => i < W ∧ s - i < W)).card = min (s + 1) W - (s + 1 - W) := by
  have : (range (s + 1)).filter (fun i => i < W ∧ s - i < W) = Ico (s + 1 - W) (min (s + 1) W) := by
    ext i; simp only [mem_filter, mem_range, mem_Ico]; omega
  rw [this, Nat.card_Ico]

lemma ccW (W s : ℕ) : cc W (fun _ => 1 / (W : ℝ)) s =
    ((min (s + 1) W - (s + 1 - W) : ℕ) : ℝ) * (1 / (W : ℝ) * (1 / (W : ℝ))) := by
  unfold cc
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, cnt_card]

lemma sq_sum_formula (n : ℕ) :
    ∑ s ∈ range n, ((s + 1 : ℕ) : ℝ) ^ 2 = (n : ℝ) * (n + 1) * (2 * n + 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma sq_sum_c (n : ℕ) (c : ℝ) :
    ∑ s ∈ range n, (((s + 1 : ℕ) : ℝ) * c) ^ 2 = c ^ 2 * ((n : ℝ) * (n + 1) * (2 * n + 1) / 6) := by
  simp_rw [mul_pow]
  rw [← Finset.sum_mul, sq_sum_formula]
  ring

/-- `m_w(4)` of the uniform weight on `[0, W)` is `m_M(4) = (2W² + 1)/(3W³)`. -/
lemma mw4_mid (W : ℕ) (hW : 1 ≤ W) : mw4 W (fun _ => 1 / (W : ℝ)) = mM4 W := by
  obtain ⟨n, rfl⟩ : ∃ n, W = n + 1 := ⟨W - 1, by omega⟩
  rw [mw4_eq]
  simp_rw [ccW]
  rw [show 2 * (n + 1) - 1 = (n + 1) + n by omega, Finset.sum_range_add]
  set c : ℝ := 1 / ((n + 1 : ℕ) : ℝ) * (1 / ((n + 1 : ℕ) : ℝ)) with hc
  have h1 : ∀ s ∈ range (n + 1), (((min (s + 1) (n + 1) - (s + 1 - (n + 1)) : ℕ) : ℝ) * c) ^ 2 =
      (((s + 1 : ℕ) : ℝ) * c) ^ 2 := by
    intro s hs; simp only [mem_range] at hs
    rw [show min (s + 1) (n + 1) - (s + 1 - (n + 1)) = s + 1 by omega]
  have h2 : ∀ t ∈ range n, (((min (n + 1 + t + 1) (n + 1) - (n + 1 + t + 1 - (n + 1)) : ℕ) : ℝ) * c) ^ 2 =
      (((n - 1 - t + 1 : ℕ) : ℝ) * c) ^ 2 := by
    intro t ht; simp only [mem_range] at ht
    rw [show min (n + 1 + t + 1) (n + 1) - (n + 1 + t + 1 - (n + 1)) = n - 1 - t + 1 by omega]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2]
  rw [Finset.sum_range_reflect (fun t => (((t + 1 : ℕ) : ℝ) * c) ^ 2) n, sq_sum_c, sq_sum_c]
  unfold mM4
  rw [hc]
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  push_cast
  ring

/-! ### Frequencies and weights -/

/-- `c'_i = b^i + b^{ℓ+2j−1−i}`. -/
def cpos (b ℓ j i : ℕ) : ℕ := b ^ i + b ^ (ℓ + 2 * j - 1 - i)

/-- Index set `(f, s)`, `f_i ≤ 2b − 2`, `s ≤ 2W − 2`. -/
abbrev Idx (b W j : ℕ) := (Fin j → Fin (2 * b - 1)) × Fin (2 * W - 1)

/-- Weight `w(f, s) = Π_i (g ∗ g)(f_i) · (g' ∗ g')(s)`. -/
noncomputable def wt (b : ℕ) (g : ℕ → ℝ) (W j : ℕ) (x : Idx b W j) : ℝ :=
  (∏ i, cc b g (x.1 i)) * cc W (fun _ => 1 / (W : ℝ)) x.2

/-- Frequency `V(f, s) = Σ_i f_i c'_i + s b^j`. -/
def Vf (b ℓ j W : ℕ) (x : Idx b W j) : ℕ := ∑ i : Fin j, (x.1 i : ℕ) * cpos b ℓ j i + (x.2 : ℕ) * b ^ j

lemma mK_le (N : ℕ) : mK N ≤ N := by unfold mK; omega

lemma ellK_pos (N : ℕ) : 1 ≤ ellK N := by unfold ellK mK; omega

lemma cK_shift (b N j i : ℕ) (hj : j < mK N) (hi : i < j) :
    cK b N (mK N - j + i) = b ^ (mK N - j) * cpos b (ellK N) j i := by
  have hm := mK_le N
  unfold cK cpos ellK
  rw [if_pos (by omega), mul_add, ← pow_add, ← pow_add]
  congr 2 <;> omega

lemma gJK_eq (b : ℕ) (g : ℕ → ℝ) (N j : ℕ) (hj : j < mK N) (α : ℝ) :
    gJK b g N j α = (∏ i : Fin j, Gg b g ((cpos b (ellK N) j i : ℝ) * ((b : ℝ) ^ (mK N - j) * α))) *
      Gg (WK b N) (fun _ => 1 / (WK b N : ℝ)) ((b : ℝ) ^ j * ((b : ℝ) ^ (mK N - j) * α)) := by
  unfold gJK
  rw [Mmid_eq, Finset.prod_Ico_eq_prod_range, show mK N - (mK N - j) = j by omega, Finset.prod_range]
  have h1 : ∀ i : Fin j, Gg b g ((cK b N (mK N - j + (i : ℕ)) : ℝ) * α) =
      Gg b g ((cpos b (ellK N) j i : ℝ) * ((b : ℝ) ^ (mK N - j) * α)) := by
    intro i
    rw [cK_shift b N j i hj i.2]
    push_cast
    rw [mul_assoc, mul_left_comm]
  have h2 : (b : ℝ) ^ mK N * α = (b : ℝ) ^ j * ((b : ℝ) ^ (mK N - j) * α) := by
    rw [← mul_assoc, ← pow_add, show j + (mK N - j) = mK N by omega]
  rw [Finset.prod_congr rfl (fun i _ => h1 i), h2]

lemma sq_expand (b : ℕ) (hb : 1 ≤ b) (g : ℕ → ℝ) (ℓ j W : ℕ) (hW : 1 ≤ W) (γ : ℝ) :
    ((∏ i : Fin j, Gg b g ((cpos b ℓ j i : ℝ) * γ)) * Gg W (fun _ => 1 / (W : ℝ)) ((b : ℝ) ^ j * γ)) ^ 2 =
      ∑ x : Idx b W j, (wt b g W j x : ℂ) * ee ((Vf b ℓ j W x : ℝ) * γ) := by
  have hP2 : (∏ i : Fin j, Gg b g ((cpos b ℓ j i : ℝ) * γ)) ^ 2 =
      ∑ f : Fin j → Fin (2 * b - 1), ((∏ i, cc b g (f i) : ℝ) : ℂ) *
        ee (((∑ i : Fin j, (f i : ℕ) * cpos b ℓ j i : ℕ) : ℝ) * γ) := by
    rw [← Finset.prod_pow]
    simp_rw [Gsq b hb g]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    apply Finset.sum_congr rfl; intro f _
    rw [Finset.prod_mul_distrib, ← ee_sum]
    push_cast
    congr 2
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [mul_pow, hP2, Gsq W hW, Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  apply Finset.sum_congr rfl
  intro x _
  unfold wt Vf
  have : (((∑ i : Fin j, (x.1 i : ℕ) * cpos b ℓ j i + (x.2 : ℕ) * b ^ j : ℕ) : ℝ) * γ) =
      ((∑ i : Fin j, (x.1 i : ℕ) * cpos b ℓ j i : ℕ) : ℝ) * γ + ((x.2 : ℕ) : ℝ) * ((b : ℝ) ^ j * γ) := by
    push_cast; ring
  rw [this, ee_add]
  push_cast
  ring

/-- `g_J(α)² = Σ_x w(x) e(V(x) b^{m−j} α)`. -/
lemma gJK_sq (b : ℕ) (hb : 1 ≤ b) (g : ℕ → ℝ) (N j : ℕ) (hj : j < mK N) (α : ℝ) :
    gJK b g N j α ^ 2 = ∑ x : Idx b (WK b N) j, (wt b g (WK b N) j x : ℂ) *
      ee ((Vf b (ellK N) j (WK b N) x : ℝ) * ((b : ℝ) ^ (mK N - j) * α)) := by
  rw [gJK_eq b g N j hj α]
  exact sq_expand b hb g (ellK N) j (WK b N) (Nat.one_le_pow _ _ (by omega)) _

/-- `Σ_x w(x)² = m_w(4)^j m_M(4)`. -/
lemma sum_wt_sq (b : ℕ) (g : ℕ → ℝ) (W j : ℕ) (hW : 1 ≤ W) :
    ∑ x : Idx b W j, wt b g W j x ^ 2 = mw4 b g ^ j * mM4 W := by
  unfold wt
  simp_rw [mul_pow]
  rw [Fintype.sum_prod_type]
  dsimp only
  rw [← Finset.sum_mul_sum]
  congr 1
  · simp_rw [← Finset.prod_pow]
    rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum (fun _ : Fin j => (univ : Finset (Fin (2 * b - 1))))
      (fun _ s => cc b g s ^ 2)]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mw4_eq,
      Fin.sum_univ_eq_sum_range (fun s => cc b g s ^ 2)]
  · rw [← mw4_mid W hW, mw4_eq, Fin.sum_univ_eq_sum_range (fun s => cc W (fun _ => 1 / (W : ℝ)) s ^ 2)]

/-- Injectivity of the frequencies (Lemma E). -/
lemma Vf_inj (b ℓ j W : ℕ) (hb : 3 ≤ b) (hℓ : 1 ≤ ℓ) (hW : W = b ^ ℓ) (x y : Idx b W j)
    (hxy : Vf b ℓ j W x = Vf b ℓ j W y) : x = y := by
  rcases Nat.eq_zero_or_pos j with hj0 | hj1
  · subst hj0
    simp only [Vf, Finset.univ_eq_empty, Finset.sum_empty, zero_add, pow_zero, mul_one] at hxy
    apply Prod.ext
    · funext i; exact i.elim0
    · exact Fin.ext hxy
  set t : ℕ → ℤ := fun i => if h : i < j then ((x.1 ⟨i, h⟩ : ℕ) : ℤ) - ((y.1 ⟨i, h⟩ : ℕ) : ℤ) else 0 with ht
  set s : ℤ := ((x.2 : ℕ) : ℤ) - ((y.2 : ℕ) : ℤ) with hs
  have hbox : ∀ i, |t i| ≤ 2 * (b : ℤ) - 2 := by
    intro i
    simp only [ht]
    split_ifs with h
    · have h1 := (x.1 ⟨i, h⟩).isLt
      have h2 := (y.1 ⟨i, h⟩).isLt
      rw [abs_le]; constructor <;> omega
    · simp; omega
  have hWz : ((W : ℕ) : ℤ) = (b : ℤ) ^ ℓ := by rw [hW]; push_cast; rfl
  have hsb : |s| ≤ 2 * (b : ℤ) ^ (ℓ + 2 * j - 2 * j) - 2 := by
    rw [show ℓ + 2 * j - 2 * j = ℓ by omega, ← hWz]
    have h1 := x.2.isLt
    have h2 := y.2.isLt
    rw [abs_le]; constructor <;> omega
  have hcast := congrArg (fun n : ℕ => (n : ℤ)) hxy
  simp only [Vf, cpos] at hcast
  push_cast at hcast
  have heq : (∑ i ∈ range j, t i * ((b : ℤ) ^ (ℓ + 2 * j - 1 - i) + (b : ℤ) ^ i)) + s * (b : ℤ) ^ j = 0 := by
    rw [Finset.sum_range (fun i => t i * ((b : ℤ) ^ (ℓ + 2 * j - 1 - i) + (b : ℤ) ^ i))]
    have e : ∀ i : Fin j, t i * ((b : ℤ) ^ (ℓ + 2 * j - 1 - (i : ℕ)) + (b : ℤ) ^ (i : ℕ)) =
        ((x.1 i : ℕ) : ℤ) * ((b : ℤ) ^ (i : ℕ) + (b : ℤ) ^ (ℓ + 2 * j - 1 - (i : ℕ))) -
          ((y.1 i : ℕ) : ℤ) * ((b : ℤ) ^ (i : ℕ) + (b : ℤ) ^ (ℓ + 2 * j - 1 - (i : ℕ))) := by
      intro i
      simp only [ht, dif_pos i.2, Fin.eta]
      ring
    rw [Finset.sum_congr rfl (fun i _ => e i), Finset.sum_sub_distrib, hs]
    linear_combination hcast
  obtain ⟨ht0, hs0⟩ := KappaOmega2.lemmaE (b : ℤ) (by exact_mod_cast hb) j (ℓ + 2 * j) hj1 (by omega) t s hbox hsb heq
  apply Prod.ext
  · funext i
    have := ht0 i i.2
    simp only [ht, dif_pos i.2, Fin.eta, sub_eq_zero] at this
    exact Fin.ext (by exact_mod_cast this)
  · have : ((x.2 : ℕ) : ℤ) = ((y.2 : ℕ) : ℤ) := by rw [hs] at hs0; linarith
    exact Fin.ext (by exact_mod_cast this)

/-- The frequencies are `< 2 W b^{2j}`. -/
lemma Vf_lt (b ℓ j W : ℕ) (hb : 2 ≤ b) (hW : W = b ^ ℓ) (x : Idx b W j) :
    Vf b ℓ j W x < 2 * W * b ^ (2 * j) := by
  set G : ℤ := ∑ i ∈ range j, (b : ℤ) ^ i with hG
  set A : ℤ := (b : ℤ) ^ j with hA
  set B : ℤ := (b : ℤ) ^ (ℓ + j) with hB
  set C : ℤ := (b : ℤ) ^ (ℓ + 2 * j) with hC
  have hGm : G * ((b : ℤ) - 1) = A - 1 := geom_sum_mul _ _
  have hR : ∑ i ∈ range j, (b : ℤ) ^ (ℓ + 2 * j - 1 - i) = B * G := by
    rw [hG, Finset.mul_sum, ← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [hB, ← pow_add]
    congr 1
    omega
  have hAB : A * B = C := by rw [hA, hB, hC, ← pow_add]; congr 1; ring
  have hWz : ((W : ℕ) : ℤ) = (b : ℤ) ^ ℓ := by rw [hW]; push_cast; rfl
  have hWA : (W : ℤ) * A = B := by rw [hWz, hA, hB, ← pow_add]
  have hWC : (W : ℤ) * (b : ℤ) ^ (2 * j) = C := by rw [hWz, hC, ← pow_add]
  have hb1 : (0 : ℤ) ≤ (b : ℤ) - 1 := by omega
  have h1 : (∑ i : Fin j, ((x.1 i : ℕ) : ℤ) * ((b : ℤ) ^ (i : ℕ) + (b : ℤ) ^ (ℓ + 2 * j - 1 - (i : ℕ)))) ≤
      (2 * (b : ℤ) - 2) * (G + B * G) := by
    calc _ ≤ ∑ i : Fin j, (2 * (b : ℤ) - 2) * ((b : ℤ) ^ (i : ℕ) + (b : ℤ) ^ (ℓ + 2 * j - 1 - (i : ℕ))) := by
          apply Finset.sum_le_sum; intro i _
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have := (x.1 i).isLt; omega
      _ = (2 * (b : ℤ) - 2) * (G + B * G) := by
          rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun i => (b : ℤ) ^ i + (b : ℤ) ^ (ℓ + 2 * j - 1 - i)),
            Finset.sum_add_distrib, hR]
  have h2 : ((x.2 : ℕ) : ℤ) * A ≤ (2 * (W : ℤ) - 2) * A := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have := x.2.isLt; omega
  have hE : (2 * (b : ℤ) - 2) * (G + B * G) + (2 * (W : ℤ) - 2) * A = 2 * C - 2 := by
    linear_combination (2 + 2 * B) * hGm + 2 * hAB + 2 * hWA
  have : (Vf b ℓ j W x : ℤ) < 2 * (W : ℤ) * (b : ℤ) ^ (2 * j) := by
    simp only [Vf, cpos]
    push_cast
    rw [mul_assoc, hWC]
    linarith
  exact_mod_cast this

end LK09

end KappaOmega2
