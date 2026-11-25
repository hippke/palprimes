import Omega3.Statements
import Palprimes.ExpSum.Farey

/-!
# L09: Lemma 2.9_w (inner large sieve with the exact fourth moment), constant 6(4D² + 2b·b^{2j})

Plan in `L09_PLAN.md`: `g_J(α) = P(b^{N−j}α)`, `P² = Σ_f w_f e(Y'(f)·)` with injective frequencies `Y'(f) < 2b^{2j+1}`,
Palprimes `large_sieve` (via a weighted copy of `ls_step`), `Σ w_f² = m_w(4)^j`.
-/

namespace Omega3

open Finset Palprimes

set_option linter.style.longLine false

namespace L09

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

lemma cK_shift (b N j i : ℕ) (hi : i < j) (hjN : j ≤ N) :
    cK b N (N - j + i) = b ^ (N - j) * cK b j i := by
  unfold cK
  rw [if_pos (by omega), if_pos hi, mul_add, ← pow_add, ← pow_add]
  congr 2 <;> omega

lemma csum (b j : ℕ) (hb : 2 ≤ b) :
    ((b : ℤ) - 1) * ∑ i ∈ range j, (cK b j i : ℤ) ≤ (b : ℤ) ^ (2 * j + 1) - 1 := by
  have e1 : ∀ i ∈ range j, cK b j i = b ^ i + b ^ (2 * j - i) := fun i hi => by
    simp [cK, mem_range.1 hi]
  have hinj : Set.InjOn (fun i => 2 * j - i) ((range j : Finset ℕ) : Set ℕ) := by
    intro x hx y hy hxy
    simp only [coe_range, Set.mem_Iio] at hx hy
    simp only at hxy; omega
  have hdisj : Disjoint (range j) ((range j).image (fun i => 2 * j - i)) := by
    rw [Finset.disjoint_left]
    intro a ha hb'
    obtain ⟨k, hk, hka⟩ := mem_image.1 hb'
    simp only [mem_range] at ha hk
    omega
  have hS : ∑ i ∈ range j, cK b j i = ∑ l ∈ range j ∪ (range j).image (fun i => 2 * j - i), b ^ l := by
    rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib, Finset.sum_union hdisj,
      Finset.sum_image (f := fun l => b ^ l) hinj]
  have hsub : range j ∪ (range j).image (fun i => 2 * j - i) ⊆ range (2 * j + 1) := by
    intro l hl
    rcases mem_union.1 hl with h | h
    · simp only [mem_range] at h ⊢; omega
    · obtain ⟨k, hk, rfl⟩ := mem_image.1 h; simp only [mem_range] at hk ⊢; omega
  have h1 : (∑ i ∈ range j, (cK b j i : ℤ)) ≤ ∑ l ∈ range (2 * j + 1), (b : ℤ) ^ l := by
    have : (∑ i ∈ range j, (cK b j i : ℤ)) = ((∑ i ∈ range j, cK b j i : ℕ) : ℤ) := by push_cast; rfl
    rw [this, hS]; push_cast
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  have h2 : (∑ l ∈ range (2 * j + 1), (b : ℤ) ^ l) * ((b : ℤ) - 1) = (b : ℤ) ^ (2 * j + 1) - 1 :=
    geom_sum_mul _ _
  have hb1 : (0 : ℤ) ≤ (b : ℤ) - 1 := by omega
  nlinarith

lemma sq_sum_le_one {X : Type*} (s : Finset X) (f : X → ℝ) (hs : s.card ≤ 1) :
    (∑ x ∈ s, f x) ^ 2 = ∑ x ∈ s, f x ^ 2 := by
  classical
  rcases Finset.eq_empty_or_nonempty s with h | ⟨a, ha⟩
  · simp [h]
  · have : s = {a} := Finset.eq_singleton_iff_unique_mem.2 ⟨ha, fun x hx => Finset.card_le_one.1 hs x hx a ha⟩
    simp [this]

/-- Weighted copy of Palprimes `ls_step`. -/
theorem ls_w (b m : ℕ) (X : Type*) [Fintype X] (w : X → ℝ) (Y' : X → ℕ) (N1 : ℕ)
    (hY' : ∀ x, Y' x < N1) (R : ℕ) (hR : 1 ≤ R) (Qs : Finset ℕ)
    (hQs : ∀ q ∈ Qs, R ≤ q ∧ q ≤ 2 * R ∧ Nat.Coprime q b) (β : ℝ) :
    ∑ q ∈ Qs, ∑ h ∈ redRes q, ‖∑ x : X, (w x : ℂ) * ee (((b ^ m * Y' x : ℕ) : ℝ) * ((h : ℝ) / q + β))‖ ^ 2 ≤
      (4 * N1 + 12 * (R : ℝ) ^ 2 + 2) *
        ∑ n ∈ range N1, (∑ x ∈ (univ : Finset X).filter (fun x => Y' x = n), w x) ^ 2 := by
  classical
  set pts := Qs.sigma (fun q => redRes q)
  set xp : (Σ _ : ℕ, ℕ) → ℝ := fun p => (b : ℝ) ^ m * ((p.2 : ℝ) / p.1 + β)
  set a : ℕ → ℂ := fun n => ((∑ x ∈ (univ : Finset X).filter (fun x => Y' x = n), w x : ℝ) : ℂ)
  have hterm : ∀ (α : ℝ) (n : ℕ), ∑ x ∈ (univ : Finset X).filter (fun x => Y' x = n),
      (w x : ℂ) * ee (((b ^ m * Y' x : ℕ) : ℝ) * α) = a n * ee ((n : ℝ) * ((b : ℝ) ^ m * α)) := by
    intro α n
    rw [Finset.sum_congr rfl (g := fun x => (w x : ℂ) * ee ((n : ℝ) * ((b : ℝ) ^ m * α))) (fun x hx => by
      rw [(Finset.mem_filter.1 hx).2]; congr 2; push_cast; ring)]
    rw [← Finset.sum_mul]
    simp only [a]; push_cast; rfl
  have hexp : ∀ α : ℝ, ∑ x : X, (w x : ℂ) * ee (((b ^ m * Y' x : ℕ) : ℝ) * α) =
      ∑ n ∈ range N1, a n * ee ((n : ℝ) * ((b : ℝ) ^ m * α)) := by
    intro α
    rw [← Finset.sum_fiberwise_of_maps_to (g := Y') (t := range N1)
      (fun x _ => mem_range.2 (hY' x))]
    exact Finset.sum_congr rfl (fun n _ => hterm α n)
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hδ : (0 : ℝ) < 1 / (4 * (R : ℝ) ^ 2) := by positivity
  have hsep : ∀ i ∈ pts, ∀ j ∈ pts, i ≠ j → 1 / (4 * (R : ℝ) ^ 2) ≤ distZ (xp i - xp j) := by
    rintro ⟨q, h⟩ hi ⟨q', h'⟩ hj hij
    rw [Finset.mem_sigma] at hi hj
    obtain ⟨hq1, hq2, hqb⟩ := hQs q hi.1
    obtain ⟨hq1', hq2', hqb'⟩ := hQs q' hj.1
    have hq0 : 0 < q := by omega
    have hq0' : 0 < q' := by omega
    set h1 := b ^ m * h % q
    set h1' := b ^ m * h' % q'
    have hmem : h1 ∈ redRes q := by
      rw [← twist_bij b m q hqb]; exact Finset.mem_image_of_mem _ hi.2
    have hmem' : h1' ∈ redRes q' := by
      rw [← twist_bij b m q' hqb']; exact Finset.mem_image_of_mem _ hj.2
    have hne : (q, h1) ≠ (q', h1') := by
      intro heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, hh⟩ := heq
      apply hij
      have hinj : Set.InjOn (fun h => b ^ m * h % q) (redRes q) := by
        rw [← Finset.card_image_iff, twist_bij b m q hqb]
      obtain rfl : h = h' := hinj hi.2 hj.2 hh
      rfl
    have hfs := farey_spacing R hR 0 (q, h1) (q', h1')
      ⟨by rw [mem_Icc]; exact ⟨hq1, hq2⟩, hmem⟩ ⟨by rw [mem_Icc]; exact ⟨hq1', hq2'⟩, hmem'⟩ hne
    simp only [add_zero] at hfs
    have hdec : ∀ (q h : ℕ), 0 < q → (b : ℝ) ^ m * ((h : ℝ) / q) =
        ((b ^ m * h % q : ℕ) : ℝ) / q + ((b ^ m * h / q : ℕ) : ℝ) := by
      intro q h hq
      have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
      have := Nat.mod_add_div (b ^ m * h) q
      have h2 : ((b ^ m * h : ℕ) : ℝ) = ((b ^ m * h % q : ℕ) : ℝ) + q * ((b ^ m * h / q : ℕ) : ℝ) := by
        exact_mod_cast this.symm
      calc (b : ℝ) ^ m * ((h : ℝ) / q) = ((b ^ m * h : ℕ) : ℝ) / q := by push_cast; ring
        _ = (((b ^ m * h % q : ℕ) : ℝ) + q * ((b ^ m * h / q : ℕ) : ℝ)) / q := by rw [h2]
        _ = _ := by rw [add_div, mul_div_cancel_left₀ _ hq']
    have : xp ⟨q, h⟩ - xp ⟨q', h'⟩ = ((h1 : ℝ) / q - (h1' : ℝ) / q') +
        (((b ^ m * h / q : ℕ) : ℤ) - ((b ^ m * h' / q' : ℕ) : ℤ) : ℤ) := by
      simp only [xp]
      rw [mul_add, mul_add, hdec q h hq0, hdec q' h' hq0']
      simp only [Int.cast_sub, Int.cast_natCast]
      ring
    rw [this, distZ_add_int]
    exact hfs
  have hls := large_sieve pts xp _ hδ hsep N1 a
  have hsq : ∑ n ∈ range N1, ‖a n‖ ^ 2 =
      ∑ n ∈ range N1, (∑ x ∈ (univ : Finset X).filter (fun x => Y' x = n), w x) ^ 2 := by
    apply Finset.sum_congr rfl; intro n _
    simp only [a]; rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hlhs : ∑ q ∈ Qs, ∑ h ∈ redRes q,
        ‖∑ x : X, (w x : ℂ) * ee (((b ^ m * Y' x : ℕ) : ℝ) * ((h : ℝ) / q + β))‖ ^ 2 =
      ∑ p ∈ pts, ‖∑ n ∈ range N1, a n * ee ((n : ℝ) * xp p)‖ ^ 2 := by
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl; intro q _
    apply Finset.sum_congr rfl; intro h _
    rw [hexp]
  rw [hlhs]
  have h12 : (3 : ℝ) / (1 / (4 * (R : ℝ) ^ 2)) = 12 * (R : ℝ) ^ 2 := by field_simp; ring
  calc _ ≤ _ := hls
    _ = _ := by rw [h12, hsq]

end L09

open L09

theorem itemL09 : ItemL09 := by
  intro b g N j D β hb hg hj1 hjN hD
  classical
  set m := N - j with hm
  set w : (Fin j → Fin (2 * b - 1)) → ℝ := fun f => ∏ i, cc b g (f i) with hw
  set Y' : (Fin j → Fin (2 * b - 1)) → ℕ := fun f => ∑ i : Fin j, (f i : ℕ) * cK b j i with hY'def
  set N1 : ℕ := 2 * b ^ (2 * j + 1) with hN1
  -- `P²`
  have hP2 : ∀ γ : ℝ, (∏ i ∈ range j, Gg b g ((cK b j i : ℝ) * γ)) ^ 2 =
      ∑ f : Fin j → Fin (2 * b - 1), (w f : ℂ) * ee ((Y' f : ℝ) * γ) := by
    intro γ
    rw [← Finset.prod_pow, ← Fin.prod_univ_eq_prod_range (fun i => Gg b g ((cK b j i : ℝ) * γ) ^ 2)]
    simp_rw [Gsq b (by omega) g]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    apply Finset.sum_congr rfl; intro f _
    rw [Finset.prod_mul_distrib, ← ee_sum]
    simp only [hw, hY'def]
    push_cast
    congr 2
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i _; ring
  -- `g_J = P(b^m ·)`
  have hgJ : ∀ α : ℝ, gJ b g N (Ico (N - j) N) α =
      ∏ i ∈ range j, Gg b g ((cK b j i : ℝ) * ((b : ℝ) ^ m * α)) := by
    intro α
    unfold gJ
    rw [Finset.prod_Ico_eq_prod_range, show N - (N - j) = j by omega]
    apply Finset.prod_congr rfl; intro i hi
    congr 1
    rw [cK_shift b N j i (mem_range.1 hi) hjN]
    push_cast; ring
  -- frequencies
  have hY' : ∀ f, Y' f < N1 := by
    intro f
    have h1 : Y' f ≤ ∑ i ∈ range j, (2 * b - 2) * cK b j i := by
      simp only [hY'def]
      rw [← Fin.sum_univ_eq_sum_range (fun i => (2 * b - 2) * cK b j i)]
      apply Finset.sum_le_sum; intro i _
      exact Nat.mul_le_mul_right _ (by have := (f i).isLt; omega)
    have h1' : (Y' f : ℤ) ≤ ∑ i ∈ range j, ((2 * (b : ℤ) - 2) * (cK b j i : ℤ)) := by
      have := (Nat.cast_le (α := ℤ)).2 h1
      push_cast [Nat.cast_sub (by omega : 2 ≤ 2 * b)] at this
      exact this
    rw [← Finset.mul_sum] at h1'
    have h2 := csum b j hb
    have : (Y' f : ℤ) < 2 * (b : ℤ) ^ (2 * j + 1) := by nlinarith
    have : (Y' f : ℤ) < (N1 : ℤ) := by rw [hN1]; push_cast; exact this
    exact_mod_cast this
  -- injectivity of the frequencies
  have hinj : ∀ f f', Y' f = Y' f' → f = f' := by
    intro f f' hff
    set s : ℕ → ℤ := fun k => if hk : k < j then ((f ⟨k, hk⟩ : ℕ) : ℤ) - ((f' ⟨k, hk⟩ : ℕ) : ℤ) else 0 with hs
    have hbd : ∀ k ≤ j, |s k| ≤ 2 * (b : ℤ) - 2 := by
      intro k _
      simp only [hs]
      split_ifs with hk
      · have h1 := (f ⟨k, hk⟩).isLt
        have h2 := (f' ⟨k, hk⟩).isLt
        rw [abs_le]; constructor <;> omega
      · simp; omega
    have hsum : ∑ k ∈ range (j + 1), s k * (cK b j k : ℤ) = 0 := by
      rw [Finset.sum_range_succ]
      have hj0 : s j = 0 := by simp [hs]
      rw [hj0, zero_mul, add_zero, ← Fin.sum_univ_eq_sum_range (fun k => s k * (cK b j k : ℤ))]
      have e : ∀ i : Fin j, s i * (cK b j i : ℤ) = ((f i : ℕ) : ℤ) * cK b j i - ((f' i : ℕ) : ℤ) * cK b j i := by
        intro i; simp only [hs, dif_pos i.2]; ring
      rw [Finset.sum_congr rfl (fun i _ => e i), Finset.sum_sub_distrib]
      have := congrArg (fun n : ℕ => (n : ℤ)) hff
      simp only [hY'def] at this; push_cast at this
      rw [this, sub_self]
    have hz := sum_cK_eq_zero b j hb s hbd hsum
    funext i
    have := hz i i.2.le
    simp only [hs, dif_pos i.2, Fin.eta] at this
    exact Fin.ext (by omega)
  -- the fiber sum
  have hfib : ∑ n ∈ range N1, (∑ f ∈ (univ : Finset (Fin j → Fin (2 * b - 1))).filter (fun f => Y' f = n), w f) ^ 2 =
      mw4 b g ^ j := by
    have e1 : ∀ n ∈ range N1, (∑ f ∈ (univ : Finset (Fin j → Fin (2 * b - 1))).filter (fun f => Y' f = n), w f) ^ 2 =
        ∑ f ∈ (univ : Finset (Fin j → Fin (2 * b - 1))).filter (fun f => Y' f = n), w f ^ 2 := by
      intro n _
      apply sq_sum_le_one
      apply Finset.card_le_one.2
      intro f hf f' hf'
      exact hinj f f' ((Finset.mem_filter.1 hf).2.trans (Finset.mem_filter.1 hf').2.symm)
    rw [Finset.sum_congr rfl e1,
      Finset.sum_fiberwise_of_maps_to (g := Y') (t := range N1) (fun f _ => mem_range.2 (hY' f))]
    simp only [hw]
    simp_rw [← Finset.prod_pow]
    rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum (fun _ : Fin j => (univ : Finset (Fin (2 * b - 1))))
      (fun _ s => cc b g s ^ 2)]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mw4_eq,
      Fin.sum_univ_eq_sum_range (fun s => cc b g s ^ 2)]
  -- left side
  set Qs := (Ico D (2 * D)).filter (fun d => Nat.Coprime d b) with hQs
  have hQ : ∀ q ∈ Qs, D ≤ q ∧ q ≤ 2 * D ∧ Nat.Coprime q b := by
    intro q hq
    simp only [hQs, mem_filter, mem_Ico] at hq
    exact ⟨hq.1.1, hq.1.2.le, hq.2⟩
  have hL : ∑ d ∈ Qs, ∑ h ∈ redRes d, ‖gJ b g N (Ico (N - j) N) ((h : ℝ) / d + β)‖ ^ 4 =
      ∑ d ∈ Qs, ∑ h ∈ redRes d,
        ‖∑ f : Fin j → Fin (2 * b - 1), (w f : ℂ) * ee (((b ^ m * Y' f : ℕ) : ℝ) * ((h : ℝ) / d + β))‖ ^ 2 := by
    apply Finset.sum_congr rfl; intro d _
    apply Finset.sum_congr rfl; intro h _
    have e4 : ∀ z : ℂ, ‖z‖ ^ 4 = ‖z ^ 2‖ ^ 2 := fun z => by rw [norm_pow]; ring
    rw [hgJ, e4, hP2]
    refine congrArg (fun z : ℂ => ‖z‖ ^ 2) (Finset.sum_congr rfl (fun f _ => ?_))
    rw [show ((b ^ m * Y' f : ℕ) : ℝ) * ((h : ℝ) / d + β) = (Y' f : ℝ) * ((b : ℝ) ^ m * ((h : ℝ) / d + β)) by
      push_cast; ring]
  have hls := ls_w b m (Fin j → Fin (2 * b - 1)) w Y' N1 hY' D hD Qs hQ β
  rw [hfib] at hls
  rw [hL]
  have hm0 : 0 ≤ mw4 b g := by unfold mw4; positivity
  have hconst : (4 * (N1 : ℝ) + 12 * (D : ℝ) ^ 2 + 2) ≤ 6 * (4 * (D : ℝ) ^ 2 + 2 * b * (b : ℝ) ^ (2 * j)) := by
    have hN1r : (N1 : ℝ) = 2 * (b : ℝ) * (b : ℝ) ^ (2 * j) := by rw [hN1]; push_cast; ring
    have hpow : (1 : ℝ) ≤ (b : ℝ) * (b : ℝ) ^ (2 * j) := by
      have : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast (by omega : 1 ≤ b)
      have h2 : (1 : ℝ) ≤ (b : ℝ) ^ (2 * j) := one_le_pow₀ this
      nlinarith
    rw [hN1r]; nlinarith
  calc _ ≤ _ := hls
    _ ≤ _ := mul_le_mul_of_nonneg_right hconst (pow_nonneg hm0 _)

end Omega3
