import KappaOmega2.Items.LK09_Core
import Palprimes.ExpSum.Farey

/-!
# LK09: Lemma 2.9_κ (inner large sieve with the exact fourth moment of the inner block and the middle)

`g_J(α)² = Σ_x w(x) e(V(x) b^{m−j} α)` (`LK09_Core`), injective frequencies `V < 2 W b^{2j}` (Lemma E),
`Σ w² = m_w(4)^j m_M(4)`. Palprimes `large_sieve` via a weighted copy of `ls_step` (as in L09, the twist
`h ↦ b^{m−j} h mod d` permutes the reduced residues for `(d, b) = 1`, Farey spacing `1/(4D²)`), constant
`4·2W b^{2j} + 12D² + 2 ≤ 16(D² + b W b^{2j})`.
-/

namespace KappaOmega2

open Finset Palprimes

set_option linter.style.longLine false

namespace LK09

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

end LK09

open LK09

theorem itemLK09 : ItemLK09 := by
  intro b g N j D β hb _hg hj hD
  classical
  set W := WK b N with hWdef
  have hW : W = b ^ ellK N := rfl
  have hW1 : 1 ≤ W := Nat.one_le_pow _ _ (by omega)
  set X := Idx b W j
  set w : X → ℝ := wt b g W j with hw
  set Y' : X → ℕ := Vf b (ellK N) j W with hY'def
  set N1 : ℕ := 2 * W * b ^ (2 * j) with hN1
  have hY' : ∀ x, Y' x < N1 := fun x => Vf_lt b (ellK N) j W (by omega) hW x
  have hinj : ∀ x x', Y' x = Y' x' → x = x' := fun x x' h =>
    Vf_inj b (ellK N) j W hb (ellK_pos N) hW x x' h
  have hfib : ∑ n ∈ range N1, (∑ x ∈ (univ : Finset X).filter (fun x => Y' x = n), w x) ^ 2 =
      mw4 b g ^ j * mM4 W := by
    have e1 : ∀ n ∈ range N1, (∑ x ∈ (univ : Finset X).filter (fun x => Y' x = n), w x) ^ 2 =
        ∑ x ∈ (univ : Finset X).filter (fun x => Y' x = n), w x ^ 2 := by
      intro n _
      apply sq_sum_le_one
      apply Finset.card_le_one.2
      intro x hx x' hx'
      exact hinj x x' ((Finset.mem_filter.1 hx).2.trans (Finset.mem_filter.1 hx').2.symm)
    rw [Finset.sum_congr rfl e1,
      Finset.sum_fiberwise_of_maps_to (g := Y') (t := range N1) (fun x _ => mem_range.2 (hY' x))]
    exact sum_wt_sq b g W j hW1
  set Qs := (Ico D (2 * D)).filter (fun d => Nat.Coprime d b) with hQs
  have hQ : ∀ q ∈ Qs, D ≤ q ∧ q ≤ 2 * D ∧ Nat.Coprime q b := by
    intro q hq
    simp only [hQs, mem_filter, mem_Ico] at hq
    exact ⟨hq.1.1, hq.1.2.le, hq.2⟩
  have hL : ∑ d ∈ Qs, ∑ h ∈ redRes d, ‖gJK b g N j ((h : ℝ) / d + β)‖ ^ 4 =
      ∑ d ∈ Qs, ∑ h ∈ redRes d,
        ‖∑ x : X, (w x : ℂ) * ee (((b ^ (mK N - j) * Y' x : ℕ) : ℝ) * ((h : ℝ) / d + β))‖ ^ 2 := by
    apply Finset.sum_congr rfl; intro d _
    apply Finset.sum_congr rfl; intro h _
    have e4 : ∀ z : ℂ, ‖z‖ ^ 4 = ‖z ^ 2‖ ^ 2 := fun z => by rw [norm_pow]; ring
    rw [e4, gJK_sq b (by omega) g N j hj]
    refine congrArg (fun z : ℂ => ‖z‖ ^ 2) (Finset.sum_congr rfl (fun x _ => ?_))
    rw [show ((b ^ (mK N - j) * Y' x : ℕ) : ℝ) * ((h : ℝ) / d + β) =
        (Y' x : ℝ) * ((b : ℝ) ^ (mK N - j) * ((h : ℝ) / d + β)) by push_cast; ring]
  have hls := ls_w b (mK N - j) X w Y' N1 hY' D hD Qs hQ β
  rw [hfib] at hls
  rw [hL]
  have hm0 : 0 ≤ mw4 b g := by unfold mw4; positivity
  have hM0 : 0 ≤ mM4 W := by unfold mM4; positivity
  have hconst : (4 * (N1 : ℝ) + 12 * (D : ℝ) ^ 2 + 2) ≤ 16 * ((D : ℝ) ^ 2 + b * (W : ℝ) * (b : ℝ) ^ (2 * j)) := by
    have hN1r : (N1 : ℝ) = 2 * (W : ℝ) * (b : ℝ) ^ (2 * j) := by rw [hN1]; push_cast; ring
    have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
    have hb1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast (by omega : 1 ≤ b)
    have hp : (0 : ℝ) ≤ (W : ℝ) * (b : ℝ) ^ (2 * j) := by positivity
    rw [hN1r]; nlinarith
  calc _ ≤ _ := hls
    _ ≤ 16 * ((D : ℝ) ^ 2 + b * (W : ℝ) * (b : ℝ) ^ (2 * j)) * (mw4 b g ^ j * mM4 W) :=
        mul_le_mul_of_nonneg_right hconst (mul_nonneg (pow_nonneg hm0 _) hM0)
    _ = _ := by ring

end KappaOmega2
