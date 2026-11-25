import Omega3.Statements
import Palprimes.Digits.LemmaThree
import Palprimes.ExpSum.Collision

/-!
# L08: Lemma 2.8 (weight-free averaged majorant products)

Expand `T(t) = Σ_{|u|≤H} τ_{|u|} e(ut)`, so `Π_{k∈K} T(c_kα) = Σ_f τ_f e(W(f)α)` with `f : K → [−H, H]`,
`W(f) = Σ_k f_k c_k`. Orthogonality: `Σ_{h<q} e(W(h/q + β)) = [q ∣ W] q e(Wβ)`. The term `f = 0` gives `q τ₀^{|K|}`.
For `f ≠ 0`, `W(f) ≠ 0` (Palprimes `sum_cK_eq_zero`, `|f_k| ≤ H ≤ 2b − 2`) and `|W(f)| ≤ H Σ_{k∈K} c_k < H b^{2N+1}`,
so at most `Td` moduli divide it, each `≤ max Qs`; summing `|τ_f|` gives `A(T)^{|K|}`.
-/

namespace Omega3

namespace L08

open Finset Palprimes

set_option linter.style.longLine false

lemma l8_ee_add (a c : ℝ) : ee (a + c) = ee a * ee c := by
  unfold ee
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma l8_ee_zero : ee 0 = 1 := by simp [ee]

lemma l8_ee_cos (t : ℝ) : ee t + ee (-t) = ((2 * Real.cos (2 * Real.pi * t) : ℝ) : ℂ) := by
  unfold ee
  have h1 : (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) = (((2 * Real.pi * t : ℝ)) : ℂ) * Complex.I := by
    push_cast; ring
  have h2 : (2 * (Real.pi : ℂ) * Complex.I * ((-t : ℝ) : ℂ)) = (-((2 * Real.pi * t : ℝ) : ℂ)) * Complex.I := by
    push_cast; ring
  rw [h1, h2, Complex.exp_mul_I, Complex.exp_mul_I]
  rw [Complex.cos_neg, Complex.sin_neg]
  push_cast
  ring

lemma l8_trigE (H : ℕ) (τ : ℕ → ℝ) (t : ℝ) :
    (trigEval H τ t : ℂ) = ∑ u ∈ Icc (-(H : ℤ)) H, (τ u.natAbs : ℂ) * ee ((u : ℝ) * t) := by
  induction H with
  | zero =>
    have : Icc (-((0 : ℕ) : ℤ)) ((0 : ℕ) : ℤ) = {0} := by
      ext u; simp only [Finset.mem_Icc, Finset.mem_singleton]; omega
    rw [this]
    simp [trigEval, l8_ee_zero]
  | succ H ih =>
    have e : Icc (-((H + 1 : ℕ) : ℤ)) ((H + 1 : ℕ) : ℤ) =
        insert (-((H + 1 : ℕ) : ℤ)) (insert ((H + 1 : ℕ) : ℤ) (Icc (-(H : ℤ)) H)) := by
      ext u; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
    have h1 : (-((H + 1 : ℕ) : ℤ)) ∉ insert ((H + 1 : ℕ) : ℤ) (Icc (-(H : ℤ)) H) := by
      simp only [Finset.mem_insert, Finset.mem_Icc, not_or]; push_cast; omega
    have h2 : ((H + 1 : ℕ) : ℤ) ∉ Icc (-(H : ℤ)) H := by
      simp only [Finset.mem_Icc]; push_cast; omega
    rw [e, Finset.sum_insert h1, Finset.sum_insert h2, ← ih]
    have hs : trigEval (H + 1) τ t = trigEval H τ t + 2 * (τ (H + 1) * Real.cos (2 * Real.pi * (((H + 1 : ℕ) : ℝ) * t))) := by
      unfold trigEval
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hX : 2 * Real.pi * ((H + 1 : ℕ) : ℝ) * t = 2 * Real.pi * (((H + 1 : ℕ) : ℝ) * t) := by ring
      rw [hX]
      ring
    rw [hs]
    have hn1 : (-((H + 1 : ℕ) : ℤ)).natAbs = H + 1 := by omega
    have hn2 : (((H + 1 : ℕ) : ℤ)).natAbs = H + 1 := by omega
    rw [hn1, hn2]
    simp only [Int.cast_neg, Int.cast_natCast]
    have h3 : ee (-((H + 1 : ℕ) : ℝ) * t) = ee (-(((H + 1 : ℕ) : ℝ) * t)) := by congr 1; ring
    have := l8_ee_cos (((H + 1 : ℕ) : ℝ) * t)
    rw [h3]
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat] at this ⊢
    linear_combination (-(τ (H + 1) : ℂ)) * this


lemma l8_mass (H : ℕ) (τ : ℕ → ℝ) :
    ∑ u ∈ Icc (-(H : ℤ)) H, |τ u.natAbs| = trigMass H τ := by
  induction H with
  | zero =>
    have : Icc (-((0 : ℕ) : ℤ)) ((0 : ℕ) : ℤ) = {0} := by
      ext u; simp only [Finset.mem_Icc, Finset.mem_singleton]; omega
    rw [this]
    simp [trigMass]
  | succ H ih =>
    have e : Icc (-((H + 1 : ℕ) : ℤ)) ((H + 1 : ℕ) : ℤ) =
        insert (-((H + 1 : ℕ) : ℤ)) (insert ((H + 1 : ℕ) : ℤ) (Icc (-(H : ℤ)) H)) := by
      ext u; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
    have h1 : (-((H + 1 : ℕ) : ℤ)) ∉ insert ((H + 1 : ℕ) : ℤ) (Icc (-(H : ℤ)) H) := by
      simp only [Finset.mem_insert, Finset.mem_Icc, not_or]; push_cast; omega
    have h2 : ((H + 1 : ℕ) : ℤ) ∉ Icc (-(H : ℤ)) H := by
      simp only [Finset.mem_Icc]; push_cast; omega
    rw [e, Finset.sum_insert h1, Finset.sum_insert h2, ih]
    have hn1 : (-((H + 1 : ℕ) : ℤ)).natAbs = H + 1 := by omega
    have hn2 : (((H + 1 : ℕ) : ℤ)).natAbs = H + 1 := by omega
    rw [hn1, hn2]
    unfold trigMass
    rw [Finset.sum_Icc_succ_top (by omega)]
    ring

lemma l8_csum (b N : ℕ) (hb : 2 ≤ b) (K : Finset ℕ) (hK : K ⊆ range N) :
    ∑ k ∈ K, cK b N k < b ^ (2 * N + 1) := by
  have e1 : ∀ k ∈ K, cK b N k = b ^ k + b ^ (2 * N - k) := fun k hk => by
    simp [cK, mem_range.1 (hK hk)]
  rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib]
  have hinj : Set.InjOn (fun k => 2 * N - k) (K : Set ℕ) := by
    intro x hx y hy hxy
    have := mem_range.1 (hK hx); have := mem_range.1 (hK hy)
    simp only at hxy; omega
  have e2 : ∑ k ∈ K, b ^ (2 * N - k) = ∑ j ∈ K.image (fun k => 2 * N - k), b ^ j :=
    (Finset.sum_image (f := fun j => b ^ j) hinj).symm
  have hdisj : Disjoint K (K.image (fun k => 2 * N - k)) := by
    rw [Finset.disjoint_left]
    intro a ha hb'
    obtain ⟨k, hk, hka⟩ := mem_image.1 hb'
    have := mem_range.1 (hK ha); have := mem_range.1 (hK hk)
    omega
  rw [e2, ← Finset.sum_union hdisj]
  apply Nat.geomSum_lt hb
  intro k hk
  rcases mem_union.1 hk with h | h
  · have := mem_range.1 (hK h); omega
  · obtain ⟨j, _, rfl⟩ := mem_image.1 h; omega

end L08

open L08 Finset Palprimes

theorem itemL08 : ItemL08 := by
  intro b H N τ K Qs β Td hb hH hK hQ hTd0 hTd
  classical
  set I : Finset ℤ := Icc (-(H : ℤ)) H with hI
  set P : Finset (K → ℤ) := Fintype.piFinset (fun _ : K => I) with hP
  set W : (K → ℤ) → ℤ := fun f => ∑ k : K, f k * (cK b N k : ℤ) with hWdef
  set tf : (K → ℤ) → ℝ := fun f => ∏ k : K, τ (f k).natAbs with htfdef
  set S : ℕ := Qs.sup id with hS
  -- expansion
  have hexp : ∀ α : ℝ, ((∏ k ∈ K, trigEval H τ ((cK b N k : ℝ) * α) : ℝ) : ℂ) =
      ∑ f ∈ P, (tf f : ℂ) * ee ((W f : ℝ) * α) := by
    intro α
    rw [Complex.ofReal_prod, ← Finset.prod_coe_sort K]
    simp_rw [l8_trigE]
    rw [Finset.prod_univ_sum]
    apply Finset.sum_congr rfl
    intro f _
    rw [Finset.prod_mul_distrib, ← ee_sum]
    simp only [htfdef, hWdef]
    push_cast
    congr 2
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro k _; ring
  -- orthogonality
  have horth : ∀ q ∈ Qs, ((∑ h ∈ range q, ∏ k ∈ K, trigEval H τ ((cK b N k : ℝ) * ((h : ℝ) / q + β)) : ℝ) : ℂ) =
      ∑ f ∈ P, (tf f : ℂ) * ee ((W f : ℝ) * β) * (if (q : ℤ) ∣ W f then (q : ℂ) else 0) := by
    intro q hq
    have hq0 : 0 < q := hQ q hq
    rw [Complex.ofReal_sum]
    simp_rw [hexp]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro f _
    rw [← sum_ee_root q hq0 (W f), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [mul_assoc, ← ee_add]
    congr 2
    field_simp
    ring
  -- the term `f = 0`
  have h0P : (0 : K → ℤ) ∈ P := Fintype.mem_piFinset.2 (fun _ => by simp [hI])
  have hW0 : W 0 = 0 := by simp [hWdef]
  have htf0 : tf 0 = τ 0 ^ K.card := by
    simp [htfdef, Finset.prod_const]
  -- `f ≠ 0`
  have hfb : ∀ f ∈ P, ∀ k : K, |f k| ≤ H := fun f hf k => by
    have := Fintype.mem_piFinset.1 hf k
    simp only [hI, mem_Icc] at this
    rw [abs_le]; exact ⟨this.1, this.2⟩
  have hWne : ∀ f ∈ P, f ≠ 0 → W f ≠ 0 := by
    intro f hf hne hW
    apply hne
    set s : ℕ → ℤ := fun k => if hk : k ∈ K then f ⟨k, hk⟩ else 0 with hs
    have hsum : ∑ k ∈ range (N + 1), s k * (cK b N k : ℤ) = W f := by
      rw [← Finset.sum_subset (fun k hk => mem_range.2 (by have := mem_range.1 (hK hk); omega))
        (fun k _ hk => by simp [hs, hk])]
      rw [← Finset.sum_coe_sort K]
      apply Finset.sum_congr rfl; intro k _; simp [hs, k.2]
    have hb' : ∀ k ≤ N, |s k| ≤ 2 * (b : ℤ) - 2 := by
      intro k _
      simp only [hs]
      split_ifs with hk
      · have h1 := hfb f hf ⟨k, hk⟩
        have h2 : (H : ℤ) ≤ 2 * (b : ℤ) - 2 := by omega
        linarith
      · simp; omega
    have hz := sum_cK_eq_zero b N hb s hb' (hsum.trans hW)
    funext k
    have hk := hz k (by have := mem_range.1 (hK k.2); omega)
    simpa [hs, k.2] using hk
  have hWle : ∀ f ∈ P, |W f| ≤ 2 * (H : ℤ) * (b : ℤ) ^ (2 * N + 1) := by
    intro f hf
    have hcs := l8_csum b N hb K hK
    calc |W f| ≤ ∑ k : K, |f k * (cK b N k : ℤ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k : K, (H : ℤ) * (cK b N k : ℤ) := by
          apply Finset.sum_le_sum; intro k _
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ cK b N k)]
          exact mul_le_mul_of_nonneg_right (hfb f hf k) (by positivity)
      _ = (H : ℤ) * ((∑ k ∈ K, cK b N k : ℕ) : ℤ) := by
          rw [← Finset.mul_sum]; push_cast
          rw [Finset.sum_coe_sort K (fun k => (cK b N k : ℤ))]
      _ ≤ (H : ℤ) * (b : ℤ) ^ (2 * N + 1) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity); exact_mod_cast hcs.le
      _ ≤ 2 * (H : ℤ) * (b : ℤ) ^ (2 * N + 1) := by
          have : (0 : ℤ) ≤ (H : ℤ) * (b : ℤ) ^ (2 * N + 1) := by positivity
          linarith
  -- mass
  have hA : ∑ f ∈ P, |tf f| = trigMass H τ ^ K.card := by
    simp only [htfdef]
    simp_rw [Finset.abs_prod]
    rw [hP, ← Finset.prod_univ_sum (fun _ : K => I) (fun _ u => |τ u.natAbs|), hI, l8_mass]
    simp [Finset.prod_const]
  -- assemble
  set G : ℕ → ℂ := fun q => ∑ f ∈ P, (tf f : ℂ) * ee ((W f : ℝ) * β) *
      (if (q : ℤ) ∣ W f then (q : ℂ) else 0) with hG
  have hLre : ∑ q ∈ Qs, ∑ h ∈ range q, ∏ k ∈ K, trigEval H τ ((cK b N k : ℝ) * ((h : ℝ) / q + β)) =
      (∑ q ∈ Qs, G q).re := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl; intro q hq
    rw [hG]; simp only; rw [← horth q hq, Complex.ofReal_re]
  have hsplit : ∀ q ∈ Qs, G q = (((q : ℝ) * τ 0 ^ K.card : ℝ) : ℂ) + ∑ f ∈ P.erase 0,
      (tf f : ℂ) * ee ((W f : ℝ) * β) * (if (q : ℤ) ∣ W f then (q : ℂ) else 0) := by
    intro q _
    simp only [hG]
    rw [← Finset.add_sum_erase _ _ h0P, hW0, htf0]
    simp only [Int.cast_zero, zero_mul, ee_zero, mul_one, dvd_zero, if_true]
    push_cast; ring
  have hbound : ∀ f ∈ P.erase 0,
      ‖∑ q ∈ Qs, (tf f : ℂ) * ee ((W f : ℝ) * β) * (if (q : ℤ) ∣ W f then (q : ℂ) else 0)‖ ≤
        |tf f| * ((S : ℝ) * Td) := by
    intro f hf
    have hfne : f ≠ 0 := Finset.ne_of_mem_erase hf
    have hfP := Finset.mem_of_mem_erase hf
    have hW := hWne f hfP hfne
    have hWl := hWle f hfP
    rw [← Finset.mul_sum, norm_mul, norm_mul, norm_ee, mul_one, Complex.norm_real, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    calc ‖∑ q ∈ Qs, (if (q : ℤ) ∣ W f then (q : ℂ) else 0)‖
        ≤ ∑ q ∈ Qs, ‖(if (q : ℤ) ∣ W f then (q : ℂ) else 0)‖ := norm_sum_le _ _
      _ ≤ ∑ q ∈ Qs.filter (fun q : ℕ => (q : ℤ) ∣ W f), (S : ℝ) := by
          rw [Finset.sum_filter]
          apply Finset.sum_le_sum; intro q hq
          split_ifs
          · rw [Complex.norm_natCast]; exact_mod_cast (Finset.le_sup (f := id) hq)
          · simp
      _ = ((Qs.filter (fun q : ℕ => (q : ℤ) ∣ W f)).card : ℝ) * (S : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Td * (S : ℝ) := mul_le_mul_of_nonneg_right (hTd _ hW hWl) (by positivity)
      _ = (S : ℝ) * Td := by ring
  rw [hLre, Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Complex.add_re]
  have hfirst : (∑ q ∈ Qs, ((((q : ℝ) * τ 0 ^ K.card : ℝ)) : ℂ)).re = (∑ q ∈ Qs, (q : ℝ)) * τ 0 ^ K.card := by
    rw [← Complex.ofReal_sum, Complex.ofReal_re, Finset.sum_mul]
  rw [hfirst]
  have hrest : (∑ q ∈ Qs, ∑ f ∈ P.erase 0, (tf f : ℂ) * ee ((W f : ℝ) * β) *
        (if (q : ℤ) ∣ W f then (q : ℂ) else 0)).re ≤ (S : ℝ) * Td * trigMass H τ ^ K.card := by
    rw [Finset.sum_comm]
    refine (Complex.re_le_norm _).trans ((norm_sum_le _ _).trans ?_)
    calc ∑ f ∈ P.erase 0, ‖∑ q ∈ Qs, (tf f : ℂ) * ee ((W f : ℝ) * β) *
          (if (q : ℤ) ∣ W f then (q : ℂ) else 0)‖
        ≤ ∑ f ∈ P.erase 0, |tf f| * ((S : ℝ) * Td) := Finset.sum_le_sum hbound
      _ ≤ ∑ f ∈ P, |tf f| * ((S : ℝ) * Td) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            (fun _ _ _ => mul_nonneg (abs_nonneg _) (by positivity))
      _ = (S : ℝ) * Td * trigMass H τ ^ K.card := by rw [← Finset.sum_mul, hA]; ring
  linarith

end Omega3
