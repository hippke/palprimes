import KappaOmega2.StatementsK
import KappaOmega2.LemmaR
import Palprimes.ExpSum.Collision

/-!
# LK08: Lemma 2.8_κ (expansion with Lemma R and the middle factor)

Expand `T(t) = Σ_{|u|≤H} τ_{|u|} e(ut)` and `K̃(β) = Σ_{|s|≤S} κ_{|s|} e(sβ)`, so
`Π_{k∈K} T(c_kα) K̃(b^m α) = Σ_{(f,s)} τ_f κ_s e((W(f) + s b^m)α)` with `W(f) = Σ_k f_k c_k`.
Orthogonality: `Σ_{h<q} e(V(h/q + β)) = [q ∣ V] q e(Vβ)`. The term `(f, s) = 0` gives `q τ₀^{|K|} κ₀`.
For `(f, s) ≠ 0` the frequency is nonzero by `KappaOmega2.lemmaR` (`|f_k| ≤ H ≤ b(b − 1)`, `|s| ≤ S ≤ W`), and
`|V| ≤ H b^{2N+1} + W b^m ≤ (2H + 1) b^{2N+1}`, so at most `Td` moduli divide it, each `≤ max Qs`.
-/

namespace KappaOmega2

namespace LK08

open Finset Palprimes

set_option linter.style.longLine false

lemma k8_ee_cos (t : ℝ) : ee t + ee (-t) = ((2 * Real.cos (2 * Real.pi * t) : ℝ) : ℂ) := by
  unfold ee
  have h1 : (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) = (((2 * Real.pi * t : ℝ)) : ℂ) * Complex.I := by
    push_cast; ring
  have h2 : (2 * (Real.pi : ℂ) * Complex.I * ((-t : ℝ) : ℂ)) = (-((2 * Real.pi * t : ℝ) : ℂ)) * Complex.I := by
    push_cast; ring
  rw [h1, h2, Complex.exp_mul_I, Complex.exp_mul_I]
  rw [Complex.cos_neg, Complex.sin_neg]
  push_cast
  ring

lemma k8_trigE (H : ℕ) (τ : ℕ → ℝ) (t : ℝ) :
    (trigEval H τ t : ℂ) = ∑ u ∈ Icc (-(H : ℤ)) H, (τ u.natAbs : ℂ) * ee ((u : ℝ) * t) := by
  induction H with
  | zero =>
    have : Icc (-((0 : ℕ) : ℤ)) ((0 : ℕ) : ℤ) = {0} := by
      ext u; simp only [Finset.mem_Icc, Finset.mem_singleton]; omega
    rw [this]
    simp [trigEval, ee_zero]
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
    have := k8_ee_cos (((H + 1 : ℕ) : ℝ) * t)
    rw [h3]
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat] at this ⊢
    linear_combination (-(τ (H + 1) : ℂ)) * this

lemma k8_mass (H : ℕ) (τ : ℕ → ℝ) :
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

lemma k8_csum (b N : ℕ) (hb : 2 ≤ b) (K : Finset ℕ) (hK : K ⊆ range N) :
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

lemma mK_le (N : ℕ) : mK N ≤ N := by unfold mK; omega

lemma ellK_pos (N : ℕ) : 1 ≤ ellK N := by unfold ellK mK; omega

end LK08

open LK08 Finset Palprimes

theorem itemLK08 : ItemLK08 := by
  intro b H N S τ κ K Qs β Td hb hH hm1 hK hSW hQ hTd0 hTd
  classical
  set m := mK N with hmdef
  have hmN : m ≤ N := mK_le N
  have hl1 : 1 ≤ ellK N := ellK_pos N
  have hKr : K ⊆ range N := fun k hk => by
    have := mem_Ico.1 (hK hk); exact mem_range.2 (by omega)
  set I : Finset ℤ := Icc (-(H : ℤ)) H with hI
  set IS : Finset ℤ := Icc (-(S : ℤ)) S with hIS
  set P : Finset (K → ℤ) := Fintype.piFinset (fun _ : K => I) with hP
  set PP : Finset ((K → ℤ) × ℤ) := P ×ˢ IS with hPP
  set W : (K → ℤ) → ℤ := fun f => ∑ k : K, f k * (cK b N k : ℤ) with hWdef
  set V : (K → ℤ) × ℤ → ℤ := fun x => W x.1 + x.2 * (b : ℤ) ^ m with hVdef
  set tf : (K → ℤ) → ℝ := fun f => ∏ k : K, τ (f k).natAbs with htfdef
  set tt : (K → ℤ) × ℤ → ℝ := fun x => tf x.1 * κ x.2.natAbs with httdef
  set Smax : ℕ := Qs.sup id with hS
  -- expansion
  have hexp : ∀ α : ℝ, ((∏ k ∈ K, trigEval H τ ((cK b N k : ℝ) * α) : ℝ) : ℂ) =
      ∑ f ∈ P, (tf f : ℂ) * ee ((W f : ℝ) * α) := by
    intro α
    rw [Complex.ofReal_prod, ← Finset.prod_coe_sort K]
    simp_rw [k8_trigE]
    rw [Finset.prod_univ_sum]
    apply Finset.sum_congr rfl
    intro f _
    rw [Finset.prod_mul_distrib, ← ee_sum]
    simp only [htfdef, hWdef]
    push_cast
    congr 2
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro k _; ring
  have hexp2 : ∀ α : ℝ, (((∏ k ∈ K, trigEval H τ ((cK b N k : ℝ) * α)) *
      trigEval S κ ((b : ℝ) ^ m * α) : ℝ) : ℂ) = ∑ x ∈ PP, (tt x : ℂ) * ee ((V x : ℝ) * α) := by
    intro α
    rw [Complex.ofReal_mul, hexp, k8_trigE, Finset.sum_mul_sum, hPP, Finset.sum_product]
    apply Finset.sum_congr rfl; intro f _
    apply Finset.sum_congr rfl; intro s _
    simp only [httdef, hVdef]
    have : ((W f + s * (b : ℤ) ^ m : ℤ) : ℝ) * α = (W f : ℝ) * α + (s : ℝ) * ((b : ℝ) ^ m * α) := by
      push_cast; ring
    rw [this, ee_add]
    push_cast; ring
  -- orthogonality
  have horth : ∀ q ∈ Qs, ((∑ h ∈ range q, (∏ k ∈ K, trigEval H τ ((cK b N k : ℝ) * ((h : ℝ) / q + β))) *
        trigEval S κ ((b : ℝ) ^ m * ((h : ℝ) / q + β)) : ℝ) : ℂ) =
      ∑ x ∈ PP, (tt x : ℂ) * ee ((V x : ℝ) * β) * (if (q : ℤ) ∣ V x then (q : ℂ) else 0) := by
    intro q hq
    have hq0 : 0 < q := hQ q hq
    rw [Complex.ofReal_sum]
    simp_rw [hexp2]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [← sum_ee_root q hq0 (V x), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [mul_assoc, ← ee_add]
    congr 2
    field_simp
    ring
  -- the term `x = 0`
  have h0P : ((0 : K → ℤ), (0 : ℤ)) ∈ PP := by
    rw [hPP, Finset.mem_product]
    exact ⟨Fintype.mem_piFinset.2 (fun _ => by simp [hI]), by simp [hIS]⟩
  have hV0 : V (0, 0) = 0 := by simp [hVdef, hWdef]
  have htt0 : tt (0, 0) = τ 0 ^ K.card * κ 0 := by
    simp [httdef, htfdef, Finset.prod_const]
  -- bounds on the coordinates
  have hfb : ∀ x ∈ PP, ∀ k : K, |x.1 k| ≤ H := fun x hx k => by
    have := Fintype.mem_piFinset.1 (Finset.mem_product.1 hx).1 k
    simp only [hI, mem_Icc] at this
    rw [abs_le]; exact ⟨this.1, this.2⟩
  have hsb : ∀ x ∈ PP, |x.2| ≤ S := fun x hx => by
    have := (Finset.mem_product.1 hx).2
    simp only [hIS, mem_Icc] at this
    rw [abs_le]; exact ⟨this.1, this.2⟩
  -- Lemma R
  have hVne : ∀ x ∈ PP, x ≠ (0, 0) → V x ≠ 0 := by
    intro x hx hne hV
    apply hne
    set t : ℕ → ℤ := fun k => if hk : k ∈ K then x.1 ⟨k, hk⟩ else 0 with ht
    have hsum : ∑ i ∈ range m, t i * ((b : ℤ) ^ (2 * N + 1 - 1 - i) + (b : ℤ) ^ i) = W x.1 := by
      have hsub : K ⊆ range m := fun k hk => by have := mem_Ico.1 (hK hk); exact mem_range.2 this.2
      rw [← Finset.sum_subset hsub (fun k _ hk => by simp [ht, hk])]
      rw [← Finset.sum_coe_sort K]
      apply Finset.sum_congr rfl; intro k _
      have hkN : (k : ℕ) < N := mem_range.1 (hKr k.2)
      simp only [ht, k.2, dif_pos, Subtype.coe_eta]
      unfold cK
      rw [if_pos hkN]
      push_cast
      ring
    have hbox : ∀ i, |t i| ≤ (b : ℤ) * ((b : ℤ) - 1) := by
      intro i
      simp only [ht]
      split_ifs with hk
      · have h1 := hfb x hx ⟨i, hk⟩
        have h2 : (H : ℤ) ≤ (b : ℤ) * ((b : ℤ) - 1) := by
          have : ((b * (b - 1) : ℕ) : ℤ) = (b : ℤ) * ((b : ℤ) - 1) := by
            push_cast [Nat.cast_sub (by omega : 1 ≤ b)]; ring
          rw [← this]; exact_mod_cast hH
        linarith
      · simp only [abs_zero]
        have : (0 : ℤ) ≤ (b : ℤ) * ((b : ℤ) - 1) := by
          have : (0 : ℤ) ≤ (b : ℤ) - 1 := by omega
          positivity
        exact this
    have hLm : 2 * N + 1 - 2 * m = ellK N := by simp [ellK, hmdef]
    have hs : |x.2| ≤ (b : ℤ) ^ (2 * N + 1 - 2 * m) := by
      rw [hLm]
      have h1 := hsb x hx
      have h2 : ((S : ℕ) : ℤ) ≤ ((WK b N : ℕ) : ℤ) := by exact_mod_cast hSW
      simp only [WK] at h2; push_cast at h2
      linarith
    have hW : (b : ℤ) ≤ (b : ℤ) ^ (2 * N + 1 - 2 * m) := by
      rw [hLm]
      calc (b : ℤ) = (b : ℤ) ^ 1 := (pow_one _).symm
        _ ≤ (b : ℤ) ^ ellK N := pow_le_pow_right₀ (by omega) hl1
    have heq : (∑ i ∈ range m, t i * ((b : ℤ) ^ (2 * N + 1 - 1 - i) + (b : ℤ) ^ i)) + x.2 * (b : ℤ) ^ m = 0 := by
      rw [hsum]; exact hV
    obtain ⟨ht0, hs0⟩ := KappaOmega2.lemmaR (b : ℤ) (by exact_mod_cast hb) m (2 * N + 1) hm1 (by omega)
      t x.2 hbox hs hW heq
    ext k
    · have hk := ht0 k (mem_Ico.1 (hK k.2)).2
      simpa [ht, k.2] using hk
    · simpa using hs0
  have hVle : ∀ x ∈ PP, |V x| ≤ (2 * (H : ℤ) + 1) * (b : ℤ) ^ (2 * N + 1) := by
    intro x hx
    have hcs := k8_csum b N (by omega) K hKr
    have hW1 : |W x.1| ≤ (H : ℤ) * (b : ℤ) ^ (2 * N + 1) := by
      calc |W x.1| ≤ ∑ k : K, |x.1 k * (cK b N k : ℤ)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k : K, (H : ℤ) * (cK b N k : ℤ) := by
            apply Finset.sum_le_sum; intro k _
            rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ cK b N k)]
            exact mul_le_mul_of_nonneg_right (hfb x hx k) (by positivity)
        _ = (H : ℤ) * ((∑ k ∈ K, cK b N k : ℕ) : ℤ) := by
            rw [← Finset.mul_sum]; push_cast
            rw [Finset.sum_coe_sort K (fun k => (cK b N k : ℤ))]
        _ ≤ (H : ℤ) * (b : ℤ) ^ (2 * N + 1) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity); exact_mod_cast hcs.le
    have hW2 : |x.2 * (b : ℤ) ^ m| ≤ (b : ℤ) ^ (2 * N + 1) := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (b : ℤ) ^ m)]
      have h1 : |x.2| ≤ (b : ℤ) ^ ellK N := by
        have h1 := hsb x hx
        have h2 : ((S : ℕ) : ℤ) ≤ ((WK b N : ℕ) : ℤ) := by exact_mod_cast hSW
        simp only [WK] at h2; push_cast at h2
        linarith
      have h2 : (b : ℤ) ^ ellK N * (b : ℤ) ^ m ≤ (b : ℤ) ^ (2 * N + 1) := by
        rw [← pow_add]
        apply pow_le_pow_right₀ (by omega)
        unfold ellK; rw [← hmdef]; omega
      calc |x.2| * (b : ℤ) ^ m ≤ (b : ℤ) ^ ellK N * (b : ℤ) ^ m :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ _ := h2
    have hP0 : (0 : ℤ) ≤ (H : ℤ) * (b : ℤ) ^ (2 * N + 1) := by positivity
    calc |V x| = |W x.1 + x.2 * (b : ℤ) ^ m| := rfl
      _ ≤ |W x.1| + |x.2 * (b : ℤ) ^ m| := abs_add_le _ _
      _ ≤ (H : ℤ) * (b : ℤ) ^ (2 * N + 1) + (b : ℤ) ^ (2 * N + 1) := add_le_add hW1 hW2
      _ ≤ (2 * (H : ℤ) + 1) * (b : ℤ) ^ (2 * N + 1) := by nlinarith
  -- mass
  have hA : ∑ x ∈ PP, |tt x| = trigMass H τ ^ K.card * trigMass S κ := by
    have hA1 : ∑ f ∈ P, |tf f| = trigMass H τ ^ K.card := by
      simp only [htfdef]
      simp_rw [Finset.abs_prod]
      rw [hP, ← Finset.prod_univ_sum (fun _ : K => I) (fun _ u => |τ u.natAbs|), hI, k8_mass]
      simp [Finset.prod_const]
    rw [hPP, Finset.sum_product, ← hA1, ← k8_mass S κ, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro f _
    apply Finset.sum_congr rfl; intro s _
    simp only [httdef, abs_mul]
  -- assemble
  set G : ℕ → ℂ := fun q => ∑ x ∈ PP, (tt x : ℂ) * ee ((V x : ℝ) * β) *
      (if (q : ℤ) ∣ V x then (q : ℂ) else 0) with hG
  have hLre : ∑ q ∈ Qs, ∑ h ∈ range q, (∏ k ∈ K, trigEval H τ ((cK b N k : ℝ) * ((h : ℝ) / q + β))) *
        trigEval S κ ((b : ℝ) ^ m * ((h : ℝ) / q + β)) = (∑ q ∈ Qs, G q).re := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl; intro q hq
    rw [hG]; simp only; rw [← horth q hq, Complex.ofReal_re]
  have hsplit : ∀ q ∈ Qs, G q = (((q : ℝ) * (τ 0 ^ K.card * κ 0) : ℝ) : ℂ) + ∑ x ∈ PP.erase (0, 0),
      (tt x : ℂ) * ee ((V x : ℝ) * β) * (if (q : ℤ) ∣ V x then (q : ℂ) else 0) := by
    intro q _
    simp only [hG]
    rw [← Finset.add_sum_erase _ _ h0P, hV0, htt0]
    simp only [Int.cast_zero, zero_mul, ee_zero, mul_one, dvd_zero, ite_true]
    push_cast; ring
  have hbound : ∀ x ∈ PP.erase (0, 0),
      ‖∑ q ∈ Qs, (tt x : ℂ) * ee ((V x : ℝ) * β) * (if (q : ℤ) ∣ V x then (q : ℂ) else 0)‖ ≤
        |tt x| * ((Smax : ℝ) * Td) := by
    intro x hx
    have hxne : x ≠ (0, 0) := Finset.ne_of_mem_erase hx
    have hxP := Finset.mem_of_mem_erase hx
    have hV := hVne x hxP hxne
    have hVl := hVle x hxP
    rw [← Finset.mul_sum, norm_mul, norm_mul, norm_ee, mul_one, Complex.norm_real, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    calc ‖∑ q ∈ Qs, (if (q : ℤ) ∣ V x then (q : ℂ) else 0)‖
        ≤ ∑ q ∈ Qs, ‖(if (q : ℤ) ∣ V x then (q : ℂ) else 0)‖ := norm_sum_le _ _
      _ ≤ ∑ q ∈ Qs.filter (fun q : ℕ => (q : ℤ) ∣ V x), (Smax : ℝ) := by
          rw [Finset.sum_filter]
          apply Finset.sum_le_sum; intro q hq
          split_ifs
          · rw [Complex.norm_natCast]; exact_mod_cast (Finset.le_sup (f := id) hq)
          · simp
      _ = ((Qs.filter (fun q : ℕ => (q : ℤ) ∣ V x)).card : ℝ) * (Smax : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Td * (Smax : ℝ) := mul_le_mul_of_nonneg_right (hTd _ hV hVl) (by positivity)
      _ = (Smax : ℝ) * Td := by ring
  rw [hLre, Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Complex.add_re]
  have hfirst : (∑ q ∈ Qs, ((((q : ℝ) * (τ 0 ^ K.card * κ 0) : ℝ)) : ℂ)).re =
      (∑ q ∈ Qs, (q : ℝ)) * τ 0 ^ K.card * κ 0 := by
    rw [← Complex.ofReal_sum, Complex.ofReal_re, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro q _; ring
  rw [hfirst]
  have hrest : (∑ q ∈ Qs, ∑ x ∈ PP.erase (0, 0), (tt x : ℂ) * ee ((V x : ℝ) * β) *
        (if (q : ℤ) ∣ V x then (q : ℂ) else 0)).re ≤
      (Smax : ℝ) * Td * (trigMass H τ ^ K.card * trigMass S κ) := by
    rw [Finset.sum_comm]
    refine (Complex.re_le_norm _).trans ((norm_sum_le _ _).trans ?_)
    calc ∑ x ∈ PP.erase (0, 0), ‖∑ q ∈ Qs, (tt x : ℂ) * ee ((V x : ℝ) * β) *
          (if (q : ℤ) ∣ V x then (q : ℂ) else 0)‖
        ≤ ∑ x ∈ PP.erase (0, 0), |tt x| * ((Smax : ℝ) * Td) := Finset.sum_le_sum hbound
      _ ≤ ∑ x ∈ PP, |tt x| * ((Smax : ℝ) * Td) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            (fun _ _ _ => mul_nonneg (abs_nonneg _) (by positivity))
      _ = (Smax : ℝ) * Td * (trigMass H τ ^ K.card * trigMass S κ) := by rw [← Finset.sum_mul, hA]; ring
  have : (Smax : ℝ) * Td * (trigMass H τ ^ K.card * trigMass S κ) =
      ((Qs.sup id : ℕ) : ℝ) * Td * trigMass H τ ^ K.card * trigMass S κ := by rw [hS]; ring
  linarith

end KappaOmega2
