import Palprimes.Squares.PropW
import Palprimes.ExpSum.LargeSieve
import Palprimes.Level.DivisorBound

/-! # M6, M7, M9. Prop. V in integer form: the Farey block

PROOF_buniform.md §2–§3, with integer block sizes instead of real exponents. For Farey pairs
`(q, h)` with `q ∈ [R, 2R]`, `(q, b) = 1`, `h` reduced, and a window `[w0, N)` of TP's indices
split (outer to inner) into `V`, `K3` (doubled), `K2` (single, shared), `K1` (doubled):
* first Cauchy–Schwarz between `V` and `U = K3 ∪ K2 ∪ K1`, second between `K1, K2` and `K3, K2`;
* `V` and `K3/K2` by the residue identity and a divisor count (`residue_bound`),
* `K1/K2` by the large sieve after the twist `h ↦ b^{N−ℓ} h` (`ls_bound`).
The outer digits `[1, w0)` are bounded separately (Col's bound, M8). -/

set_option linter.style.longLine false

open Finset Real

namespace Palprimes

/-- `‖Σ_x e(Z_x α)‖² = Σ_{x,x'} Re e((Z_x − Z_{x'})α)`. -/
theorem norm_sq_sum_ee_fam {X : Type*} [Fintype X] (Z : X → ℤ) (α : ℝ) :
    ‖∑ x : X, ee (Z x * α)‖ ^ 2 = ∑ x : X, ∑ x' : X, (ee (((Z x - Z x' : ℤ) : ℝ) * α)).re := by
  set F := ∑ x : X, ee (Z x * α)
  have h1 : ‖F‖ ^ 2 = (F * starRingEnd ℂ F).re := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [h1, map_sum, Finset.sum_mul_sum, Complex.re_sum]
  apply Finset.sum_congr rfl; intro x _
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl; intro x' _
  rw [conj_ee, ← ee_add]
  congr 2; push_cast; ring

/-- **Residue identity for a family** (any real shift `β`). -/
theorem sum_sq_fam_le (X : Type*) [Fintype X] (Z : X → ℤ) (q : ℕ) (hq : 0 < q) (β : ℝ) :
    ∑ h ∈ range q, ‖∑ x : X, ee (Z x * ((h : ℝ) / q + β))‖ ^ 2 ≤
      q * #((univ : Finset (X × X)).filter (fun p => (q : ℤ) ∣ Z p.1 - Z p.2)) := by
  simp_rw [norm_sq_sum_ee_fam]
  rw [Finset.sum_comm, Finset.card_filter, Fintype.sum_prod_type]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro x _
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum; intro x' _
  set k : ℤ := Z x - Z x'
  have hsum : ∑ h ∈ range q, (ee ((k : ℝ) * ((h : ℝ) / q + β))).re =
      (ee (k * β) * (if (q : ℤ) ∣ k then (q : ℂ) else 0)).re := by
    rw [← sum_ee_root q hq k, Finset.mul_sum, Complex.re_sum]
    apply Finset.sum_congr rfl; intro h _
    rw [← ee_add]; congr 3; ring
  have hk : ((k : ℤ) : ℝ) = (Z x : ℝ) - Z x' := by simp only [k]; push_cast; ring
  rw [← hk, hsum]
  split_ifs with hd
  · rw [show (q : ℂ) = ((q : ℝ) : ℂ) by push_cast; rfl, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    nlinarith [re_ee_le_one (k * β), (Nat.cast_nonneg q : (0 : ℝ) ≤ q)]
  · simp

theorem psiB_le_one (b : ℕ) (hb : 1 ≤ b) (t : ℝ) : psiB b t ≤ 1 := by
  unfold psiB
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_pow, div_le_one (by positivity)]
  have h := phiB_le b t
  have h0 := phiB_nonneg b t
  nlinarith

theorem psiB_nonneg (b : ℕ) (t : ℝ) : 0 ≤ psiB b t := by unfold psiB; positivity

theorem phiB_eq_sqrt (b : ℕ) (hb : 1 ≤ b) (t : ℝ) : phiB b t = b * Real.sqrt (psiB b t) := by
  unfold psiB
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  rw [Real.sqrt_sq (div_nonneg (phiB_nonneg b t) hb0.le)]
  field_simp

theorem PhiN_eq (b N : ℕ) (hb : 1 ≤ b) (α : ℝ) :
    PhiN b N α = (b : ℝ) ^ (N - 1) * ∏ n ∈ Ico 1 N, Real.sqrt (psiB b (cK b N n * α)) := by
  unfold PhiN
  have : ∀ n ∈ Ico 1 N, phiB b (α * ((b : ℝ) ^ n + (b : ℝ) ^ (2 * N - n))) =
      b * Real.sqrt (psiB b (cK b N n * α)) := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    rw [phiB_eq_sqrt b hb]
    congr 3
    simp [cK, hn.2]; ring
  rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ico]

/-- Counting divisibility over a family of moduli, with a common factor `M` removed. -/
theorem sum_card_dvd_le {X : Type*} [Fintype X] (Qs : Finset ℕ) (Z : X → ℤ) (M W : ℤ)
    (_hM : M ≠ 0) (hstruct : ∀ x, ∃ t, Z x = M * t ∧ |t| ≤ W)
    (hcop : ∀ q ∈ Qs, IsCoprime (q : ℤ) M) (T : ℝ) (hT0 : 0 ≤ T)
    (hT : ∀ w : ℤ, w ≠ 0 → |w| ≤ W → (#(Qs.filter (fun q : ℕ => (q : ℤ) ∣ w)) : ℝ) ≤ T) :
    ∑ q ∈ Qs, (#((univ : Finset X).filter (fun x => (q : ℤ) ∣ Z x)) : ℝ) ≤
      #Qs * #((univ : Finset X).filter (fun x => Z x = 0)) + Fintype.card X * T := by
  classical
  have hswap : ∑ q ∈ Qs, (#((univ : Finset X).filter (fun x => (q : ℤ) ∣ Z x)) : ℝ) =
      ∑ x : X, (#(Qs.filter (fun q : ℕ => (q : ℤ) ∣ Z x)) : ℝ) := by
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    exact Finset.sum_comm
  rw [hswap]
  have hpt : ∀ x : X, (#(Qs.filter (fun q : ℕ => (q : ℤ) ∣ Z x)) : ℝ) ≤
      (if Z x = 0 then (#Qs : ℝ) else 0) + T := by
    intro x
    obtain ⟨t, ht, htW⟩ := hstruct x
    by_cases hx : Z x = 0
    · rw [ite_eq_left hx]
      have : (#(Qs.filter (fun q : ℕ => (q : ℤ) ∣ Z x)) : ℝ) ≤ #Qs := by
        exact_mod_cast card_le_card (filter_subset _ _)
      linarith
    · rw [ite_eq_right hx, zero_add]
      have ht0 : t ≠ 0 := by rintro rfl; rw [mul_zero] at ht; exact hx ht
      have e : Qs.filter (fun q : ℕ => (q : ℤ) ∣ Z x) = Qs.filter (fun q : ℕ => (q : ℤ) ∣ t) := by
        apply Finset.filter_congr
        intro q hq
        rw [ht]
        exact ⟨fun h => (hcop q hq).dvd_of_dvd_mul_left h, fun h => Dvd.dvd.mul_left h M⟩
      rw [e]
      exact hT t ht0 htW
  calc ∑ x : X, (#(Qs.filter (fun q : ℕ => (q : ℤ) ∣ Z x)) : ℝ)
      ≤ ∑ x : X, ((if Z x = 0 then (#Qs : ℝ) else 0) + T) := Finset.sum_le_sum (fun x _ => hpt x)
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- `Π_A ψ² Π_B ψ` as a normalized exponential sum over pairs of digit vectors. -/
theorem piK_eq_expsum (b N : ℕ) (hb : 2 ≤ b) (A B : Finset ℕ) (hA : A ⊆ range (N + 1))
    (hB : B ⊆ range (N + 1)) (hAB : Disjoint A B) (α : ℝ) :
    piK b N A α ^ 2 * piK b N B α =
      ‖∑ w : DigVec b N × DigVec b N, ee ((yVal b N A B (extDig w.1) (extDig w.2) : ℝ) * α)‖ ^ 2 /
        (b : ℝ) ^ (4 * (N + 1)) := by
  rw [← fourier_yVal b N hb A B hA hB hAB α, norm_div, div_pow, norm_pow, Complex.norm_natCast,
    ← pow_mul, show 2 * (N + 1) * 2 = 4 * (N + 1) by ring]

/-- **Residue step** for a general family. -/
theorem residue_step_gen (X : Type*) [Fintype X] (Y : X → ℕ) (C : ℝ) (hC : 0 < C)
    (Pf : ℝ → ℝ) (hPf0 : ∀ α, 0 ≤ Pf α)
    (hPf : ∀ α, Pf α = ‖∑ x : X, ee ((Y x : ℝ) * α)‖ ^ 2 / C)
    (Qs : Finset ℕ) (hQ0 : ∀ q ∈ Qs, 0 < q) (β : ℝ) :
    ∑ q ∈ Qs, ∑ h ∈ redRes q, Pf ((h : ℝ) / q + β) ≤
      ∑ q ∈ Qs, (q : ℝ) * #((univ : Finset (X × X)).filter
        (fun p => (q : ℤ) ∣ (Y p.1 : ℤ) - (Y p.2 : ℤ))) / C := by
  apply Finset.sum_le_sum
  intro q hq
  have hq0 := hQ0 q hq
  have key := sum_sq_fam_le X (fun x => (Y x : ℤ)) q hq0 β
  simp only [Int.cast_natCast] at key
  calc ∑ h ∈ redRes q, Pf ((h : ℝ) / q + β) ≤ ∑ h ∈ range q, Pf ((h : ℝ) / q + β) :=
        Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun h _ _ => hPf0 _)
    _ = (∑ h ∈ range q, ‖∑ x : X, ee ((Y x : ℝ) * ((h : ℝ) / q + β))‖ ^ 2) / C := by
        rw [Finset.sum_div]; exact Finset.sum_congr rfl (fun h _ => hPf _)
    _ ≤ _ := div_le_div_of_nonneg_right key hC.le

theorem card_eq_sum_sq_nat {X : Type*} [Fintype X] (Y : X → ℕ) (N1 : ℕ) (hY : ∀ x, Y x < N1) :
    (#((univ : Finset (X × X)).filter (fun p => Y p.1 = Y p.2)) : ℝ) =
      ∑ n ∈ range N1, ((#((univ : Finset X).filter (fun x => Y x = n)) : ℝ)) ^ 2 := by
  classical
  have h := card_filter_eq_sum_fiber (fun x => (Y x : ℤ)) (fun x => (Y x : ℤ))
    ((range N1).image (fun n : ℕ => (n : ℤ))) (fun x => Finset.mem_image.2 ⟨Y x, mem_range.2 (hY x), rfl⟩)
  rw [Finset.sum_image (fun a _ c _ h => by exact_mod_cast h)] at h
  have e1 : (univ : Finset (X × X)).filter (fun p => (Y p.1 : ℤ) = (Y p.2 : ℤ)) =
      (univ : Finset (X × X)).filter (fun p => Y p.1 = Y p.2) := by
    ext p; simp
  have e2 : ∀ n : ℕ, (univ : Finset X).filter (fun x => (Y x : ℤ) = (n : ℤ)) =
      (univ : Finset X).filter (fun x => Y x = n) := by
    intro n; ext x; simp
  rw [e1] at h
  simp only [e2] at h
  rw [h]; push_cast; simp only [sq]

/-- **Large-sieve step** for an inner block whose values carry the factor `b^m`. -/
theorem ls_step (b m : ℕ) (_hb : 2 ≤ b) (X : Type*) [Fintype X] (Y Y' : X → ℕ) (N1 : ℕ)
    (hYY : ∀ x, Y x = b ^ m * Y' x) (hY' : ∀ x, Y' x < N1) (C : ℝ) (hC : 0 < C)
    (Pf : ℝ → ℝ) (hPf : ∀ α, Pf α = ‖∑ x : X, ee ((Y x : ℝ) * α)‖ ^ 2 / C)
    (R : ℕ) (hR : 1 ≤ R) (Qs : Finset ℕ) (hQs : ∀ q ∈ Qs, R ≤ q ∧ q ≤ 2 * R ∧ Nat.Coprime q b)
    (β : ℝ) :
    ∑ q ∈ Qs, ∑ h ∈ redRes q, Pf ((h : ℝ) / q + β) ≤
      (4 * N1 + 12 * (R : ℝ) ^ 2 + 2) *
        #((univ : Finset (X × X)).filter (fun p => Y' p.1 = Y' p.2)) / C := by
  classical
  set pts := Qs.sigma (fun q => redRes q)
  set xp : (Σ _ : ℕ, ℕ) → ℝ := fun p => (b : ℝ) ^ m * ((p.2 : ℝ) / p.1 + β)
  set a : ℕ → ℂ := fun n => (#((univ : Finset X).filter (fun x => Y' x = n)) : ℂ)
  -- the exponential sum in the large-sieve form
  have hterm : ∀ (α : ℝ) (n : ℕ), ∑ x ∈ (univ : Finset X).filter (fun x => Y' x = n),
      ee ((Y x : ℝ) * α) = a n * ee ((n : ℝ) * ((b : ℝ) ^ m * α)) := by
    intro α n
    rw [Finset.sum_congr rfl (g := fun _ => ee ((n : ℝ) * ((b : ℝ) ^ m * α))) (fun x hx => by
      rw [hYY x, (Finset.mem_filter.1 hx).2]; congr 1; push_cast; ring)]
    rw [Finset.sum_const, nsmul_eq_mul]
  have hexp : ∀ α : ℝ, ∑ x : X, ee ((Y x : ℝ) * α) =
      ∑ n ∈ range N1, a n * ee ((n : ℝ) * ((b : ℝ) ^ m * α)) := by
    intro α
    rw [← Finset.sum_fiberwise_of_maps_to (g := Y') (t := range N1)
      (fun x _ => mem_range.2 (hY' x))]
    exact Finset.sum_congr rfl (fun n _ => hterm α n)
  -- spacing of the twisted points
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
  -- apply the large sieve
  have hls := large_sieve pts xp _ hδ hsep N1 a
  have hsq : ∑ n ∈ range N1, ‖a n‖ ^ 2 =
      #((univ : Finset (X × X)).filter (fun p => Y' p.1 = Y' p.2)) := by
    rw [card_eq_sum_sq_nat Y' N1 hY']
    apply Finset.sum_congr rfl; intro n _
    simp [a]
  have hlhs : ∑ q ∈ Qs, ∑ h ∈ redRes q, Pf ((h : ℝ) / q + β) =
      (∑ p ∈ pts, ‖∑ n ∈ range N1, a n * ee ((n : ℝ) * xp p)‖ ^ 2) / C := by
    rw [Finset.sum_div, Finset.sum_sigma]
    apply Finset.sum_congr rfl; intro q _
    apply Finset.sum_congr rfl; intro h _
    rw [hPf, hexp]
  rw [hlhs]
  apply div_le_div_of_nonneg_right _ hC.le
  have h12 : (3 : ℝ) / (1 / (4 * (R : ℝ) ^ 2)) = 12 * (R : ℝ) ^ 2 := by field_simp; ring
  calc _ ≤ _ := hls
    _ = _ := by rw [h12, hsq]


/-! ## The Farey block -/

theorem piK_empty (b L : ℕ) (α : ℝ) : piK b L ∅ α = 1 := by simp [piK]

theorem piK_nonneg (b L : ℕ) (K : Finset ℕ) (α : ℝ) : 0 ≤ piK b L K α :=
  Finset.prod_nonneg (fun _ _ => psiB_nonneg _ _)

theorem yVal_empty (b N : ℕ) (B : Finset ℕ) (d d' : ℕ → ℕ) :
    yVal b N ∅ B d d' = ∑ k ∈ B, d k * cK b N k := by simp [yVal]

/-- Exact collision count of `Y = yVal A B` over pairs of pairs. -/
theorem card_yVal_eq (b N : ℕ) (hb : 2 ≤ b) (A B : Finset ℕ) (hA : A ⊆ range (N + 1))
    (hB : B ⊆ range (N + 1)) (hAB : Disjoint A B) :
    (#((univ : Finset ((DigVec b N × DigVec b N) × (DigVec b N × DigVec b N))).filter
      (fun p => yVal b N A B (extDig p.1.1) (extDig p.1.2) = yVal b N A B (extDig p.2.1) (extDig p.2.2))) : ℝ) =
      (b : ℝ) ^ (4 * (N + 1)) * (((2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 3)) ^ #A *
        ((b : ℝ) ^ #B)⁻¹) := by
  rw [← card_Y_eq_pairs b N hb A B hA hB hAB]
  have e : (univ : Finset ((DigVec b N × DigVec b N) × (DigVec b N × DigVec b N))).filter
      (fun p => yVal b N A B (extDig p.1.1) (extDig p.1.2) = yVal b N A B (extDig p.2.1) (extDig p.2.2)) =
      (univ : Finset ((DigVec b N × DigVec b N) × (DigVec b N × DigVec b N))).filter
      (fun p => Ypair b N A B p.1 = Ypair b N A B p.2) := by
    apply Finset.filter_congr
    intro p _
    simp only [Ypair]
    rw [← yVal_eq_blk, ← yVal_eq_blk]
    exact_mod_cast Iff.rfl
  rw [e]

/-- Residue + divisor step with explicit output `2R (#Qs ρ + T)`. -/
theorem residue_bound (b N : ℕ) (hb : 2 ≤ b) (A B : Finset ℕ) (hA : A ⊆ range (N + 1))
    (hB : B ⊆ range (N + 1)) (hAB : Disjoint A B) (w0 ℓ' : ℕ)
    (hpos : ∀ k ∈ A ∪ B, w0 ≤ k ∧ k ≤ N) (hcard : #(A ∪ B) ≤ ℓ')
    (R : ℕ) (Qs : Finset ℕ) (hQs : ∀ q ∈ Qs, R ≤ q ∧ q ≤ 2 * R ∧ Nat.Coprime q b) (hR : 1 ≤ R)
    (T : ℝ) (hT0 : 0 ≤ T)
    (hT : ∀ w : ℤ, w ≠ 0 → |w| ≤ ((8 * b * ℓ' * b ^ (2 * (N - w0)) + 1 : ℕ) : ℤ) →
      (#(Qs.filter (fun q : ℕ => (q : ℤ) ∣ w)) : ℝ) ≤ T) (β : ℝ) :
    ∑ q ∈ Qs, ∑ h ∈ redRes q, piK b N A ((h : ℝ) / q + β) ^ 2 * piK b N B ((h : ℝ) / q + β) ≤
      2 * R * (#Qs * (((2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 3)) ^ #A * ((b : ℝ) ^ #B)⁻¹) + T) := by
  classical
  have hb1 : 1 ≤ b := by omega
  set C : ℝ := (b : ℝ) ^ (4 * (N + 1)) with hC
  have hC0 : 0 < C := by positivity
  set Y : DigVec b N × DigVec b N → ℕ := fun w => yVal b N A B (extDig w.1) (extDig w.2)
  have h1 := residue_step_gen (DigVec b N × DigVec b N) Y C hC0
    (fun α => piK b N A α ^ 2 * piK b N B α)
    (fun α => mul_nonneg (sq_nonneg _) (piK_nonneg _ _ _ _))
    (fun α => piK_eq_expsum b N hb A B hA hB hAB α) Qs (fun q hq => by have := (hQs q hq).1; omega) β
  refine h1.trans ?_
  -- bound q by 2R and count divisibility
  have hstruct : ∀ x : (DigVec b N × DigVec b N) × (DigVec b N × DigVec b N),
      ∃ t, ((Y x.1 : ℤ) - (Y x.2 : ℤ)) = ((b ^ w0 : ℕ) : ℤ) * t ∧
        |t| ≤ ((8 * b * ℓ' * b ^ (2 * (N - w0)) + 1 : ℕ) : ℤ) := by
    intro x
    obtain ⟨t, ht, htW⟩ := Y_diff_struct b N w0 ℓ' hb1 A B hAB hpos hcard x.1 x.2
    refine ⟨t, ?_, htW.le⟩
    simp only [Y]
    rw [yVal_eq_blk, yVal_eq_blk, ht]
    push_cast; ring
  have hcop : ∀ q ∈ Qs, IsCoprime (q : ℤ) ((b ^ w0 : ℕ) : ℤ) := by
    intro q hq
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact Nat.Coprime.pow_right w0 (hQs q hq).2.2
  have h2 := sum_card_dvd_le Qs (fun x : (DigVec b N × DigVec b N) × (DigVec b N × DigVec b N) =>
      (Y x.1 : ℤ) - (Y x.2 : ℤ)) _ _ (by positivity) hstruct hcop T hT0 hT
  have hzero : ((univ : Finset ((DigVec b N × DigVec b N) × (DigVec b N × DigVec b N))).filter
      (fun x => (Y x.1 : ℤ) - (Y x.2 : ℤ) = 0)) =
      (univ : Finset ((DigVec b N × DigVec b N) × (DigVec b N × DigVec b N))).filter
      (fun p => yVal b N A B (extDig p.1.1) (extDig p.1.2) = yVal b N A B (extDig p.2.1) (extDig p.2.2)) := by
    ext x; simp only [mem_filter, mem_univ, true_and, sub_eq_zero, Y]; exact_mod_cast Iff.rfl
  rw [hzero, card_yVal_eq b N hb A B hA hB hAB] at h2
  have hcardX : (Fintype.card ((DigVec b N × DigVec b N) × (DigVec b N × DigVec b N)) : ℝ) = C := by
    rw [hC, Fintype.card_prod, card_pairs]; push_cast; ring
  rw [hcardX] at h2
  set ρ : ℝ := ((2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 3)) ^ #A * ((b : ℝ) ^ #B)⁻¹
  calc ∑ q ∈ Qs, (q : ℝ) * #((univ : Finset ((DigVec b N × DigVec b N) × (DigVec b N × DigVec b N))).filter
        (fun p => (q : ℤ) ∣ (Y p.1 : ℤ) - (Y p.2 : ℤ))) / C
      ≤ ∑ q ∈ Qs, (2 * R : ℝ) * #((univ : Finset ((DigVec b N × DigVec b N) × (DigVec b N × DigVec b N))).filter
        (fun p => (q : ℤ) ∣ (Y p.1 : ℤ) - (Y p.2 : ℤ))) / C := by
        apply Finset.sum_le_sum; intro q hq
        apply div_le_div_of_nonneg_right _ hC0.le
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        have := (hQs q hq).2.1
        exact_mod_cast this
    _ = (2 * R : ℝ) / C * ∑ q ∈ Qs, (#((univ : Finset ((DigVec b N × DigVec b N) × (DigVec b N × DigVec b N))).filter
        (fun p => (q : ℤ) ∣ (Y p.1 : ℤ) - (Y p.2 : ℤ))) : ℝ) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring
    _ ≤ (2 * R : ℝ) / C * (#Qs * (C * ρ) + C * T) := by
        apply mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 2 * R * (#Qs * ρ + T) := by field_simp

theorem cK_div_spec (b N k m0 : ℕ) (hb : 1 ≤ b) (hk : m0 ≤ k) (hkN : k ≤ N) :
    cK b N k = b ^ m0 * (cK b N k / b ^ m0) ∧ cK b N k / b ^ m0 ≤ 2 * b ^ (2 * (N - m0)) := by
  obtain ⟨c', hc', hle⟩ := cK_factor b N k m0 hb hk hkN
  have hpos : 0 < b ^ m0 := by positivity
  rw [hc', Nat.mul_div_cancel_left _ hpos]
  exact ⟨rfl, hle⟩

/-- **Large-sieve bound** for the doubled/single inner block (`K1 ∪ K2 ⊆ [m0, N]`). -/
theorem ls_bound (b N : ℕ) (hb : 2 ≤ b) (A B : Finset ℕ) (hA : A ⊆ range (N + 1))
    (hB : B ⊆ range (N + 1)) (hAB : Disjoint A B) (m0 ℓ : ℕ)
    (hpos : ∀ k ∈ A ∪ B, m0 ≤ k ∧ k ≤ N) (hcard : #(A ∪ B) ≤ ℓ)
    (R : ℕ) (hR : 1 ≤ R) (Qs : Finset ℕ) (hQs : ∀ q ∈ Qs, R ≤ q ∧ q ≤ 2 * R ∧ Nat.Coprime q b)
    (β : ℝ) :
    ∑ q ∈ Qs, ∑ h ∈ redRes q, piK b N A ((h : ℝ) / q + β) ^ 2 * piK b N B ((h : ℝ) / q + β) ≤
      (4 * ((4 * b * ℓ * b ^ (2 * (N - m0)) + 1 : ℕ) : ℝ) + 12 * (R : ℝ) ^ 2 + 2) *
        (((2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 3)) ^ #A * ((b : ℝ) ^ #B)⁻¹) := by
  classical
  have hb1 : 1 ≤ b := by omega
  set C : ℝ := (b : ℝ) ^ (4 * (N + 1)) with hC
  have hC0 : 0 < C := by positivity
  set c' : ℕ → ℕ := fun k => cK b N k / b ^ m0
  set Y : DigVec b N × DigVec b N → ℕ := fun w => yVal b N A B (extDig w.1) (extDig w.2)
  set Y' : DigVec b N × DigVec b N → ℕ := fun w =>
    ∑ k ∈ A, (extDig w.1 k + extDig w.2 k) * c' k + ∑ k ∈ B, extDig w.1 k * c' k
  have hYY : ∀ w, Y w = b ^ m0 * Y' w := by
    intro w
    simp only [Y, Y', yVal, mul_add, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl; intro k hk
      rw [(cK_div_spec b N k m0 hb1 (hpos k (mem_union_left _ hk)).1
        (hpos k (mem_union_left _ hk)).2).1]
      ring
    · apply Finset.sum_congr rfl; intro k hk
      rw [(cK_div_spec b N k m0 hb1 (hpos k (mem_union_right _ hk)).1
        (hpos k (mem_union_right _ hk)).2).1]
      ring
  have hY' : ∀ w, Y' w < 4 * b * ℓ * b ^ (2 * (N - m0)) + 1 := by
    intro w
    have hle : Y' w ≤ ∑ k ∈ A ∪ B, 2 * b * (2 * b ^ (2 * (N - m0))) := by
      simp only [Y']
      rw [Finset.sum_union hAB]
      apply Nat.add_le_add
      · apply Finset.sum_le_sum; intro k hk
        have h1 := extDig_le hb1 w.1 k
        have h2 := extDig_le hb1 w.2 k
        have h3 := (cK_div_spec b N k m0 hb1 (hpos k (mem_union_left _ hk)).1
          (hpos k (mem_union_left _ hk)).2).2
        exact Nat.mul_le_mul (by omega) h3
      · apply Finset.sum_le_sum; intro k hk
        have h1 := extDig_le hb1 w.1 k
        have h3 := (cK_div_spec b N k m0 hb1 (hpos k (mem_union_right _ hk)).1
          (hpos k (mem_union_right _ hk)).2).2
        exact Nat.mul_le_mul (by omega) h3
    rw [Finset.sum_const, smul_eq_mul] at hle
    have : #(A ∪ B) * (2 * b * (2 * b ^ (2 * (N - m0)))) ≤ ℓ * (2 * b * (2 * b ^ (2 * (N - m0)))) :=
      Nat.mul_le_mul_right _ hcard
    nlinarith
  have h := ls_step b m0 hb (DigVec b N × DigVec b N) Y Y' _ hYY hY' C hC0
    (fun α => piK b N A α ^ 2 * piK b N B α) (fun α => piK_eq_expsum b N hb A B hA hB hAB α)
    R hR Qs hQs β
  refine h.trans (le_of_eq ?_)
  have hcoll : ((univ : Finset ((DigVec b N × DigVec b N) × (DigVec b N × DigVec b N))).filter
      (fun p => Y' p.1 = Y' p.2)) =
      (univ : Finset ((DigVec b N × DigVec b N) × (DigVec b N × DigVec b N))).filter
      (fun p => yVal b N A B (extDig p.1.1) (extDig p.1.2) = yVal b N A B (extDig p.2.1) (extDig p.2.2)) := by
    apply Finset.filter_congr
    intro p _
    have e1 := hYY p.1
    have e2 := hYY p.2
    simp only [Y] at e1 e2
    rw [e1, e2]
    have hpos' : 0 < b ^ m0 := by positivity
    exact ⟨fun h => by rw [h], fun h => Nat.eq_of_mul_eq_mul_left hpos' h⟩
  rw [hcoll, card_yVal_eq b N hb A B hA hB hAB, ← hC]
  field_simp

/-- Cauchy–Schwarz over Farey pairs `(q, h)`. -/
theorem cs_farey (Qs : Finset ℕ) (f g : ℕ → ℕ → ℝ) (hf : ∀ q h, 0 ≤ f q h) (hg : ∀ q h, 0 ≤ g q h) :
    ∑ q ∈ Qs, ∑ h ∈ redRes q, Real.sqrt (f q h) * Real.sqrt (g q h) ≤
      Real.sqrt (∑ q ∈ Qs, ∑ h ∈ redRes q, f q h) * Real.sqrt (∑ q ∈ Qs, ∑ h ∈ redRes q, g q h) := by
  rw [Finset.sum_sigma' Qs (fun q => redRes q) (fun q h => Real.sqrt (f q h) * Real.sqrt (g q h)),
    Finset.sum_sigma' Qs (fun q => redRes q) f, Finset.sum_sigma' Qs (fun q => redRes q) g]
  have := Real.sum_mul_le_sqrt_mul_sqrt (Qs.sigma (fun q => redRes q))
    (fun p => Real.sqrt (f p.1 p.2)) (fun p => Real.sqrt (g p.1 p.2))
  simpa [Real.sq_sqrt (hf _ _), Real.sq_sqrt (hg _ _)] using this

theorem prod_sqrt_eq (s : Finset ℕ) (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n) :
    ∏ n ∈ s, Real.sqrt (F n) = Real.sqrt (∏ n ∈ s, F n) := by
  rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq (Finset.prod_nonneg (fun n _ => hF n))
    (Finset.prod_nonneg (fun n _ => Real.sqrt_nonneg _)), ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl; intro n _
  rw [Real.mul_self_sqrt (hF n)]

theorem piK3_nonneg (b N : ℕ) (K1 K2 K3 : Finset ℕ) (α : ℝ) :
    0 ≤ piK b N K1 α * piK b N K2 α * piK b N K3 α :=
  mul_nonneg (mul_nonneg (piK_nonneg _ _ _ _) (piK_nonneg _ _ _ _)) (piK_nonneg _ _ _ _)

theorem piK12_nonneg (b N : ℕ) (K1 K2 : Finset ℕ) (α : ℝ) :
    0 ≤ piK b N K1 α ^ 2 * piK b N K2 α :=
  mul_nonneg (sq_nonneg _) (piK_nonneg _ _ _ _)

/-- **Farey block bound** (window `[w0, N)` with `w0 = N − ℓ − m − v`). -/
theorem farey_block (b N ℓ a m v R : ℕ) (hb : 2 ≤ b) (ha : a ≤ ℓ) (hlay : ℓ + m + v + 1 ≤ N)
    (hR : 1 ≤ R) (Qs : Finset ℕ) (hQs : ∀ q ∈ Qs, R ≤ q ∧ q ≤ 2 * R ∧ Nat.Coprime q b)
    (T : ℝ) (hT0 : 0 ≤ T)
    (hT : ∀ w : ℤ, w ≠ 0 →
      |w| ≤ ((8 * b * (ℓ + m + v) * b ^ (2 * (N - (N - ℓ - m - v))) + 1 : ℕ) : ℤ) →
      (#(Qs.filter (fun q : ℕ => (q : ℤ) ∣ w)) : ℝ) ≤ T) (β : ℝ) :
    ∑ q ∈ Qs, ∑ h ∈ redRes q, ∏ n ∈ Ico (N - ℓ - m - v) N,
        Real.sqrt (psiB b (cK b N n * ((h : ℝ) / q + β))) ≤
      Real.sqrt (2 * R * (#Qs * ((b : ℝ) ^ v)⁻¹ + T)) *
        Real.sqrt (Real.sqrt ((4 * ((4 * b * ℓ * b ^ (2 * (N - (N - ℓ))) + 1 : ℕ) : ℝ) +
            12 * (R : ℝ) ^ 2 + 2) *
            (((2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 3)) ^ a * ((b : ℝ) ^ (ℓ - a))⁻¹)) *
          Real.sqrt (2 * R * (#Qs * (((2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 3)) ^ m *
            ((b : ℝ) ^ (ℓ - a))⁻¹) + T))) := by
  set w0 := N - ℓ - m - v with hw0
  set K1 := Ico (N - a) N
  set K2 := Ico (N - ℓ) (N - a)
  set K3 := Ico (N - ℓ - m) (N - ℓ)
  set V := Ico w0 (N - ℓ - m)
  have hsub : ∀ {s t : ℕ}, t ≤ N → Ico s t ⊆ range (N + 1) := by
    intro s t ht k hk; rw [mem_Ico] at hk; rw [mem_range]; omega
  have hK1 : K1 ⊆ range (N + 1) := hsub le_rfl
  have hK2 : K2 ⊆ range (N + 1) := hsub (by omega)
  have hK3 : K3 ⊆ range (N + 1) := hsub (by omega)
  have hV : V ⊆ range (N + 1) := hsub (by omega)
  have d12 : Disjoint K1 K2 := by
    rw [Finset.disjoint_left]; intro k h1 h2; rw [mem_Ico] at h1 h2; omega
  have d32 : Disjoint K3 K2 := by
    rw [Finset.disjoint_left]; intro k h1 h2; rw [mem_Ico] at h1 h2; omega
  have cK1 : #K1 = a := by simp only [K1, Nat.card_Ico]; omega
  have cK2 : #K2 = ℓ - a := by simp only [K2, Nat.card_Ico]; omega
  have cK3 : #K3 = m := by simp only [K3, Nat.card_Ico]; omega
  have cV : #V = v := by simp only [V, Nat.card_Ico]; omega
  -- the window splits into V, K3, K2, K1
  have hwin : Ico w0 N = V ∪ (K3 ∪ (K2 ∪ K1)) := by
    ext k; simp only [mem_Ico, mem_union, V, K1, K2, K3]; omega
  have hdisj1 : Disjoint V (K3 ∪ (K2 ∪ K1)) := by
    rw [Finset.disjoint_left]; intro k h1 h2
    simp only [mem_Ico, mem_union, V, K1, K2, K3] at h1 h2; omega
  have hdisj2 : Disjoint K3 (K2 ∪ K1) := by
    rw [Finset.disjoint_left]; intro k h1 h2
    simp only [mem_Ico, mem_union, K1, K2, K3] at h1 h2; omega
  have hdisj3 : Disjoint K2 K1 := d12.symm
  have hsplit : ∀ α : ℝ, ∏ n ∈ Ico w0 N, Real.sqrt (psiB b (cK b N n * α)) =
      Real.sqrt (piK b N ∅ α ^ 2 * piK b N V α) *
        Real.sqrt (piK b N K1 α * piK b N K2 α * piK b N K3 α) := by
    intro α
    rw [hwin, Finset.prod_union hdisj1, Finset.prod_union hdisj2, Finset.prod_union hdisj3,
      prod_sqrt_eq _ _ (fun n => psiB_nonneg _ _), prod_sqrt_eq _ _ (fun n => psiB_nonneg _ _),
      prod_sqrt_eq _ _ (fun n => psiB_nonneg _ _), prod_sqrt_eq _ _ (fun n => psiB_nonneg _ _),
      piK_empty, one_pow, one_mul]
    unfold piK
    rw [← Real.sqrt_mul (Finset.prod_nonneg (fun _ _ => psiB_nonneg _ _)),
      ← Real.sqrt_mul (Finset.prod_nonneg (fun _ _ => psiB_nonneg _ _))]
    congr 2; ring
  have hU : ∀ α : ℝ, piK b N K1 α * piK b N K2 α * piK b N K3 α =
      Real.sqrt (piK b N K1 α ^ 2 * piK b N K2 α) * Real.sqrt (piK b N K3 α ^ 2 * piK b N K2 α) := by
    intro α
    rw [← Real.sqrt_mul (piK12_nonneg b N K1 K2 α),
      show piK b N K1 α ^ 2 * piK b N K2 α * (piK b N K3 α ^ 2 * piK b N K2 α) =
      (piK b N K1 α * piK b N K2 α * piK b N K3 α) ^ 2 by ring,
      Real.sqrt_sq (piK3_nonneg b N K1 K2 K3 α)]
  set α : ℕ → ℕ → ℝ := fun q h => (h : ℝ) / q + β
  simp only [hsplit]
  -- first Cauchy–Schwarz
  refine (cs_farey Qs (fun q h => piK b N ∅ (α q h) ^ 2 * piK b N V (α q h))
    (fun q h => piK b N K1 (α q h) * piK b N K2 (α q h) * piK b N K3 (α q h))
    (fun q h => mul_nonneg (sq_nonneg _) (piK_nonneg _ _ _ _))
    (fun q h => piK3_nonneg b N K1 K2 K3 (α q h))).trans ?_
  apply mul_le_mul _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · -- V block
    apply Real.sqrt_le_sqrt
    have h := residue_bound b N hb ∅ V (empty_subset _) hV (disjoint_empty_left _) w0 (ℓ + m + v)
      (fun k hk => by rw [empty_union] at hk; simp only [V, mem_Ico] at hk; omega)
      (by rw [empty_union, cV]; omega) R Qs hQs hR T hT0 hT β
    rw [card_empty, pow_zero, one_mul, cV] at h
    exact h
  · -- U block: second Cauchy–Schwarz
    apply Real.sqrt_le_sqrt
    have hU' : ∀ q h, piK b N K1 (α q h) * piK b N K2 (α q h) * piK b N K3 (α q h) =
        Real.sqrt (piK b N K1 (α q h) ^ 2 * piK b N K2 (α q h)) *
          Real.sqrt (piK b N K3 (α q h) ^ 2 * piK b N K2 (α q h)) := fun q h => hU _
    simp only [hU']
    refine (cs_farey Qs _ _ (fun q h => mul_nonneg (sq_nonneg _) (piK_nonneg _ _ _ _))
      (fun q h => mul_nonneg (sq_nonneg _) (piK_nonneg _ _ _ _))).trans ?_
    apply mul_le_mul _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    · apply Real.sqrt_le_sqrt
      have h := ls_bound b N hb K1 K2 hK1 hK2 d12 (N - ℓ) ℓ
        (fun k hk => by simp only [K1, K2, mem_union, mem_Ico] at hk; omega)
        (by rw [Finset.card_union_of_disjoint d12, cK1, cK2]; omega) R hR Qs hQs β
      rw [cK1, cK2] at h
      exact h
    · apply Real.sqrt_le_sqrt
      have h := residue_bound b N hb K3 K2 hK3 hK2 d32 w0 (ℓ + m + v)
        (fun k hk => by simp only [K3, K2, mem_union, mem_Ico] at hk; omega)
        (by rw [Finset.card_union_of_disjoint d32, cK3, cK2]; omega) R Qs hQs hR T hT0 hT β
      rw [cK3, cK2] at h
      exact h

end Palprimes
