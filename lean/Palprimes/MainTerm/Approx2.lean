import Palprimes.MainTerm.Reduce
import Palprimes.MainTerm.JR
import Palprimes.MainTerm.VB

/-! Merged from the former `Approx1.lean` (to keep the import depth below the lake limit). -/

/-! # Analytic helpers for the main-term asymptotics

* `VB_pos`, `VB_split`, `prod_one_add_le` (`Π_{[lo,hi)} (1 + g) ≤ V(lo)/V(hi)`), `sum_le_prod_one_add`;
* `VB_ratio`: `V(w)/V(y) = log y / log w + o(1)` uniformly in `y^a ≤ w ≤ y`;
* `chain_range`: a Rosser chain ending at `p` leaves `z' ≥ p` (odd length) or `z' ≥ p²` (even length);
* `leaf_E1`: E1 at a chain leaf. -/

set_option linter.style.longLine false

open Finset Real

namespace Palprimes.MT

open Palprimes.Greaves

theorem gB_le_half (b p : ℕ) : gB b p ≤ 1 / 2 := by
  unfold gB; split_ifs with h
  · have : (2 : ℝ) ≤ p := by exact_mod_cast h.1.two_le
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  · norm_num

theorem VB_pos (b : ℕ) (w : ℝ) : 0 < VB b w := by
  unfold VB; apply Finset.prod_pos; intro p _; linarith [gB_le_half b p]

theorem primesBelow_filter_lt' (lo hi : ℝ) (h : lo ≤ hi) :
    (primesBelow hi).filter (fun q : ℕ => (q : ℝ) < lo) = primesBelow lo := by
  ext q; rw [Finset.mem_filter, mem_primesBelow, mem_primesBelow]
  constructor
  · rintro ⟨⟨hq, _⟩, h2⟩; exact ⟨hq, h2⟩
  · rintro ⟨hq, h2⟩; exact ⟨⟨hq, by linarith⟩, h2⟩

/-- The primes in `[lo, hi)`. -/
noncomputable def pIco (lo hi : ℝ) : Finset ℕ := (primesBelow hi).filter (fun q : ℕ => ¬ (q : ℝ) < lo)

theorem mem_pIco (lo hi : ℝ) (q : ℕ) : q ∈ pIco lo hi ↔ q.Prime ∧ lo ≤ q ∧ (q : ℝ) < hi := by
  unfold pIco; rw [Finset.mem_filter, mem_primesBelow, not_lt]; tauto

theorem VB_split (b : ℕ) (lo hi : ℝ) (h : lo ≤ hi) :
    VB b hi = VB b lo * ∏ q ∈ pIco lo hi, (1 - gB b q) := by
  unfold VB pIco
  rw [← Finset.prod_filter_mul_prod_filter_not (primesBelow hi) (fun q : ℕ => (q : ℝ) < lo),
    primesBelow_filter_lt' lo hi h]

theorem prod_one_add_le (b : ℕ) (lo hi : ℝ) (h : lo ≤ hi) :
    ∏ q ∈ pIco lo hi, (1 + gB b q) ≤ VB b lo / VB b hi := by
  have hpos : 0 < ∏ q ∈ pIco lo hi, (1 - gB b q) := by
    apply Finset.prod_pos; intro q _; linarith [gB_le_half b q]
  have hV := VB_pos b lo
  rw [VB_split b lo hi h, show VB b lo / (VB b lo * ∏ q ∈ pIco lo hi, (1 - gB b q)) =
    1 / ∏ q ∈ pIco lo hi, (1 - gB b q) by field_simp, le_div_iff₀ hpos, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_one₀
  · intro q _; have := gB_le_half b q; have := gB_nonneg b q; nlinarith
  · intro q _; have := gB_nonneg b q; nlinarith

theorem sum_le_prod_one_add (b : ℕ) (A : Finset ℕ) : ∑ q ∈ A, gB b q ≤ ∏ q ∈ A, (1 + gB b q) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | insert a A ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have h1 : 1 ≤ ∏ q ∈ A, (1 + gB b q) :=
      Finset.one_le_prod₀ (fun q _ => by linarith [gB_nonneg b q])
    have := gB_nonneg b a
    nlinarith

theorem log_ge_of_rpow_le (y a w : ℝ) (hy : 0 < y) (h : y ^ a ≤ w) : a * Real.log y ≤ Real.log w := by
  have := Real.log_le_log (Real.rpow_pos_of_pos hy a) h
  rwa [Real.log_rpow hy] at this

/-- **Ratio of `V`**: `V(w)/V(y) = log y / log w + o(1)`, uniformly in `y^a ≤ w ≤ y`. -/
theorem VB_ratio (b : ℕ) (hb : 2 ≤ b) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ y₀ : ℝ, 1 < y₀ ∧ ∀ y : ℝ, y₀ ≤ y → ∀ w : ℝ, y ^ a ≤ w → w ≤ y →
      |VB b w / VB b y - Real.log y / Real.log w| ≤ δ := by
  obtain ⟨C, hC0, hC⟩ := VB_log b hb
  set κ := kappaB b
  have hκ : 0 < κ := kappaB_pos b
  set B4 : ℝ := (Palprimes.bigB b : ℝ) + 4
  have hB4 : 1 < B4 := by have : (0 : ℝ) ≤ Palprimes.bigB b := Nat.cast_nonneg _; simp only [B4]; linarith
  set L₀ : ℝ := max (Real.log B4 / a) (max (2 * C / κ) (2 * C * (1 / a + 1) / (a * κ * δ))) + 1
  have hL0pos : 0 < L₀ := by
    have : 0 ≤ Real.log B4 / a := div_nonneg (Real.log_nonneg hB4.le) ha.le
    have := le_max_left (Real.log B4 / a) (max (2 * C / κ) (2 * C * (1 / a + 1) / (a * κ * δ)))
    simp only [L₀] <;> linarith
  refine ⟨Real.exp L₀, by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 hL0pos, ?_⟩
  intro y hy w hw1 hw2
  have hy0 : 0 < y := lt_of_lt_of_le (Real.exp_pos _) hy
  set L := Real.log y
  have hL : L₀ ≤ L := by rw [← Real.log_exp L₀]; exact Real.log_le_log (Real.exp_pos _) hy
  have hLpos : 0 < L := by linarith
  have hlw : a * L ≤ Real.log w := log_ge_of_rpow_le y a w hy0 hw1
  have hlwpos : 0 < Real.log w := by nlinarith
  have hw0 : 0 < w := lt_of_lt_of_le (Real.rpow_pos_of_pos hy0 a) hw1
  -- `w ≥ B + 4` and `y ≥ B + 4`
  have hm1 : Real.log B4 / a ≤ L₀ - 1 := by simp only [L₀] <;> linarith [le_max_left (Real.log B4 / a) (max (2 * C / κ) (2 * C * (1 / a + 1) / (a * κ * δ)))]
  have hm2 : 2 * C / κ ≤ L₀ - 1 := by
    simp only [L₀] <;>
    linarith [le_max_left (2 * C / κ) (2 * C * (1 / a + 1) / (a * κ * δ)),
      le_max_right (Real.log B4 / a) (max (2 * C / κ) (2 * C * (1 / a + 1) / (a * κ * δ)))]
  have hm3 : 2 * C * (1 / a + 1) / (a * κ * δ) ≤ L₀ - 1 := by
    simp only [L₀] <;>
    linarith [le_max_right (2 * C / κ) (2 * C * (1 / a + 1) / (a * κ * δ)),
      le_max_right (Real.log B4 / a) (max (2 * C / κ) (2 * C * (1 / a + 1) / (a * κ * δ)))]
  have hlogB : Real.log B4 ≤ a * L := by
    have := (div_le_iff₀ ha).1 (show Real.log B4 / a ≤ L by linarith)
    linarith
  have hwB : B4 ≤ w := by
    have : Real.log B4 ≤ Real.log w := by linarith
    exact (Real.log_le_log_iff (by linarith) hw0).1 this
  have hyB : B4 ≤ y := le_trans hwB hw2
  have hρw := hC w hwB
  have hρy := hC y hyB
  set ρw := VB b w * Real.log w
  set ρy := VB b y * L
  have hCL : C / L ≤ κ / 2 := by
    rw [div_le_iff₀ hLpos]
    have := (div_le_iff₀ hκ).1 (show 2 * C / κ ≤ L by linarith)
    linarith
  have hρy_ge : κ / 2 ≤ ρy := by
    have := (abs_le.1 hρy).1; linarith
  have hρy_pos : 0 < ρy := by linarith
  have hVy := VB_pos b y
  have hVw := VB_pos b w
  have key : VB b w / VB b y - L / Real.log w = (L / Real.log w) * ((ρw - ρy) / ρy) := by
    simp only [ρw, ρy]; field_simp
  rw [key, abs_mul, abs_of_pos (div_pos hLpos hlwpos), abs_div, abs_of_pos hρy_pos]
  have h1 : L / Real.log w ≤ 1 / a := by
    rw [div_le_div_iff₀ hlwpos ha]; linarith
  have h2 : |ρw - ρy| ≤ C / (a * L) + C / L := by
    have e1 : C / Real.log w ≤ C / (a * L) := div_le_div_of_nonneg_left hC0 (by positivity) hlw
    have := abs_sub_le ρw κ ρy
    rw [abs_sub_comm κ ρy] at this
    linarith
  have h3 : |ρw - ρy| / ρy ≤ (C / (a * L) + C / L) / (κ / 2) := by
    calc |ρw - ρy| / ρy ≤ (C / (a * L) + C / L) / ρy := div_le_div_of_nonneg_right h2 hρy_pos.le
      _ ≤ (C / (a * L) + C / L) / (κ / 2) := div_le_div_of_nonneg_left (by positivity) (by positivity) hρy_ge
  have h4 : (1 / a) * ((C / (a * L) + C / L) / (κ / 2)) ≤ δ := by
    have e : (1 / a) * ((C / (a * L) + C / L) / (κ / 2)) = (2 * C * (1 / a + 1) / (a * κ * δ)) * δ / L := by
      field_simp
    rw [e, div_le_iff₀ hLpos]
    have : 2 * C * (1 / a + 1) / (a * κ * δ) ≤ L := by linarith
    nlinarith
  calc L / Real.log w * (|ρw - ρy| / ρy) ≤ (1 / a) * ((C / (a * L) + C / L) / (κ / 2)) :=
        mul_le_mul h1 h3 (div_nonneg (abs_nonneg _) hρy_pos.le) (by positivity)
    _ ≤ δ := h4

end Palprimes.MT

/-! # Chain ranges, E1 at the leaves, and the large-prime leaf

* `chain_range`: a Rosser chain `l ++ [p]` (decreasing, `l` above `p`) leaves `z/(Πl·p) ≥ p` (`|l|` even)
  and `≥ p²` (`|l|` odd); for `l = []` this needs `p² ≤ z`.
* `leaf_E1`: E1 at `S^±(z, log z / log p)` with sifting limit exactly `p`.
* `bigLeaf_eq`: for `z = y/Q ≥ 8`, `Sg⁺(z, primes < Q) = S^+(z, s)` with `z^{1/s} = ⌊z^{1/3}⌋ + 1`,
  `1 < s < 3`. -/

set_option linter.style.longLine false

open Finset Real

namespace Palprimes.MT

open Palprimes.Greaves

theorem chain_range (p : ℕ) (hp : 0 < p) : ∀ (l : List ℕ) (z : ℝ), 0 < z →
    RosOK false z (l ++ [p]) → (∀ q ∈ l, p < q) → l.Pairwise (· > ·) →
    (l = [] → (p : ℝ) ^ 2 ≤ z) →
    (Even l.length → (p : ℝ) ≤ z / ((l.map (fun q : ℕ => (q : ℝ))).prod * p)) ∧
    (Odd l.length → (p : ℝ) ^ 2 ≤ z / ((l.map (fun q : ℕ => (q : ℝ))).prod * p))
  | [], z, _, _, _, _, h0 => by
    have h := h0 rfl
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
    refine ⟨fun _ => ?_, fun h' => by simp at h'⟩
    simp only [List.map_nil, List.prod_nil, one_mul]
    rw [le_div_iff₀ hp0]; nlinarith
  | [a], z, _, hR, hl, _, _ => by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
    have ha : (p : ℝ) < a := by exact_mod_cast hl a (by simp)
    have ha0 : (0 : ℝ) < a := by linarith
    have hR' : (p : ℝ) ^ 3 ≤ z / a := hR.2.1
    refine ⟨fun h' => by simp at h', fun _ => ?_⟩
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ ha0] at hR'
    have : (p : ℝ) ^ 2 * (a * p) = (p : ℝ) ^ 3 * a := by ring
    linarith
  | a :: c :: rest, z, hz, hR, hl, hpw, _ => by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
    have ha : (p : ℝ) < a := by exact_mod_cast hl a (by simp)
    have hc : (p : ℝ) < c := by exact_mod_cast hl c (by simp)
    have ha0 : (0 : ℝ) < a := by linarith
    have hc0 : (0 : ℝ) < c := by linarith
    have hc3 : (c : ℝ) ^ 3 ≤ z / a := hR.2.1
    have hR2 : RosOK false (z / a / c) (rest ++ [p]) := hR.2.2
    have hpw2 : rest.Pairwise (· > ·) := (List.pairwise_cons.1 (List.pairwise_cons.1 hpw).2).2
    have IH := chain_range p hp rest (z / a / c) (by positivity) hR2
      (fun q hq => hl q (by simp [hq])) hpw2 (fun _ => by
        rw [le_div_iff₀ hc0, le_div_iff₀ ha0]
        rw [le_div_iff₀ ha0] at hc3
        have h1 : (p : ℝ) ^ 2 ≤ (c : ℝ) ^ 2 := pow_le_pow_left₀ hp0.le hc.le 2
        have h2 : (p : ℝ) ^ 2 * c * a ≤ (c : ℝ) ^ 2 * c * a := by
          have := mul_pos hc0 ha0
          nlinarith
        have h3 : (c : ℝ) ^ 2 * c * a = (c : ℝ) ^ 3 * a := by ring
        linarith)
    set R := (rest.map (fun q : ℕ => (q : ℝ))).prod
    have e : z / (((a :: c :: rest).map (fun q : ℕ => (q : ℝ))).prod * p) = z / a / c / (R * p) := by
      simp only [List.map_cons, List.prod_cons, R]
      rw [div_div, div_div]; ring_nf
    rw [e]
    simp only [List.length_cons, Nat.even_add_one, Nat.odd_add_one, not_not]
    exact ⟨fun h => IH.1 h, fun h => IH.2 h⟩

/-- **E1 at a chain leaf**: sifting limit exactly `p`. -/
theorem leaf_E1 (b : ℕ) (hE1 : RosserAsymp b) (ε : ℝ) (hε : 0 < ε) : ∃ z₀ : ℝ, ∀ (p : ℕ), 2 ≤ p →
    ∀ z : ℝ, z₀ ≤ z → (p : ℝ) ≤ z → ∀ σ : Bool,
    (σ = true → 1 ≤ Real.log z / Real.log p) → (σ = false → 2 ≤ Real.log z / Real.log p) →
    Real.log z / Real.log p ≤ 9 →
    |Sg (gB b) σ z (toDec (primesBelow p)) - VB b p * (if σ then FjrC else fjr) (Real.log z / Real.log p)| ≤ ε * VB b p := by
  obtain ⟨z₀, hz₀⟩ := hE1 ε hε
  refine ⟨z₀, fun p hp z hz hpz σ h1 h2 h9 => ?_⟩
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have hlp : 0 < Real.log p := Real.log_pos hp1
  have hz0 : 0 < z := by linarith
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  set s := Real.log z / Real.log p
  have hzs : z ^ (1 / s) = p := by
    rw [Real.rpow_def_of_pos hz0]
    have : Real.log z * (1 / s) = Real.log p := by simp only [s]; field_simp
    rw [this, Real.exp_log (by linarith)]
  obtain ⟨hA, hB⟩ := hz₀ z hz
  cases σ with
  | true =>
    have := hA s (h1 rfl) h9; unfold Splus at this; rw [hzs] at this
    simp only [↓reduceIte]; exact this
  | false =>
    have := hB s (h2 rfl) h9; unfold Sminus at this; rw [hzs] at this
    simp only [Bool.false_eq_true, ↓reduceIte]; exact this

/-- Cube-root sifting limit `⌊z^{1/3}⌋ + 1`. -/
noncomputable def wcube (z : ℝ) : ℝ := (⌊z ^ (1 / (3 : ℝ))⌋₊ : ℝ) + 1

theorem cube_rpow (z : ℝ) (hz : 0 ≤ z) : (z ^ (1 / (3 : ℝ))) ^ 3 = z := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hz]; norm_num

theorem wcube_gt (z : ℝ) (hz : 0 ≤ z) : z < wcube z ^ 3 := by
  have h := Nat.lt_floor_add_one (z ^ (1 / (3 : ℝ)))
  have h0 : 0 ≤ z ^ (1 / (3 : ℝ)) := Real.rpow_nonneg hz _
  unfold wcube
  calc z = (z ^ (1 / (3 : ℝ))) ^ 3 := (cube_rpow z hz).symm
    _ < _ := pow_lt_pow_left₀ h h0 (by norm_num)

theorem wcube_bounds (z : ℝ) (hz : 8 ≤ z) : 2 < wcube z ∧ wcube z < z := by
  have h0 : 0 ≤ z ^ (1 / (3 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hu : 2 ≤ z ^ (1 / (3 : ℝ)) := by
    have : (2 : ℝ) = (8 : ℝ) ^ (1 / (3 : ℝ)) := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [this]; exact Real.rpow_le_rpow (by norm_num) hz (by norm_num)
  have hfl := Nat.floor_le h0
  have hfl2 : (2 : ℝ) ≤ ⌊z ^ (1 / (3 : ℝ))⌋₊ := by
    have : 2 ≤ ⌊z ^ (1 / (3 : ℝ))⌋₊ := Nat.le_floor (by exact_mod_cast hu)
    exact_mod_cast this
  have hc := cube_rpow z (by linarith)
  unfold wcube
  set u := z ^ (1 / (3 : ℝ))
  have hu3 : 4 * u ≤ u ^ 3 := by
    have : (4 : ℝ) ≤ u ^ 2 := by nlinarith
    calc 4 * u ≤ u ^ 2 * u := mul_le_mul_of_nonneg_right this h0
      _ = u ^ 3 := by ring
  constructor
  · linarith
  · linarith

/-- Primes `q ∈ [wcube z, ·)` have `z < q³`. -/
theorem prime_ge_wcube (z : ℝ) (hz : 0 ≤ z) (q : ℕ) (hq : wcube z ≤ q) : z < (q : ℝ) ^ 3 := by
  have := wcube_gt z hz
  have hw0 : 0 ≤ wcube z := by unfold wcube; positivity
  have : wcube z ^ 3 ≤ (q : ℝ) ^ 3 := pow_le_pow_left₀ hw0 hq 3
  linarith

/-- **The large-prime leaf as `S^+`.** -/
theorem bigLeaf_eq (b : ℕ) (z : ℝ) (hz : 8 ≤ z) (Q : ℕ) (hQ : z ≤ Q) :
    Sg (gB b) true z (toDec (primesBelow Q)) = Splus b z (Real.log z / Real.log (wcube z)) := by
  classical
  obtain ⟨hw2, hwz⟩ := wcube_bounds z hz
  have hwQ : wcube z ≤ Q := by linarith
  have hz0 : 0 < z := by linarith
  have hlw : 0 < Real.log (wcube z) := Real.log_pos (by linarith)
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hzs : z ^ (1 / (Real.log z / Real.log (wcube z))) = wcube z := by
    rw [Real.rpow_def_of_pos hz0]
    have : Real.log z * (1 / (Real.log z / Real.log (wcube z))) = Real.log (wcube z) := by field_simp
    rw [this, Real.exp_log (by linarith)]
  unfold Splus; rw [hzs]
  rw [toDec_filter_split (fun q : ℕ => ¬ (q : ℝ) < wcube z) (primesBelow (Q : ℝ)) (by
      intro a _ c _ hc ha; rw [not_lt] at hc; rw [not_not] at ha
      have : (a : ℝ) < c := lt_of_lt_of_le ha hc
      exact_mod_cast this),
    Sg_true_skip]
  · congr 2
    have := primesBelow_filter_lt' (wcube z) Q hwQ
    rw [← this]; congr 1; ext q; simp
  · intro q hq
    rw [mem_toDec, Finset.mem_filter, not_lt] at hq
    exact prime_ge_wcube z hz0.le q hq.2

theorem bigLeaf_s (z : ℝ) (hz : 8 ≤ z) :
    1 < Real.log z / Real.log (wcube z) ∧ Real.log z / Real.log (wcube z) < 3 := by
  obtain ⟨hw2, hwz⟩ := wcube_bounds z hz
  have hlw : 0 < Real.log (wcube z) := Real.log_pos (by linarith)
  have hz0 : 0 < z := by linarith
  constructor
  · rw [one_lt_div hlw]; exact Real.log_lt_log (by linarith) hwz
  · rw [div_lt_iff₀ hlw]
    have := wcube_gt z hz0.le
    have h3 : Real.log z < Real.log (wcube z ^ 3) := Real.log_lt_log hz0 this
    rw [Real.log_pow] at h3; push_cast at h3; linarith

end Palprimes.MT
