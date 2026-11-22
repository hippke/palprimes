import Palprimes.MainTerm.Approx2

/-! # The main term up to `o(V(y))`

`MainY P b y`: `MT` with every Rosser leaf replaced by its E1 limit, `V(y)·G(s')·(log y/log p)` for a
chain ending at `p`, `V(y)·2e^γ·log y/log(y/Q)` for a large prime `Q`. `MT_approx`: under E1,
`|MT − MainY| ≤ η V(y)` eventually, for every `η > 0`. -/

set_option linter.style.longLine false

open Finset Real Filter Topology

namespace Palprimes.MT

open Palprimes.Greaves

/-- `G^±`: `F` (with `F(1) = 2e^γ`) in the plus state, `f` in the minus state. -/
noncomputable def Gs (σ : Bool) (s : ℝ) : ℝ := if σ then FjrC s else fjr s

/-- The bound `2e^γ 8^{10}` for `F`, `f` on `s ≤ 9`. -/
noncomputable def CG : ℝ := 2 * Real.exp Real.eulerMascheroniConstant * 8 ^ 10

theorem CG_pos : 0 < CG := by unfold CG; positivity

theorem Gs_bounds (σ : Bool) (s : ℝ) (hs : s ≤ 9) : 0 ≤ Gs σ s ∧ Gs σ s ≤ CG := by
  have he := Real.exp_pos Real.eulerMascheroniConstant
  unfold Gs CG
  cases σ with
  | true =>
    simp only [↓reduceIte]
    unfold FjrC
    split_ifs
    · constructor
      · positivity
      · have : (1 : ℝ) ≤ 8 ^ 10 := by norm_num
        nlinarith
    · exact Fjr_bounds hs
  | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact fjr_bounds hs

noncomputable def leafLim (b : ℕ) (y : ℝ) (p : ℕ) (σ : Bool) (z : ℝ) : ℝ :=
  VB b y * Gs σ (Real.log z / Real.log p) * (Real.log y / Real.log p)

noncomputable def bigLim (b : ℕ) (y : ℝ) (Q : ℕ) : ℝ :=
  VB b y * (2 * Real.exp Real.eulerMascheroniConstant) * (Real.log y / Real.log (y / Q))

noncomputable def MainY (P : WPar) (b : ℕ) (y : ℝ) : ℝ :=
  ∑ Q ∈ bgP y, (P.wn y Q - P.wn y 1) * gB b Q * bigLim b y Q +
  ∑ p ∈ smP y, ∑ T ∈ ((primesBelow y).filter (fun q => p < q)).powerset,
    P.wn y p * csTerm (gB b) p (leafLim b y p) false y T

/-! ## Small helpers -/

theorem stF_false_iff (n : ℕ) : stF false n = true ↔ Odd n := by
  induction n with
  | zero => simp [stF]
  | succ n ih =>
    simp only [stF, Bool.not_eq_true', Nat.odd_add_one]
    rw [← ih]; simp

theorem prod_toDec (T : Finset ℕ) : ((toDec T).map (fun q : ℕ => (q : ℝ))).prod = ∏ q ∈ T, (q : ℝ) := by
  rw [← Finset.prod_map_toList]
  exact List.Perm.prod_eq (List.Perm.map _ (Finset.sort_perm_toList T _))

theorem length_toDec (T : Finset ℕ) : (toDec T).length = T.card := Finset.length_sort _

theorem rpow_one_div_logdiv (z w : ℝ) (hz : 0 < z) (hlz : Real.log z ≠ 0) (hw : 0 < w) :
    z ^ (1 / (Real.log z / Real.log w)) = w := by
  rw [Real.rpow_def_of_pos hz]
  have : Real.log z * (1 / (Real.log z / Real.log w)) = Real.log w := by field_simp
  rw [this, Real.exp_log hw]

theorem ev_VB_ratio (b : ℕ) (hb : 2 ≤ b) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ y : ℝ in atTop, ∀ w : ℝ, y ^ a ≤ w → w ≤ y → |VB b w / VB b y - Real.log y / Real.log w| ≤ δ := by
  obtain ⟨y₀, _, h⟩ := VB_ratio b hb a ha ha1 δ hδ
  exact eventually_atTop.2 ⟨y₀, h⟩

theorem ev_rpow_ge (c : ℝ) (hc : 0 < c) (M : ℝ) : ∀ᶠ y : ℝ in atTop, M ≤ y ^ c :=
  (tendsto_rpow_atTop hc).eventually (eventually_ge_atTop M)

/-- `V(w) ≤ (log y / log w + δ) V(y)`. -/
theorem VB_le_of_ratio (b : ℕ) (y w δ : ℝ) (h : |VB b w / VB b y - Real.log y / Real.log w| ≤ δ) :
    VB b w ≤ (Real.log y / Real.log w + δ) * VB b y := by
  have hV := VB_pos b y
  have := (abs_le.1 h).2
  have e : VB b w = VB b w / VB b y * VB b y := by field_simp
  rw [e]; exact mul_le_mul_of_nonneg_right (by linarith) hV.le

theorem csTerm_sub (g : ℕ → ℝ) (p : ℕ) (l1 l2 : Bool → ℝ → ℝ) (σ : Bool) (z : ℝ) (T : Finset ℕ) :
    csTerm g p l1 σ z T - csTerm g p l2 σ z T =
      open Classical in if RosOK σ z (toDec T ++ [p]) then (-1) ^ T.card * (∏ q ∈ T, g q) * g p *
        (l1 (stF σ (T.card + 1)) (z / ((∏ q ∈ T, (q : ℝ)) * p)) - l2 (stF σ (T.card + 1)) (z / ((∏ q ∈ T, (q : ℝ)) * p))) else 0 := by
  unfold csTerm; split_ifs <;> ring

theorem abs_csTerm_sub_le (g : ℕ → ℝ) (hg : ∀ q, 0 ≤ g q) (p : ℕ) (l1 l2 : Bool → ℝ → ℝ) (σ : Bool) (z : ℝ)
    (T : Finset ℕ) (M : ℝ) (hM : RosOK σ z (toDec T ++ [p]) →
      |l1 (stF σ (T.card + 1)) (z / ((∏ q ∈ T, (q : ℝ)) * p)) - l2 (stF σ (T.card + 1)) (z / ((∏ q ∈ T, (q : ℝ)) * p))| ≤ M)
    (hM0 : 0 ≤ M) :
    |csTerm g p l1 σ z T - csTerm g p l2 σ z T| ≤ (∏ q ∈ T, g q) * g p * M := by
  have hP : 0 ≤ ∏ q ∈ T, g q := Finset.prod_nonneg (fun q _ => hg q)
  rw [csTerm_sub]
  split_ifs with h
  · rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg hP,
      abs_of_nonneg (hg p)]
    exact mul_le_mul_of_nonneg_left (hM h) (mul_nonneg hP (hg p))
  · simp only [abs_zero]; exact mul_nonneg (mul_nonneg hP (hg p)) hM0

/-! ## Part A: `w(1) S^-(y, 2) = o(V(y))` -/

theorem errA (P : WPar) (b : ℕ) (hb : 2 ≤ b) (hE1 : RosserAsymp b) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ y : ℝ in atTop, |P.wn y 1 * Sminus b y 2| ≤ η * VB b y := by
  have hw1 : 0 < P.U - P.V := P.UV_pos
  obtain ⟨z₀, hz₀⟩ := hE1 (η / (3 * (P.U - P.V))) (by positivity)
  filter_upwards [ev_VB_ratio b hb (1 / 2) (by norm_num) (by norm_num) 1 one_pos, eventually_ge_atTop z₀,
    eventually_ge_atTop 2] with y hr hy0 hy2
  have hy : 0 < y := by linarith
  have h2 := (hz₀ y hy0).2 2 le_rfl (by norm_num)
  rw [fjr_le_two le_rfl, mul_zero, sub_zero] at h2
  have hw : y ^ (1 / (2 : ℝ)) ≤ y := Real.rpow_le_self_of_one_le (by linarith) (by norm_num)
  have hr' := hr (y ^ (1 / (2 : ℝ))) le_rfl hw
  have hlog : Real.log y / Real.log (y ^ (1 / (2 : ℝ))) = 2 := by
    rw [Real.log_rpow hy]
    have : Real.log y ≠ 0 := (Real.log_pos (by linarith)).ne'
    field_simp
  rw [hlog] at hr'
  have hV := VB_le_of_ratio b y _ 1 (by rw [hlog]; exact hr')
  rw [hlog] at hV
  rw [WPar.wn_one, abs_mul, abs_of_pos hw1]
  calc (P.U - P.V) * |Sminus b y 2| ≤ (P.U - P.V) * (η / (3 * (P.U - P.V)) * VB b (y ^ (1 / (2 : ℝ)))) :=
        mul_le_mul_of_nonneg_left h2 hw1.le
    _ ≤ (P.U - P.V) * (η / (3 * (P.U - P.V)) * ((2 + 1) * VB b y)) := by
        gcongr
    _ = η * VB b y := by field_simp; ring

/-! ## Part B: the large primes -/

theorem bigLeaf_approx (b : ℕ) (hb : 2 ≤ b) (hE1 : RosserAsymp b) (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∀ᶠ y : ℝ in atTop, ∀ Q : ℕ, Q ∈ bgP y → y ^ c ≤ y / Q →
      |bigLeaf b y Q - bigLim b y Q| ≤ (ε * (3 / c + 1) + 2 * Real.exp Real.eulerMascheroniConstant * δ) * VB b y := by
  obtain ⟨z₀, hz₀⟩ := hE1 ε hε
  filter_upwards [ev_VB_ratio b hb (c / 3) (by positivity) (by linarith) δ hδ, ev_rpow_ge c hc (max z₀ 8),
    eventually_ge_atTop 2] with y hr hyc hy2 Q hQ hz
  have hy : 0 < y := by linarith
  have hQmem := Finset.mem_filter.1 hQ
  have hQp := (mem_primesBelow y Q).1 hQmem.1
  have hQ2 : y ≤ (Q : ℝ) ^ 2 := not_lt.1 hQmem.2
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQp.1.pos
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQp.1.one_lt.le
  set z := y / (Q : ℝ) with hzdef
  have hz8 : 8 ≤ z := le_trans (le_trans (le_max_right _ _) hyc) hz
  have hzz : z₀ ≤ z := le_trans (le_trans (le_max_left _ _) hyc) hz
  have hzQ : z ≤ Q := by rw [hzdef, div_le_iff₀ hQ0]; nlinarith
  obtain ⟨hw2, hwz⟩ := wcube_bounds z hz8
  set w := wcube z with hwdef
  have hz0 : 0 < z := by linarith
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlw : 0 < Real.log w := Real.log_pos (by linarith)
  obtain ⟨hs1, hs3⟩ := bigLeaf_s z hz8
  set s := Real.log z / Real.log w with hsdef
  have hE := (hz₀ z hzz).1 s hs1.le (by linarith)
  rw [hsdef, rpow_one_div_logdiv z w hz0 hlz.ne' (by linarith), ← hsdef] at hE
  have hF : FjrC s = 2 * Real.exp Real.eulerMascheroniConstant / s := by
    unfold FjrC; rw [if_neg hs1.ne']; exact Fjr_eq hs1 hs3.le
  rw [hF] at hE
  have hwy : y ^ (c / 3) ≤ w := by
    have h1 : y ^ (c / 3) = (y ^ c) ^ (1 / (3 : ℝ)) := by rw [← Real.rpow_mul hy.le]; ring_nf
    have h2 : (y ^ c) ^ (1 / (3 : ℝ)) ≤ z ^ (1 / (3 : ℝ)) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hy.le _) hz (by norm_num)
    have h3 : z ^ (1 / (3 : ℝ)) ≤ w := (Nat.lt_floor_add_one _).le
    linarith
  have hzy : z ≤ y := by rw [hzdef, div_le_iff₀ hQ0]; nlinarith
  have hwy' : w ≤ y := by linarith
  have hrat := hr w hwy hwy'
  have hlwy : (c / 3) * Real.log y ≤ Real.log w := log_ge_of_rpow_le y (c / 3) w hy hwy
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hratio : Real.log y / Real.log w ≤ 3 / c := by
    rw [div_le_div_iff₀ hlw hc]; nlinarith
  have hVw := VB_le_of_ratio b y w δ hrat
  have hbl : bigLeaf b y Q = Splus b z s := bigLeaf_eq b z hz8 Q hzQ
  have hVy := VB_pos b y
  set E := 2 * Real.exp Real.eulerMascheroniConstant with hE'
  have hEpos : 0 < E := by positivity
  have key : VB b w * (E / s) - bigLim b y Q =
      E * VB b y * (Real.log w / Real.log z) * (VB b w / VB b y - Real.log y / Real.log w) := by
    unfold bigLim; rw [← hzdef, ← hE', hsdef]; field_simp
  have hlwz : Real.log w ≤ Real.log z := Real.log_le_log (by linarith) hwz.le
  have hq1 : Real.log w / Real.log z ≤ 1 := (div_le_one hlz).2 hlwz
  have hk : |VB b w * (E / s) - bigLim b y Q| ≤ E * δ * VB b y := by
    rw [key, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ E * VB b y * (Real.log w / Real.log z))]
    calc E * VB b y * (Real.log w / Real.log z) * |VB b w / VB b y - Real.log y / Real.log w|
        ≤ E * VB b y * 1 * δ := mul_le_mul (mul_le_mul_of_nonneg_left hq1 (by positivity)) hrat (abs_nonneg _)
          (by positivity)
      _ = E * δ * VB b y := by ring
  rw [hbl]
  calc |Splus b z s - bigLim b y Q| ≤ |Splus b z s - VB b w * (E / s)| + |VB b w * (E / s) - bigLim b y Q| :=
        abs_sub_le _ _ _
    _ ≤ ε * VB b w + E * δ * VB b y := add_le_add hE hk
    _ ≤ ε * ((3 / c + 1) * VB b y) + E * δ * VB b y := by
        gcongr
        calc VB b w ≤ (Real.log y / Real.log w + δ) * VB b y := hVw
          _ ≤ (3 / c + 1) * VB b y := by gcongr
    _ = (ε * (3 / c + 1) + E * δ) * VB b y := by ring

theorem W_gt_U (P : WPar) (t : ℝ) (h : P.U < t) : P.W t = P.U - P.V := by unfold WPar.W; rw [if_pos h]

theorem W_le_T0 (P : WPar) (t : ℝ) (h : t ≤ P.T0) : P.W t = 0 := by
  have := P.hT1; have := P.hU
  unfold WPar.W
  rw [if_neg (by linarith), if_neg (by linarith), if_neg (by linarith)]

theorem wn_nonneg_le (P : WPar) (y : ℝ) (p : ℕ) (hp : p.Prime) : 0 ≤ P.wn y p ∧ P.wn y p ≤ P.U - P.V := by
  rw [WPar.wn_prime P y p hp]; exact ⟨P.W_nonneg _, P.W_le _⟩

/-- `Π_{[y^a, y)} (1 + g) ≤ 1/a + 1` eventually. -/
theorem K_bound (b : ℕ) (hb : 2 ≤ b) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    ∀ᶠ y : ℝ in atTop, ∏ q ∈ pIco (y ^ a) y, (1 + gB b q) ≤ 1 / a + 1 := by
  filter_upwards [ev_VB_ratio b hb a ha ha1 1 one_pos, eventually_ge_atTop 2] with y hr hy2
  have hy : 0 < y := by linarith
  have hya : y ^ a ≤ y := Real.rpow_le_self_of_one_le (by linarith) ha1
  have h1 := prod_one_add_le b (y ^ a) y hya
  have h2 := VB_le_of_ratio b y (y ^ a) 1 (hr (y ^ a) le_rfl hya)
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hl : Real.log y / Real.log (y ^ a) = 1 / a := by rw [Real.log_rpow hy]; field_simp
  rw [hl] at h2
  have hV := VB_pos b y
  calc _ ≤ VB b (y ^ a) / VB b y := h1
    _ ≤ 1 / a + 1 := by rw [div_le_iff₀ hV]; exact h2

theorem sum_g_le_K (b : ℕ) (A B : Finset ℕ) (h : B ⊆ A) : ∑ q ∈ B, gB b q ≤ ∏ q ∈ A, (1 + gB b q) :=
  le_trans (Finset.sum_le_sum_of_subset_of_nonneg h (fun q _ _ => gB_nonneg b q)) (sum_le_prod_one_add b A)

theorem errB (P : WPar) (b : ℕ) (hb : 2 ≤ b) (hE1 : RosserAsymp b) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ y : ℝ in atTop, |∑ Q ∈ bgP y, (P.wn y Q - P.wn y 1) * gB b Q * (bigLeaf b y Q - bigLim b y Q)| ≤ η * VB b y := by
  have hw1 : 0 < P.U - P.V := P.UV_pos
  have hU := P.hU; have hU1 := P.hU1; have hT0 := P.hT1
  have hT0p : 0 < P.T0 := lt_of_le_of_lt (div_nonneg (by linarith) (by norm_num)) P.hT0
  set c := 1 - P.U
  have hc : 0 < c := by simp only [c]; linarith
  set K₀ := 1 / (1 / 2 : ℝ) + 1
  set A := 3 / c + 1
  have hA : 0 < A := by positivity
  set E := 2 * Real.exp Real.eulerMascheroniConstant
  have hE : 0 < E := by positivity
  set ε := η / (2 * (P.U - P.V) * K₀ * A)
  set δ := min 1 (η / (2 * (P.U - P.V) * K₀ * E))
  have hε : 0 < ε := by positivity
  have hδ : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ η / (2 * (P.U - P.V) * K₀ * E) := min_le_right _ _
  filter_upwards [bigLeaf_approx b hb hE1 c hc (by simp only [c]; linarith) ε δ hε hδ hδ1,
    K_bound b hb (1 / 2) (by norm_num) (by norm_num), eventually_ge_atTop 2] with y hB hK hy2
  have hy : 0 < y := by linarith
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hV := VB_pos b y
  set M := (ε * A + E * δ) * VB b y
  have hM : 0 ≤ M := by positivity
  have hterm : ∀ Q ∈ bgP y, |(P.wn y Q - P.wn y 1) * gB b Q * (bigLeaf b y Q - bigLim b y Q)| ≤
      (P.U - P.V) * gB b Q * M := by
    intro Q hQ
    have hQp := ((mem_primesBelow y Q).1 (Finset.mem_filter.1 hQ).1).1
    have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQp.pos
    obtain ⟨hw0, hwle⟩ := wn_nonneg_le P y Q hQp
    rw [WPar.wn_one]
    by_cases hQU : y ^ P.U < Q
    · have ht : P.U < Real.log Q / Real.log y := by
        rw [lt_div_iff₀ hly]
        have := Real.log_lt_log (Real.rpow_pos_of_pos hy _) hQU
        rwa [Real.log_rpow hy] at this
      rw [WPar.wn_prime P y Q hQp, W_gt_U P _ ht, sub_self, zero_mul, zero_mul, abs_zero]
      exact mul_nonneg (mul_nonneg hw1.le (gB_nonneg b Q)) hM
    · have hz : y ^ c ≤ y / Q := by
        rw [le_div_iff₀ hQ0]
        have : y ^ c * y ^ P.U = y := by rw [← Real.rpow_add hy]; simp [c]
        have := mul_le_mul_of_nonneg_left (not_lt.1 hQU) (Real.rpow_nonneg hy.le c)
        linarith
      have h := hB Q hQ hz
      rw [abs_mul, abs_mul, abs_of_nonneg (gB_nonneg b Q)]
      have h1 : |P.wn y Q - (P.U - P.V)| ≤ P.U - P.V := by rw [abs_le]; constructor <;> linarith
      exact mul_le_mul (mul_le_mul_of_nonneg_right h1 (gB_nonneg b Q)) h (abs_nonneg _)
        (mul_nonneg hw1.le (gB_nonneg b Q))
  have hsub : bgP y ⊆ pIco (y ^ (1 / 2 : ℝ)) y := by
    intro Q hQ
    have hQm := Finset.mem_filter.1 hQ
    have hQp := (mem_primesBelow y Q).1 hQm.1
    rw [mem_pIco]
    refine ⟨hQp.1, ?_, hQp.2⟩
    have hQ2 : y ≤ (Q : ℝ) ^ 2 := not_lt.1 hQm.2
    have hs : (y ^ (1 / 2 : ℝ)) ^ 2 = y := by rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le]; norm_num
    have h0 : 0 ≤ y ^ (1 / 2 : ℝ) := Real.rpow_nonneg hy.le _
    nlinarith [Nat.cast_nonneg (α := ℝ) Q]
  have hsum := sum_g_le_K b _ _ hsub
  calc _ ≤ ∑ Q ∈ bgP y, |(P.wn y Q - P.wn y 1) * gB b Q * (bigLeaf b y Q - bigLim b y Q)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ Q ∈ bgP y, (P.U - P.V) * gB b Q * M := Finset.sum_le_sum hterm
    _ = (P.U - P.V) * M * ∑ Q ∈ bgP y, gB b Q := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro Q _; ring
    _ ≤ (P.U - P.V) * M * K₀ := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hw1.le hM)
        exact le_trans hsum hK
    _ ≤ η * VB b y := by
        simp only [M]
        have hK0 : (0 : ℝ) < K₀ := by simp only [K₀]; norm_num
        have e1 : (P.U - P.V) * ε * A * K₀ = η / 2 := by simp only [ε]; field_simp
        have e2 : (P.U - P.V) * E * δ * K₀ ≤ η / 2 := by
          calc (P.U - P.V) * E * δ * K₀ ≤ (P.U - P.V) * E * (η / (2 * (P.U - P.V) * K₀ * E)) * K₀ := by gcongr
            _ = η / 2 := by field_simp
        have e3 : (P.U - P.V) * ((ε * A + E * δ) * VB b y) * K₀ =
            ((P.U - P.V) * ε * A * K₀ + (P.U - P.V) * E * δ * K₀) * VB b y := by ring
        rw [e3]
        exact mul_le_mul_of_nonneg_right (by rw [e1, add_comm]; have h := add_le_add_left e2 (η / 2); rwa [add_halves] at h) hV.le

/-! ## Part C: the chains -/

theorem Gs_eq (σ : Bool) (s : ℝ) : Gs σ s = (if σ then FjrC else fjr) s := by cases σ <;> rfl

/-- **E1 at a chain leaf, against `leafLim`.** -/
theorem chainLeaf_approx (b : ℕ) (hb : 2 ≤ b) (hE1 : RosserAsymp b) (a : ℝ) (ha : 1 / 9 ≤ a) (ha1 : a ≤ 1)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∀ᶠ y : ℝ in atTop, ∀ p : ℕ, p.Prime → y ^ a < p → (p : ℝ) ^ 2 < y →
      ∀ T ∈ ((primesBelow y).filter (fun q => p < q)).powerset, RosOK false y (toDec T ++ [p]) →
      |Sg (gB b) (stF false (T.card + 1)) (y / ((∏ q ∈ T, (q : ℝ)) * p)) (toDec (primesBelow p)) -
        leafLim b y p (stF false (T.card + 1)) (y / ((∏ q ∈ T, (q : ℝ)) * p))| ≤
        (ε * (1 / a + 1) + CG * δ) * VB b y := by
  have ha0 : 0 < a := by linarith
  obtain ⟨z₀, hz₀⟩ := leaf_E1 b hE1 ε hε
  filter_upwards [ev_VB_ratio b hb a ha0 ha1 δ hδ, ev_rpow_ge a ha0 z₀, eventually_ge_atTop 2] with
    y hr hya hy2 p hp hpa hp2 T hT hR
  have hy : 0 < y := by linarith
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlp : 0 < Real.log p := Real.log_pos hp1
  have hTsub := Finset.mem_powerset.1 hT
  have hTgt : ∀ q ∈ T, p < q := fun q hq => (Finset.mem_filter.1 (hTsub hq)).2
  have hTpos : ∀ q ∈ T, (1 : ℝ) ≤ q := fun q hq => by
    have := hTgt q hq; have : 1 ≤ q := by omega
    exact_mod_cast this
  obtain ⟨hev, hodd⟩ := chain_range p hp.pos (toDec T) y hy hR (fun q hq => hTgt q ((mem_toDec T q).1 hq))
    (toDec_pairwise T) (fun _ => hp2.le)
  rw [prod_toDec, length_toDec] at hev hodd
  set z' := y / ((∏ q ∈ T, (q : ℝ)) * p) with hz'
  have hPi : 1 ≤ ∏ q ∈ T, (q : ℝ) := Finset.one_le_prod₀ hTpos
  have hz'y : z' ≤ y := by
    have h1 : 1 ≤ (∏ q ∈ T, (q : ℝ)) * p := by nlinarith
    rw [hz', div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left h1 hy.le
    linarith
  have hpz : (p : ℝ) ≤ z' := by
    rcases Nat.even_or_odd T.card with he | ho
    · exact hev he
    · have := hodd ho; nlinarith
  have hz0 : 0 < z' := by linarith
  have hlz : 0 < Real.log z' := Real.log_pos (by linarith)
  set σ := stF false (T.card + 1) with hσ
  have hs1 : σ = true → 1 ≤ Real.log z' / Real.log p := by
    intro h
    rw [hσ, stF_false_iff, Nat.odd_add_one, Nat.not_odd_iff_even] at h
    rw [le_div_iff₀ hlp, one_mul]; exact Real.log_le_log hp0 (hev h)
  have hs2 : σ = false → 2 ≤ Real.log z' / Real.log p := by
    intro h
    have h' : ¬ Odd (T.card + 1) := by rw [← stF_false_iff, ← hσ, h]; simp
    rw [Nat.odd_add_one, not_not] at h'
    rw [le_div_iff₀ hlp]
    have := Real.log_le_log (by positivity) (hodd h')
    rw [Real.log_pow] at this; push_cast at this; linarith
  -- bounds on `s'` and the ratio
  have hlpy : a * Real.log y ≤ Real.log p := log_ge_of_rpow_le y a p hy hpa.le
  have hpy : (p : ℝ) ≤ y := by nlinarith
  have hrat := hr p hpa.le hpy
  have hL : Real.log y / Real.log p ≤ 1 / a := by
    rw [div_le_div_iff₀ hlp ha0]; linarith
  have hs9 : Real.log z' / Real.log p ≤ 9 := by
    have h1 : Real.log z' / Real.log p ≤ Real.log y / Real.log p :=
      div_le_div_of_nonneg_right (Real.log_le_log hz0 hz'y) hlp.le
    have h2 : 1 / a ≤ 9 := by rw [div_le_iff₀ ha0]; linarith
    linarith
  have hE := hz₀ p hp.two_le z' (le_trans (le_trans hya hpa.le) hpz) hpz σ hs1 hs2 hs9
  rw [← Gs_eq] at hE
  obtain ⟨hG0, hG1⟩ := Gs_bounds σ _ hs9
  have hVy := VB_pos b y
  have hVp := VB_le_of_ratio b y p δ hrat
  have key : VB b p * Gs σ (Real.log z' / Real.log p) - leafLim b y p σ z' =
      VB b y * Gs σ (Real.log z' / Real.log p) * (VB b p / VB b y - Real.log y / Real.log p) := by
    unfold leafLim; field_simp
  have hk : |VB b p * Gs σ (Real.log z' / Real.log p) - leafLim b y p σ z'| ≤ CG * δ * VB b y := by
    rw [key, abs_mul, abs_of_nonneg (mul_nonneg hVy.le hG0)]
    calc VB b y * Gs σ (Real.log z' / Real.log p) * |VB b p / VB b y - Real.log y / Real.log p|
        ≤ VB b y * CG * δ := mul_le_mul (mul_le_mul_of_nonneg_left hG1 hVy.le) hrat (abs_nonneg _)
          (mul_nonneg hVy.le CG_pos.le)
      _ = CG * δ * VB b y := by ring
  calc _ ≤ |Sg (gB b) σ z' (toDec (primesBelow p)) - VB b p * Gs σ (Real.log z' / Real.log p)| +
        |VB b p * Gs σ (Real.log z' / Real.log p) - leafLim b y p σ z'| := abs_sub_le _ _ _
    _ ≤ ε * VB b p + CG * δ * VB b y := add_le_add hE hk
    _ ≤ ε * ((1 / a + 1) * VB b y) + CG * δ * VB b y := by
        gcongr
        calc VB b p ≤ (Real.log y / Real.log p + δ) * VB b y := hVp
          _ ≤ (1 / a + 1) * VB b y := by gcongr
    _ = (ε * (1 / a + 1) + CG * δ) * VB b y := by ring

theorem errC (P : WPar) (b : ℕ) (hb : 2 ≤ b) (hE1 : RosserAsymp b) (hT9 : 1 / 9 ≤ P.T0) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ y : ℝ in atTop, |∑ p ∈ smP y, ∑ T ∈ ((primesBelow y).filter (fun q => p < q)).powerset,
        P.wn y p * (csTerm (gB b) p (fun σ z => Sg (gB b) σ z (toDec (primesBelow p))) false y T -
          csTerm (gB b) p (leafLim b y p) false y T)| ≤ η * VB b y := by
  have hw1 : 0 < P.U - P.V := P.UV_pos
  have hT1 := P.hT1
  have ha0 : 0 < P.T0 := by linarith
  have hK0 : 0 < 1 / P.T0 + 1 := by positivity
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℝ, K₀ = 1 / P.T0 + 1 := ⟨_, rfl⟩
  rw [← hK₀] at hK0
  obtain ⟨ε, hεd⟩ : ∃ ε : ℝ, ε = η / (2 * (P.U - P.V) * K₀ ^ 3) := ⟨_, rfl⟩
  obtain ⟨δ, hδd⟩ : ∃ δ : ℝ, δ = min 1 (η / (2 * (P.U - P.V) * K₀ ^ 2 * CG)) := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεd]; have := CG_pos; positivity
  have hδ : 0 < δ := by rw [hδd]; exact lt_min one_pos (by have := CG_pos; positivity)
  have hδ1 : δ ≤ 1 := by rw [hδd]; exact min_le_left _ _
  have hδ2 : δ ≤ η / (2 * (P.U - P.V) * K₀ ^ 2 * CG) := by rw [hδd]; exact min_le_right _ _
  filter_upwards [chainLeaf_approx b hb hE1 P.T0 hT9 (by linarith) ε δ hε hδ hδ1,
    K_bound b hb P.T0 ha0 (by linarith), eventually_ge_atTop 2] with y hC hK hy2
  rw [← hK₀] at hK
  have hy : 0 < y := by linarith
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hV := VB_pos b y
  obtain ⟨M, hMd⟩ : ∃ M : ℝ, M = (ε * K₀ + CG * δ) * VB b y := ⟨_, rfl⟩
  have hM : 0 ≤ M := by rw [hMd]; have := CG_pos; positivity
  set A := pIco (y ^ P.T0) y
  have hper : ∀ p ∈ smP y, |∑ T ∈ ((primesBelow y).filter (fun q => p < q)).powerset,
      P.wn y p * (csTerm (gB b) p (fun σ z => Sg (gB b) σ z (toDec (primesBelow p))) false y T -
        csTerm (gB b) p (leafLim b y p) false y T)| ≤
      (P.U - P.V) * M * K₀ * (if y ^ P.T0 < p then gB b p else 0) := by
    intro p hp
    have hpm := Finset.mem_filter.1 hp
    have hpp := (mem_primesBelow y p).1 hpm.1
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.1.pos
    obtain ⟨hw0, hwle⟩ := wn_nonneg_le P y p hpp.1
    by_cases hpa : y ^ P.T0 < p
    · rw [if_pos hpa]
      have hsub : (primesBelow y).filter (fun q => p < q) ⊆ A := by
        intro q hq
        have hqm := Finset.mem_filter.1 hq
        have hqp := (mem_primesBelow y q).1 hqm.1
        rw [mem_pIco]
        refine ⟨hqp.1, ?_, hqp.2⟩
        have : (p : ℝ) < q := by exact_mod_cast hqm.2
        linarith
      have hprod : ∑ T ∈ ((primesBelow y).filter (fun q => p < q)).powerset, ∏ q ∈ T, gB b q ≤ K₀ := by
        rw [← Finset.prod_one_add]
        refine le_trans ?_ hK
        exact Finset.prod_le_prod_of_subset_of_one_le₀ hsub (fun q _ => by linarith [gB_nonneg b q]) (fun q _ _ => by linarith [gB_nonneg b q])
      have hterm : ∀ T ∈ ((primesBelow y).filter (fun q => p < q)).powerset,
          |P.wn y p * (csTerm (gB b) p (fun σ z => Sg (gB b) σ z (toDec (primesBelow p))) false y T -
            csTerm (gB b) p (leafLim b y p) false y T)| ≤ (P.U - P.V) * ((∏ q ∈ T, gB b q) * gB b p * M) := by
        intro T hT
        rw [abs_mul, abs_of_nonneg hw0]
        apply mul_le_mul hwle _ (abs_nonneg _) hw1.le
        apply abs_csTerm_sub_le (gB b) (gB_nonneg b) p _ _ false y T M _ hM
        intro hR
        have := hC p hpp.1 hpa hpm.2 T hT hR
        rw [hMd]
        calc _ ≤ (ε * (1 / P.T0 + 1) + CG * δ) * VB b y := this
          _ = (ε * K₀ + CG * δ) * VB b y := by rw [hK₀]
      calc _ ≤ ∑ T ∈ ((primesBelow y).filter (fun q => p < q)).powerset, (P.U - P.V) * ((∏ q ∈ T, gB b q) * gB b p * M) :=
            le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hterm)
        _ = (P.U - P.V) * M * gB b p * ∑ T ∈ ((primesBelow y).filter (fun q => p < q)).powerset, ∏ q ∈ T, gB b q := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro T _; ring
        _ ≤ (P.U - P.V) * M * gB b p * K₀ :=
            mul_le_mul_of_nonneg_left hprod (mul_nonneg (mul_nonneg hw1.le hM) (gB_nonneg b p))
        _ = _ := by ring
    · rw [if_neg hpa, mul_zero]
      have ht : Real.log p / Real.log y ≤ P.T0 := by
        rw [div_le_iff₀ hly]
        have := Real.log_le_log hp0 (not_lt.1 hpa)
        rw [Real.log_rpow hy] at this; linarith
      rw [WPar.wn_prime P y p hpp.1, W_le_T0 P _ ht]
      simp
  have hsum : ∑ p ∈ smP y, (if y ^ P.T0 < p then gB b p else 0) ≤ K₀ := by
    rw [← Finset.sum_filter]
    refine le_trans (sum_g_le_K b A _ ?_) hK
    intro p hp
    have hpm := Finset.mem_filter.1 hp
    have hpp := (mem_primesBelow y p).1 (Finset.mem_filter.1 hpm.1).1
    rw [mem_pIco]; exact ⟨hpp.1, hpm.2.le, hpp.2⟩
  calc _ ≤ ∑ p ∈ smP y, (P.U - P.V) * M * K₀ * (if y ^ P.T0 < p then gB b p else 0) :=
        le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hper)
    _ = (P.U - P.V) * M * K₀ * ∑ p ∈ smP y, (if y ^ P.T0 < p then gB b p else 0) := by rw [Finset.mul_sum]
    _ ≤ (P.U - P.V) * M * K₀ * K₀ := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ η * VB b y := by
        rw [hMd]
        have e1 : (P.U - P.V) * ε * K₀ ^ 3 = η / 2 := by rw [hεd]; field_simp
        have e2 : (P.U - P.V) * CG * δ * K₀ ^ 2 ≤ η / 2 := by
          have := CG_pos
          calc (P.U - P.V) * CG * δ * K₀ ^ 2 ≤ (P.U - P.V) * CG * (η / (2 * (P.U - P.V) * K₀ ^ 2 * CG)) * K₀ ^ 2 := by gcongr
            _ = η / 2 := by field_simp
        have e3 : (P.U - P.V) * ((ε * K₀ + CG * δ) * VB b y) * K₀ * K₀ =
            ((P.U - P.V) * ε * K₀ ^ 3 + (P.U - P.V) * CG * δ * K₀ ^ 2) * VB b y := by ring
        rw [e3]
        exact mul_le_mul_of_nonneg_right (by rw [e1, add_comm]; have h := add_le_add_left e2 (η / 2); rwa [add_halves] at h) hV.le

/-- **The main term up to `o(V(y))`** (Greaves (4.2) with E1 inserted). -/
theorem MT_approx (P : WPar) (b : ℕ) (hb : 2 ≤ b) (hE1 : RosserAsymp b) (hT9 : 1 / 9 ≤ P.T0) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ y : ℝ in atTop, |MT P b y - MainY P b y| ≤ η * VB b y := by
  filter_upwards [errA P b hb hE1 (η / 3) (by positivity), errB P b hb hE1 (η / 3) (by positivity),
    errC P b hb hE1 hT9 (η / 3) (by positivity), eventually_gt_atTop 1] with y hA hB hC hy
  rw [MT_reduce P b y hy]
  unfold MainY
  have e : P.wn y 1 * Sminus b y 2 + ∑ Q ∈ bgP y, (P.wn y Q - P.wn y 1) * gB b Q * bigLeaf b y Q +
      ∑ p ∈ smP y, ∑ T ∈ ((primesBelow y).filter (fun q => p < q)).powerset,
        P.wn y p * csTerm (gB b) p (fun σ z => Sg (gB b) σ z (toDec (primesBelow p))) false y T -
      (∑ Q ∈ bgP y, (P.wn y Q - P.wn y 1) * gB b Q * bigLim b y Q +
      ∑ p ∈ smP y, ∑ T ∈ ((primesBelow y).filter (fun q => p < q)).powerset,
        P.wn y p * csTerm (gB b) p (leafLim b y p) false y T) =
      P.wn y 1 * Sminus b y 2 + ∑ Q ∈ bgP y, (P.wn y Q - P.wn y 1) * gB b Q * (bigLeaf b y Q - bigLim b y Q) +
      ∑ p ∈ smP y, ∑ T ∈ ((primesBelow y).filter (fun q => p < q)).powerset,
        P.wn y p * (csTerm (gB b) p (fun σ z => Sg (gB b) σ z (toDec (primesBelow p))) false y T -
          csTerm (gB b) p (leafLim b y p) false y T) := by
    simp only [mul_sub, Finset.sum_sub_distrib]; ring
  rw [e]
  calc _ ≤ |P.wn y 1 * Sminus b y 2| + |∑ Q ∈ bgP y, (P.wn y Q - P.wn y 1) * gB b Q * (bigLeaf b y Q - bigLim b y Q)| +
        |∑ p ∈ smP y, ∑ T ∈ ((primesBelow y).filter (fun q => p < q)).powerset,
          P.wn y p * (csTerm (gB b) p (fun σ z => Sg (gB b) σ z (toDec (primesBelow p))) false y T -
            csTerm (gB b) p (leafLim b y p) false y T)| := abs_add_three _ _ _
    _ ≤ η / 3 * VB b y + η / 3 * VB b y + η / 3 * VB b y := add_le_add (add_le_add hA hB) hC
    _ = η * VB b y := by ring

end Palprimes.MT
