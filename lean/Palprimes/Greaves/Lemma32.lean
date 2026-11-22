import Palprimes.Greaves.Lemma31

/-! # Greaves Lemmas 3.2 and 3.3: the weight `W` satisfies (3.8)

Real part: `chain_m` (Lemma 3.2) for an abstract `m`; `Wg`, `mg` the weight (1.11) and the function of
Lemma 3.3 in the case `3V + U ≤ 1`; `Wg_le` (3.23); the axioms (3.20)–(3.22) for `mg`. -/

set_option linter.style.longLine false

open Finset Real

namespace Palprimes.Greaves

/-- **Lemma 3.2 (real form).** -/
theorem chain_m (m : ℝ → ℝ) (hm0 : ∀ t, 0 ≤ t → 0 ≤ m t)
    (hmlin : ∀ l t, 0 ≤ l → l ≤ 1 → 0 ≤ t → t ≤ 1 / 4 → m (l * t) ≤ l * m t)
    (hq : m (1 / 4) = 1 / 4)
    (hfun : ∀ s, 0 < s → s ≤ 1 / 4 → m (1 / 4 + 3 * s) - 1 / 4 = 3 * (1 / 4 - m (1 / 4 - s)))
    (t1 t2 : ℝ) (rest : List ℝ) (h21 : t2 ≤ t1) (h1 : t1 ≤ 1) (hrest : ∀ x ∈ rest, 0 ≤ x ∧ x ≤ t2)
    (h20 : 0 ≤ t2) (h13 : t1 + 3 * t2 ≤ 1) (hsum : t1 + t2 + rest.sum ≤ 1) :
    m t1 + m t2 + (rest.map m).sum ≤ 1 := by
  have hle_t : ∀ t, 0 ≤ t → t ≤ 1 / 4 → m t ≤ t := by
    intro t ht0 ht1
    have := hmlin (4 * t) (1 / 4) (by linarith) (by linarith) (by norm_num) le_rfl
    rw [show 4 * t * (1 / 4) = t by ring, hq] at this
    linarith
  have hall : ∀ x ∈ t2 :: rest, 0 ≤ x ∧ x ≤ t2 := by
    intro x hx; rcases List.mem_cons.1 hx with rfl | h
    · exact ⟨h20, le_rfl⟩
    · exact hrest x h
  have hsum' : ((t2 :: rest).map id).sum ≤ 1 - t1 := by simp; linarith
  rcases le_or_gt t1 (1 / 4) with hsmall | hbig
  · -- all `t_i ≤ 1/4`: `m(t) ≤ t`
    have hr : ((t2 :: rest).map m).sum ≤ ((t2 :: rest).map id).sum :=
      List.sum_le_sum (fun x hx => by
        have := hall x hx; simp only [id]; exact hle_t x this.1 (by linarith [this.2]))
    have h1' := hle_t t1 (by linarith) hsmall
    simp only [List.map_cons, List.sum_cons] at hr hsum'
    linarith
  · set s1 := (t1 - 1 / 4) / 3 with hs1
    have hs10 : 0 < s1 := by rw [hs1]; linarith
    have hs11 : s1 ≤ 1 / 4 := by rw [hs1]; linarith
    set u := 1 / 4 - s1 with hu
    have hu0 : 0 ≤ u := by rw [hu]; linarith
    have ht2u : t2 ≤ u := by rw [hu, hs1]; linarith
    have hmt1 : m t1 = 1 - 3 * m u := by
      have := hfun s1 hs10 hs11
      rw [show 1 / 4 + 3 * s1 = t1 by rw [hs1]; ring] at this
      linarith
    have hmu0 : 0 ≤ m u := hm0 u hu0
    have hbound : ((t2 :: rest).map m).sum ≤ 3 * m u := by
      rcases hu0.eq_or_lt with hu0' | hupos
      · -- `u = 0`: all entries vanish
        have hm00 : m 0 ≤ 0 := by
          have := hmlin 0 0 le_rfl (by norm_num) le_rfl (by norm_num); simpa using this
        have : ((t2 :: rest).map m).sum ≤ ((t2 :: rest).map (fun _ => (0 : ℝ))).sum :=
          List.sum_le_sum (fun x hx => by
            have hx' := hall x hx
            have : x = 0 := le_antisymm (by linarith [hx'.2]) hx'.1
            rw [this]; exact hm00)
        have hz : ((t2 :: rest).map (fun _ => (0 : ℝ))).sum = 0 := by simp
        linarith
      · have hpt : ∀ x ∈ t2 :: rest, m x ≤ x * (m u / u) := by
          intro x hx
          have hx' := hall x hx
          have hl1 : x / u ≤ 1 := by rw [div_le_one hupos]; linarith [hx'.2]
          have := hmlin (x / u) u (div_nonneg hx'.1 hupos.le) hl1 hu0 (by rw [hu]; linarith)
          rw [div_mul_cancel₀ x hupos.ne'] at this
          calc m x ≤ x / u * m u := this
            _ = x * (m u / u) := by ring
        have h1 : ((t2 :: rest).map m).sum ≤ ((t2 :: rest).map (fun x => x * (m u / u))).sum :=
          List.sum_le_sum hpt
        rw [List.sum_map_mul_right] at h1
        have h2 : ((t2 :: rest).map id).sum = (t2 :: rest).sum := by simp
        have h3 : (t2 :: rest).sum ≤ 3 * u := by
          rw [← h2]; have : 1 - t1 = 3 * u := by rw [hu, hs1]; ring
          linarith
        have h4 : 0 ≤ m u / u := div_nonneg hmu0 hupos.le
        calc ((t2 :: rest).map m).sum ≤ (t2 :: rest).sum * (m u / u) := by
              simpa using h1
          _ ≤ 3 * u * (m u / u) := mul_le_mul_of_nonneg_right h3 h4
          _ = 3 * m u := by field_simp
    simp only [List.map_cons, List.sum_cons] at hbound
    linarith

/-! ## Greaves' weight (1.11) and the function `m` of Lemma 3.3 -/

/-- Parameters `1/2 < U < 1`, `0 ≤ V`, `U + 3V ≤ 1`, `c = (1−U)/3 < T₀ < 1/4`. -/
structure WPar where
  U : ℝ
  V : ℝ
  T0 : ℝ
  hU : 1 / 2 < U
  hU1 : U < 1
  hV : 0 ≤ V
  hUV : U + 3 * V ≤ 1
  hT0 : (1 - U) / 3 < T0
  hT1 : T0 < 1 / 4

namespace WPar

variable (P : WPar)

noncomputable def c : ℝ := (1 - P.U) / 3

/-- Greaves' `W` (1.11) (with `W = U − V` also above `1`). -/
noncomputable def W (t : ℝ) : ℝ :=
  if P.U < t then P.U - P.V else if 1 / 4 < t then t - P.V else if P.T0 < t then t - P.c else 0

/-- The function `m` of Lemma 3.3 (`V* = V`). -/
noncomputable def m (t : ℝ) : ℝ :=
  if P.U ≤ t then 1 else if 1 / 4 < t then (t - P.V) / (P.U - P.V) else if t = 1 / 4 then 1 / 4
  else if P.c < t then (t - P.c) / (P.U - P.V) else 0

theorem UV_pos : 0 < P.U - P.V := by have := P.hU; have := P.hUV; have := P.hV; linarith
theorem V_lt : P.V < 1 / 6 := by have := P.hU; have := P.hUV; linarith
theorem c_nonneg : 0 ≤ P.c := by unfold c; have := P.hU1; linarith
theorem c_ge_V : P.V ≤ P.c := by unfold c; have := P.hUV; linarith
theorem c_lt_T0 : P.c < P.T0 := P.hT0

theorem m_nonneg (t : ℝ) (_ht : 0 ≤ t) : 0 ≤ P.m t := by
  have h1 := P.UV_pos; have h2 := P.V_lt
  unfold m; split_ifs with a b d e
  · norm_num
  · exact div_nonneg (by linarith) h1.le
  · norm_num
  · exact div_nonneg (by linarith) h1.le
  · exact le_rfl

theorem m_quarter : P.m (1 / 4) = 1 / 4 := by
  have := P.hU
  unfold m; rw [if_neg (by linarith), if_neg (by norm_num), if_pos rfl]

theorem m_lin (l t : ℝ) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 4) :
    P.m (l * t) ≤ l * P.m t := by
  have hUV := P.UV_pos; have hc0 := P.c_nonneg; have hU := P.hU
  have hlt : l * t ≤ t := by nlinarith
  have hc4 : (1 - P.U + P.V) / 4 ≤ P.c := by unfold c; have := P.hUV; linarith
  -- `m` below `1/4`
  have hm_low : ∀ x, x < 1 / 4 → P.m x = if P.c < x then (x - P.c) / (P.U - P.V) else 0 := by
    intro x hx
    unfold m; rw [if_neg (by linarith), if_neg (by linarith), if_neg (by linarith)]
  rcases lt_or_eq_of_le ht1 with ht | ht
  · rw [hm_low t ht, hm_low (l * t) (by linarith)]
    split_ifs with h1 h2 h2
    · rw [mul_div_assoc']
      apply div_le_div_of_nonneg_right _ hUV.le
      nlinarith
    · linarith
    · exact mul_nonneg hl0 (div_nonneg (by linarith) hUV.le)
    · simp
  · rw [ht, P.m_quarter]
    rcases lt_or_eq_of_le hl1 with hl | hl
    · rw [hm_low (l * (1 / 4)) (by linarith)]
      split_ifs with h1
      · rw [div_le_iff₀ hUV]
        nlinarith
      · linarith
    · rw [hl, one_mul, P.m_quarter]

theorem m_fun (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1 / 4) :
    P.m (1 / 4 + 3 * s) - 1 / 4 = 3 * (1 / 4 - P.m (1 / 4 - s)) := by
  have hUV := P.UV_pos; have hU := P.hU
  have hlow : P.m (1 / 4 - s) = if P.c < 1 / 4 - s then (1 / 4 - s - P.c) / (P.U - P.V) else 0 := by
    unfold m; rw [if_neg (by linarith), if_neg (by linarith), if_neg (by linarith)]
  rw [hlow]
  by_cases hbig : P.U ≤ 1 / 4 + 3 * s
  · have h1 : ¬ P.c < 1 / 4 - s := by unfold c; push Not; linarith
    rw [if_neg h1]
    unfold m; rw [if_pos hbig]; ring
  · have h1 : P.c < 1 / 4 - s := by unfold c; push Not at hbig; linarith
    rw [if_pos h1]
    unfold m; rw [if_neg hbig, if_pos (by linarith)]
    field_simp
    unfold c
    ring

theorem W_le_m (t : ℝ) : P.W t ≤ (P.U - P.V) * P.m t := by
  have hUV := P.UV_pos; have hU := P.hU; have hT0 := P.c_lt_T0; have hT1 := P.hT1
  have hc4 : 1 / 4 - P.c ≤ (P.U - P.V) / 4 := by unfold c; have := P.hUV; linarith
  unfold W m
  split_ifs <;> first
    | (field_simp; linarith)
    | (rw [mul_div_cancel₀ _ hUV.ne']) | linarith
    | (subst_vars; linarith)
    | (nlinarith [P.m_nonneg t])

theorem W_nonneg (t : ℝ) : 0 ≤ P.W t := by
  have := P.V_lt; have := P.c_lt_T0; have := P.UV_pos; have := P.hU
  unfold W; split_ifs <;> linarith

theorem W_le (t : ℝ) : P.W t ≤ P.U - P.V := by
  have := P.V_lt; have := P.c_lt_T0; have := P.UV_pos; have := P.hU; have := P.c_ge_V
  have hc4 : 1 / 4 - P.c ≤ (P.U - P.V) / 4 := by unfold c; have := P.hUV; linarith
  unfold W; split_ifs <;> linarith

/-- The weight on naturals: `w 1 = W(1) = U − V`, `w p = W(log p / log y)`. -/
noncomputable def wn (y : ℝ) (n : ℕ) : ℝ := if n = 1 then P.U - P.V else P.W (Real.log n / Real.log y)

theorem wn_one (y : ℝ) : P.wn y 1 = P.U - P.V := by simp [wn]

theorem wn_prime (y : ℝ) (p : ℕ) (hp : p.Prime) : P.wn y p = P.W (Real.log p / Real.log y) := by
  simp [wn, hp.one_lt.ne']

/-- **Lemma 3.2 for prime chains**: `p₁ > p₂ > ⋯` primes below `y` with `p₂³p₁ ≤ y`, `Π p_i ≤ y`. -/
theorem chain_sum (y : ℝ) (hy : 1 < y) (p1 p2 : ℕ) (rest : List ℕ)
    (hsort : (p1 :: p2 :: rest).Pairwise (· > ·)) (hpr : ∀ p ∈ p1 :: p2 :: rest, p.Prime)
    (hlt : ∀ p ∈ p1 :: p2 :: rest, (p : ℝ) < y)
    (h3 : (p2 : ℝ) ^ 3 * p1 ≤ y) (hprod : (((p1 :: p2 :: rest).map (fun p : ℕ => (p : ℝ))).prod) ≤ y) :
    ((p1 :: p2 :: rest).map (P.wn y)).sum ≤ P.U - P.V := by
  have hL : 0 < Real.log y := Real.log_pos hy
  set t : ℕ → ℝ := fun p => Real.log p / Real.log y with ht
  have hpos : ∀ p ∈ p1 :: p2 :: rest, (1 : ℝ) < p := fun p hp => by exact_mod_cast (hpr p hp).one_lt
  have ht0 : ∀ p ∈ p1 :: p2 :: rest, 0 ≤ t p := fun p hp =>
    div_nonneg (Real.log_nonneg (hpos p hp).le) hL.le
  have hmono : ∀ p ∈ p1 :: p2 :: rest, ∀ q ∈ p1 :: p2 :: rest, q ≤ p → t q ≤ t p := by
    intro p hp q hq hqp
    apply div_le_div_of_nonneg_right _ hL.le
    exact Real.log_le_log (by linarith [hpos q hq]) (by exact_mod_cast hqp)
  -- `w ≤ (U − V) m(t)`
  have hw : ∀ p ∈ p1 :: p2 :: rest, P.wn y p ≤ (P.U - P.V) * P.m (t p) := by
    intro p hp; rw [P.wn_prime y p (hpr p hp)]; exact P.W_le_m _
  have hsumw : ((p1 :: p2 :: rest).map (P.wn y)).sum ≤
      ((p1 :: p2 :: rest).map (fun p => (P.U - P.V) * P.m (t p))).sum := List.sum_le_sum hw
  rw [List.sum_map_mul_left] at hsumw
  -- the `t`-conditions
  have hpw := List.pairwise_cons.1 hsort
  have h21 : p2 < p1 := hpw.1 p2 (by simp)
  have hprodlog : ((p1 :: p2 :: rest).map t).sum ≤ 1 := by
    have hlog : Real.log ((((p1 :: p2 :: rest).map (fun p : ℕ => (p : ℝ))).prod)) =
        ((p1 :: p2 :: rest).map (fun p : ℕ => Real.log p)).sum := by
      rw [Real.log_list_prod]
      · simp [List.map_map, Function.comp_def]
      · intro x hx; rw [List.mem_map] at hx; obtain ⟨p, hp, rfl⟩ := hx; linarith [hpos p hp]
    have h1 := Real.log_le_log (by
      apply List.prod_pos; intro x hx; rw [List.mem_map] at hx
      obtain ⟨p, hp, rfl⟩ := hx; linarith [hpos p hp]) hprod
    rw [hlog] at h1
    have : ((p1 :: p2 :: rest).map t).sum = ((p1 :: p2 :: rest).map (fun p : ℕ => Real.log p)).sum /
        Real.log y := by
      simp only [ht]
      clear * -
      induction (p1 :: p2 :: rest) with
      | nil => simp
      | cons x l ih => simp only [List.map_cons, List.sum_cons, ih]; ring
    rw [this, div_le_one hL]; exact h1
  have h13 : t p1 + 3 * t p2 ≤ 1 := by
    have h1 : Real.log ((p2 : ℝ) ^ 3 * p1) ≤ Real.log y :=
      Real.log_le_log (by have := hpos p1 (by simp); have := hpos p2 (by simp); positivity) h3
    rw [Real.log_mul (by have := hpos p2 (by simp); positivity) (by have := hpos p1 (by simp); positivity),
      Real.log_pow] at h1
    rw [show t p1 + 3 * t p2 = (Real.log p1 + 3 * Real.log p2) / Real.log y by simp only [ht]; ring,
      div_le_one hL]
    push_cast at h1; linarith
  have hchain := chain_m P.m (fun t ht => P.m_nonneg t ht) (fun l t a b c d => P.m_lin l t a b c d)
    P.m_quarter (fun s a b => P.m_fun s a b) (t p1) (t p2) (rest.map t)
    (hmono p1 (by simp) p2 (by simp) h21.le)
    (by
      have : t p1 < 1 := by
        simp only [ht]; rw [div_lt_one hL]
        exact Real.log_lt_log (by linarith [hpos p1 (by simp)]) (hlt p1 (by simp))
      linarith)
    (by
      intro x hx; rw [List.mem_map] at hx; obtain ⟨q, hq, rfl⟩ := hx
      have hq' : q ∈ p1 :: p2 :: rest := by simp [hq]
      refine ⟨ht0 q hq', hmono p2 (by simp) q hq' ?_⟩
      have := (List.pairwise_cons.1 hpw.2).1 q hq; omega)
    (ht0 p2 (by simp)) h13
    (by simpa [List.map_map, Function.comp_def, add_assoc] using hprodlog)
  have hm : ((p1 :: p2 :: rest).map (fun p => P.m (t p))).sum ≤ 1 := by
    simpa [List.map_map, Function.comp_def, add_assoc] using hchain
  have hUV := P.UV_pos
  calc ((p1 :: p2 :: rest).map (P.wn y)).sum ≤ (P.U - P.V) * ((p1 :: p2 :: rest).map (fun p => P.m (t p))).sum := hsumw
    _ ≤ (P.U - P.V) * 1 := mul_le_mul_of_nonneg_left hm hUV.le
    _ = _ := mul_one _

/-- Real product of a list of naturals. -/
noncomputable def rprod (l : List ℕ) : ℝ := (l.map (fun p : ℕ => (p : ℝ))).prod

theorem rprod_append (l m : List ℕ) : rprod (l ++ m) = rprod l * rprod m := by
  simp [rprod, List.map_append, List.prod_append]

theorem rprod_pos (l : List ℕ) (h : ∀ p ∈ l, 0 < p) : 0 < rprod l := by
  unfold rprod; apply List.prod_pos; intro x hx; rw [List.mem_map] at hx
  obtain ⟨p, hp, rfl⟩ := hx; exact_mod_cast h p hp

theorem sublist_pair (pre0 pre1 l' : List ℕ) (P P' : ℕ) :
    List.Sublist ([P, P'] ++ l') (pre0 ++ P :: (pre1 ++ P' :: l')) :=
  (List.Sublist.cons_cons P (List.sublist_append_right pre1 (P' :: l'))).trans (List.sublist_append_right pre0 _)

/-- **(3.8) along every Rosser chain** (Lemma 3.2 + 3.3), by induction on `ℓ`. The prefix
`pre = p₁ p₂ ⋯` carries `p₂³p₁ ≤ y`, its least element `L` and `L² · Π pre ≤ y`. -/
theorem hyp_gen (y : ℝ) (hy : 1 < y) : ∀ (n : ℕ) (ℓ : List ℕ) (p1 p2 : ℕ) (rest : List ℕ) (L : ℕ),
    ℓ.length ≤ n →
    ((p1 :: p2 :: rest) ++ ℓ).Pairwise (· > ·) →
    (∀ p ∈ (p1 :: p2 :: rest) ++ ℓ, p.Prime ∧ (p : ℝ) < y) →
    (p2 : ℝ) ^ 3 * p1 ≤ y →
    L ∈ p1 :: p2 :: rest → (∀ q ∈ ℓ, q < L) →
    (L : ℝ) ^ 2 * rprod (p1 :: p2 :: rest) ≤ y →
    Hyp (P.wn y) (y / rprod (p1 :: p2 :: rest)) ℓ
      (P.U - P.V - ((p1 :: p2 :: rest).map (P.wn y)).sum) := by
  intro n
  induction n with
  | zero =>
    intro ℓ p1 p2 rest L hn _ _ _ _ _ _
    have : ℓ = [] := List.length_eq_zero_iff.1 (by omega)
    subst this
    rw [Hyp]; intro R1 l hPl; obtain ⟨pre, hpre⟩ := hPl; simp at hpre
  | succ n ih =>
    intro ℓ p1 p2 rest L hn hsort hpr h3 hL hLℓ hL2
    rw [Hyp]
    intro R1 l hPl R2 l' hPl'
    obtain ⟨pre0, rfl⟩ := hPl
    obtain ⟨pre1, rfl⟩ := hPl'
    set pre := p1 :: p2 :: rest with hpre
    -- order facts
    have hPP' : R2 < R1 := by
      have := (List.pairwise_append.1 hsort).1
      have h := (List.pairwise_append.1 (List.pairwise_append.1 hsort).2.1).2.1
      exact (List.pairwise_cons.1 h).1 R2 (by simp)
    have hPL : R1 < L := hLℓ R1 (by simp)
    have hP'L : R2 < L := hLℓ R2 (by simp)
    have hmemP : R1 ∈ pre ++ (pre0 ++ R1 :: (pre1 ++ R2 :: l')) := by simp
    have hmemP' : R2 ∈ pre ++ (pre0 ++ R1 :: (pre1 ++ R2 :: l')) := by simp
    have hPpos : (0 : ℝ) < R1 := by exact_mod_cast (hpr R1 hmemP).1.pos
    have hP'pos : (0 : ℝ) < R2 := by exact_mod_cast (hpr R2 hmemP').1.pos
    have hprepos : 0 < rprod pre := rprod_pos pre (fun q hq => (hpr q (by simp [hq])).1.pos)
    -- the extended prefix `pre ++ [R1, R2]`
    have hsub : List.Sublist (pre ++ [R1, R2] ++ l') (pre ++ (pre0 ++ R1 :: (pre1 ++ R2 :: l'))) := by
      rw [List.append_assoc]
      exact (sublist_pair pre0 pre1 l' R1 R2).append_left pre
    have hsort' : (pre ++ [R1, R2] ++ l').Pairwise (· > ·) := hsort.sublist hsub
    have hpr' : ∀ p ∈ pre ++ [R1, R2] ++ l', p.Prime ∧ (p : ℝ) < y := fun p hp => hpr p (hsub.subset hp)
    have hrp : rprod (pre ++ [R1, R2]) = rprod pre * R1 * R2 := by
      rw [rprod_append]; simp [rprod]; ring
    have hLR : (L : ℝ) ^ 2 * rprod pre ≤ y := hL2
    have hPLr : (R1 : ℝ) < L := by exact_mod_cast hPL
    have hP'Lr : (R2 : ℝ) < L := by exact_mod_cast hP'L
    constructor
    · -- (i) the chain `pre ++ [R1, R2]`
      have hch := P.chain_sum y hy p1 p2 (rest ++ [R1, R2])
        (by have := hsort'.sublist (List.sublist_append_left (pre ++ [R1, R2]) l'); simpa [hpre] using this)
        (fun p hp => (hpr' p (by simp [hpre] at hp ⊢; tauto)).1)
        (fun p hp => (hpr' p (by simp [hpre] at hp ⊢; tauto)).2) h3
        (by
          have : rprod (pre ++ [R1, R2]) ≤ y := by
            rw [hrp]
            have h1 : (R1 : ℝ) * R2 ≤ (L : ℝ) ^ 2 := by nlinarith
            nlinarith
          simpa [rprod, hpre] using this)
      have e : ((p1 :: p2 :: (rest ++ [R1, R2])).map (P.wn y)).sum =
          (pre.map (P.wn y)).sum + P.wn y R1 + P.wn y R2 := by
        simp [hpre, List.map_append, List.sum_append]; ring
      rw [e] at hch; linarith
    · -- (ii) recursion with the new prefix
      intro hcond
      have hlen : l'.length ≤ n := by simp at hn; omega
      have h3' : (R2 : ℝ) ^ 2 * rprod (pre ++ [R1, R2]) ≤ y := by
        rw [hrp]
        rw [le_div_iff₀ hPpos, le_div_iff₀ hprepos] at hcond
        nlinarith
      have := ih l' p1 p2 (rest ++ [R1, R2]) R2 hlen
        (by simpa [hpre, List.append_assoc] using hsort')
        (by intro p hp; exact hpr' p (by simpa [hpre, List.append_assoc] using hp))
        h3 (by simp)
        (by
          intro q hq
          have h := (List.pairwise_append.1 hsort').2.2 R2 (by simp) q hq
          exact h)
        (by simpa [hpre, List.append_assoc] using h3')
      have e1 : y / rprod (p1 :: p2 :: (rest ++ [R1, R2])) = y / rprod pre / R1 / R2 := by
        have : rprod (p1 :: p2 :: (rest ++ [R1, R2])) = rprod (pre ++ [R1, R2]) := by simp [hpre]
        rw [this, hrp]; field_simp
      have e2 : P.U - P.V - ((p1 :: p2 :: (rest ++ [R1, R2])).map (P.wn y)).sum =
          P.U - P.V - (pre.map (P.wn y)).sum - P.wn y R1 - P.wn y R2 := by
        simp [hpre, List.map_append, List.sum_append]; ring
      rw [e1, e2] at this
      exact this

/-- **(3.8) for the top level**: `HypTop` for every decreasing list of primes below `y`. -/
theorem hypTop (y : ℝ) (hy : 1 < y) (ℓ : List ℕ) (hsort : ℓ.Pairwise (· > ·))
    (hpr : ∀ p ∈ ℓ, p.Prime ∧ (p : ℝ) < y) :
    HypTop (P.wn y) y ℓ (P.wn y 1) := by
  intro Q l hQl Q' l' hQl' hcond
  obtain ⟨pre0, rfl⟩ := hQl
  obtain ⟨pre1, rfl⟩ := hQl'
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (hpr Q (by simp)).1.pos
  have hQ'pos : (0 : ℝ) < Q' := by exact_mod_cast (hpr Q' (by simp)).1.pos
  have hsub : List.Sublist ([Q, Q'] ++ l') (pre0 ++ Q :: (pre1 ++ Q' :: l')) :=
    sublist_pair pre0 pre1 l' Q Q'
  have h3 : (Q' : ℝ) ^ 3 * Q ≤ y := by rw [le_div_iff₀ hQpos] at hcond; linarith
  have := P.hyp_gen y hy l'.length l' Q Q' [] Q' le_rfl
    (hsort.sublist hsub) (fun p hp => hpr p (hsub.subset hp)) h3 (by simp)
    (by
      intro q hq
      have := (List.pairwise_append.1 (hsort.sublist hsub)).2.2 Q' (by simp) q hq
      exact this)
    (by simp [rprod]; nlinarith)
  have e1 : y / rprod [Q, Q'] = y / Q / Q' := by simp [rprod]; field_simp
  have e2 : P.U - P.V - ([Q, Q'].map (P.wn y)).sum = P.wn y 1 - P.wn y Q - P.wn y Q' := by
    rw [P.wn_one]; simp; ring
  rw [e1, e2] at this
  exact this

end WPar

end Palprimes.Greaves
