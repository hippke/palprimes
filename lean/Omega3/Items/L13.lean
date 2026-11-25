import Omega3.Statements

namespace Omega3

open Finset Palprimes

/-! Item L13: `X_w ≥ c > 0`.  Doeblin argument: fix the digits at `0`, `N` and at `2, 4, …, 2L` (`L = b² − 1`)
to make `n ≡ 1 (mod b³ − b)`; all other digits free.  See reports/L13.md. -/

/-- Existence of the correcting count `T`. -/
lemma l13_exists_T (M : ℕ) (hM : 0 < M) (s : ℤ) (h : ¬ (2 : ℤ) ∣ (M : ℤ) ∨ ¬ (2 : ℤ) ∣ s) :
    ∃ T : ℕ, T < M ∧ (M : ℤ) ∣ 1 - s - 2 * T := by
  have hM' : (0 : ℤ) < M := by exact_mod_cast hM
  by_cases ha : (2 : ℤ) ∣ 1 - s
  · obtain ⟨m, hm⟩ := ha
    refine ⟨(m % M).toNat, ?_, ?_⟩
    · have := Int.emod_lt_of_pos m hM'
      have h0 := Int.emod_nonneg m hM'.ne'
      omega
    · have h0 := Int.emod_nonneg m hM'.ne'
      rw [Int.toNat_of_nonneg h0, hm]
      have : 2 * m - 2 * (m % (M : ℤ)) = (M : ℤ) * (2 * (m / M)) := by
        have := Int.emod_add_mul_ediv m M
        nlinarith
      rw [show 2 * m - 2 * (m % (M : ℤ)) = 2 * m - 2 * (m % (M : ℤ)) from rfl, this]
      exact dvd_mul_right _ _
  · have hodd : ¬ (2 : ℤ) ∣ (M : ℤ) := by
      rcases h with h | h
      · exact h
      · exfalso; apply ha
        have : (2 : ℤ) ∣ s ∨ ¬ (2 : ℤ) ∣ s := em _
        rcases this with h2 | h2
        · exfalso; exact h h2
        · omega
    have hev : (2 : ℤ) ∣ 1 - s + M := by omega
    obtain ⟨m, hm⟩ := hev
    refine ⟨(m % M).toNat, ?_, ?_⟩
    · have := Int.emod_lt_of_pos m hM'
      have h0 := Int.emod_nonneg m hM'.ne'
      omega
    · have h0 := Int.emod_nonneg m hM'.ne'
      rw [Int.toNat_of_nonneg h0]
      have hmm := Int.emod_add_mul_ediv m M
      have : 1 - s - 2 * (m % (M : ℤ)) = (M : ℤ) * (2 * (m / M) - 1) := by nlinarith
      rw [this]
      exact dvd_mul_right _ _

/-! ### The modified digit string -/

def l13L (b : ℕ) : ℕ := b ^ 2 - 1

def l13inF (b N k : ℕ) : Prop := k = 0 ∨ k = N ∨ (k % 2 = 0 ∧ 1 ≤ k ∧ k ≤ 2 * l13L b)

instance (b N k : ℕ) : Decidable (l13inF b N k) := by unfold l13inF; infer_instance

def l13phi (b N T : ℕ) (hb : 1 < b) (o : DigVec b N) : DigVec b N := fun k =>
  if k.val = 0 ∨ k.val = N then ⟨1, hb⟩
  else if (k.val % 2 = 0 ∧ 1 ≤ k.val ∧ k.val ≤ 2 * l13L b) then
    (if k.val / 2 ≤ T then ⟨1, hb⟩ else ⟨0, by omega⟩)
  else o k

lemma l13_phi_notF (b N T : ℕ) (hb : 1 < b) (o : DigVec b N) (k : Fin (N + 1))
    (hk : ¬ l13inF b N k.val) : l13phi b N T hb o k = o k := by
  unfold l13inF at hk
  unfold l13phi
  rw [if_neg (by tauto), if_neg (by tauto)]

lemma l13_phi_le (b N T : ℕ) (hb : 1 < b) (o : DigVec b N) (k : Fin (N + 1))
    (hk : l13inF b N k.val) : ((l13phi b N T hb o k : Fin b) : ℕ) ≤ 1 := by
  unfold l13inF at hk
  unfold l13phi
  split_ifs <;> first | simp | omega

/-- Pointwise decomposition of the modified palindrome sum. -/
lemma l13_decomp (b N T : ℕ) (hb : 1 < b) (hN : 2 * l13L b < N) (o : DigVec b N)
    (ho : ∀ k : Fin (N + 1), l13inF b N k.val → ((o k : Fin b) : ℕ) = 0) (k : Fin (N + 1)) :
    (((l13phi b N T hb o k : Fin b) : ℕ) : ℤ) * (cK b N k : ℤ) =
      (if k.val = 0 ∨ k.val = N then (cK b N k : ℤ) else 0) +
      (if (k.val % 2 = 0 ∧ 1 ≤ k.val ∧ k.val ≤ 2 * l13L b ∧ k.val / 2 ≤ T) then (cK b N k : ℤ) else 0) +
      (((o k : Fin b) : ℕ) : ℤ) * (cK b N k : ℤ) := by
  by_cases h1 : k.val = 0 ∨ k.val = N
  · have h2 : ¬ (k.val % 2 = 0 ∧ 1 ≤ k.val ∧ k.val ≤ 2 * l13L b ∧ k.val / 2 ≤ T) := by omega
    have hF : l13inF b N k.val := by unfold l13inF; tauto
    have : ((o k : Fin b) : ℕ) = 0 := ho k hF
    unfold l13phi
    rw [if_pos h1, if_pos h1, if_neg h2, this]
    simp
  · by_cases h2 : (k.val % 2 = 0 ∧ 1 ≤ k.val ∧ k.val ≤ 2 * l13L b)
    · have hF : l13inF b N k.val := by unfold l13inF; tauto
      have : ((o k : Fin b) : ℕ) = 0 := ho k hF
      unfold l13phi
      rw [if_neg h1, if_neg h1, if_pos h2, this]
      by_cases h3 : k.val / 2 ≤ T
      · rw [if_pos h3, if_pos ⟨h2.1, h2.2.1, h2.2.2, h3⟩]; simp
      · rw [if_neg h3, if_neg (by tauto)]; simp
    · have hF : ¬ l13inF b N k.val := by unfold l13inF; tauto
      rw [l13_phi_notF b N T hb o k hF, if_neg h1, if_neg (by tauto)]
      simp

/-! ### Congruences for `c_k` -/

lemma l13_cK_lt (b N k : ℕ) (hk : k < N) : cK b N k = b ^ k + b ^ (2 * N - k) := by
  simp [cK, hk]

lemma l13_cK_N (b N : ℕ) : cK b N N = b ^ N := by simp [cK]

lemma l13_cast_L (b : ℕ) (hb : 1 ≤ b) : ((l13L b : ℕ) : ℤ) = (b : ℤ) ^ 2 - 1 := by
  unfold l13L
  have : 1 ≤ b ^ 2 := Nat.one_le_pow _ _ hb
  push_cast [Nat.cast_sub this]
  ring

lemma l13_dvd_b (b N k : ℕ) (hN : 1 ≤ N) (hk1 : 1 ≤ k) (hkN : k ≤ N) : (b : ℤ) ∣ (cK b N k : ℤ) := by
  rcases Nat.lt_or_ge k N with h | h
  · rw [l13_cK_lt b N k h]
    push_cast
    exact dvd_add (dvd_pow_self _ (by omega)) (dvd_pow_self _ (by omega))
  · have : k = N := by omega
    subst this
    rw [l13_cK_N]
    push_cast
    exact dvd_pow_self _ (by omega)

lemma l13_dvd_L (b N k : ℕ) (hb : 1 ≤ b) (hk0 : k % 2 = 0) (hk1 : 1 ≤ k) (hkN : k < N) :
    (((l13L b : ℕ) : ℤ)) ∣ (cK b N k : ℤ) - 2 := by
  rw [l13_cast_L b hb, l13_cK_lt b N k hkN]
  obtain ⟨j, hj⟩ : ∃ j, k = 2 * j := ⟨k / 2, by omega⟩
  have h1 : (b : ℤ) ^ 2 - 1 ∣ (b : ℤ) ^ (2 * j) - 1 := by
    have := sub_dvd_pow_sub_pow ((b : ℤ) ^ 2) 1 j
    simpa [← pow_mul] using this
  have h2 : (b : ℤ) ^ 2 - 1 ∣ (b : ℤ) ^ (2 * (N - j)) - 1 := by
    have := sub_dvd_pow_sub_pow ((b : ℤ) ^ 2) 1 (N - j)
    simpa [← pow_mul] using this
  have h3 : 2 * N - k = 2 * (N - j) := by omega
  push_cast
  rw [h3, hj]
  have := dvd_add h1 h2
  convert this using 1
  ring

lemma l13_Bsum (b N T : ℕ) (hb : 1 ≤ b) (hN : 2 * l13L b < N) (hT : T < l13L b) :
    (((l13L b : ℕ) : ℤ)) ∣
      (∑ k ∈ range (N + 1),
        (if (k % 2 = 0 ∧ 1 ≤ k ∧ k ≤ 2 * l13L b ∧ k / 2 ≤ T) then (cK b N k : ℤ) else 0)) - 2 * T := by
  have hcard : ((range (N + 1)).filter (fun k => k % 2 = 0 ∧ 1 ≤ k ∧ k ≤ 2 * l13L b ∧ k / 2 ≤ T)).card = T := by
    have : (range (N + 1)).filter (fun k => k % 2 = 0 ∧ 1 ≤ k ∧ k ≤ 2 * l13L b ∧ k / 2 ≤ T) =
        (Icc 1 T).image (fun j => 2 * j) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Finset.mem_Icc]
      constructor
      · intro h
        exact ⟨k / 2, by omega, by omega⟩
      · rintro ⟨j, hj, rfl⟩
        omega
    rw [this, Finset.card_image_of_injective _ (fun a c h => by simpa using h)]
    simp
  have h2 : (∑ k ∈ range (N + 1),
      (if (k % 2 = 0 ∧ 1 ≤ k ∧ k ≤ 2 * l13L b ∧ k / 2 ≤ T) then (2 : ℤ) else 0)) = 2 * T := by
    rw [← Finset.sum_filter, Finset.sum_const, hcard]
    simp [mul_comm]
  rw [← h2, ← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro k hk
  rw [Finset.mem_range] at hk
  by_cases h : (k % 2 = 0 ∧ 1 ≤ k ∧ k ≤ 2 * l13L b ∧ k / 2 ≤ T)
  · rw [if_pos h, if_pos h]
    exact l13_dvd_L b N k hb h.1 h.2.1 (by omega)
  · rw [if_neg h, if_neg h]; simp

lemma l13_bigB (b : ℕ) (hb : 1 ≤ b) : bigB b = b * l13L b := by
  unfold bigB l13L
  have h1 : 1 ≤ b ^ 2 := Nat.one_le_pow _ _ hb
  have h2 : b ^ 3 = b * b ^ 2 := by ring
  rw [h2, Nat.mul_sub, mul_one]

lemma l13_coprime (b N T : ℕ) (hb : 3 ≤ b) (hN : 2 * l13L b < N) (o : DigVec b N)
    (ho : ∀ k : Fin (N + 1), l13inF b N k.val → ((o k : Fin b) : ℕ) = 0) (hT : T < l13L b)
    (hTd : ((l13L b : ℕ) : ℤ) ∣ 1 - ((palVal b N o : ℕ) : ℤ) - (cK b N 0 : ℤ) - (cK b N N : ℤ) - 2 * T) :
    Nat.Coprime (palVal b N (l13phi b N T (by omega) o)) (bigB b) := by
  have hL : 8 ≤ l13L b := by
    unfold l13L
    have : 9 ≤ b ^ 2 := by nlinarith
    omega
  set n := palVal b N (l13phi b N T (by omega) o) with hn
  have hn1 : (n : ℤ) = (∑ k : Fin (N + 1), ((if k.val = 0 ∨ k.val = N then (cK b N k : ℤ) else 0) +
      (if (k.val % 2 = 0 ∧ 1 ≤ k.val ∧ k.val ≤ 2 * l13L b ∧ k.val / 2 ≤ T) then (cK b N k : ℤ) else 0) +
      (((o k : Fin b) : ℕ) : ℤ) * (cK b N k : ℤ))) := by
    rw [hn]
    unfold palVal
    push_cast
    apply Finset.sum_congr rfl
    intro k _
    exact l13_decomp b N T (by omega) hN o ho k
  have hPo : ((palVal b N o : ℕ) : ℤ) = ∑ k : Fin (N + 1), (((o k : Fin b) : ℕ) : ℤ) * (cK b N k : ℤ) := by
    unfold palVal; push_cast; rfl
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← hPo] at hn1
  set f1 : ℕ → ℤ := fun k => if k = 0 ∨ k = N then (cK b N k : ℤ) else 0 with hf1
  set f2 : ℕ → ℤ := fun k => if (k % 2 = 0 ∧ 1 ≤ k ∧ k ≤ 2 * l13L b ∧ k / 2 ≤ T) then (cK b N k : ℤ) else 0 with hf2
  have hA : ∑ k : Fin (N + 1), (if k.val = 0 ∨ k.val = N then (cK b N k : ℤ) else 0) =
      (cK b N 0 : ℤ) + (cK b N N : ℤ) := by
    have := Fin.sum_univ_eq_sum_range f1 (N + 1)
    simp only [hf1] at this
    rw [this]
    have e : ∀ k : ℕ, f1 k = (if k = 0 then (cK b N 0 : ℤ) else 0) + (if k = N then (cK b N N : ℤ) else 0) := by
      intro k
      simp only [hf1]
      by_cases h0 : k = 0
      · subst h0; simp; omega
      · by_cases hN' : k = N
        · subst hN'; simp [h0]
        · simp [h0, hN']
    simp only [hf1] at e
    simp_rw [e]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (range (N + 1)) 0, Finset.sum_ite_eq' (range (N + 1)) N]
    simp
  have hB : ∑ k : Fin (N + 1), (if (k.val % 2 = 0 ∧ 1 ≤ k.val ∧ k.val ≤ 2 * l13L b ∧ k.val / 2 ≤ T) then (cK b N k : ℤ) else 0) =
      ∑ k ∈ range (N + 1), (if (k % 2 = 0 ∧ 1 ≤ k ∧ k ≤ 2 * l13L b ∧ k / 2 ≤ T) then (cK b N k : ℤ) else 0) :=
    Fin.sum_univ_eq_sum_range f2 (N + 1)
  rw [hA, hB] at hn1
  set S := ∑ k ∈ range (N + 1), (if (k % 2 = 0 ∧ 1 ≤ k ∧ k ≤ 2 * l13L b ∧ k / 2 ≤ T) then (cK b N k : ℤ) else 0) with hS
  have hSd := l13_Bsum b N T (by omega) hN hT
  -- mod L
  have hdL : ((l13L b : ℕ) : ℤ) ∣ (n : ℤ) - 1 := by
    have : (n : ℤ) - 1 = (S - 2 * T) - (1 - ((palVal b N o : ℕ) : ℤ) - (cK b N 0 : ℤ) - (cK b N N : ℤ) - 2 * T) := by
      rw [hn1]; ring
    rw [this]
    exact dvd_sub hSd hTd
  -- mod b
  have hdb : (b : ℤ) ∣ (n : ℤ) - 1 := by
    have hc0 : (cK b N 0 : ℤ) - 1 = (b : ℤ) ^ (2 * N) := by
      have : 0 < N := by omega
      simp [cK, this]
    have hcN : (b : ℤ) ∣ (cK b N N : ℤ) := l13_dvd_b b N N (by omega) (by omega) le_rfl
    have hSb : (b : ℤ) ∣ S := by
      rw [hS]
      apply Finset.dvd_sum
      intro k hk
      rw [Finset.mem_range] at hk
      by_cases h : (k % 2 = 0 ∧ 1 ≤ k ∧ k ≤ 2 * l13L b ∧ k / 2 ≤ T)
      · rw [if_pos h]; exact l13_dvd_b b N k (by omega) h.2.1 (by omega)
      · rw [if_neg h]; exact dvd_zero _
    have hPb : (b : ℤ) ∣ ((palVal b N o : ℕ) : ℤ) := by
      rw [hPo]
      apply Finset.dvd_sum
      intro k _
      by_cases h0 : k.val = 0
      · have : ((o k : Fin b) : ℕ) = 0 := ho k (by unfold l13inF; tauto)
        rw [this]; simp
      · exact Dvd.dvd.mul_left (l13_dvd_b b N k (by omega) (by omega) (by have := k.2; omega)) _
    have : (n : ℤ) - 1 = ((cK b N 0 : ℤ) - 1) + (cK b N N : ℤ) + S + ((palVal b N o : ℕ) : ℤ) := by
      rw [hn1]; ring
    rw [this, hc0]
    exact dvd_add (dvd_add (dvd_add (dvd_pow_self _ (by omega)) hcN) hSb) hPb
  have hcop : IsCoprime (b : ℤ) ((l13L b : ℕ) : ℤ) := by
    refine ⟨b, -1, ?_⟩
    rw [l13_cast_L b (by omega)]
    ring
  have hdbL : ((b * l13L b : ℕ) : ℤ) ∣ (n : ℤ) - 1 := by
    push_cast
    exact hcop.mul_dvd hdb hdL
  rw [← l13_bigB b (by omega)] at hdbL
  obtain ⟨t, ht⟩ := hdbL
  apply Nat.isCoprime_iff_coprime.1
  exact ⟨1, -t, by linarith⟩

/-! ### Choice of `T` and parity -/

noncomputable def l13T (b N : ℕ) (o : DigVec b N) : ℕ :=
  open Classical in
  if h : ∃ T : ℕ, T < l13L b ∧ ((l13L b : ℕ) : ℤ) ∣
      1 - ((palVal b N o : ℕ) : ℤ) - (cK b N 0 : ℤ) - (cK b N N : ℤ) - 2 * T then Classical.choose h else 0

lemma l13_s_odd (b N : ℕ) (hb : 3 ≤ b) (hN : 2 * l13L b < N) (hbo : b % 2 = 1) (o : DigVec b N)
    (ho : ∀ k : Fin (N + 1), l13inF b N k.val → ((o k : Fin b) : ℕ) = 0) :
    (palVal b N o + cK b N 0 + cK b N N) % 2 = 1 := by
  have hbodd : Odd b := Nat.odd_iff.2 hbo
  have hP : 2 ∣ palVal b N o := by
    unfold palVal
    apply Finset.dvd_sum
    intro k _
    by_cases hk : k.val = N
    · have : ((o k : Fin b) : ℕ) = 0 := ho k (by unfold l13inF; tauto)
      rw [this]; simp
    · have hkN : k.val < N := by have := k.2; omega
      apply Dvd.dvd.mul_left
      rw [l13_cK_lt b N k hkN]
      exact even_iff_two_dvd.1 (Odd.add_odd (hbodd.pow) (hbodd.pow))
  have h0 : 2 ∣ cK b N 0 := by
    have : 0 < N := by omega
    have e : cK b N 0 = 1 + b ^ (2 * N) := by simp [cK, this]
    rw [e]
    exact even_iff_two_dvd.1 (Odd.add_odd odd_one (hbodd.pow))
  have hN' : cK b N N % 2 = 1 := by
    rw [l13_cK_N]
    exact Nat.odd_iff.1 hbodd.pow
  omega

lemma l13_T_spec (b N : ℕ) (hb : 3 ≤ b) (hN : 2 * l13L b < N) (o : DigVec b N)
    (ho : ∀ k : Fin (N + 1), l13inF b N k.val → ((o k : Fin b) : ℕ) = 0) :
    l13T b N o < l13L b ∧ ((l13L b : ℕ) : ℤ) ∣
      1 - ((palVal b N o : ℕ) : ℤ) - (cK b N 0 : ℤ) - (cK b N N : ℤ) - 2 * (l13T b N o : ℕ) := by
  have hL : 8 ≤ l13L b := by
    unfold l13L
    have : 9 ≤ b ^ 2 := by nlinarith
    omega
  have hex : ∃ T : ℕ, T < l13L b ∧ ((l13L b : ℕ) : ℤ) ∣
      1 - ((palVal b N o : ℕ) : ℤ) - (cK b N 0 : ℤ) - (cK b N N : ℤ) - 2 * T := by
    have := l13_exists_T (l13L b) (by omega) (((palVal b N o + cK b N 0 + cK b N N : ℕ) : ℤ)) (by
      rcases Nat.mod_two_eq_zero_or_one b with hbe | hbo
      · left
        have hb2 : b ^ 2 % 2 = 0 := by
          rw [Nat.pow_mod]; simp [hbe]
        have : ¬ 2 ∣ l13L b := by
          unfold l13L
          have : 9 ≤ b ^ 2 := by nlinarith
          omega
        intro h
        exact this (by exact_mod_cast h)
      · right
        have := l13_s_odd b N hb hN hbo o ho
        intro h
        have h' : 2 ∣ palVal b N o + cK b N 0 + cK b N N := by exact_mod_cast h
        omega)
    obtain ⟨T, hT, hd⟩ := this
    refine ⟨T, hT, ?_⟩
    convert hd using 2
    push_cast
    ring
  unfold l13T
  rw [dif_pos hex]
  exact Classical.choose_spec hex

/-! ### The weighted count -/

/-- The set `Ω` of digit strings vanishing on the fixed positions. -/
def l13Om (b N : ℕ) (h1 : 1 < b) : Finset (DigVec b N) :=
  Fintype.piFinset (fun k : Fin (N + 1) => if l13inF b N k.val then ({⟨0, by omega⟩} : Finset (Fin b)) else Finset.univ)

lemma l13_mem_Om (b N : ℕ) (h1 : 1 < b) (o : DigVec b N) (ho : o ∈ l13Om b N h1) :
    ∀ k : Fin (N + 1), l13inF b N k.val → ((o k : Fin b) : ℕ) = 0 := by
  classical
  unfold l13Om at ho
  rw [Fintype.mem_piFinset] at ho
  intro k hk
  have := ho k
  rw [if_pos hk] at this
  rw [Finset.mem_singleton] at this
  rw [this]

lemma l13_card_F (b N : ℕ) :
    (Finset.univ.filter (fun k : Fin (N + 1) => l13inF b N k.val)).card ≤ l13L b + 2 := by
  classical
  have hsub : (Finset.univ.filter (fun k : Fin (N + 1) => l13inF b N k.val)).image (fun k => k.val) ⊆
      insert 0 (insert N ((Icc 1 (l13L b)).image (fun j => 2 * j))) := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    rw [Finset.mem_filter] at hk
    have := hk.2
    unfold l13inF at this
    simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_Icc]
    rcases this with h | h | h
    · left; exact h
    · right; left; exact h
    · right; right; exact ⟨k.val / 2, ⟨by omega, by omega⟩, by omega⟩
  calc _ = ((Finset.univ.filter (fun k : Fin (N + 1) => l13inF b N k.val)).image (fun k => k.val)).card :=
        (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ ≤ (insert 0 (insert N ((Icc 1 (l13L b)).image (fun j => 2 * j)))).card := Finset.card_le_card hsub
    _ ≤ 1 + (1 + ((Icc 1 (l13L b)).image (fun j => 2 * j)).card) := by
        refine (Finset.card_insert_le _ _).trans ?_
        have := Finset.card_insert_le N ((Icc 1 (l13L b)).image (fun j => 2 * j))
        omega
    _ ≤ l13L b + 2 := by
        have := Finset.card_image_le (s := Icc 1 (l13L b)) (f := fun j => 2 * j)
        simp at this
        omega

theorem itemL13 : ItemL13 := by
  classical
  intro b g hb hg hg0 hg1
  have h1 : 1 < b := by omega
  have hb0 : 0 < b := by omega
  set L := l13L b with hLdef
  set δ := min (g 0) (g 1) with hδ
  have hδpos : 0 < δ := lt_min hg0 hg1
  have hg_le : ∀ a, a < b → g a ≤ 1 := by
    intro a ha
    have := Finset.single_le_sum (f := g) (fun i _ => hg.1 i) (Finset.mem_range.2 ha)
    rw [hg.2] at this
    exact this
  have hδ1 : δ ≤ 1 := (min_le_left _ _).trans (hg_le 0 (by omega))
  refine ⟨δ ^ (L + 2), pow_pos hδpos _, 2 * L + 1, ?_⟩
  intro N hN
  have hN' : 2 * L < N := by omega
  -- the weight function f on digits
  set f : Fin (N + 1) → Fin b → ℝ := fun k a => if l13inF b N k.val then 1 else g a with hf
  have hfnn : ∀ k a, 0 ≤ f k a := by
    intro k a; simp only [hf]; split_ifs
    · exact zero_le_one
    · exact hg.1 _
  -- total mass of Ω is 1
  have hmass : ∑ o ∈ l13Om b N h1, ∏ k, f k (o k) = 1 := by
    unfold l13Om
    rw [← Finset.prod_univ_sum _ f]
    apply Finset.prod_eq_one
    intro k _
    by_cases hk : l13inF b N k.val
    · simp [hf, hk]
    · simp only [hf, hk, if_false]
      have := Fin.sum_univ_eq_sum_range (fun a => g a) b
      rw [hg.2] at this
      exact this
  set φ : DigVec b N → DigVec b N := fun o => l13phi b N (l13T b N o) h1 o with hφ
  have hinj : Set.InjOn φ (l13Om b N h1 : Set (DigVec b N)) := by
    intro o ho o' ho' hoo
    have ho1 := l13_mem_Om b N h1 o ho
    have ho2 := l13_mem_Om b N h1 o' ho'
    funext k
    by_cases hk : l13inF b N k.val
    · exact Fin.ext (by rw [ho1 k hk, ho2 k hk])
    · have e1 := l13_phi_notF b N (l13T b N o) h1 o k hk
      have e2 := l13_phi_notF b N (l13T b N o') h1 o' k hk
      have : φ o k = φ o' k := by rw [hoo]
      simp only [hφ] at this
      rw [← e1, ← e2]; exact this
  have hcop : ∀ o ∈ l13Om b N h1, Nat.Coprime (palVal b N (φ o)) (bigB b) := by
    intro o ho
    have ho1 := l13_mem_Om b N h1 o ho
    obtain ⟨hT, hd⟩ := l13_T_spec b N hb hN' o ho1
    exact l13_coprime b N (l13T b N o) hb hN' o ho1 hT hd
  have hw : ∀ o ∈ l13Om b N h1, δ ^ (L + 2) * ∏ k, f k (o k) ≤ wDig b g N (φ o) := by
    intro o ho
    have pt : ∀ k : Fin (N + 1), (if l13inF b N k.val then δ else 1) * f k (o k) ≤ g (φ o k) := by
      intro k
      by_cases hk : l13inF b N k.val
      · have hle : ((φ o k : Fin b) : ℕ) ≤ 1 := l13_phi_le b N (l13T b N o) h1 o k hk
        simp only [hf, if_pos hk, mul_one]
        have : ((φ o k : Fin b) : ℕ) = 0 ∨ ((φ o k : Fin b) : ℕ) = 1 := by omega
        rcases this with h | h
        · simp only [hφ] at h ⊢; rw [h]; exact min_le_left _ _
        · simp only [hφ] at h ⊢; rw [h]; exact min_le_right _ _
      · simp only [hf, if_neg hk, one_mul]
        have := l13_phi_notF b N (l13T b N o) h1 o k hk
        simp only [hφ]; rw [this]
    have hprod : ∏ k : Fin (N + 1), ((if l13inF b N k.val then δ else 1) * f k (o k)) ≤ wDig b g N (φ o) := by
      unfold wDig
      exact Finset.prod_le_prod₀ (fun k _ => mul_nonneg (by by_cases h : l13inF b N k.val <;> simp [h, hδpos.le]) (hfnn _ _)) (fun k _ => pt k)
    refine le_trans ?_ hprod
    rw [Finset.prod_mul_distrib]
    have hp : ∏ k : Fin (N + 1), (if l13inF b N k.val then δ else 1) =
        δ ^ (Finset.univ.filter (fun k : Fin (N + 1) => l13inF b N k.val)).card := by
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    rw [hp]
    apply mul_le_mul_of_nonneg_right
    · exact pow_le_pow_of_le_one hδpos.le hδ1 (l13_card_F b N)
    · exact Finset.prod_nonneg (fun k _ => hfnn _ _)
  unfold XW AW
  calc δ ^ (L + 2) = δ ^ (L + 2) * ∑ o ∈ l13Om b N h1, ∏ k, f k (o k) := by rw [hmass, mul_one]
    _ = ∑ o ∈ l13Om b N h1, δ ^ (L + 2) * ∏ k, f k (o k) := Finset.mul_sum _ _ _
    _ ≤ ∑ o ∈ l13Om b N h1, wDig b g N (φ o) := Finset.sum_le_sum hw
    _ = ∑ d ∈ (l13Om b N h1).image φ, wDig b g N d := (Finset.sum_image hinj).symm
    _ = ∑ d ∈ (l13Om b N h1).image φ,
          (if Nat.Coprime (palVal b N d) (bigB b) ∧ 1 ∣ palVal b N d then wDig b g N d else 0) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [Finset.mem_image] at hd
        obtain ⟨o, ho, rfl⟩ := hd
        rw [if_pos ⟨hcop o ho, one_dvd _⟩]
    _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro d _ _
        split_ifs
        · exact Finset.prod_nonneg (fun k _ => hg.1 _)
        · exact le_rfl

end Omega3
