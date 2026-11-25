import KappaOmega2.StatementsK

/-!
# LK17 helper: base-`b` digits of the κ-palindrome `n(u, w)`

Digit `i` of `n(u, w)` is `u_i` for `i < m`, digit `i − m` of `w` for `m ≤ i < m + ℓ`, and `u_{2N−i}` above.
-/

namespace KappaOmega2

open Finset Palprimes

lemma LK17_m_le (N : ℕ) : mK N ≤ N := by unfold mK; omega

lemma LK17_m_pos (N : ℕ) (hN : 1 ≤ N) : 0 < mK N := by unfold mK; omega

lemma LK17_two_m_ell (N : ℕ) : 2 * mK N + ellK N = 2 * N + 1 := by
  have := LK17_m_le N; unfold ellK; omega

/-- Digit `i` of `n(u, w)`. -/
def kdig (b N : ℕ) (u : KVec b N) (w i : ℕ) : ℕ :=
  if h : i < mK N then (u ⟨i, h⟩ : ℕ)
  else if i < mK N + ellK N then w / b ^ (i - mK N) % b
  else if h' : 2 * N - i < mK N then (u ⟨2 * N - i, h'⟩ : ℕ) else 0

/-- The digit list (least significant first) of `n(u, w)`. -/
def kList (b N : ℕ) (u : KVec b N) (w : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin (2 * N + 1) => kdig b N u w i)

lemma kList_length (b N : ℕ) (u : KVec b N) (w : ℕ) : (kList b N u w).length = 2 * N + 1 := by
  simp [kList]

lemma kdig_lt (b N : ℕ) (hb : 1 ≤ b) (u : KVec b N) (w i : ℕ) : kdig b N u w i < b := by
  unfold kdig
  split_ifs
  · exact (u _).isLt
  · exact Nat.mod_lt _ (by omega)
  · exact (u _).isLt
  · omega

lemma kdig_low (b N : ℕ) (u : KVec b N) (w i : ℕ) (hi : i < mK N) :
    kdig b N u w i = (u ⟨i, hi⟩ : ℕ) := by
  unfold kdig; rw [dif_pos hi]

lemma kdig_mid (b N : ℕ) (u : KVec b N) (w j : ℕ) (hj : j < ellK N) :
    kdig b N u w (mK N + j) = w / b ^ j % b := by
  unfold kdig
  rw [dif_neg (by omega), if_pos (by omega), show mK N + j - mK N = j by omega]

lemma kdig_top (b N : ℕ) (u : KVec b N) (w j : ℕ) (hj : j < mK N) :
    kdig b N u w (mK N + ellK N + j) = (u ⟨mK N - 1 - j, by omega⟩ : ℕ) := by
  have h2 := LK17_two_m_ell N
  unfold kdig
  rw [dif_neg (by omega), if_neg (by omega), dif_pos (by omega)]
  congr 2
  apply Fin.ext
  simp only
  omega

lemma LK17_sum_digits (b w ℓ : ℕ) : ∑ j ∈ range ℓ, (w / b ^ j % b) * b ^ j = w % b ^ ℓ := by
  induction ℓ with
  | zero => simp [Nat.mod_one]
  | succ l ih => rw [sum_range_succ, ih, Nat.mod_pow_succ]; ring

lemma LK17_fin_sum (b N : ℕ) (u : KVec b N) (w : ℕ) (f : ℕ → ℕ) :
    ∑ k : Fin (mK N), (u k : ℕ) * f k = ∑ k ∈ range (mK N), kdig b N u w k * f k := by
  rw [← Fin.sum_univ_eq_sum_range (fun k => kdig b N u w k * f k)]
  apply Finset.sum_congr rfl
  intro k _
  rw [kdig_low b N u w k k.isLt]

/-- `n(u, w) = Σ_{i ≤ 2N} digit_i b^i`. -/
lemma LK17_val_sum (b N : ℕ) (u : KVec b N) (w : ℕ) (hw : w < WK b N) :
    kpalVal b N u w = ∑ i ∈ range (2 * N + 1), kdig b N u w i * b ^ i := by
  have h2 := LK17_two_m_ell N
  have hmN := LK17_m_le N
  rw [show 2 * N + 1 = mK N + ellK N + mK N by omega, sum_range_add, sum_range_add]
  have hmid : ∑ j ∈ range (ellK N), kdig b N u w (mK N + j) * b ^ (mK N + j) = w * b ^ mK N := by
    have : ∑ j ∈ range (ellK N), kdig b N u w (mK N + j) * b ^ (mK N + j) =
        b ^ mK N * ∑ j ∈ range (ellK N), (w / b ^ j % b) * b ^ j := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      rw [kdig_mid b N u w j (mem_range.mp hj), pow_add]; ring
    rw [this, LK17_sum_digits, Nat.mod_eq_of_lt (show w < b ^ ellK N from hw)]; ring
  have htop : ∑ j ∈ range (mK N), kdig b N u w (mK N + ellK N + j) * b ^ (mK N + ellK N + j) =
      ∑ k ∈ range (mK N), kdig b N u w k * b ^ (2 * N - k) := by
    rw [← sum_range_reflect (fun k => kdig b N u w k * b ^ (2 * N - k)) (mK N)]
    apply sum_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    rw [kdig_top b N u w j hj', kdig_low b N u w (mK N - 1 - j) (by omega)]
    congr 2
    omega
  rw [hmid, htop]
  unfold kpalVal
  rw [LK17_fin_sum b N u w (fun k => cK b N k)]
  have hc : ∀ k ∈ range (mK N), kdig b N u w k * cK b N k =
      kdig b N u w k * b ^ k + kdig b N u w k * b ^ (2 * N - k) := by
    intro k hk
    have hk' := mem_range.mp hk
    unfold cK
    rw [if_pos (by omega)]; ring
  rw [sum_congr rfl hc, sum_add_distrib]
  ring

lemma LK17_ofDigits (b N : ℕ) (u : KVec b N) (w : ℕ) :
    Nat.ofDigits b (kList b N u w) = ∑ i ∈ range (2 * N + 1), kdig b N u w i * b ^ i := by
  rw [Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_ofFn, List.sum_ofFn]
  have : ∀ i : Fin (kList b N u w).length, (kList b N u w).get i * b ^ (i : ℕ) =
      kdig b N u w i * b ^ (i : ℕ) := by
    intro i
    rw [List.get_eq_getElem]
    simp only [kList, List.getElem_ofFn]
  simp only [this]
  rw [Fin.sum_univ_eq_sum_range (fun i => kdig b N u w i * b ^ i), kList_length]

lemma LK17_digits (b N : ℕ) (hb : 2 ≤ b) (hN : 1 ≤ N) (u : KVec b N) (w : ℕ) (hw : w < WK b N)
    (hu0 : (u ⟨0, LK17_m_pos N hN⟩ : ℕ) ≠ 0) :
    Nat.digits b (kpalVal b N u w) = kList b N u w := by
  rw [LK17_val_sum b N u w hw, ← LK17_ofDigits]
  apply Nat.digits_ofDigits b (by omega)
  · intro l hl
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hl
    exact kdig_lt b N (by omega) u w _
  · intro h
    rw [List.getLast_eq_getElem]
    simp only [kList, List.getElem_ofFn, List.length_ofFn]
    have h2 := LK17_two_m_ell N
    have hmN := LK17_m_le N
    have hm := LK17_m_pos N hN
    have : kdig b N u w (2 * N + 1 - 1) = (u ⟨0, LK17_m_pos N hN⟩ : ℕ) := by
      unfold kdig
      rw [dif_neg (by omega), if_neg (by omega), dif_pos (by omega)]
      congr 2
      apply Fin.ext
      simp only
      omega
    rw [this]
    exact hu0

lemma LK17_mod_b (b N : ℕ) (hN : 1 ≤ N) (u : KVec b N) (w : ℕ) (hw : w < WK b N) :
    kpalVal b N u w % b = (u ⟨0, LK17_m_pos N hN⟩ : ℕ) := by
  rw [LK17_val_sum b N u w hw, sum_range_succ']
  have hS : ∑ i ∈ range (2 * N), kdig b N u w (i + 1) * b ^ (i + 1) =
      b * ∑ i ∈ range (2 * N), kdig b N u w (i + 1) * b ^ i := by
    rw [mul_sum]; apply sum_congr rfl; intro i _; rw [pow_succ]; ring
  rw [hS, kdig_low b N u w 0 (LK17_m_pos N hN), pow_zero, mul_one, add_comm,
    Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (u _).isLt

lemma LK17_getD (b N : ℕ) (u : KVec b N) (w i : ℕ) (hi : i < 2 * N + 1) :
    (kList b N u w).getD i 0 = kdig b N u w i := by
  have hl : i < (kList b N u w).length := by rw [kList_length]; exact hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
  simp only [kList, List.getElem_ofFn]

lemma LK17_inj (b N : ℕ) (hb : 2 ≤ b) (hN : 1 ≤ N) (u u' : KVec b N) (w w' : ℕ)
    (hw : w < WK b N) (hw' : w' < WK b N)
    (hu0 : (u ⟨0, LK17_m_pos N hN⟩ : ℕ) ≠ 0) (hu0' : (u' ⟨0, LK17_m_pos N hN⟩ : ℕ) ≠ 0)
    (h : kpalVal b N u w = kpalVal b N u' w') : u = u' ∧ w = w' := by
  have hL : kList b N u w = kList b N u' w' := by
    rw [← LK17_digits b N hb hN u w hw hu0, ← LK17_digits b N hb hN u' w' hw' hu0', h]
  have hf : ∀ i, i < 2 * N + 1 → kdig b N u w i = kdig b N u' w' i := by
    intro i hi
    have := congrArg (fun l : List ℕ => l.getD i 0) hL
    rwa [LK17_getD b N u w i hi, LK17_getD b N u' w' i hi] at this
  have h2 := LK17_two_m_ell N
  constructor
  · funext k
    apply Fin.ext
    have := hf k (by omega)
    rwa [kdig_low b N u w k k.isLt, kdig_low b N u' w' k k.isLt] at this
  · have e : ∀ v : ℕ, v < WK b N → ∀ v' : ℕ, v' = v →
        v = ∑ j ∈ range (ellK N), (v / b ^ j % b) * b ^ j := by
      intro v hv _ _
      rw [LK17_sum_digits, Nat.mod_eq_of_lt (show v < b ^ ellK N from hv)]
    rw [e w hw w rfl, e w' hw' w' rfl]
    apply sum_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    have := hf (mK N + j) (by omega)
    rw [kdig_mid b N u w j hj', kdig_mid b N u' w' j hj'] at this
    rw [this]


/-- The κ-palindrome `n(u, w)` with `u_0 ≠ 0` has `2N + 1` digits and is a κ-palindrome. -/
lemma LK17_mem (b N : ℕ) (hb : 2 ≤ b) (hN : 1 ≤ N) (u : KVec b N) (w : ℕ) (hw : w < WK b N)
    (hu0 : (u ⟨0, LK17_m_pos N hN⟩ : ℕ) ≠ 0) :
    b ^ (2 * N) ≤ kpalVal b N u w ∧ kpalVal b N u w < b ^ (2 * N + 1) ∧ IsKappaPal b (kpalVal b N u w) := by
  have hd := LK17_digits b N hb hN u w hw hu0
  have hlen : (Nat.digits b (kpalVal b N u w)).length = 2 * N + 1 := by rw [hd, kList_length]
  have hn0 : kpalVal b N u w ≠ 0 := by
    intro h0
    rw [h0, Nat.digits_zero] at hlen
    simp at hlen
  refine ⟨?_, ?_, ?_⟩
  · have hle := Nat.base_pow_length_digits_le b (kpalVal b N u w) (by omega) hn0
    rw [hlen, pow_succ] at hle
    have hb0 : 0 < b := by omega
    rw [mul_comm] at hle
    exact Nat.le_of_mul_le_mul_left hle hb0
  · have hlt := Nat.lt_base_pow_length_digits (m := kpalVal b N u w) (by omega : 1 < b)
    rwa [hlen] at hlt
  · unfold IsKappaPal
    rw [hd, kList_length]
    intro i hi
    have hi' : i < mK N := hi
    have h2 := LK17_two_m_ell N
    have hmN := LK17_m_le N
    rw [LK17_getD b N u w i (by omega), LK17_getD b N u w _ (by omega), kdig_low b N u w i hi']
    unfold kdig
    rw [dif_neg (by omega), if_neg (by omega), dif_pos (by omega)]
    congr 2
    apply Fin.ext
    simp only
    omega

end KappaOmega2
