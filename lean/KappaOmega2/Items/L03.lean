import KappaOmega2.Statements

namespace KappaOmega2

open Finset


/-! Helper definitions for Item N. Integer tent `nU m i = min(i+1, 2m-1-i)` on `[0, 2m-2]`. -/
def nU (m i : ℕ) : ℕ := if i + 1 < 2 * m then min (i + 1) (2 * m - 1 - i) else 0

def nR (c i : ℕ) : ℚ := ((i + 1 - c : ℕ) : ℚ)

def nConv (f g : ℕ → ℚ) (s : ℕ) : ℚ := ∑ i ∈ range (s + 1), f i * g (s - i)

def nTri (x : ℚ) : ℚ := x * (x + 1) * (x + 2) / 6

def nT (n : ℕ) : ℚ := nTri (n : ℚ)

def nPhi (m s : ℕ) : ℚ :=
  nT (s + 1 - 0 - 0) - 2 * nT (s + 1 - 0 - m) + nT (s + 1 - 0 - (2 * m))
  - 2 * nT (s + 1 - m - 0) + 4 * nT (s + 1 - m - m) - 2 * nT (s + 1 - m - (2 * m))
  + nT (s + 1 - (2 * m) - 0) - 2 * nT (s + 1 - (2 * m) - m) + nT (s + 1 - (2 * m) - (2 * m))

def nE0 (m t : ℚ) : ℚ := nTri (t + 1)
def nE1 (m t : ℚ) : ℚ := nTri (m + t + 1) - 4 * nTri (t + 1)
def nE2 (m t : ℚ) : ℚ := nTri (2 * m + t + 1) - 4 * nTri (m + t + 1) + 6 * nTri (t + 1)
def nE3 (m t : ℚ) : ℚ := nTri (3 * m + t + 1) - 4 * nTri (2 * m + t + 1) + 6 * nTri (m + t + 1) - 4 * nTri (t + 1)

lemma nU_arith (m i : ℕ) : nU m i + 2 * (i + 1 - m) = (i + 1) + (i + 1 - 2 * m) := by
  unfold nU
  split_ifs <;> (try simp only [min_def]) <;> (try split_ifs) <;> omega

lemma nU_decomp (m i : ℕ) : (nU m i : ℚ) = nR 0 i + (-2) * nR m i + 1 * nR (2 * m) i := by
  have h' : ((nU m i : ℕ) : ℚ) + 2 * ((i + 1 - m : ℕ) : ℚ) = ((i + 1 : ℕ) : ℚ) + ((i + 1 - 2 * m : ℕ) : ℚ) := by
    exact_mod_cast nU_arith m i
  unfold nR
  rw [Nat.sub_zero]
  linarith

lemma nSum_id (N : ℕ) : ∑ i ∈ range N, ((i : ℚ) + 1) = (N : ℚ) * ((N : ℚ) + 1) / 2 := by
  induction N with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

lemma nSum_tri (N : ℕ) : ∑ i ∈ range N, ((i : ℚ) + 1) * ((N - i : ℕ) : ℚ) = nT N := by
  induction N with
  | zero => simp [nT, nTri]
  | succ n ih =>
    have h1 : ∀ i ∈ range (n + 1), ((i : ℚ) + 1) * ((n + 1 - i : ℕ) : ℚ)
        = ((i : ℚ) + 1) * ((n - i : ℕ) : ℚ) + ((i : ℚ) + 1) := by
      intro i hi
      have hi' := Finset.mem_range.1 hi
      have e : n + 1 - i = (n - i) + 1 := by omega
      rw [e]; push_cast; ring
    have h2 : ∑ i ∈ range (n + 1), ((i : ℚ) + 1) * ((n - i : ℕ) : ℚ)
        = ∑ i ∈ range n, ((i : ℚ) + 1) * ((n - i : ℕ) : ℚ) := by
      rw [sum_range_succ]; simp
    rw [sum_congr rfl h1, sum_add_distrib, h2, ih, nSum_id]
    unfold nT nTri; push_cast; ring

lemma nConv_zero_zero (n : ℕ) : nConv (nR 0) (nR 0) n = nT (n + 1) := by
  rw [← nSum_tri (n + 1)]
  unfold nConv
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.1 hi
  simp only [nR, Nat.sub_zero]
  have e : n - i + 1 = n + 1 - i := by omega
  rw [e]; push_cast; ring

lemma nConv_shiftL (a : ℕ) (g : ℕ → ℚ) (s : ℕ) :
    nConv (nR (a + 1)) g (s + 1) = nConv (nR a) g s := by
  unfold nConv
  rw [Finset.sum_range_succ' _ (s + 1)]
  have h0 : nR (a + 1) 0 = 0 := by
    unfold nR; rw [show (0 + 1 - (a + 1) : ℕ) = 0 by omega]; simp
  rw [h0, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  have e1 : nR (a + 1) (i + 1) = nR a i := by
    unfold nR; congr 1; omega
  have e2 : s + 1 - (i + 1) = s - i := by omega
  rw [e1, e2]

lemma nConv_shiftR (f : ℕ → ℚ) (b s : ℕ) :
    nConv f (nR (b + 1)) (s + 1) = nConv f (nR b) s := by
  unfold nConv
  rw [Finset.sum_range_succ _ (s + 1)]
  have h0 : nR (b + 1) 0 = 0 := by
    unfold nR; rw [show (0 + 1 - (b + 1) : ℕ) = 0 by omega]; simp
  rw [Nat.sub_self, h0, mul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.1 hi
  have e1 : nR (b + 1) (s + 1 - i) = nR b (s - i) := by
    unfold nR; congr 1; omega
  rw [e1]

lemma nConv_R0 (b : ℕ) : ∀ n : ℕ, nConv (nR 0) (nR b) n = nT (n + 1 - b) := by
  induction b with
  | zero => intro n; simpa using nConv_zero_zero n
  | succ b ih =>
    intro n
    cases n with
    | zero =>
      have h1 : nR (b + 1) 0 = 0 := by
        unfold nR; rw [show (0 + 1 - (b + 1) : ℕ) = 0 by omega]; simp
      unfold nConv
      rw [show (0 + 1 - (b + 1) : ℕ) = 0 by omega]
      simp [h1, nT, nTri]
    | succ m' =>
      rw [nConv_shiftR, ih]
      congr 1
      omega

lemma nConv_R (a : ℕ) : ∀ b n : ℕ, nConv (nR a) (nR b) n = nT (n + 1 - a - b) := by
  induction a with
  | zero => intro b n; simpa using nConv_R0 b n
  | succ a ih =>
    intro b n
    cases n with
    | zero =>
      have h1 : nR (a + 1) 0 = 0 := by
        unfold nR; rw [show (0 + 1 - (a + 1) : ℕ) = 0 by omega]; simp
      rw [show (0 + 1 - (a + 1) - b : ℕ) = 0 by omega]
      unfold nConv
      simp [h1, nT, nTri]
    | succ m' =>
      rw [nConv_shiftL, ih]
      congr 1
      omega

lemma nConv_lin_left (A B C : ℕ → ℚ) (c d : ℚ) (g : ℕ → ℚ) (s : ℕ) :
    nConv (fun i => A i + c * B i + d * C i) g s
      = nConv A g s + c * nConv B g s + d * nConv C g s := by
  unfold nConv
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

lemma nConv_lin_right (f A B C : ℕ → ℚ) (c d : ℚ) (s : ℕ) :
    nConv f (fun i => A i + c * B i + d * C i) s
      = nConv f A s + c * nConv f B s + d * nConv f C s := by
  unfold nConv
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

lemma nD_eq (m s : ℕ) : ∑ i ∈ range (s + 1), (nU m i : ℚ) * (nU m (s - i) : ℚ) = nPhi m s := by
  have key : nConv (fun i => nR 0 i + (-2) * nR m i + 1 * nR (2 * m) i)
      (fun i => nR 0 i + (-2) * nR m i + 1 * nR (2 * m) i) s = nPhi m s := by
    rw [nConv_lin_left]
    simp only [nConv_lin_right, nConv_R]
    unfold nPhi
    ring
  simp only [nU_decomp]
  exact key

lemma fejer_eq (m i : ℕ) : fejerW m i = (nU m i : ℚ) / ((m : ℚ) ^ 2) := by
  unfold fejerW nU
  split_ifs <;> simp

lemma nSum_fejer (m s : ℕ) :
    ∑ i ∈ range (s + 1), fejerW m i * fejerW m (s - i) = nPhi m s / (m : ℚ) ^ 4 := by
  have h : ∀ i ∈ range (s + 1), fejerW m i * fejerW m (s - i)
      = (nU m i : ℚ) * (nU m (s - i) : ℚ) / ((m : ℚ) ^ 4) := by
    intro i _
    rw [fejer_eq, fejer_eq]; ring
  rw [sum_congr rfl h, ← sum_div, nD_eq]


lemma nPhi_blk0 (m x : ℕ) (hx : x < m) : nPhi m (x) = nE0 (m : ℚ) (x : ℚ) := by
  unfold nPhi nE0
  rw [show x + 1 - 0 - 0 = x + 1 by omega, show x + 1 - 0 - m = 0 by omega, show x + 1 - 0 - 2 * m = 0 by omega, show x + 1 - m - 0 = 0 by omega, show x + 1 - m - m = 0 by omega, show x + 1 - m - 2 * m = 0 by omega, show x + 1 - 2 * m - 0 = 0 by omega, show x + 1 - 2 * m - m = 0 by omega, show x + 1 - 2 * m - 2 * m = 0 by omega]
  simp only [nT, nTri]
  push_cast
  ring

lemma nPhi_blk1 (m x : ℕ) (hx : x < m) : nPhi m (m + x) = nE1 (m : ℚ) (x : ℚ) := by
  unfold nPhi nE1
  rw [show m + x + 1 - 0 - 0 = 1 * m + x + 1 by omega, show m + x + 1 - 0 - m = x + 1 by omega, show m + x + 1 - 0 - 2 * m = 0 by omega, show m + x + 1 - m - 0 = x + 1 by omega, show m + x + 1 - m - m = 0 by omega, show m + x + 1 - m - 2 * m = 0 by omega, show m + x + 1 - 2 * m - 0 = 0 by omega, show m + x + 1 - 2 * m - m = 0 by omega, show m + x + 1 - 2 * m - 2 * m = 0 by omega]
  simp only [nT, nTri]
  push_cast
  ring

lemma nPhi_blk2 (m x : ℕ) (hx : x < m) : nPhi m (m + m + x) = nE2 (m : ℚ) (x : ℚ) := by
  unfold nPhi nE2
  rw [show m + m + x + 1 - 0 - 0 = 2 * m + x + 1 by omega, show m + m + x + 1 - 0 - m = 1 * m + x + 1 by omega, show m + m + x + 1 - 0 - 2 * m = x + 1 by omega, show m + m + x + 1 - m - 0 = 1 * m + x + 1 by omega, show m + m + x + 1 - m - m = x + 1 by omega, show m + m + x + 1 - m - 2 * m = 0 by omega, show m + m + x + 1 - 2 * m - 0 = x + 1 by omega, show m + m + x + 1 - 2 * m - m = 0 by omega, show m + m + x + 1 - 2 * m - 2 * m = 0 by omega]
  simp only [nT, nTri]
  push_cast
  ring

lemma nPhi_blk3 (m x : ℕ) (hx : x < m) : nPhi m (m + m + m + x) = nE3 (m : ℚ) (x : ℚ) := by
  unfold nPhi nE3
  rw [show m + m + m + x + 1 - 0 - 0 = 3 * m + x + 1 by omega, show m + m + m + x + 1 - 0 - m = 2 * m + x + 1 by omega, show m + m + m + x + 1 - 0 - 2 * m = 1 * m + x + 1 by omega, show m + m + m + x + 1 - m - 0 = 2 * m + x + 1 by omega, show m + m + m + x + 1 - m - m = 1 * m + x + 1 by omega, show m + m + m + x + 1 - m - 2 * m = x + 1 by omega, show m + m + m + x + 1 - 2 * m - 0 = 1 * m + x + 1 by omega, show m + m + m + x + 1 - 2 * m - m = x + 1 by omega, show m + m + m + x + 1 - 2 * m - 2 * m = 0 by omega]
  simp only [nT, nTri]
  push_cast
  ring

lemma nS1 (m : ℕ) : ∑ t ∈ range m, (t : ℚ) ^ 1 = ((-1/2)*(m:ℚ) + (1/2)*(m:ℚ)^2) := by
  induction m with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

lemma nS2 (m : ℕ) : ∑ t ∈ range m, (t : ℚ) ^ 2 = ((1/6)*(m:ℚ) + (-1/2)*(m:ℚ)^2 + (1/3)*(m:ℚ)^3) := by
  induction m with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

lemma nS3 (m : ℕ) : ∑ t ∈ range m, (t : ℚ) ^ 3 = ((1/4)*(m:ℚ)^2 + (-1/2)*(m:ℚ)^3 + (1/4)*(m:ℚ)^4) := by
  induction m with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

lemma nS4 (m : ℕ) : ∑ t ∈ range m, (t : ℚ) ^ 4 = ((-1/30)*(m:ℚ) + (1/3)*(m:ℚ)^3 + (-1/2)*(m:ℚ)^4 + (1/5)*(m:ℚ)^5) := by
  induction m with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

lemma nS5 (m : ℕ) : ∑ t ∈ range m, (t : ℚ) ^ 5 = ((-1/12)*(m:ℚ)^2 + (5/12)*(m:ℚ)^4 + (-1/2)*(m:ℚ)^5 + (1/6)*(m:ℚ)^6) := by
  induction m with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

lemma nS6 (m : ℕ) : ∑ t ∈ range m, (t : ℚ) ^ 6 = ((1/42)*(m:ℚ) + (-1/6)*(m:ℚ)^3 + (1/2)*(m:ℚ)^5 + (-1/2)*(m:ℚ)^6 + (1/7)*(m:ℚ)^7) := by
  induction m with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

lemma nSumE0 (m : ℕ) : ∑ x ∈ range m, (nE0 (m : ℚ) (x : ℚ)) ^ 2 = ((1/140)*(m:ℚ) + (1/8)*(m:ℚ)^2 + (23/72)*(m:ℚ)^3 + (1/3)*(m:ℚ)^4 + (61/360)*(m:ℚ)^5 + (1/24)*(m:ℚ)^6 + (1/252)*(m:ℚ)^7) := by
  have h : ∀ t : ℚ, (nE0 (m : ℚ) t) ^ 2 = ((1)) + (((11/3))) * t ^ 1 + (((193/36))) * t ^ 2 + ((4)) * t ^ 3 + (((29/18))) * t ^ 4 + (((1/3))) * t ^ 5 + (((1/36))) * t ^ 6 := by
    intro t; unfold nE0 nTri; ring
  simp only [h]
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul, nS1, nS2, nS3, nS4, nS5, nS6]
  ring

lemma nSumE1 (m : ℕ) : ∑ x ∈ range m, (nE1 (m : ℚ) (x : ℚ)) ^ 2 = ((9/140)*(m:ℚ) + (3/8)*(m:ℚ)^2 + (-29/120)*(m:ℚ)^3 + (-1)*(m:ℚ)^4 + (-7/120)*(m:ℚ)^5 + (5/8)*(m:ℚ)^6 + (33/140)*(m:ℚ)^7) := by
  have h : ∀ t : ℚ, (nE1 (m : ℚ) t) ^ 2 = ((9 + (-11)*(m:ℚ) + (-95/36)*(m:ℚ)^2 + (8/3)*(m:ℚ)^3 + (29/18)*(m:ℚ)^4 + (1/3)*(m:ℚ)^5 + (1/36)*(m:ℚ)^6)) + ((33 + (-193/6)*(m:ℚ) + (-20/3)*(m:ℚ)^2 + 4*(m:ℚ)^3 + (5/3)*(m:ℚ)^4 + (1/6)*(m:ℚ)^5)) * t ^ 1 + (((193/4) + (-36)*(m:ℚ) + (-17/3)*(m:ℚ)^2 + 2*(m:ℚ)^3 + (5/12)*(m:ℚ)^4)) * t ^ 2 + ((36 + (-58/3)*(m:ℚ) + (-2)*(m:ℚ)^2 + (1/3)*(m:ℚ)^3)) * t ^ 3 + (((29/2) + (-5)*(m:ℚ) + (-1/4)*(m:ℚ)^2)) * t ^ 4 + ((3 + (-1/2)*(m:ℚ))) * t ^ 5 + (((1/4))) * t ^ 6 := by
    intro t; unfold nE1 nTri; ring
  simp only [h]
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul, nS1, nS2, nS3, nS4, nS5, nS6]
  ring

lemma nSumE2 (m : ℕ) : ∑ x ∈ range m, (nE2 (m : ℚ) (x : ℚ)) ^ 2 = ((9/140)*(m:ℚ) + (-3/8)*(m:ℚ)^2 + (-29/120)*(m:ℚ)^3 + 1*(m:ℚ)^4 + (-7/120)*(m:ℚ)^5 + (-5/8)*(m:ℚ)^6 + (33/140)*(m:ℚ)^7) := by
  have h : ∀ t : ℚ, (nE2 (m : ℚ) t) ^ 2 = ((9 + (-22)*(m:ℚ) + (121/9)*(m:ℚ)^2 + 4*(m:ℚ)^3 + (-44/9)*(m:ℚ)^4 + (4/9)*(m:ℚ)^6)) + ((33 + (-193/3)*(m:ℚ) + (88/3)*(m:ℚ)^2 + (22/3)*(m:ℚ)^3 + (-16/3)*(m:ℚ)^4)) * t ^ 1 + (((193/4) + (-72)*(m:ℚ) + (70/3)*(m:ℚ)^2 + 4*(m:ℚ)^3 + (-4/3)*(m:ℚ)^4)) * t ^ 2 + ((36 + (-116/3)*(m:ℚ) + 8*(m:ℚ)^2 + (2/3)*(m:ℚ)^3)) * t ^ 3 + (((29/2) + (-10)*(m:ℚ) + 1*(m:ℚ)^2)) * t ^ 4 + ((3 + (-1)*(m:ℚ))) * t ^ 5 + (((1/4))) * t ^ 6 := by
    intro t; unfold nE2 nTri; ring
  simp only [h]
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul, nS1, nS2, nS3, nS4, nS5, nS6]
  ring

lemma nSumE3 (m : ℕ) : ∑ x ∈ range m, (nE3 (m : ℚ) (x : ℚ)) ^ 2 = ((1/140)*(m:ℚ) + (-1/8)*(m:ℚ)^2 + (23/72)*(m:ℚ)^3 + (-1/3)*(m:ℚ)^4 + (61/360)*(m:ℚ)^5 + (-1/24)*(m:ℚ)^6 + (1/252)*(m:ℚ)^7) := by
  have h : ∀ t : ℚ, (nE3 (m : ℚ) t) ^ 2 = ((1 + (-11/3)*(m:ℚ) + (193/36)*(m:ℚ)^2 + (-4)*(m:ℚ)^3 + (29/18)*(m:ℚ)^4 + (-1/3)*(m:ℚ)^5 + (1/36)*(m:ℚ)^6)) + (((11/3) + (-193/18)*(m:ℚ) + 12*(m:ℚ)^2 + (-58/9)*(m:ℚ)^3 + (5/3)*(m:ℚ)^4 + (-1/6)*(m:ℚ)^5)) * t ^ 1 + (((193/36) + (-12)*(m:ℚ) + (29/3)*(m:ℚ)^2 + (-10/3)*(m:ℚ)^3 + (5/12)*(m:ℚ)^4)) * t ^ 2 + ((4 + (-58/9)*(m:ℚ) + (10/3)*(m:ℚ)^2 + (-5/9)*(m:ℚ)^3)) * t ^ 3 + (((29/18) + (-5/3)*(m:ℚ) + (5/12)*(m:ℚ)^2)) * t ^ 4 + (((1/3) + (-1/6)*(m:ℚ))) * t ^ 5 + (((1/36))) * t ^ 6 := by
    intro t; unfold nE3 nTri; ring
  simp only [h]
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul, nS1, nS2, nS3, nS4, nS5, nS6]
  ring

lemma nSumPhi (m : ℕ) :
    ∑ s ∈ range (4 * m), (nPhi m s) ^ 2 = (m : ℚ) * (151 * (m : ℚ) ^ 6 + 70 * (m : ℚ) ^ 4 + 49 * (m : ℚ) ^ 2 + 45) / 315 := by
  rw [show 4 * m = m + m + m + m by omega, sum_range_add, sum_range_add, sum_range_add]
  have hb0 : ∑ x ∈ range m, (nPhi m x) ^ 2 = ∑ x ∈ range m, (nE0 (m : ℚ) (x : ℚ)) ^ 2 :=
    sum_congr rfl (fun x hx => by rw [nPhi_blk0 m x (Finset.mem_range.1 hx)])
  have hb1 : ∑ x ∈ range m, (nPhi m (m + x)) ^ 2 = ∑ x ∈ range m, (nE1 (m : ℚ) (x : ℚ)) ^ 2 :=
    sum_congr rfl (fun x hx => by rw [nPhi_blk1 m x (Finset.mem_range.1 hx)])
  have hb2 : ∑ x ∈ range m, (nPhi m (m + m + x)) ^ 2 = ∑ x ∈ range m, (nE2 (m : ℚ) (x : ℚ)) ^ 2 :=
    sum_congr rfl (fun x hx => by rw [nPhi_blk2 m x (Finset.mem_range.1 hx)])
  have hb3 : ∑ x ∈ range m, (nPhi m (m + m + m + x)) ^ 2 = ∑ x ∈ range m, (nE3 (m : ℚ) (x : ℚ)) ^ 2 :=
    sum_congr rfl (fun x hx => by rw [nPhi_blk3 m x (Finset.mem_range.1 hx)])
  rw [hb0, hb1, hb2, hb3, nSumE0, nSumE1, nSumE2, nSumE3]
  ring

theorem itemL03 : ItemL03 := by
  unfold ItemL03
  intro m hm
  have hm0 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h1 : ∀ s : ℕ, (∑ i ∈ Finset.range (s + 1), fejerW m i * fejerW m (s - i)) ^ 2
      = (nPhi m s) ^ 2 / ((m : ℚ) ^ 4) ^ 2 := by
    intro s; rw [nSum_fejer]; ring
  simp only [h1]
  rw [← Finset.sum_div, nSumPhi]
  field_simp

end KappaOmega2
