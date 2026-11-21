import Mathlib

/-!
# Shared definitions (blueprint S1)

Notation follows `r37_writeup/PROOF_buniform.md` and Tuxanidy–Panario v3 (TP).
Everything here is a definition; there are no `sorry`s in this file.
-/

open Finset Real

namespace Palprimes

/-- `e(t) = exp(2πit)`. -/
noncomputable def ee (t : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * t)

/-- `φ_b(t) = |Σ_{d<b} e(dt)|`. -/
noncomputable def phiB (b : ℕ) (t : ℝ) : ℝ := ‖∑ d ∈ range b, ee (d * t)‖

/-- `ψ(t) = (φ_b(t)/b)² ∈ [0, 1]`. -/
noncomputable def psiB (b : ℕ) (t : ℝ) : ℝ := (phiB b t / b) ^ 2

/-- `c_k = b^k + b^{2L−k}` for `k < L`, and `c_L = b^L` (middle digit). -/
def cK (b L k : ℕ) : ℕ := if k < L then b ^ k + b ^ (2 * L - k) else b ^ L

/-- `Π_K(α) = Π_{k∈K} ψ(c_k α)`. -/
noncomputable def piK (b L : ℕ) (K : Finset ℕ) (α : ℝ) : ℝ :=
  ∏ k ∈ K, psiB b (cK b L k * α)

/-- `n` is a palindrome in base `b`. -/
def IsPalindrome (b n : ℕ) : Prop := (Nat.digits b n).reverse = Nat.digits b n

instance (b : ℕ) : DecidablePred (IsPalindrome b) := fun n => by
  unfold IsPalindrome; infer_instance

/-- `b³ − b`. -/
def bigB (b : ℕ) : ℕ := b ^ 3 - b

/-- TP's `Π*_b(2N)`: palindromes with exactly `2N+1` digits, coprime to `b³ − b`. -/
def piStar (b N : ℕ) : Finset ℕ :=
  (Ico (b ^ (2 * N)) (b ^ (2 * N + 1))).filter
    (fun n => IsPalindrome b n ∧ Nat.Coprime n (bigB b))

/-- `A_d = #{n ∈ A : d ∣ n}`. -/
def countDvd (A : Finset ℕ) (d : ℕ) : ℕ := #(A.filter (d ∣ ·))

/-- `θ_b = log_b(3b²/(2b²+1))`. -/
noncomputable def thetaB (b : ℕ) : ℝ := Real.logb b (3 * b ^ 2 / (2 * b ^ 2 + 1))

/-- `η' = (θ_b/2)·min(κ/(1−κ), 1+θ_b)` (Proposition V). -/
noncomputable def etaPrime (b : ℕ) (κ : ℝ) : ℝ :=
  thetaB b / 2 * min (κ / (1 - κ)) (1 + thetaB b)

/-- Distance to the nearest integer, `‖t‖`. -/
noncomputable def distZ (t : ℝ) : ℝ := |t - round t|

/-- Reduced residues `h mod q`, `(h, q) = 1`. -/
def redRes (q : ℕ) : Finset ℕ := (range q).filter (fun h => Nat.Coprime h q)

/-- The Farey sum of Proposition V:
`Σ_{Q≤q≤2Q, (q,b)=1} Σ*_{h mod q} Π_{[0,L−1]}(h/q + β)`. -/
noncomputable def sumV (b L Q : ℕ) (β : ℝ) : ℝ :=
  ∑ q ∈ (Icc Q (2 * Q)).filter (fun q => Nat.Coprime q b),
    ∑ h ∈ redRes q, piK b L (range L) ((h : ℝ) / q + β)

/-- `τ* = max_{0<w<2b^{2L+1}} #{q ∈ [Q, 2Q] : q ∣ w}` (by symmetry `w > 0` suffices). -/
def tauStar (b L Q : ℕ) : ℕ :=
  (Icc 1 (2 * b ^ (2 * L + 1))).sup fun w => #((Icc Q (2 * Q)).filter (· ∣ w))

/-- Digit vector extended by zero: `Fin (L+1) → Fin b` read as `ℕ → ℕ`. -/
def extDig {b L : ℕ} (d : Fin (L + 1) → Fin b) (k : ℕ) : ℕ :=
  if h : k < L + 1 then (d ⟨k, h⟩ : ℕ) else 0

/-- `Y = Σ_{K1} (d_k + d'_k) c_k + Σ_{K2} d_k c_k` (doubled digits on `K1`, single on `K2`). -/
def yVal (b L : ℕ) (K1 K2 : Finset ℕ) (d d' : ℕ → ℕ) : ℕ :=
  ∑ k ∈ K1, (d k + d' k) * cK b L k + ∑ k ∈ K2, d k * cK b L k

/-- Digit vectors of length `L+1`. -/
abbrev DigVec (b L : ℕ) := Fin (L + 1) → Fin b

/-- TP's `Φ_N(α) = Π_{1≤n<N} φ_b(α(b^n + b^{2N−n}))`. -/
noncomputable def PhiN (b N : ℕ) (α : ℝ) : ℝ :=
  ∏ n ∈ Ico 1 N, phiB b (α * ((b : ℝ) ^ n + (b : ℝ) ^ (2 * N - n)))

/-- TP's `P_M(α) = Π_{1≤n≤M} φ_b(α(b^n + b^{2N−n}))`. -/
noncomputable def prodPM (b N M : ℕ) (α : ℝ) : ℝ :=
  ∏ n ∈ Icc 1 M, phiB b (α * ((b : ℝ) ^ n + (b : ℝ) ^ (2 * N - n)))

/-- Value of the palindrome with outer-to-middle digits `d_0, …, d_N`:
`Σ_{k<N} d_k (b^k + b^{2N−k}) + d_N b^N`. -/
def palVal (b N : ℕ) (d : DigVec b N) : ℕ := ∑ k : Fin (N + 1), (d k : ℕ) * cK b N k

end Palprimes
