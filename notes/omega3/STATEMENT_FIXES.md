# Pending statement fixes (apply in one batch when no agent depends on the old text, then re-freeze)

- Lemma10Stmt (DefsSieve.lean:381, used by ItemM09 and as a hypothesis of ItemM10): false at n = 1 when p ≥ y
  (bfun y m p 1 = 0, statement says 1). Counterexample y = 2, m = 1, p = 5, n = 1, Lean proof of ¬Lemma10Stmt in
  /tmp/claude-1000/m09/M09check.lean (rechecked by the main session 2026-11-24). Fix: add hypothesis (p : ℝ) < y
  (Lemma 11 uses p < z = y^U < y). Check M10's use and the skeleton after the change. Found by the Haiku queue.

- SETTLED 21:47 (L11 PASS as stated, no fix). ItemL11 (flagged by Haiku queue 2, 2026-11-24 20:36, not confirmed): TL1w covers D in (x^θ₀, x^θ] only, SSStmt claims all
  D ≥ D₀. Lemma SS (r238 §2.4) is exactly the self-similarity that extends below the window, so the statement is probably
  right in intent; review against r238 §2.4 whether Lemma K or another input is needed as an extra hypothesis.
- ItemM03, ItemM06: flagged as "blocked" by Haiku (missing Mertens asymptotic with 1/φ weights; link Tpm vs Palprimes
  Splus). These look like missing proofs, not wrong statements. Sonnet queue retries them.

# Build notes (for the final assembly and audit)
- M12_KF.h2F_eq (~50 s, 10–12 GB) and M12_KC.restC_eq (~45 s) must be built one at a time (parallel build OOM at 12G).
- M10 uses Lemma 10 only through Lemma10LtStmt (p < y); after the Lemma10Stmt fix, lemma10Lt_of in M10_X.lean needs a one-line update.

# APPLIED 2026-11-24 21:52 (main session), skeleton and corollaries rebuilt, frozen.sha256 updated (old copies in reports/prefix_backup/)
1. Lemma10Stmt: added (p : ℝ) < y.
2. Lemma28Stmt: added 0 ≤ Td (L08 counterexample H = 0, Td = −1).
3. Lemma29wStmt: constant 6·(4D² + 2b·b^{2j}) (sharp MV constant not in Palprimes; 4N + 3/δ + 2 fits under 5×).
4. ItemS04 hypothesis and ItemS05 conjunct 6: only primes q with q²δ < y (S05 counterexample y = 101^{10/7}, δ = 101, q = 97).
Items to recheck/update: L10 (uses Lemma28Stmt, Lemma29wStmt), M10 (lemma10Lt_of), S04 (in progress), all others rebuilt.
- Lake .trace files double per helper import level (M11_S3b.trace reached 1.2 GB, lake build OOM at 14 GB); keep helper chains shallow. (from the M07/M11/L12 agent)

# APPLIED 2026-11-24 ~22:10 (main session), second batch, skeleton rebuilt, refrozen
5. ItemS04 hypothesis and ItemS05 conjunct 6 (replaces fix 4): 0 ≤ φ(δ) for all δ ∈ 𝒟, and w(q) ≤ φ(δ) for all primes
   q < p(δ) only when ω(δ) ≥ 3. Fix 4 made S04 false (A = 5005, y = 25025, z = 14, w(5) = 100: Σ₃ needs all q < p(δ)
   for ν ≥ 3); the S05 counterexample has δ prime. r182 §2: (3.10) holds for odd ν ≥ 3 from W(t) ≤ t − m.
6. ItemS02: added m ≤ 1 (Lean disproof for m = 2 in Omega3/Items/S02_Neg.lean); SkelSieve passes `by norm_num [mm]`.
