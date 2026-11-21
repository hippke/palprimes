# Notes

The mathematics behind the Lean proof, written during the project.

| File | Content |
|---|---|
| `PROOF_buniform.md` | Level of distribution 1/4 − ε for palindromes in every base and the Ω ≤ 5 corollary: Lemma 3 (injectivity), Proposition V (Farey sums), b-uniform constants |
| `PROP_W.md`, `AUDIT_W.md` | Proposition W: prime-square divisors of palindromes without the Baier–Zhao large sieve, and its audit |
| `SIEVE_ROUTE.md` | The weighted sieve used in Lean: Selberg + Rankin + smooth-number bound, Buchstab, Richert weights, rational certificate |
| `LEAN_PLAN.md`, `LEAN_BLUEPRINT.md` | Formalization plan and statement map (milestones M1–M15) |
| `LEAN_AUDIT.md` | Verification of the final theorem (axioms, leanchecker, comparator with six kernels) |

The planning notes refer to the Lean files by their names during development. Map:

| development name | repository module |
|---|---|
| `PalLean/Defs` | `Palprimes/Defs` |
| `LemmaThree`, `ExpSum` | `Digits/LemmaThree`, `Digits/Palindromes` |
| `Collision`, `LargeSieve`, `Farey`, `Col` | `ExpSum/Collision`, `ExpSum/LargeSieve`, `ExpSum/Farey`, `ExpSum/ColBound` |
| `DivisorBound`, `Level` | `Level/DivisorBound`, `Level/Level` |
| `PropW` | `Squares/PropW` |
| `Mertens`, `Selberg` | `Sieve/Vendor/Mertens`, `Sieve/Vendor/Selberg` |
| `SieveG`, `SieveComb`, `SieveAsm`, `SieveSums` | `Sieve/SelbergSum`, `Sieve/Combinatorics`, `Sieve/Assembly`, `Sieve/PrimeSums` |
| `SieveMain`, `SieveFinal`, `SieveTot`, `SieveNum`, `SieveCert` | `Sieve/Bounds`, `Sieve/Intervals`, `Sieve/Totals`, `Sieve/Numerics`, `Sieve/Certificate` |
| `Sieve`, `Main` | `Sieve/Weighted`, `AlmostPrime/OmegaLeFive` |

The `r..` labels in the notes are research rounds of the project and are kept for reference.
