# Sanity checks of the item statements (run with system python3; logs in ../../logs/sanity_*.log)

| script | items | log |
|---|---|---|
| level_records.py | L01, L03, L04, L05, L06, L07, L16 | sanity_level_records.log |
| seq_small.py (needs level_records.py in the same folder) | L08, L09, L12, L13, L14, L17, Q01, Q02, Q03 | sanity_seq_small.log |
| greaves_comb.py | S01, S02 (radical form), S03, S04; first-run finding on non-squarefree a in NOTES §3 | sanity_greaves_comb.log |
| sieve_small.py | S06, S09 (exact part), S11 (support), S12, S13, M01 | sanity_sieve_small.log |
| analytic_checks.py | S05, S07, BandOK x_n, M03, M12/M13 (value of 𝓜(W)) | sanity_analytic.log |
| lemmaA_check.py | S08, S09, M02 (plausibility at finite level) | sanity_lemmaA.log |
| greaves_lemma10.py (arg `even` for the stated case) | M09 | sanity_lemma10.log |
| g4_check.py, g4_identity.py | M07, M08, M10, M11 (finite y ≤ 10⁶, pre-asymptotic) | sanity_g4.log, sanity_g4_identity.log |
Commands: `cd scripts/sanity && python3 <script> ../../logs/<log>` (greaves_comb.py and greaves_lemma10.py print to stdout).
